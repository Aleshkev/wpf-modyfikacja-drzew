(*
 * PSet - Polymorphic sets
 * Copyright (C) 1996-2003 Xavier Leroy, Nicolas Cannasse, Markus Mottl
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version,
 * with the special exception on linking described in file LICENSE.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *)

module PSet = struct
  type 'k set = Empty | Node of 'k set * 'k * 'k set * int
  type 'k t = { cmp : 'k -> 'k -> int; set : 'k set }

  let height = function
    | Node (_, _, _, h) -> h
    | Empty -> 0

  let make l k r = Node (l, k, r, max (height l) (height r) + 1)

  let bal l k r =
    let hl = height l in
    let hr = height r in
    if hl > hr + 2
    then
      match l with
      | Node (ll, lk, lr, _) -> (
          if height ll >= height lr
          then make ll lk (make lr k r)
          else
            match lr with
            | Node (lrl, lrk, lrr, _) ->
                make (make ll lk lrl) lrk (make lrr k r)
            | Empty -> assert false)
      | Empty -> assert false
    else if hr > hl + 2
    then
      match r with
      | Node (rl, rk, rr, _) -> (
          if height rr >= height rl
          then make (make l k rl) rk rr
          else
            match rl with
            | Node (rll, rlk, rlr, _) ->
                make (make l k rll) rlk (make rlr rk rr)
            | Empty -> assert false)
      | Empty -> assert false
    else Node (l, k, r, max hl hr + 1)

  let rec min_elt = function
    | Node (Empty, k, _, _) -> k
    | Node (l, _, _, _) -> min_elt l
    | Empty -> raise Not_found

  let rec remove_min_elt = function
    | Node (Empty, _, r, _) -> r
    | Node (l, k, r, _) -> bal (remove_min_elt l) k r
    | Empty -> invalid_arg "PSet.remove_min_elt"

  let merge t1 t2 =
    match t1, t2 with
    | Empty, _ -> t2
    | _, Empty -> t1
    | _ ->
        let k = min_elt t2 in
        bal t1 k (remove_min_elt t2)

  let create cmp = { cmp; set = Empty }
  let empty = { cmp = compare; set = Empty }
  let is_empty x = x.set = Empty

  let rec add_one cmp x = function
    | Node (l, k, r, h) ->
        let c = cmp x k in
        if c = 0
        then Node (l, x, r, h)
        else if c < 0
        then
          let nl = add_one cmp x l in
          bal nl k r
        else
          let nr = add_one cmp x r in
          bal l k nr
    | Empty -> Node (Empty, x, Empty, 1)

  let add x { cmp; set } = { cmp; set = add_one cmp x set }

  let rec join cmp l v r =
    match l, r with
    | Empty, _ -> add_one cmp v r
    | _, Empty -> add_one cmp v l
    | Node (ll, lv, lr, lh), Node (rl, rv, rr, rh) ->
        if lh > rh + 2
        then bal ll lv (join cmp lr v r)
        else if rh > lh + 2
        then bal (join cmp l v rl) rv rr
        else make l v r

  let split x { cmp; set } =
    let rec loop x = function
      | Empty -> Empty, None, Empty
      | Node (l, v, r, _) ->
          let c = cmp x v in
          if c = 0
          then l, Some v, r
          else if c < 0
          then
            let ll, pres, rl = loop x l in
            ll, pres, join cmp rl v r
          else
            let lr, pres, rr = loop x r in
            join cmp l v lr, pres, rr
    in
    let setl, pres, setr = loop x set in
    { cmp; set = setl }, pres, { cmp; set = setr }

  let remove x { cmp; set } =
    let rec loop = function
      | Node (l, k, r, _) ->
          let c = cmp x k in
          if c = 0
          then merge l r
          else if c < 0
          then bal (loop l) k r
          else bal l k (loop r)
      | Empty -> Empty
    in
    { cmp; set = loop set }

  let mem x { cmp; set } =
    let rec loop = function
      | Node (l, k, r, _) ->
          let c = cmp x k in
          c = 0 || loop (if c < 0 then l else r)
      | Empty -> false
    in
    loop set

  (* let exists = mem *)

  let iter f { set; _ } =
    let rec loop = function
      | Empty -> ()
      | Node (l, k, r, _) ->
          loop l;
          f k;
          loop r
    in
    loop set

  let fold f { set; _ } acc =
    let rec loop acc = function
      | Empty -> acc
      | Node (l, k, r, _) -> loop (f k (loop acc l)) r
    in
    loop acc set

  let elements { set; _ } =
    let rec loop acc = function
      | Empty -> acc
      | Node (l, k, r, _) -> loop (k :: loop acc r) l
    in
    loop [] set
end

type interval = int * int
type t = interval PSet.t

let cmp_interval (a, b) (a', b') =
  let b = b + 1 and b' = b' + 1 in
  if max a a' <= min b b' then 0 else if b < a' then -1 else 1

let string_of_interval (a, b) = Printf.sprintf "(%i, %i)" a b

let string_of_t t =
  "{" ^ String.concat "; " (List.map string_of_interval (PSet.elements t)) ^ "}"

let string_of_interval_option = function
  | Some x -> string_of_interval x
  | None -> "nil"

let empty = { PSet.empty with cmp = cmp_interval }
let is_empty = PSet.is_empty

let join (s : t) (z : t) =
  match s.set with
  | PSet.Empty -> z
  | Node (_, x, _, _) ->
      let s = PSet.remove x s in
      { empty with set = PSet.join s.cmp s.set x z.set }

let intersect set (a, b) =
  let superleft, left, rest = PSet.split (a, a - 1) set in
  let rest, right, superright = PSet.split (b + 1, b) rest in
  let right = if Option.is_some right then right else left in
  superleft, left, rest, right, superright

let add (a, b) set =
  let superleft, left, _, right, superright = intersect set (a, b) in
  let a' =
    match left with
    | Some (x, _) when x < a -> x
    | _ -> a
  and b' =
    match right with
    | Some (_, x) when x > b -> x
    | _ -> b
  in
  join superleft superright |> PSet.add (a', b')

let elements = PSet.elements
let iter = PSet.iter
let fold = PSet.fold

let split x set =
  let superleft, left, _, right, superright = intersect set (x, x - 1) in
  let new_left =
    match left with
    | Some (a, _) when a < x -> PSet.add (a, x - 1) superleft
    | _ -> superleft
  in
  let new_right =
    match right with
    | Some (_, b) when b > x -> PSet.add (x + 1, b) superright
    | _ -> superright
  in
  new_left, Option.is_some left, new_right

let mem x set =
  let _, present, _ = split x set in
  present

let below x set =
  let lesser_than_x, x_present, _ = split x set in
  if x_present then 1 else 0

let remove (a, b) set =
  let lesser_than_a, _, _ = split a set in
  let _, _, greater_than_b = split b set in
  join lesser_than_a greater_than_b

let from_elements = List.fold_left (fun set x -> add x set) empty

let test_intersect s x a b c d e =
  let s = from_elements s
  and a = from_elements a
  and c = from_elements c
  and e = from_elements e in
  let a', b', c', d', e' = intersect s x in
  Printf.printf "split %s on %s\n-> %s %s %s %s %s\n== %s %s %s %s %s\n"
    (string_of_t s) (string_of_interval x) (string_of_t a)
    (string_of_interval_option b)
    (string_of_t c)
    (string_of_interval_option d)
    (string_of_t e) (string_of_t a')
    (string_of_interval_option b')
    (string_of_t c')
    (string_of_interval_option d')
    (string_of_t e');
  print_endline
    (String.concat ", "
       (List.map (fun y -> string_of_int @@ cmp_interval x y) (elements s)))

let a = from_elements [ 1, 3; 5, 5; 7, 8; 9, 9; 11, 11 ]

let () =
  print_endline "hi!";
  print_endline @@ string_of_t a;
  test_intersect
    [ 1, 1; 3, 3; 5, 5; 7, 7; 9, 9 ]
    (2, 2) []
    (Some (1, 1))
    []
    (Some (3, 3))
    [ 5, 5; 7, 7; 9, 9 ];
  test_intersect
    [ 1, 1; 3, 3; 5, 5; 7, 7; 9, 9 ]
    (5, 5) [ 1, 1; 3, 3 ]
    (Some (5, 5))
    [] None [ 7, 7; 9, 9 ];
  test_intersect
    [ 1, 1; 3, 3; 5, 5; 7, 7; 9, 9 ]
    (5, 6) [ 1, 1; 3, 3 ]
    (Some (5, 5))
    []
    (Some (7, 7))
    [ 9, 9 ];
  test_intersect [ 1, 1; 3, 6; 8, 8 ] (3, 3) [ 1, 1 ]
    (Some (3, 6))
    []
    (Some (3, 6))
    [ 8, 8 ]
