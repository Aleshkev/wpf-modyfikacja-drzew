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

(* Zmiany:

   -> dodana populacja drzewa

   -> [split x s] zwraca dokładną wartość elementu [x] zamiast tylko informacji
   czy występuje

   -> typ to zawsze [interval], porównanie to zawsze [cmp_interval] *)

type interval = int * int

let debug s = Printf.printf "%s" s
let m = -min_int;;

assert (min_int = -m && max_int = m - 1)

let ( +% ) a b = if a > 0 then min (-m + a + b) (-1) + m else a + b

let ( -% ) a b =
  let r =
    if Stdlib.compare a 0 = Stdlib.compare b 0
    then a - b
    else if a == min_int || b == min_int
    then max_int
    else abs a +% abs b
  in
  (* debug @@ Printf.sprintf "  ( -%% ) %i %i -> %i\n" a b r; *)
  r

(* let debug _ = () *)

let cmp (a, b) (a', b') =
  let r = if max a a' <= min b b' +% 1 then 0 else if b < a' then -1 else 1 in
  (* debug @@ Printf.sprintf " cmp (%i, %i) (%i, %i) -> %i\n" a b a' b' r; *)
  r

module PSet = struct
  type t = Empty | Node of t * interval * t * int * int

  let height = function
    | Node (_, _, _, h, _) -> h
    | Empty -> 0

  let population = function
    | Node (_, _, _, _, p) -> p
    | Empty -> 0

  let add_population l r (a, b) = population l +% population r +% (b -% a) +% 1

  let make l k r =
    Node (l, k, r, max (height l) (height r) + 1, add_population l r k)

  let bal l k r =
    let hl = height l in
    let hr = height r in
    if hl > hr + 2
    then
      match l with
      | Node (ll, lk, lr, _, _) -> (
          if height ll >= height lr
          then make ll lk (make lr k r)
          else
            match lr with
            | Node (lrl, lrk, lrr, _, _) ->
                make (make ll lk lrl) lrk (make lrr k r)
            | Empty -> assert false)
      | Empty -> assert false
    else if hr > hl + 2
    then
      match r with
      | Node (rl, rk, rr, _, _) -> (
          if height rr >= height rl
          then make (make l k rl) rk rr
          else
            match rl with
            | Node (rll, rlk, rlr, _, _) ->
                make (make l k rll) rlk (make rlr rk rr)
            | Empty -> assert false)
      | Empty -> assert false
    else make l k r

  let rec min_elt = function
    | Node (Empty, k, _, _, _) -> k
    | Node (l, _, _, _, _) -> min_elt l
    | Empty -> raise Not_found

  let rec remove_min_elt = function
    | Node (Empty, _, r, _, _) -> r
    | Node (l, k, r, _, _) -> bal (remove_min_elt l) k r
    | Empty -> invalid_arg "PSet.remove_min_elt"

  let merge t1 t2 =
    match t1, t2 with
    | Empty, _ -> t2
    | _, Empty -> t1
    | _ ->
        let k = min_elt t2 in
        bal t1 k (remove_min_elt t2)

  (* let create cmp = { cmp; set = Empty } *)
  let empty = Empty
  let is_empty x = x = Empty

  let rec add_one x = function
    | Node (l, k, r, _, _) ->
        let c = cmp x k in
        if c = 0
        then make l x r
        else if c < 0
        then
          let nl = add_one x l in
          bal nl k r
        else
          let nr = add_one x r in
          bal l k nr
    | Empty -> make Empty x Empty

  let add x set = add_one x set

  let rec join l v r =
    match l, r with
    | Empty, _ -> add_one v r
    | _, Empty -> add_one v l
    | Node (ll, lv, lr, lh, _), Node (rl, rv, rr, rh, _) ->
        if lh > rh + 2
        then bal ll lv (join lr v r)
        else if rh > lh + 2
        then bal (join l v rl) rv rr
        else make l v r

  let split x set =
    let rec loop x = function
      | Empty -> Empty, None, Empty
      | Node (l, v, r, _, _) ->
          let c = cmp x v in
          if c = 0
          then l, Some v, r
          else if c < 0
          then
            let ll, pres, rl = loop x l in
            ll, pres, join rl v r
          else
            let lr, pres, rr = loop x r in
            join l v lr, pres, rr
    in
    let setl, pres, setr = loop x set in
    setl, pres, setr

  let remove x set =
    let rec loop = function
      | Node (l, k, r, _, _) ->
          let c = cmp x k in
          if c = 0
          then merge l r
          else if c < 0
          then bal (loop l) k r
          else bal l k (loop r)
      | Empty -> Empty
    in
    loop set

  let mem x set =
    let rec loop = function
      | Node (l, k, r, _, _) ->
          let c = cmp x k in
          c = 0 || loop (if c < 0 then l else r)
      | Empty -> false
    in
    loop set

  let iter f set =
    let rec loop = function
      | Empty -> ()
      | Node (l, k, r, _, _) ->
          loop l;
          f k;
          loop r
    in
    loop set

  let fold f set acc =
    let rec loop acc = function
      | Empty -> acc
      | Node (l, k, r, _, _) -> loop (f k (loop acc l)) r
    in
    loop acc set

  let elements set =
    let rec loop acc = function
      | Empty -> acc
      | Node (l, k, r, _, _) -> loop (k :: loop acc r) l
    in
    loop [] set
end

type t = PSet.t

let string_of_interval (a, b) = Printf.sprintf "(%i, %i)" a b

let string_of_t t =
  "{ "
  ^ String.concat "; " (List.map string_of_interval (PSet.elements t))
  ^ " }"

let string_of_interval_option = function
  | Some x -> string_of_interval x
  | None -> "nil"

let empty = PSet.empty
let is_empty = PSet.is_empty

let intersect set (a, b) =
  let superleft, left, rest =
    PSet.split (a, if a > min_int then a - 1 else a) set
  in
  let _, right, superright =
    PSet.split ((if b < max_int then b + 1 else b), b) rest
  in
  let right = if Option.is_some right then right else left in
  let a', b', d, e = superleft, left, right, superright in
  (* debug @@ Printf.sprintf " intersect %s %s -> %s %s %s %s\n" (string_of_t
     set) (string_of_interval (a, b)) (string_of_t a')
     (string_of_interval_option b') (string_of_interval_option d) (string_of_t
     e); *)
  superleft, left, right, superright

let add (a, b) set =
  let superleft, left, right, superright = intersect set (a, b) in
  let a' =
    match left with
    | Some (x, _) when x < a -> x
    | _ -> a
  and b' =
    match right with
    | Some (_, x) when x > b -> x
    | _ -> b
  in
  let r = PSet.merge superleft superright |> PSet.add (a', b') in
  (* debug
  @@ Printf.sprintf "  add (%i, %i) %s -> %s\n" a b (string_of_t set)
       (string_of_t r); *)
  r

let elements = PSet.elements
let iter = PSet.iter
let fold = PSet.fold

let split x set =
  let superleft, left, right, superright =
    intersect set (x, if x > min_int then x - 1 else x)
  in
  let new_left =
    match left with
    | Some (a, _) when a < x -> PSet.add (a, x - 1) superleft
    | _ -> superleft
  and present =
    match left with
    | Some (_, b) when x <= b -> true
    | _ -> false
  and new_right =
    match right with
    | Some (_, b) when b > x -> PSet.add (x + 1, b) superright
    | _ -> superright
  in
  (* debug
  @@ Printf.sprintf "  split %s %s -> %s %s %s\n" (string_of_int x)
       (string_of_t set) (string_of_t new_left) (string_of_bool present)
       (string_of_t new_right); *)
  new_left, present, new_right

let mem x set =
  let a, present, b = split x set in
  present

let below x set =
  let lesser_than_x, x_present, _ = split x set in
  let r = PSet.population lesser_than_x +% if x_present then 1 else 0 in
  (* debug @@ Printf.sprintf "  below %i %s -> %i\n" x (string_of_t set) r; *)
  r

let remove (a, b) set =
  let lesser_than_a, _, _ = split a set in
  let _, _, greater_than_b = split b set in
  let r = PSet.merge lesser_than_a greater_than_b in
  (* debug @@ Printf.sprintf " remove %s %s -> %s\n" (string_of_interval (a, b))
     (string_of_t set) (string_of_t r); *)
  r

let from_elements = List.fold_left (fun set x -> add x set) empty

(* let test_intersect s x a b d e = let s = from_elements s and a =
   from_elements a and e = from_elements e in let a', b', d', e' = intersect s x
   in Printf.printf " split %s on %s\n-> %s %s %s %s\n== %s %s %s %s\n"
   (string_of_t s) (string_of_interval x) (string_of_t a)
   (string_of_interval_option b) (string_of_interval_option d) (string_of_t e)
   (string_of_t a') (string_of_interval_option b') (string_of_interval_option
   d') (string_of_t e'); print_endline (String.concat ", " (List.map (fun y ->
   string_of_int @@ cmp x y) (elements s)))

   let a = from_elements [ 1, 3; 5, 5; 7, 8; 9, 9; 11, 11 ]

   let () = print_endline "hi!"; print_endline @@ string_of_t a; test_intersect
   [ 1, 1; 3, 3; 5, 5; 7, 7; 9, 9 ] (2, 2) [] (Some (1, 1)) (Some (3, 3)) [ 5,
   5; 7, 7; 9, 9 ]; test_intersect [ 1, 1; 3, 3; 5, 5; 7, 7; 9, 9 ] (5, 5) [ 1,
   1; 3, 3 ] (Some (5, 5)) None [ 7, 7; 9, 9 ]; test_intersect [ 1, 1; 3, 3; 5,
   5; 7, 7; 9, 9 ] (5, 6) [ 1, 1; 3, 3 ] (Some (5, 5)) (Some (7, 7)) [ 9, 9 ];
   test_intersect [ 1, 1; 3, 6; 8, 8 ] (3, 3) [ 1, 1 ] (Some (3, 6)) (Some (3,
   6)) [ 8, 8 ]; test_intersect [ 10, 12 ] (13, 12) [ 10, 12 ] None None [] *)
