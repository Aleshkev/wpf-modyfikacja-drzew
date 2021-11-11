(** [a +% b = min max_int (a + b)], tylko bez overflowów. *)
let ( +% ) a b =
  match () with
  | _ when a > 0 -> min (min_int + a + b) (-1) - min_int
  | _ -> a + b

(** [a -% b = min max_int (a - b)] dla [a > b], tylko bez overflowów. *)
let rec ( -% ) a b =
  match () with
  | _ when a < b -> -(b -% a)
  | _ when Stdlib.compare a 0 = Stdlib.compare b 0 -> a - b
  | _ when a = min_int || b = min_int -> max_int
  | _ -> abs a +% abs b

type interval = int * int
(** Przedział liczb od [a] do [b] włącznie. *)

(** Porównuje dwa przedziały: ustalamy, że są "równe" jeżeli tworzą spójny
    przedział liczb. *)
let cmp (a, b) (a', b') =
  match () with
  | _ when max a a' <= min b b' +% 1 -> 0
  | _ when b < a' -> -1
  | _ -> 1

(** Tutaj jest moduł pSet bardzo lekko zmodyfikowany. Wszystkie zmiany:

    1. typ wartości to zawsze [interval], porównanie to zawsze [cmp], więc
    PSet.t zostało troszeczkę uproszczone;

    2. każdy wierzchołek przechowuje "populację" -- liczbę liczb w przedziałach
    trzymanych w poddrzewie;

    3. [split x s] zwraca dokładną wartość elementu w drzewie równego [x] jeżeli
    taki istnieje;

    4. funkcje [remove] i [mem] zostały usunięte, bo nie były używane.

    Ten moduł NIE ROZUMIE co to są przedziały przekształcając swoje drzewko,
    dopiero my karmimy go tylko takimi przedzialikami, że nie ma żadnych
    sąsiednich, i wyszukujemy tylko takie, że są "równe" co najwyżej jednej
    wartości w drzewku. *)

module PSet = struct
  (* PSet - Polymorphic sets

     Copyright (C) 1996-2003 Xavier Leroy, Nicolas Cannasse, Markus Mottl

     This library is free software; you can redistribute it and/or modify it
     under the terms of the GNU Lesser General Public License as published by
     the Free Software Foundation; either version 2.1 of the License, or (at
     your option) any later version, with the special exception on linking
     described in file LICENSE.

     This library is distributed in the hope that it will be useful, but WITHOUT
     ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
     FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public License
     for more details.

     You should have received a copy of the GNU Lesser General Public License
     along with this library; if not, write to the Free Software Foundation,
     Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA *)

  (** Wierzchołek to lewy syn, wartość, prawy syn, wysokość poddrzewa, populacja
      poddrzewa. Puste drzewo to [Empty]. *)
  type t = Empty | Node of t * interval * t * int * int

  let height = function
    | Node (_, _, _, h, _) -> h
    | Empty -> 0

  let population = function
    | Node (_, _, _, _, p) -> p
    | Empty -> 0

  let make l k r =
    let add_populations l r (a, b) =
      population l +% population r +% (b -% a) +% 1
    in
    Node (l, k, r, max (height l) (height r) + 1, add_populations l r k)

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

(** Dla przedziału [(a, b)] zwraca [left] i [right] -- najbardziej na lewo i na
    prawo przedziały z seta, które są "równe" [(a, b)], jeśli istnieją, mogą być
    tym samym przedziałem -- oraz [prefix] i [suffix] -- sety z przedziałami na
    lewo od [left] i na prawo od [right]. Wszystko pomiędzy [left] a [right]
    wyrzucamy bo nie jest potrzebne. *)
let intersect set (a, b) =
  (* Przedział (a, a - 1) wyobrazić sobie należy jako przedział sąsiadujący z
     (_, a - 1), ale nie (a, _) -- żeby był "równy" co najwyżej jednej wartości
     na secie. Uważamy też na overflowy intów. *)
  let prefix, left, rest = PSet.split (a, a -% 1) set in
  let _, right, suffix = PSet.split (b +% 1, b) rest in
  let right = if Option.is_some right then right else left in
  prefix, left, right, suffix

let add (a, b) set =
  (* Znajdujemy skrajne przedziały sąsiadujące/przecinające się z (a, b),
     łączymy je jeśli istnieją a jeśli nie to bierzemy (a, b); zachowujemy
     wszystko na lewo i na prawo. *)
  let prefix, left, right, suffix = intersect set (a, b) in
  let a' =
    match left with
    | Some (x, _) when x < a -> x
    | _ -> a
  and b' =
    match right with
    | Some (_, x) when x > b -> x
    | _ -> b
  in
  PSet.merge prefix suffix |> PSet.add (a', b')

let split x set =
  (* Znajdujemy skrajne przedziały sąsiadujące/przecinające się z (x, x),
     sprawdzamy czy zawierają x-a, kawałkujemy żeby nie zawierały i doklejamy
     kawałki do zachowanych wartości z lewej/prawej. *)
  let prefix, left, right, suffix = intersect set (x, x) in
  let prefix' =
    match left with
    | Some (a, _) when a < x -> prefix |> PSet.add (a, x - 1)
    | _ -> prefix
  and contains_x =
    match left with
    | Some (_, b) when x <= b -> true
    | _ -> false
  and suffix' =
    match right with
    | Some (_, b) when b > x -> suffix |> PSet.add (x + 1, b)
    | _ -> suffix
  in
  prefix', contains_x, suffix'

let empty = PSet.empty
let is_empty = PSet.is_empty
let elements = PSet.elements
let iter = PSet.iter
let fold = PSet.fold

let mem x set =
  let _, contains_x, _ = split x set in
  contains_x

let below x set =
  let lesser_than_x, contains_x, _ = split x set in
  PSet.population lesser_than_x +% if contains_x then 1 else 0

let remove (a, b) set =
  let lesser_than_a, _, _ = split a set in
  let _, _, greater_than_b = split b set in
  PSet.merge lesser_than_a greater_than_b
