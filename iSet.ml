(** [a +% b = min max_int (a + b)], tylko bez overflowów. *)
let ( +% ) a b =
  match () with
  | _ when a > 0 -> min (min_int + a + b) (-1) - min_int
  | _ -> a + b

(** [a -% b = min max_int (a - b)] dla [a > b], tylko bez overflowów. *)
let ( -% ) a b =
  match () with
  | _ when Stdlib.compare a 0 = Stdlib.compare b 0 -> a - b
  | _ when a = min_int || b = min_int -> max_int
  | _ -> abs a +% abs b

type interval = int * int
(** Przedział liczb od [a] do [b] włącznie. *)

(** Porównuje dwa przedziały: ustalamy, że są równe jeżeli się przecinają. *)
let cmp (a, b) (a', b') =
  match () with
  | _ when max a a' <= min b b' +% 1 -> 0
  | _ when b < a' -> -1
  | _ -> 1

(** Tutaj jest moduł pSet bardzo mało modyfikowany. Wszystkie zmiany:

    1. typ wartości to zawsze [interval], porównanie to zawsze [cmp], więc
    PSet.t zostało troszeczkę uproszczone;

    2. każdy wierzchołek przechowuje "populację" -- liczbę liczb w przedziałach
    trzymanych w poddrzewie;

    3. [split x s] zwraca dokładną wartość elementu w drzewie równego [x] jeżeli
    taki istnieje.

    Ten moduł NIE ROZUMIE co to są przedziały, dopiero my później karmimy go
    tylko takimi przedziałami, że 1. nie ma sąsiednich; 2. wyszukujemy tylko
    takie, że się przecinają z co najwyżej jednym przedziałem z seta. *)

module PSet = struct
  (** Wierzchołek to lewy syn, wartość, prawy syn, wysokość poddrzewa, populacja
      poddrzewa. *)
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

(** Ta funkcja dzieli podzbiór *)
let intersect set (a, b) =
  let superleft, left, rest =
    PSet.split (a, if a > min_int then a - 1 else a) set
  in
  let _, right, superright =
    PSet.split ((if b < max_int then b + 1 else b), b) rest
  in
  let right = if Option.is_some right then right else left in
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
  PSet.merge superleft superright |> PSet.add (a', b')

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
  new_left, present, new_right

let empty = PSet.empty
let is_empty = PSet.is_empty
let elements = PSet.elements
let iter = PSet.iter
let fold = PSet.fold

let mem x set =
  let _, present, _ = split x set in
  present

let below x set =
  let lesser_than_x, x_present, _ = split x set in
  PSet.population lesser_than_x +% if x_present then 1 else 0

let remove (a, b) set =
  let lesser_than_a, _, _ = split a set in
  let _, _, greater_than_b = split b set in
  PSet.merge lesser_than_a greater_than_b
