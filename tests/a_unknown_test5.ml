open ISet

let a = empty
let a = add (-20, 5) a
let a = add (6, 18) a
let a = add (4, 10) a
let a = add (14, 16) a
let a = remove (-18, 14) a
let a = remove (5, 17) a;;

assert (mem 14 a = false)

let a = add (-4, 9) a;;

assert (mem 16 a = false);;
assert (mem (-14) a = false);;
assert (mem 10 a = false)

let a = remove (-9, 10) a
let a = add (-6, 7) a
let a = add (-2, 7) a
let a = add (-12, 17) a
let a = add (-13, 8) a
let a = add (-13, -2) a;;

assert (mem 11 a = true);;
assert (elements a = [ -20, -19; -13, 18 ])
