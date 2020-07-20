open Optimized.Judge

let s1 = read_line ()
let s2 = read_line ()

let _ = Printf.printf "%s\n" (string_of_bool (judge_string (explode s1) (explode s2)))
