(* conversion to and from coq*)

open BinInt
open BinPos
open Datatypes
open Big_int

let two_big_int = big_int_of_int 2

(* Coq to ML *)
module C2M = struct

let rec nat : nat -> int= function
  | O -> 0
  | S n -> 1 + nat n

let rec positive : positive -> big_int = function
  | Coq_xH -> unit_big_int
  | Coq_xO p -> shift_left_big_int (positive p) 1
  | Coq_xI p -> succ_big_int (shift_left_big_int (positive p) 1)

let zed = function
  | Z0 -> zero_big_int
  | Zpos p -> positive p
  | Zneg p -> minus_big_int (positive p)

end


module M2C = struct

let rec nat i : nat =
  if i <0 then failwith "Natural numbers are positive!";
  if i = 0 then O else S(nat (pred i))

let positive bi =
  let sgn = sign_big_int bi in
  if sgn <= 0 then failwith "Positive must be strictly positive!";
  let rec unsafe_pos bi =
    if eq_big_int unit_big_int bi then
      Coq_xH
    else
      if eq_big_int zero_big_int (mod_big_int bi two_big_int) then
        Coq_xO (unsafe_pos (shift_right_big_int bi 1))
      else
        Coq_xI (unsafe_pos (shift_right_big_int bi 1))
  in
  unsafe_pos bi


let zed bi =
  let sgn = sign_big_int bi in
  if sgn = 0 then Z0
  else if sgn <0 then
    Zneg (positive (minus_big_int bi))
  else
    Zpos (positive bi)
end

let z_of_string s =
  M2C.zed (big_int_of_string s)

let string_of_z z =
  string_of_big_int (C2M.zed z)

let pos_of_string s =
  M2C.positive (big_int_of_string s)

let string_of_pos p =
  string_of_big_int (C2M.positive p)

let smt_string_of_z z =
  let bi = C2M.zed z in
  let s = string_of_big_int (abs_big_int bi) in
  if lt_big_int bi zero_big_int then
    Printf.sprintf "(- %s)" s
  else
    s


