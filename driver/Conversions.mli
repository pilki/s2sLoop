val two_big_int : Big_int.big_int
module C2M :
  sig
    val nat : Datatypes.nat -> int
    val positive : BinPos.positive -> Big_int.big_int
    val zed : BinInt.coq_Z -> Big_int.big_int
  end
module M2C :
  sig
    val nat : int -> Datatypes.nat
    val positive : Big_int.big_int -> BinPos.positive
    val zed : Big_int.big_int -> BinInt.coq_Z
  end
val z_of_string : string -> BinInt.coq_Z
val string_of_z : BinInt.coq_Z -> string

val pos_of_string : string -> BinPos.positive
val string_of_pos : BinPos.positive -> string


val smt_string_of_z : BinInt.coq_Z -> string
