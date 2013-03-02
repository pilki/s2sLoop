Require Import Libs.
(*Require Import Floats.*)
Require Import AST.
Require Import Setoid.
Require Import ArithClasses.
Require Import Memory.
Require Import Instructions.
Require Import Bounds.

Parameter ocaml_string: Type.
Extract Constant ocaml_string =>
  "string".


Module BM := BMem(ZNum).


Module Instructions <:INSTRS(ZNum) with Definition Value := BM.Value.
  Module T := Tools(ZNum).
  Import T.


  (* The values of the language *)
  Definition Value := BM.Value.

  Inductive Binary_opp:=
  | BO_add
  | BO_mul
  | BO_sub
  | BO_div.

  Inductive Expression (n:nat) : Type :=
  | Exp_const: ZVector (S n) -> Expression n
  | Exp_loc: Array_Id * list (ZVector (S n)) -> Expression n
  | Exp_bin: Expression n -> Binary_opp -> Expression n -> Expression n
  | Exp_opp: Expression n -> Expression n.




  Record Instruction': Type :=
    { context_size: nat;
      write_loc: Array_Id * list (ZVector (S context_size));
      body: Expression context_size;
      (* what follows is here for pretty printing reasons *)
      instr_loop_vars : list ocaml_string;
      instr_body_string: ocaml_string
    }.

  Definition Instruction := Instruction'.

  Fixpoint exp_read_locs {n} (exp: Expression n) :=
    match exp with
      | Exp_const _ => []
      | Exp_loc loc => [loc]
      | Exp_bin l _ r => exp_read_locs l ++ exp_read_locs r
      | Exp_opp e => exp_read_locs e
    end.


  Definition read_locs instr:=
    exp_read_locs (body instr).

  Definition eval_bin_opp opp arg1 arg2 :=
    match opp with
    | BO_add => Some (arg1 + arg2)
    | BO_mul => Some (arg1 * arg2)
    | BO_sub => Some (arg1 - arg2)
    | BO_div => if arg2 == 0 then None else Some (arg1 / arg2)
  end.

  Fixpoint eval_exp {n}  ectxt (exp: Expression n) rvals :
    option (Value * list Value):=
    match exp with
    | Exp_const v => Some (〈v, ectxt〉, rvals)
    | Exp_loc _ =>
      match rvals with
      | [] => None
      | z :: rvals' =>
        Some (z, rvals')
      end
    | Exp_bin l opp r =>
      do{;
        (zl, rvals1) <- eval_exp ectxt l rvals;;
        (zr, rvals2) <- eval_exp ectxt r rvals1;;
        res <- eval_bin_opp opp zl zr;
        Some (res, rvals2)
      }
    | Exp_opp e =>
      do (res, rvals') <- eval_exp ectxt e rvals;
      Some (- res, rvals')
    end.


  Definition semantics (instr:Instruction) ctxt rvals res : Prop :=
    eval_exp (1:::ctxt) instr.(body) rvals = Some(res, []).

  Lemma semantics_deterministic:
    forall i v lv val1 val2,
      semantics i v lv val1 -> semantics i v lv val2 -> val1 = val2.
  Proof.
    unfold semantics; intros; congruence.
  Qed.
End Instructions.
