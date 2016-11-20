open OCamlInterface
open Conversions
open SimpleLanguage
open BinPos
open BinInt

(* aliases *)
type coq_Z =  BinInt.coq_Z
type bin_opp = Instructions.coq_Binary_opp

(* in the raw AST, and array ident is a string, same for a variable *)
type array_ident = string
type variable_ident = string

(* an expression, of the form 3 * i + 5 * N + 5 *)
type short_z_expression = coq_Z * (variable_ident option)
type z_expression =  short_z_expression list

(* an array access, of the form t[3 * i ...][5] *)
type array_access =
    array_ident * z_expression list

type expression =
  | Exp_Z_expression of short_z_expression
  | Exp_array_access of array_access
  | Exp_Bin_opp of expression * bin_opp * expression
  | Exp_Opp of expression

type instruction =
    { i_write_loc: array_access;
      i_body: expression;
      i_loop_vars: string list;
      i_body_string: string}

type naked_statement =
  | NLoop of variable_ident * z_expression * z_expression * (naked_statement list)
  | NInstr of instruction

(* the name of the global variables *)
let names_of_global_vars = ref []

(* find_global_variables udate in place the hash table glob_vars (même
   pas peur) and returns the number of global variables found *)

let find_variables prog =
  let glob_vars = Hashtbl.create 19 in
  let local_variables = Hashtbl.create 19 in
  let arrays = Hashtbl.create 19 in
  let next_array_id = ref BinPos.Coq_xH in

  let add_array_id id =
    if not (Hashtbl.mem arrays id) then
      let () = Hashtbl.add arrays id !next_array_id in
      next_array_id := BinPos.coq_Psucc !next_array_id in

  let check_variable var num_glob_vars =
    if Hashtbl.mem local_variables var || Hashtbl.mem glob_vars var then
      num_glob_vars
    else
      let () = Hashtbl.add glob_vars var num_glob_vars in
      succ num_glob_vars in

  let rec aux_short_z_expr num_glob_vars (szexp: short_z_expression) =
    match snd szexp with
    | None -> num_glob_vars
    | Some var -> check_variable var num_glob_vars

  and aux_z_expr num_glob_vars zexpr =
    List.fold_left aux_short_z_expr num_glob_vars zexpr

  and aux_expression num_glob_vars = function
    | Exp_Z_expression  szexp -> aux_short_z_expr num_glob_vars szexp
    | Exp_array_access (array_id, zexps) ->
        add_array_id array_id;
        List.fold_left aux_z_expr num_glob_vars zexps
    | Exp_Bin_opp (exp1, _, exp2) ->
        aux_expression (aux_expression num_glob_vars exp1) exp2
    | Exp_Opp exp -> aux_expression num_glob_vars exp

  and aux_instr num_glob_vars (p: instruction) =
    add_array_id (fst p.i_write_loc);
    aux_expression (List.fold_left aux_z_expr num_glob_vars (snd p.i_write_loc)) p.i_body

  and aux_stmt num_glob_vars = function
    | NLoop (vid, lb, ub, stmts) ->
        Hashtbl.add local_variables vid ();
        let num1 = aux_z_expr num_glob_vars lb in
        let num2 = aux_z_expr num1 ub in
        let res = List.fold_left aux_stmt num2 stmts in
        Hashtbl.remove local_variables vid;
        res
    | NInstr i -> aux_instr num_glob_vars i in
  let nbr_global_parameters = List.fold_left aux_stmt 0 prog in
  let a = Array.make nbr_global_parameters "" in
  Hashtbl.iter (fun k i -> a.(i) <- k) glob_vars;
  names_of_global_vars := List.rev (Array.to_list a);
  (nbr_global_parameters, arrays, glob_vars)

let z_one = BinInt.coq_Zsucc BinInt.Z0

let program_of_naked_statement_list prog =
  let nbr_global_parameters, array_idents, vars = find_variables prog in
  let nbr_var = ref nbr_global_parameters in
  let get_array_id name = Hashtbl.find array_idents name in
  let get_nbr_var oname =
    match oname with
    | None -> !nbr_var
    | Some name -> Hashtbl.find vars name in
  let enter_loop name = Hashtbl.add vars name !nbr_var; incr nbr_var in
  let exit_loop name = Hashtbl.remove vars name; decr nbr_var in
  let trans_short_z_expr ((v, oname):short_z_expression) =
    let a = Array.make (succ !nbr_var) BinInt.Z0 in
    a.(get_nbr_var oname) <- v;
    List.rev (Array.to_list a) in
  let trans_z_expr zexpr =
    let a = Array.make (succ !nbr_var) BinInt.Z0 in
    List.iter (fun (v, oname) ->
      let i = get_nbr_var oname in
        a.(i) <- BinInt.coq_Zplus a.(i) v) zexpr;
    List.rev (Array.to_list a) in
  let rec trans_expression = function
    | Exp_Z_expression szexpr -> PExp_const (trans_short_z_expr szexpr)
    | Exp_array_access (name, zexprs) -> PExp_loc (get_array_id name, List.map trans_z_expr zexprs)
    | Exp_Bin_opp (lexpr, opp, rexpr) -> PExp_bin (trans_expression lexpr, opp, trans_expression rexpr)
    | Exp_Opp expr -> PExp_opp (trans_expression expr) in
  let trans_instruction instr  =
    match
      make_Instruction
        {  coq_Pnumber_of_arguments = M2C.nat !nbr_var;
           coq_Pwrite_loc = (get_array_id (fst instr.i_write_loc), List.map trans_z_expr (snd instr.i_write_loc));
           coq_Pbody = trans_expression instr.i_body;
           coq_Pinstr_loop_vars = instr.i_loop_vars;
           coq_Pinstr_body_string= instr.i_body_string} with
    | None -> assert false
    | Some i -> i in
  let rec trans_naked_statement = function
    | NLoop (var_name, lb, ub, body) ->
        let plb = [(z_one, trans_z_expr lb)] in
        let pub = [(z_one, trans_z_expr ub)] in
        enter_loop var_name;
        let res = PLoop (plb, pub, trans_nstatement_list body) in
        exit_loop var_name;
        res
    | NInstr i -> PInstr (trans_instruction i, ext_ZMidentity (M2C.nat !nbr_var))
  and trans_nstatement_list = function
    | [] -> Pstl_nil
    | hd :: tl -> Pstl_cons (trans_naked_statement hd, trans_nstatement_list tl)
  in
  match make_Program { coq_Pprog_nbr_global_parameters = M2C.nat nbr_global_parameters;
                       coq_Pprog_main = trans_nstatement_list prog} with
  | None -> assert false
  | Some p -> p
