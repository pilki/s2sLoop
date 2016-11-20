open OCamlInterface
open Conversions
open SimpleLanguage.Instructions
open BinPos
open BinInt
open ParsingHelp
open Printf
open PolyBase
open SV.Per.Til.EP.P
open BoxedPolyhedra

type printer =
    {p : 'a.('a, out_channel, unit) format -> 'a}

let rev_split n l =
  let rec aux n l acc =
    if n = 0 then (acc, l)
    else
      match l with
      | [] -> assert false
      | h::t ->
          aux (pred n) t (h::acc)
  in
  aux n l []


let print_poly p nbr_global_parameters depth poly =
  let p = p.p in
  p "%i %i\n" (List.length poly) (1 + 1 + nbr_global_parameters + depth);
  List.iter (fun c ->
    (match c.constr_comp with
    | EQ -> p "  0"
    | GE -> p "  1");
    let fst_part, snd_part = rev_split depth c.constr_vect in
    List.iter (fun z -> p " %s" (string_of_z z)) fst_part;
    List.iter (fun z -> p " %s" (string_of_z z)) snd_part;
    p " %s\n" (string_of_z (coq_Zopp c.constr_val))) poly

let print_line_no_prefix p depth l =
  let p = p.p in
  match l with
  | [] -> assert false
  | const :: l ->
  let fst_part, snd_part = rev_split depth l in
  List.iter (fun z -> p " %s" (string_of_z z)) fst_part;
  List.iter (fun z -> p " %s" (string_of_z z)) snd_part;
  p " %s\n" (string_of_z const)


let print_matrix pr nbr_global_parameters depth mat =
  let p = pr.p in
  p "%i %i\n" (List.length mat) (1 + 1 + nbr_global_parameters + depth);
  List.iter (fun l ->
    p "  0";
    print_line_no_prefix pr depth l
            ) mat

let print_access pr depth (array_id, accesses) =
  let p = pr.p in
  p "  %s" (string_of_pos array_id);
  let (_:bool) = List.fold_left (fun add_0 access->
    if add_0 then p "  0";
    print_line_no_prefix pr depth access;
    true) false accesses in ()


let print_statement pr pnl nbr_global_parameters num_stmt stmt =
  let p = pr.p in
  let depth = C2M.nat stmt.pi_depth in
  p "# =============================================== Statement %i\n" num_stmt;
  p "# ----------------------------------------------  %i.1 Domain\n" num_stmt;
  pnl "# Iteration domain";
  pnl "1";
  print_poly pr nbr_global_parameters depth stmt.pi_poly.bp_poly;

  p "\n# ----------------------------------------------  %i.2 Scattering\n" num_stmt;
  pnl "# Scattering function is provided";
  pnl "1";
  pnl "# Scattering function";
  print_matrix pr nbr_global_parameters depth stmt.pi_schedule;

  p "\n# ----------------------------------------------  %i.3 Access\n" num_stmt;
  pnl "# Access informations are provided";
  pnl "1";
  pnl "# Read access informations";
  let rlocs = read_locs stmt.pi_instr in
  let nbr_lines = List.fold_left (fun acc l -> acc + List.length (snd l)) 0 rlocs in
  p "%i %i\n" nbr_lines (1 + 1 + nbr_global_parameters + depth);
  List.iter (print_access pr depth) rlocs;
  let wlocs = write_loc stmt.pi_instr in
  let nbr_lines = List.length (snd wlocs) in
  p "%i %i\n" nbr_lines (1 + 1 + nbr_global_parameters + depth);
  print_access pr depth wlocs;

  p "\n# ----------------------------------------------  %i.4 Body\n" num_stmt;
  pnl "# Statement body is provided";
  pnl "1";
  pnl "# Original iterator names";
  List.iter (p " %s") (List.rev stmt.pi_instr.instr_loop_vars);
  pnl "";
  pnl "# Statement body";
  pnl stmt.pi_instr.instr_body_string;
  p "\n\n"



(* printing Poly_Program *)
let print_pp out (pprog: coq_Poly_Program) =
  let nbr_global_parameters =C2M.nat pprog.pp_nbr_global_parameters in
  assert ( nbr_global_parameters = List.length !names_of_global_vars);
  let p s = fprintf out s in
  let pr = {p} in
  let pnl = p "%s\n" in
  pnl "SCoP";
  pnl "# =============================================== Global";
  pnl "# Language";
  pnl "C";
  pnl "";
  pnl "# Context";
  p "0 %i\n" (2 + List.length !names_of_global_vars);
  pnl "";
  pnl "# Parameter names are provided";
  pnl "1";
  pnl "# Parameter names";
  let (_ : string) =
    List.fold_left (fun sp name -> p "%s%s" sp name; " ") "" !names_of_global_vars in
  pnl "";
  pnl "# Number of statements";
  p "%i\n\n" (List.length pprog.pp_poly_instrs);
  let (_:int) = List.fold_left (fun num_stmt stmt ->
    print_statement pr pnl nbr_global_parameters num_stmt stmt;
    succ num_stmt) 1 pprog.pp_poly_instrs in
  ()
