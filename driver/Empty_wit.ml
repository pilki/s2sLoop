(* genearaion of the witness *)
open PolyBase
open BinInt
open Conversions
open Printf
open ArithClasses

let debug = true
let num_pid = Unix.getpid ()
let num_bench = ref 0

type vector = coq_Z coq_Vector


let out_prob (kont: string -> unit) bench_name
    (size:int) (vects: vector list) (vals: coq_Z list) =
  let nbr_lam = List.length vects in
  assert (List.length vals = nbr_lam);
  ksprintf kont "(benchmark %s\n" bench_name;
  for i = 0 to nbr_lam - 1 do
    (* LAM stands for lambda *)
    ksprintf kont " :extrafuns ((LAM_%i Int))\n" i
  done;
  ksprintf kont " :formula\n  (and\n";

  for i = 0 to nbr_lam - 1 do
    (* LAM stands for lambda *)
    ksprintf kont "  (<= 0 LAM_%i)\n" i
  done;

(* yes, I use a reference on a list. Yes, it's pretty ugly. Nop, I
   don't really care :) *)
  let lst_vect = ref vects in
  (* output "= 0" constraint for each column *)
  for i = 0 to size - 1 do
    let coefs = List.map List.hd !lst_vect in
    ksprintf kont "  (= 0 (+\n";
    let (_: int) =
      List.fold_left
        (fun i c ->
          ksprintf kont "   ( * %s LAM_%i)" (smt_string_of_z c) i;
          succ i) 0 coefs in
    ksprintf kont "  ))\n";
    lst_vect := List.map List.tl !lst_vect
  done;

  (* negative constraint for vals *)
  ksprintf kont "  (< 0 (+\n";

  let (_: int) = List.fold_left
      (fun i c ->
        ksprintf kont "   ( * %s LAM_%i)" (smt_string_of_z c) i;
        succ i) 0 vals in
  ksprintf kont "  ))\n))\n";
  nbr_lam


let parse_answer ic nbr_lam =
  let res = input_line ic in
  if res = "unsat" then None
  else begin
  if res <> "sat" then failwith "I don't understand the output format of the SMT solver";
  let a = Array.make nbr_lam Z0 in
  try
    while true do
      let line = input_line ic in
      try Scanf.sscanf line " ( = LAM_%u %s@)"
          (fun i s ->
            let z = z_of_string s in
            a.(i) <- z)
      with Scanf.Scan_failure _ -> ()
    done;
    assert false
  with
  | End_of_file ->
      Some (Array.to_list a)
  end



let gen_emptyness_witness size_nat poly =
  let size = C2M.nat size_nat in
  let vects = List.map (fun c -> c.constr_vect) poly in
  let vals = List.map (fun c -> c.constr_val) poly in
  incr num_bench;
  let bench_name = Printf.sprintf "empty_wit_%i_%i.smt" num_pid !num_bench in
  let kont, ic, flush, close =
    if debug then
      (* solver input and output *)
      let sic, sout = Unix.open_process "yices -e -smt" in
      (* file out_channel *)
      let fout = open_out bench_name in
      (* kont function *)
      ((fun s -> output_string sout s; output_string fout s)
      (* input channel *)
      , sic, (fun () -> close_out sout; close_out fout)
      (* closing function*)
      ,(fun () -> close_in sic))
    else
      (* solver input and output *)
      let sic, sout = Unix.open_process "yices -e -smt" in
      (* kont function *)
      ((fun s -> output_string sout s)
      (* input channel *)
      , sic, (fun () -> close_out sout)
      (* closing function*)
      ,(fun () -> close_in sic))
  in
  let nbr_lam = out_prob kont bench_name size vects vals in
  flush ();
  let res = parse_answer ic nbr_lam in
  close ();
  res

