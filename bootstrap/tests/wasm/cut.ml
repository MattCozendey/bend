(* Cut
   ===

   cut.exe x.wast: the binary script of the test script x.wast, as
   wasm -d x.wast -o x.bin.wast writes it, except that each module that a
   command defines keeps only its functions inside the subset of the Bend copy
   of WASM (W2), with their types and exports; the other functions and their
   exports go. A module with imports, tables, globals, elements, tags or a
   start function stays whole, as do the modules of assertions. So the model
   refuses only what is outside the subset, and the official results still
   hold for the functions that a module keeps (W6). It uses the spec's own
   parser, syntax and encoder (convert.sh builds it with them). *)

open Types
open Ast
open Source

let is_i32 (t : valtype) = t = NumT I32T

let rec instrs_ok es = List.for_all instr_ok es

(* the instructions of W2 *)
and instr_ok (e : instr) =
  match e.it with
  | Block (ValBlockType None, es) | Loop (ValBlockType None, es) -> instrs_ok es
  | Br _ | BrIf _ | BrTable _ -> true
  | LocalGet _ | LocalSet _ | LocalTee _ -> true
  | Load (x, {ty = I32T; pack = None; _}) -> x.it = 0l
  | Load (x, {ty = I32T; pack = Some (Pack.Pack8, Pack.U); _}) -> x.it = 0l
  | Store (x, {ty = I32T; pack = None; _}) -> x.it = 0l
  | Store (x, {ty = I32T; pack = Some Pack.Pack8; _}) -> x.it = 0l
  | MemorySize x | MemoryGrow x -> x.it = 0l
  | Const {it = Value.I32 _; _} -> true
  | Test (Value.I32 I32Op.Eqz) -> true
  | Compare (Value.I32 (I32Op.Eq | I32Op.Ne | I32Op.Lt Pack.U | I32Op.Gt Pack.U
                       | I32Op.Le Pack.U | I32Op.Ge Pack.U)) -> true
  | Binary (Value.I32 (I32Op.Add | I32Op.Sub | I32Op.And | I32Op.Or | I32Op.Shl
                      | I32Op.Shr Pack.U)) -> true
  | _ -> false

(* the defined types, one per subtype of each recursion group *)
let subtypes (m : module_) =
  List.concat_map (fun (t : type_) -> let RecT sts = t.it in sts) m.it.types

(* the type of a function, when it is of the subset: i32 parameters, and at
   most one result, an i32 *)
let functype (m : module_) (Func (x, _, _)) =
  match List.nth_opt (subtypes m) (Int32.to_int x.it) with
  | Some (SubT (_, _, FuncT (ins, outs)))
    when List.for_all is_i32 ins && List.for_all is_i32 outs && List.length outs <= 1 ->
    Some (ins, outs)
  | _ -> None

let func_ok (m : module_) (f : func) =
  let Func (_, ls, body) = f.it in
  functype m f.it <> None
  && List.for_all (fun (l : local) -> let Local t = l.it in is_i32 t) ls
  && instrs_ok body

let is_whole (m : module_) =
  m.it.imports <> [] || m.it.tables <> [] || m.it.globals <> [] || m.it.elems <> []
  || m.it.tags <> [] || m.it.start <> None

let index_of x xs =
  let rec go i = function [] -> None | y :: ys -> if y = x then Some i else go (i + 1) ys in
  go 0 xs

let cut (m : module_) : module_ =
  if is_whole m then m else
  let kept = List.filter (fun (_, f) -> func_ok m f) (List.mapi (fun i f -> (i, f)) m.it.funcs) in
  let tys = List.sort_uniq compare (List.filter_map (fun (_, (f : func)) -> functype m f.it) kept) in
  let types = List.map (fun t -> RecT [SubT (Final, [], FuncT t)] @@ no_region) tys in
  let funcs = List.map (fun (_, (f : func)) ->
      let Func (_, ls, body) = f.it in
      let t = Option.get (functype m f.it) in
      Func (Int32.of_int (Option.get (index_of t tys)) @@ no_region, ls, body) @@ f.at) kept in
  let exports = List.filter_map (fun (e : export) ->
      let Export (n, xx) = e.it in
      match xx.it with
      | FuncX x ->
        Option.map (fun j -> Export (n, FuncX (Int32.of_int j @@ x.at) @@ xx.at) @@ e.at)
          (index_of (Int32.to_int x.it) (List.map fst kept))
      | _ -> Some e) m.it.exports in
  {m with it = {m.it with types; funcs; exports}}

let command (c : Script.command) =
  match c.it with
  | Script.Module (x, {it = Script.Textual (m, _); at}) ->
    {c with it = Script.Module (x, {it = Script.Textual (cut m, []); at})}
  | _ -> c

let () =
  let scr = Parse.Script.parse_file Sys.argv.(1) in
  Print.script stdout 80 `Binary (List.map command scr)
