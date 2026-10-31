(* Cut
   ===

   cut.exe x.wast x.pure: the binary script of the test script x.wast, as
   wasm -d x.wast -o x.bin.wast writes it, except that each module that a
   command defines keeps only its functions inside the subset of the Bend copy
   of WASM (W2), with their types and exports; the other functions and their
   exports go. A module with imports, tables, globals, elements, tags or a
   start function stays whole, as do the modules of assertions. So the model
   refuses only what is outside the subset, and the official results still
   hold for the functions that a module keeps (W6). For each command that
   defines a module, x.pure gets a line (pure i "name" ...): the command's
   index in the script, and the exports of the module's functions that change
   nothing in its instance (pure_exports). It uses the spec's own parser,
   syntax and encoder (convert.sh builds it with them). *)

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

(* an instruction that changes nothing in the instance: it writes no memory,
   table or global, drops no segment, and calls only functions i that are
   pure i; any instruction not listed here counts as a change *)
let rec instrs_pure pure es = List.for_all (instr_pure pure) es

and instr_pure pure (e : instr) =
  match e.it with
  | Block (_, es) | Loop (_, es) -> instrs_pure pure es
  | If (_, es1, es2) -> instrs_pure pure es1 && instrs_pure pure es2
  | Call x -> pure (Int32.to_int x.it)
  | Unreachable | Nop | Drop | Select _ | Br _ | BrIf _ | BrTable _ | BrOnNull _
  | BrOnNonNull _ | BrOnCast _ | BrOnCastFail _ | Return | LocalGet _ | LocalSet _
  | LocalTee _ | GlobalGet _ | TableGet _ | TableSize _ | Load _ | VecLoad _
  | VecLoadLane _ | MemorySize _ | RefNull _ | RefFunc _ | RefIsNull | RefAsNonNull
  | RefTest _ | RefCast _ | RefEq | RefI31 | I31Get _ | StructGet _ | ArrayGet _
  | ArrayLen | ExternConvert _ | Const _ | Test _ | Compare _ | Unary _ | Binary _
  | Convert _ | VecConst _ | VecTest _ | VecCompare _ | VecUnary _ | VecBinary _
  | VecTernary _ | VecConvert _ | VecShift _ | VecBitmask _ | VecTestBits _
  | VecUnaryBits _ | VecBinaryBits _ | VecTernaryBits _ | VecSplat _ | VecExtract _
  | VecReplace _ -> true
  | _ -> false

(* the exports of the functions of a module that change nothing in its
   instance: an action on one that the model does not run to its end leaves
   the instance as the script expects (WasmTests.lean). A function is pure
   when its body is, with the functions it calls; a module that stays whole
   has none, as its imports could do anything. *)
let pure_exports (m : module_) : name list =
  if is_whole m then [] else
  let fs = Array.of_list m.it.funcs in
  let pure = Array.make (Array.length fs) true in
  let changed = ref true in
  while !changed do
    changed := false;
    Array.iteri (fun i (f : func) ->
        let Func (_, _, body) = f.it in
        if pure.(i)
        && not (instrs_pure (fun j -> j < Array.length fs && pure.(j)) body) then begin
          pure.(i) <- false;
          changed := true
        end) fs
  done;
  List.filter_map (fun (e : export) ->
      let Export (n, xx) = e.it in
      match xx.it with
      | FuncX x when pure.(Int32.to_int x.it) -> Some n
      | _ -> None) m.it.exports

(* a name as a string of the binary script: each of its UTF-8 bytes escaped *)
let quoted (n : name) =
  "\"" ^ String.concat ""
    (List.map (fun c -> Printf.sprintf "\\%02x" (Char.code c))
       (List.of_seq (String.to_seq (Utf8.encode n)))) ^ "\""

let () =
  let scr = Parse.Script.parse_file Sys.argv.(1) in
  let oc = open_out Sys.argv.(2) in
  List.iteri (fun i (c : Script.command) ->
      match c.it with
      | Script.Module (_, {it = Script.Textual (m, _); _}) ->
        Printf.fprintf oc "(pure %d%s)\n" i
          (String.concat "" (List.map (fun n -> " " ^ quoted n) (pure_exports m)))
      | _ -> ()) scr;
  close_out oc;
  Print.script stdout 80 `Binary (List.map command scr)
