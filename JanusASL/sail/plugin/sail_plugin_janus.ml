(* Sail plugin for JanusASL (docs/ASL.md): `sail --janus-lean --janus-roots "f g ..." ...`
   slices the type-checked model to the definitions reachable from the root functions, keeping
   the Sail standard library, and only then runs the Lean target's own rewrite pipeline and
   printer (looked up from the installed Lean plugin, unchanged). Slicing before the Lean rewrites
   keeps them cheap; it is the same callgraph slice as the REPL's `:slice`
   (Callgraph.filter_ast_extra), with every standard-library definition added to the roots. *)
open Libsail
open Ast
open Ast_defs
open Ast_util
open Ast_compare
module C = Callgraph

let roots = ref []

let std_dir default = Filename.concat (Reporting.get_sail_dir default) "lib"

let in_std dir def =
  match Reporting.simp_loc (def_loc def) with
  | Some (p, _) ->
      let f = Sail_file.Path.to_string (Sail_file.to_path p.Sail_file.Position.pos_fname) in
      String.length f >= String.length dir && String.sub f 0 (String.length dir) = dir
  | None -> false

let node_of_id env id =
  if Ast_compare.IdSet.mem id (Type_check.Env.get_toplevel_lets env) then C.Letbind id
  else if Ast_compare.IdSet.mem id (Type_check.Env.get_defined_val_specs env) then C.Function id
  else if Type_check.Env.bound_typ_id env id then C.Type id
  else (
    prerr_endline ("janus: warning: unknown root " ^ string_of_id id);
    C.Function id
  )

let action out (istate : Interactive.State.istate) =
  let lean = match Target.get ~name:"lean" with Some t -> t | None -> failwith "janus: no lean target" in
  let ast = istate.ast in
  let dir = std_dir istate.default_sail_dir in
  let std_nodes =
    List.fold_left
      (fun acc def -> if in_std dir def then C.NodeSet.union acc (C.nodes_of_def def) else acc)
      C.NodeSet.empty ast.defs
  in
  let user = List.map (node_of_id istate.env) (List.map mk_id !roots) |> C.NodeSet.of_list in
  let g = C.graph_of_ast ast in
  let g = C.G.prune (C.NodeSet.union user std_nodes) C.NodeSet.empty g in
  let sliced = C.filter_ast_extra C.NodeSet.empty g ast false in
  Printf.eprintf "janus: sliced %d -> %d top-level definitions\n%!" (List.length ast.defs)
    (List.length sliced.defs);
  let ctx, ast, effect_info, env =
    Rewrites.rewrite istate.ctx istate.effect_info istate.env (Target.rewrites lean) sliced
  in
  Target.action lean out { istate with ctx; ast; effect_info; env }

let options =
  [
    ( Flag.create ~prefix:["janus"] ~arg:"ids" "roots",
      Arg.String (fun s -> roots := !roots @ List.filter (( <> ) "") (String.split_on_char ' ' s)),
      "space-separated root functions of the slice"
    );
  ]

let _ =
  Target.register ~name:"janus_lean" ~flag:"janus-lean" ~description:"sliced Lean output for JanusASL" ~options
    ~asserts_termination:true action
