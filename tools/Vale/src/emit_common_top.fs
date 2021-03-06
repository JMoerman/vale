// Turn high-level AST into low-level lemmas:
//   - call transform.fs
//   - then generate lemmas

module Emit_common_top

open Ast
open Ast_util
open Parse
open Parse_util
open TypeChecker
open Transform
open Emit_common_base
open Microsoft.FSharp.Math
open System.Numerics

let add_reprint_decl (env:env) (loc:loc) (d:decl):unit =
  let new_decls =
    match d with
    | DVar _ | DFun _ -> if !reprint_ghost_decls then [d] else []
    | DVerbatim _ -> if !reprint_verbatims then [d] else []
    | DConst _ | DUnsupported _ | DType _ | DOperandType _ -> []
    | DPragma _ -> [d]
    | DProc p ->
        let p = if !reprint_specs then p else {p with pspecs = []} in
        let fs (s:stmt):stmt list map_modify =
          let modGhost = if !reprint_ghost_stmts then Unchanged else Replace [] in
          match s with
          | SLoc _ | SLabel _ | SGoto _ | SReturn | SAlias _ | SLetUpdates _ | SBlock _ -> Unchanged
          | SIfElse ((SmInline | SmPlain), _, _, _) -> Unchanged
          | SWhile _ when !reprint_loop_invs -> Unchanged
          | SWhile (e, _, (l, _), s) -> Replace [SWhile (e, [], (l, []), s)]
          | SAssign (_, e) ->
            (
              match skip_loc e with
              | EApply (e, _, _, _) when is_id e && Map.containsKey (id_of_exp e) env.procs -> Unchanged
              | _ -> modGhost
            )
          | SAssume _ | SAssert _ | SCalc _ | SVar _ -> modGhost
          | SIfElse (SmGhost, _, _, _) -> modGhost
          | SForall _ | SExists _ -> modGhost
          in
        let bodyOpt =
          match p.pbody with
          | None -> None
          | Some ss -> Some (List.collect (map_stmt (fun e -> e) fs) ss) in
        let p = {p with pbody = bodyOpt} in
        [DProc p]
    in
  reprint_decls_rev := (List.map (fun d -> (loc, d)) new_decls) @ (!reprint_decls_rev)

let build_one_decl (verify:bool) (loc:loc) (envr:env, envBody:env, d:decl):decls =
  try
    match d with
    | DProc p ->
        let isQuick = List_mem_assoc (Id "quick") p.pattrs in
        let isRestart = attrs_get_bool (Id "restartProver") false p.pattrs in
        let isCodeOnly = attrs_get_bool (Id "codeOnly") false p.pattrs || !global_code_only in
        let options = attrs_get_exps_opt (Id "options") p.pattrs in
        if verify then
          let ds_p = Emit_common_lemmas.build_proc envBody envr loc p in
          let ds_q = if isQuick && not !no_lemmas && not isCodeOnly then Emit_common_quick_export.build_proc envr loc p else [] in
          let comment (s:string) : loc * decl =
            let isPublic = attrs_get_bool (Id "public") false p.pattrs in
            let attrs = if isPublic then [(Id "interface", []); (Id "implementation", [])] else [] in
            (loc, DVerbatim (attrs, [s]))
            in
          let beginComment = comment ("//-- " + (err_id p.pname)) in
          let endComment = comment "//--" in
          let (pushes, pops) =
            match (!fstar, options) with
            | (false, _) -> ([], [])
            | (true, None) -> ([], [])
            | (true, Some es) -> ([(loc, DPragma (PushOptions es))], [(loc, DVerbatim ([], ["#pop-options"]))])
            in
          let restarts = if !fstar && isRestart then [(loc, DVerbatim ([], ["#restart-solver"]))] else [] in
          [beginComment] @ pushes @ restarts @ ds_p @ ds_q @ pops @ [endComment]
        else
          []
    | DVerbatim (attrs, lines) ->
        if verify then [(loc, DVerbatim (attrs, lines))] else []
    | _ ->
        if verify then [(loc, d)] else []
  with err -> raise (LocErr (loc, err))

let build_decl (env:env) ((loc:loc, d1:decl), verify:bool):env * decls =
  try
    let dReprint = d1 in
    let (envBodyDs, env) = transform_decl env loc d1 in
    let ds = List.collect (build_one_decl verify loc) envBodyDs in
    (match (verify, !reprint_file) with (true, Some _) -> add_reprint_decl env loc dReprint | _ -> ());
    (env, ds)
  with err -> raise (LocErr (loc, err))

let build_decls (env:env) (includes:(string * string option option * (((loc * decl) * bool) list)) list) (ds:((loc * decl) * bool) list):decls =
  let ds = tc_decls includes ds in
  let (env, dss) = List_mapFoldFlip build_decl env ds in
  List.concat dss

