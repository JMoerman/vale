open Ast
open Parse
open Parse_util
open Microsoft.FSharp.Text.Lexing
open System.IO

exception Err of string
exception InternalErr of string
exception LocErr of loc * exn
let err (s:string):'a = raise (Err s)

type string_tree_raw =
| StLeaf of string
| StList of string * string * string_tree list
and string_tree = int(*printed length in characters*) * string_tree_raw

let st_leaf (s:string):string_tree =
  (s.Length, StLeaf s)

let make_st_list (l:string) (r:string) (ts:string_tree list):string_tree =
  let len = List.fold (fun len t -> len + fst t + 1) (l.Length + r.Length) ts in
  (len, StList (l, r, ts))

let st_list = make_st_list "" ""
let st_paren = make_st_list "(" ")"
let st_angle = make_st_list "<" ">"
let st_brace = make_st_list "{" "}"
let st_bracket = make_st_list "[" "]"

let list_opt (m:'a option) (f:'a -> 'b list):'b list = match m with None -> [] | Some x -> f x in

let rec string_of_tree (t:string_tree):string =
  match snd t with
  | StLeaf s -> s
  | StList (l, r, ts) -> l + String.concat " " (List.map string_of_tree ts) + r

let rec print_tree (indent:string) (t:string_tree):unit =
  let (len, r) = t in
  match r with
  | StLeaf s ->
      printfn "%s%s" indent s
  | StList _ when len < 100 ->
      printfn "%s%s" indent (string_of_tree t)
  | StList (l, r, (t1::ts)) when fst t1 < 100 ->
      printfn "%s%s%s%s" indent l (if l.Length = 1 then " " else "") (string_of_tree t1);
      List.iter (print_tree (indent + "  ")) ts;
      (if r.Length > 0 then printfn "%s%s" indent r)
  | StList (l, r, (t1::ts)) when l.Length = 0 && r.Length = 0 ->
      print_tree indent t1;
      List.iter (print_tree (indent + "  ")) ts
  | StList (l, r, ts) ->
      (if l.Length > 0 then printfn "%s%s" indent l);
      List.iter (print_tree (indent + "  ")) ts;
      (if r.Length > 0 then printfn "%s%s" indent r)

let rec tree_of_raw_exp (e:raw_exp):string_tree =
  match e with
  | RLet _ -> st_leaf "LET"
  | RFun _ -> st_leaf "FUN"
  | RArrow _ -> st_leaf "->"
  | RTildeArrow _ -> st_leaf "~>"
  | RDollarDollar _ -> st_leaf "$$"
  | RPlus _ -> st_leaf "+"
  | RRefine _ -> st_leaf "REFINE"
  | RLtGt _ -> st_leaf "<>"
  | RMeta _ -> st_leaf "META"
  | RComma _ -> st_leaf ","
  | RAttribute _ -> st_leaf "ATTRIBUTE"
  | RAttributes _ -> st_leaf "ATTRIBUTES"
  | RDecreases _ -> st_leaf "DECREASES"
  | RDollar _ -> st_leaf "$"
  | RHash _ -> st_leaf "#"
  | RColon _ -> st_leaf ":"
  | RSColon _ -> st_leaf "::"
  | RSemi _ -> st_leaf ";"
  | RMatch _ -> st_leaf "MATCH"
  | RWith _ -> st_leaf "WITH"
  | RBar _ -> st_leaf "|"
  | RHashDot _ -> st_leaf "#."
  | RType _ -> st_leaf "TYPE"
  | RAscribed _ -> st_leaf "ASCRIBED"
  | RPattern _ -> st_leaf "PATTERN"
  | RDecl (_, s) -> st_leaf s
  | RQualifier (_, s) -> st_leaf s
  | RUnitValue _ -> st_leaf "UNIT_VALUE"
  | RInt (_, i) -> st_leaf (i.ToString())
  | RString _ -> st_leaf "STRING"
  | RId (_, s) -> st_leaf s
  | RList es -> st_paren (List.map tree_of_raw_exp es)

let rec string_of_raw_exp (e:raw_exp):string =
  string_of_tree (tree_of_raw_exp e)

let rec simplify_raw_exp (e:raw_exp):raw_exp =
  match e with
  | RList [RDollarDollar _; e; _; _; _] -> simplify_raw_exp e
  | RList ((RAscribed _)::e::_) -> simplify_raw_exp e
  | RList [RLet _; _; RMeta _; e] -> simplify_raw_exp e
  | RList es ->
      let es = List.filter (fun e -> match e with RMeta _ -> false | _ -> true) es in
      let es = List.map simplify_raw_exp es in
      RList es
  | _ -> e

let string_opt m f = match m with None -> "" | Some x -> f x in

let string_of_id (id:id):string =
  match id with
  | { name = None; index = None } -> "__"
  | _ -> (string_opt id.name (fun x -> x)) + (string_opt id.index (fun i -> "@" + i.ToString()))

let tree_of_id (id:id):string_tree =
  st_leaf (string_of_id id)

let tree_of_aqual (a:aqual) (t:string_tree):string_tree =
  match a with
  | Explicit -> t
  | Implicit -> st_list [st_leaf "#"; t]
  | Equality -> st_list [st_leaf "$"; t]

let rec tree_of_univ (u:univ):string_tree =
  match u with
  | UId x -> tree_of_id x
  | UInt i -> st_leaf (i.ToString())
  | UPlus (u1, u2) -> st_paren [tree_of_univ u1; st_leaf " + "; tree_of_univ u2]
  | UMax us -> st_paren (st_leaf "max" :: List.map tree_of_univ us)

let rec tree_of_exp (e:exp):string_tree =
  let r = tree_of_exp in
  match e with
  | EId x -> tree_of_id x
  | EInt i -> st_leaf (i.ToString())
  | EUnitValue -> st_leaf "UNIT_VALUE"
  | EBool -> st_leaf "BOOL"
  | EProp -> st_leaf "PROP"
  | EType u -> st_paren [st_leaf "Type"; tree_of_univ u]
  | EComp (e1, e2, es) -> st_paren (st_list [st_leaf "!!"; r e1] :: List.map r (e2::es))
  | EApp (e, aes) -> st_paren (r e :: List.map tree_of_aqual_exp aes)
  | EAppUnivs (e, us) -> st_paren ([r e; st_leaf "<"] @ List.map tree_of_univ us @ [st_leaf ">"])
  | EArrow (a, x, e1, e2) ->
      st_paren [
        st_list [st_list [tree_of_aqual a (tree_of_id x); st_leaf ":"]; r e1; st_leaf "->"];
        r e2
      ]
  | ERefine (x, e1, e2) ->
      st_paren [st_list [st_list [tree_of_id x; st_leaf ":"]; r e1]; st_brace [r e2]]
  | ETyped (e1, e2) -> st_paren [r e1; st_leaf ":"; r e2]
  | EAscribed (e1, e2) -> st_paren [r e1; st_leaf ":>"; r e2]
  | EPattern (pats, e) ->
      st_paren [st_leaf "PATTERN"; st_paren (List.map st_paren (List.map (List.map r) pats)); r e]
  | ELet (b, e1, e2) -> st_paren [st_leaf "let"; tree_of_binder b; st_leaf "="; r e1; st_leaf "in"; r e2]
  | EFun (bs, e) -> st_paren ([st_leaf "fun"] @ trees_of_binders bs @ [st_leaf "->"; r e])
  | EUnsupported s -> st_paren [st_leaf "UNSUPPORTED"; st_leaf ("\"" + s + "\"")]
and tree_of_aqual_exp ((a:aqual), (e:exp)):string_tree =
  tree_of_aqual a (tree_of_exp e)
and tree_of_binder ((a, x, tOpt):binder):string_tree =
  let st =
    match tOpt with
    | None -> tree_of_id x
    | Some t -> st_list [st_list [tree_of_id x; st_leaf ":"]; tree_of_exp t]
  in
  tree_of_aqual a st
and trees_of_binders (bs:binder list):string_tree list =
  List.map tree_of_binder bs

let string_of_exp (e:exp):string =
  string_of_tree (tree_of_exp e)

let tree_of_decl (d:decl):string_tree =
  let
    {
      d_name = x;
      d_qualifiers = quals;
      d_category = category;
      d_udecls = udecls;
      d_binders = bs;
      d_typ = t;
      d_body = body_opt;
    }
    = d
    in
  st_list
    ([st_list ([st_list ([st_leaf x; st_leaf "<"] @ List.map tree_of_id udecls @ [st_leaf ">"])]
      @ trees_of_binders bs @ [st_leaf "::"])]
    @ [tree_of_exp t]
    @ (list_opt body_opt (fun e -> [st_leaf "="; tree_of_exp e])))

let parse_id (s:string):id =
  let i = s.IndexOf("@") in
  if i >= 0 then
    let name = if i = 0 then None else Some (s.Substring(0, i)) in
    let index = Some (System.Int32.Parse(s.Substring(i + 1))) in
    { name = name ; index = index }
  else
    { name = Some s; index = None }

let parse_rid (e:raw_exp):id =
  match e with
  | RId (_, x) -> parse_id x
  | _ -> err ("parse_rid: " + string_of_raw_exp e)

let rec parse_univ (e:raw_exp):univ =
  match e with
  | RId (_, x) -> UId (parse_id x)
  | RInt (_, i) -> UInt i
  | RList [RPlus _; e1; e2] -> UPlus (parse_univ e1, parse_univ e2)
  | RList (RId (_, "max") :: us) -> UMax (parse_univs us)
  | _ -> err ("parse_univ: " + string_of_raw_exp e)
and parse_univs (es:raw_exp list):univ list =
  match es with
  | [e] -> [parse_univ e]
  | e::(RComma _)::es -> (parse_univ e)::(parse_univs es)
  | _ -> err ("parse_univs: " + string_of_raw_exp (RList es))

let get_aqual (e:raw_exp):aqual * raw_exp =
  match e with
  | RList [RDollar _; e] -> (Equality, e)
  | RList [(RHash _ | RHashDot _); e] -> (Implicit, e)
  | _ -> (Explicit, e)

let rec parse_exp (e:raw_exp):exp =
  match e with
  | RId (_, x) -> EId (parse_id x)
  | RInt (_, i) -> EInt i
  | RUnitValue _ -> EUnitValue
  | RList [RType _; e1] -> EType (parse_univ e1)
  | RList (((RId _ | RList _) as e0)::es) ->
    (
      match List.rev es with
      | (RList ((RDecreases _)::_))::(RList ((RAttributes _)::_))::es_rev
      | (RList ((RAttributes _)::_))::es_rev ->
        (
          let es = List.rev es_rev in
          match es with
          | e1::es -> EComp (parse_exp e0, parse_exp e1, parse_comma_exps es)
          | _ -> err ("parse_exp: EComp: " + string_of_raw_exp e)
        )
      | _ -> EApp (parse_exp e0, List.map parse_aqual_exp es)
    )
  | RList [RLtGt _; e; RList us] -> EAppUnivs (parse_exp e, parse_univs us)
  | RList [RArrow _; RList ((RMatch _)::_); _] -> EUnsupported "MATCH"
  | RList [RArrow _; e1; e2] ->
      let (a, e1) = get_aqual e1 in
      let (x, e1) =
        match e1 with
        | RList [RColon _; RId (_, x); e1] -> (parse_id x, e1)
        | _ -> err ("parse_exp: RArrow: " + string_of_raw_exp e)
        in
      EArrow (a, x, parse_exp e1, parse_exp e2)
  | RList [RColon _; e1; RId (_, ("Tm_type" | "Tm_delayed-resolved"))] -> parse_exp e1
  | RList [RColon _; e1; RList [RColon _; RId (_, ("Tm_name" | "Tm_fvar")); _]] -> parse_exp e1
  | RList [RColon _; e1; e2] -> ETyped (parse_exp e1, parse_exp e2)
  | RList [RRefine _; RList [RColon _; RId (_, x); e1]; e2] -> ERefine (parse_id x, parse_exp e1, parse_exp e2)
  | RList [RAscribed _; e1; e2] -> ETyped (parse_exp e1, parse_exp e2)
  | RList [RPattern _; RList pats; e] ->
      let f (e:raw_exp):exp list =
        match e with
        | RList es -> List.map parse_exp es
        | _ -> err ("parse_exp: EPattern: " + string_of_raw_exp e)
        in
      EPattern (List.map f pats, parse_exp e)
  | RList [RLet _; b; e1; e2] -> ELet (parse_binder b, parse_exp e1, parse_exp e2)
  | RList [RFun _; RList bs; e] -> EFun (List.map parse_binder bs, parse_exp e)
//  | RList (e::_) | e -> EUnsupported (string_of_raw_exp e)
  | e -> EUnsupported (string_of_raw_exp e)
and parse_aqual_exp (e:raw_exp):(aqual * exp) =
  let (a, e) = get_aqual e in
  (a, parse_exp e)
and parse_comma_exps (es:raw_exp list):exp list =
  match es with
  | [] -> []
  | (RComma _)::es -> parse_comma_exps es
  | e::es -> (parse_exp e)::(parse_comma_exps es)
and parse_binder (e:raw_exp):binder = parse_binder_a Explicit e
and parse_binder_a (a:aqual) (e:raw_exp):binder =
  match e with
  | RId (_, x) -> (a, parse_id x, None)
  | RList [RColon _; RId (_, x); t] -> (a, parse_id x, Some (parse_exp t))
  | RList [RDollar _; b] -> parse_binder_a Equality b
  | RList [(RHash _ | RHashDot _); b] -> parse_binder_a Implicit b
  | _ -> err ("parse_binder: " + string_of_raw_exp e)

let parse_qualifier (e:raw_exp):string =
  match e with
  | RQualifier (_, s) -> s
  | _ -> err ("parse_qualifier: " + string_of_raw_exp e)

let parse_decl (e:raw_exp):decl =
  match e with
  | RList [RList quals; RDecl (_, category); RId (_, x); RList udecls; RList bs; t; body_opt] ->
      {
        d_name = x;
        d_qualifiers = List.map parse_qualifier quals
        d_category = category;
        d_udecls = List.map parse_rid udecls;
        d_binders = List.map parse_binder bs;
        d_typ = parse_exp t;
        d_body = match body_opt with RList [] -> None | RList [e] -> Some (parse_exp e) | _ -> err ("body: " + string_of_raw_exp body_opt);
      }
  | _ -> err ("parse_decl: " + string_of_raw_exp e)

let filter_decls (ds:decl list):decl list =
  let filter_decl_pair ((d:decl option), (dnext:decl option)):decl list =
    // turn "val f ... let f ..." into "let f..."
    match (d, dnext) with
    | (None, _) -> []
    | (Some d, None) -> [d]
    | (Some d, Some dnext) when d.d_name = dnext.d_name -> []
    | (Some d, Some _) -> [d]
    in
  let filter_decl (d:decl):bool =
    List.forall (fun x -> x <> "private") d.d_qualifiers
    in
  let abstract_decl (d:decl):decl =
    if List.forall (fun x -> x <> "abstract") d.d_qualifiers then d else
    {d with d_body = None}
    in
  let ds_opt = List.map Some ds in
  let ds_prev = ds_opt @ [None] in
  let ds_next = None::ds_opt in
  let ds = List.collect filter_decl_pair (List.zip ds_prev ds_next) in
  let ds = List.filter filter_decl ds in
  let ds = List.map abstract_decl ds in
  ds

// Move a:Type _ from d_typ into d_binders
let decl_lift_type_binders (d:decl):decl =
  let rec f (d:decl):decl option =
    match d.d_typ with
    | EArrow (a, x, k, EApp (EAppUnivs (EId {name = Some ("Prims.Tot" | "Prims.GTot" | "Tot" | "GTot")}, _), [(_, t)]))
    | EArrow (a, x, k, EApp (EId {name = Some ("Prims.Tot" | "Prims.GTot" | "Tot" | "GTot")}, [(_, t)]))
    | EArrow (a, x, k, t) ->
        let (body, x) =
          match d.d_body with
          | Some (EFun ([(_, x, _)], e)) -> (Some e, x)
          | Some (EFun ((_, x, _)::bs, e)) -> (Some (EFun (bs, e)), x)
          | _ -> (None, x)
          in
        let d = {d with d_binders = d.d_binders @ [(a, x, Some k)]; d_typ = t; d_body = body} in
        f d
    | EType _ -> Some d
    | _ -> None
    in
  match f d with None -> d | Some d -> d

let rec unsupported (e:exp):string option =
  match e with
  | EId x -> None
  | EInt i -> None
  | EUnitValue -> None
  | EBool -> None
  | EProp -> None
  | EType u -> None
  | EComp (e1, e2, es) -> exps_unsupported (e1::e2::es)
  | EApp (e, aes) -> exps_unsupported (e::(List.map snd aes))
  | EAppUnivs (e, us) -> unsupported e
  | EArrow (a, x, e1, e2) -> exps_unsupported [e1; e2]
  | ERefine (x, e1, e2) -> exps_unsupported [e1; e2]
  | ETyped (e1, e2) -> exps_unsupported [e1; e2]
  | EAscribed (e1, e2) -> exps_unsupported [e1; e2]
  | EPattern (pats, e) ->
      let upats = list_unsupported (List.map exps_unsupported pats) in
      list_unsupported [upats; unsupported e]
  | ELet (b, e1, e2) -> exps_unsupported (e1::e2::(binder_exps b))
  | EFun (bs, e) -> exps_unsupported (e::(List.collect binder_exps bs))
  | EUnsupported s -> Some s
and binder_exps (b:binder):exp list =
  let (_, _, e_opt) = b in
  list_opt e_opt (fun e -> [e])
and exps_unsupported (es:exp list):string option =
  list_unsupported (List.map unsupported es)
and list_unsupported (ss:string option list):string option =
  match ss with
  | [] -> None
  | (Some s)::_ -> Some s
  | None::t -> list_unsupported t

let decl_unsupported (d:decl):decl =
  let u_binders = exps_unsupported (List.collect binder_exps d.d_binders) in
  let u_typ = unsupported d.d_typ in
  let body_opt =
    match d.d_body with
    | None -> None
    | Some e -> match unsupported e with None -> Some e | Some _ -> None
    in
  let d = {d with d_body = body_opt} in
  let u = list_unsupported [u_binders; u_typ] in
  match u with
  | None -> d
  | Some s -> {d with d_udecls = []; d_binders = []; d_typ = EUnsupported s; d_body = None}

let rec index_to_var_id (xs:string list) (id:id):id =
  match id with
  | {index = None} -> id
  | {name = Some x; index = Some i} ->
      let y = List.item i xs in
      if y.StartsWith(x) then {name = Some y; index = None}
      else err ("expected variable " + x + " but found " + y)
  | {name = None; index = Some i} ->
      {name = Some (List.item i xs); index = None}

let rec index_to_var_univ (xs:string list) (u:univ):univ =
  let r = index_to_var_univ xs in
  match u with
  | UId x -> UId (index_to_var_id xs x)
  | UInt _ -> u
  | UPlus (u1, u2) -> UPlus (r u1, r u2)
  | UMax us -> UMax (List.map r us)

let rec index_to_var_exp (xs:string list) (e:exp):exp =
  let r = index_to_var_exp xs in
  match e with
  | EArrow (_, {name = None}, _, _)
  | EArrow (_, {index = Some _}, _, _)
  | ERefine ({name = None}, _, _)
  | ERefine ({index = Some _}, _, _) ->
      err ("index_to_var_exp: " + string_of_exp e)
  | EId x -> EId (index_to_var_id xs x)
  | EInt _ | EUnitValue | EBool | EProp -> e
  | EType u -> EType (index_to_var_univ xs u)
  | EComp (e1, e2, es) -> EComp (r e1, r e2, List.map r es)
  | EApp (e, aes) -> EApp (r e, List.map (fun (a, e) -> (a, r e)) aes)
  | EAppUnivs (e, us) -> EAppUnivs (r e, List.map (index_to_var_univ xs) us)
  | EArrow (a, ({name = Some x; index = None} as id), e1, e2) ->
      EArrow (a, id, r e1, index_to_var_exp (x::xs) e2)
  | ERefine (({name = Some x; index = None} as id), e1, e2) ->
      ERefine (id, r e1, index_to_var_exp (x::xs) e2)
  | ETyped (e1, e2) -> ETyped (r e1, r e2)
  | EAscribed (e1, e2) -> EAscribed (r e1, r e2)
  | EPattern (pats, e) -> EPattern (List.map (List.map r) pats, r e)
  | ELet (b, e1, e2) ->
      let (xs, bs) = index_to_var_binders xs [b] in
      ELet (List.head bs, r e1, index_to_var_exp xs e2)
  | EFun (bs, e) ->
      let (xs, bs) = index_to_var_binders xs bs in
      EFun (bs, index_to_var_exp xs e)
  | EUnsupported s -> e
and index_to_var_binders (xs:string list) (bs:binder list):(string list * binder list) =
  match bs with
  | [] -> (xs, bs)
  | (_, {name = None}, _)::_
  | (_, {index = Some _}, _)::_ ->
      err ("index_to_var_binders: " + string_of_tree (st_paren (trees_of_binders bs)))
  | (a, ({name = Some x; index = None} as id), e_opt)::bs ->
      let e_opt = Option.map (index_to_var_exp xs) e_opt in
      let (xs, bs) = index_to_var_binders (x::xs) bs in
      (xs, (a, id, e_opt)::bs)

let index_to_var_decl (d:decl):decl =
  let id_name (id:id):string =
    match id with
    | {name = None}
    | {index = Some _} -> err ("index_to_var_decl: " + d.d_name)
    | {name = Some x} -> x
    in
  try
    let xs = List.rev (List.map id_name d.d_udecls) in
    let (xs, bs) = index_to_var_binders xs d.d_binders in
    let t = index_to_var_exp xs d.d_typ in
    let body = Option.map (index_to_var_exp xs) d.d_body in
    {d with d_binders = bs; d_typ = t; d_body = body}
  with
  | :? System.ArgumentException ->
      {d with d_binders = []; d_typ = EUnsupported "bad variable index"; d_body = None}

let rec universe0_univ_int (u:univ):bigint =
  let r = universe0_univ_int in
  match u with
  | UId x -> bigint.Zero
  | UInt i -> i
  | UPlus (u1, u2) -> r u1 + r u2
  | UMax [] -> err "universe0_univ_int"
  | UMax us -> List.fold (fun i j -> if i > j then i else j) bigint.Zero (List.map r us)

let universe0_univ (u:univ):univ =
  UInt (universe0_univ_int u)

let rec universe0_exp (e:exp):exp =
  let r = universe0_exp in
  match e with
  | EId {name = Some "Prims.bool"} -> EBool
  | EId {name = Some ("Prop_s.prop0" | "Prims.prop" | "Prims.logical")} -> EProp
  | EId _ | EInt _ | EUnitValue | EBool | EProp | EUnsupported _ -> e
  | EType u -> EType (universe0_univ u)
  | EComp (e1, e2, es) -> EComp (r e1, r e2, List.map r es)
  | EApp (e, aes) -> EApp (r e, List.map (fun (a, e) -> (a, r e)) aes)
  | EAppUnivs (e, us) -> r e
  | EArrow (a, x, e1, e2) -> EArrow (a, x, r e1, r e2)
  | ERefine (x, e1, e2) -> ERefine (x, r e1, r e2)
  | ETyped (e1, e2) -> ETyped (r e1, r e2)
  | EAscribed (e1, e2) -> EAscribed (r e1, r e2)
  | EPattern (pats, e) -> EPattern (List.map (List.map r) pats, r e)
  | ELet (b, e1, e2) -> ELet (universe0_binder b, r e1, r e2)
  | EFun (bs, e) -> EFun (List.map universe0_binder bs, r e)
and universe0_binder (b:binder):binder =
  match b with
  | (a, x, e_opt) ->
      (a, x, Option.map universe0_exp e_opt)

let universe0_decl (d:decl):decl =
  let (++) = Set.union in
  let bs = List.map universe0_binder d.d_binders in
  let body = Option.map universe0_exp d.d_body in
  let t =
    // more sketchy Type(0) vs prop heuristics:
    match (d.d_typ, body) with
    | (EType (UInt i), None) when i.Equals(bigint.Zero) -> d.d_typ
    | (EType (UInt i), Some e) when i.Equals(bigint.Zero) ->
      (
        match e with
        | EApp (EId {name = Some "Prims.squash"}, _) -> universe0_exp d.d_typ
        | EId _ | EApp _ | ERefine _ -> d.d_typ
        | _ -> universe0_exp d.d_typ
      )
    | _ -> universe0_exp d.d_typ
    in
  {d with d_udecls = []; d_binders = bs; d_typ = t; d_body = body}

type env = Map<string, decl>
let reason = ref (None:string option)
let set_reason (s:string):unit =
  match !reason with Some _ -> () | None -> reason := Some s

let rec take_arrows (e:exp):(exp list * exp) =
  match e with
  | EArrow (_, x, e1, e2) ->
      let (es, e) = take_arrows e2 in
      (e1::es, e)
  | _ -> ([], e)

let rec is_vale_type (outer:bool) (leftmost:bool) (env:env) (e:exp):bool =
  //printfn "is_vale_type? %s" (string_of_exp e);
  //let r e = let b = is_vale_type false false env e in printfn "is_vale_type %A %s" b (string_of_exp e); b in
  let r = is_vale_type false false env in
  let may_be_refine e =
    match e with
    | ERefine ({name = Some x}, e1, e2) when outer ->
        let dx = { d_name = x; d_qualifiers = []; d_category = "val"; d_udecls = []; d_binders = []; d_typ = e1; d_body = None} in
        let env = Map.add x dx env in
        //printfn "%A %A" (r e1) (is_vale_exp env e2);
        r e1 && is_vale_exp env e2
    | _ -> r e
    in
  match e with
  | EId _ -> is_vale_type_id env e
  | EBool -> true
  | EProp -> true
  | EComp (EId {name = Some ("Prims.Pure" | "Prims.Ghost" | "Prims.Lemma")}, e1, [er; EFun ([(_, {name = Some xe}, _)], ee)]) when outer ->
      let dxe = { d_name = xe; d_qualifiers = []; d_category = "val"; d_udecls = []; d_binders = []; d_typ = e1; d_body = None} in
      let env2 = Map.add xe dxe env in
      //printfn "%A %A %A" (r e1) (is_vale_exp env er) (is_vale_exp env2 ee);
      r e1 && is_vale_exp env er && is_vale_exp env2 ee
  | EComp (EId {name = Some ("Prims.Tot" | "Prims.GTot")}, e, [])
  | EApp (EId {name = Some ("Tot" | "GTot")}, [(_, e)]) ->
      may_be_refine e
  | EApp (e, aes) -> is_vale_type_id env e && List.forall r (List.map snd aes)
  | EArrow (_, {name = Some x}, ((EType (UInt i)) as t), e2) when leftmost && i.Equals(bigint.Zero) ->
      let dx = { d_name = x; d_qualifiers = []; d_category = "type"; d_udecls = []; d_binders = []; d_typ = t; d_body = None} in
      let env = Map.add x dx env in
      is_vale_type outer true env e2
  | EArrow (_, {name = Some x}, ((EType (UInt i)) as t), e2) when not leftmost && i.Equals(bigint.Zero) ->
      set_reason ("type parameters must be in outermost position: " + x); false
  | EArrow (a, {name = Some x}, e1, e2) ->
    (
      let dx = { d_name = x; d_qualifiers = []; d_category = "val"; d_udecls = []; d_binders = []; d_typ = e1; d_body = None} in
      let env = Map.add x dx env in
      let b = may_be_refine e1 && is_vale_type outer false env e2 in
      match a with Explicit -> b | _ -> set_reason ("non-type parameters must be explicit, not inferred: " + x); false
    )
  // TODO: more cases
  | EUnsupported s -> set_reason s; false
  | _ -> set_reason ("not vale type: " + string_of_exp e); false
and is_vale_type_id (env:env) (e:exp):bool =
  match e with
  | EId {name = Some "Prims.logical"} -> true
  | EId {name = Some x} ->
    (
      match Map.tryFind x env with
      // REVIEW: is any "type" ok?
      | Some { d_category = "type" } -> true
      | _ -> set_reason x; false
    )
  | _ -> false
and is_vale_exp (env:env) (e:exp):bool =
  //printfn "is_vale_exp? %s" (string_of_exp e);
  let r = is_vale_exp env in
  match e with
  | EId _ -> Option.isSome (get_vale_exp_id env e)
  | EInt i -> true
  | EUnitValue -> true
  | EApp (e, aes) ->
    (
      match get_vale_exp_id env e with
      | None -> false
      | Some d ->
          let (ts, _) = take_arrows d.d_typ in
          if List.length ts <> List.length aes then false else
          let f (t:exp) (e:exp):bool =
            match t with
            | EType _ -> is_vale_type false false env e
            | _ -> is_vale_exp env e
            in
          List.forall (fun b -> b) (List.map2 f ts (List.map snd aes))
    )
  // TODO: more cases
  | EUnsupported s -> set_reason s; false
  | _ -> set_reason ("not vale expression: " + string_of_exp e); false
and get_vale_exp_id (env:env) (e:exp):decl option =
  match e with
  | EId {name = Some x} ->
    (
      match Map.tryFind x env with
      | Some ({ d_category = "val" } as d) -> Some d
      | _ -> set_reason x; None
    )
  | _ -> None

let as_int_constant (env:env) (e:exp):bigint option =
  match e with
  | EInt i -> Some i
  | EId {name = Some x} when Map.containsKey x env ->
    (
      match Map.find x env with
      | {d_category = "val"; d_udecls = []; d_binders = []; d_body = Some (EInt i)} -> Some i
      | _ -> None
    )
  | _ -> None

type range = bigint option * bigint option
let range_intersect (r1:range) (r2:range):range =
  let mix (merge:bigint * bigint -> bigint) (b1:bigint option) (b2:bigint option):bigint option =
    match (b1, b2) with
    | (None, None) -> None
    | (Some i, None) -> Some i
    | (None, Some i) -> Some i
    | (Some i1, Some i2) -> Some (merge (i1, i2))
    in
  ( mix System.Numerics.BigInteger.Max (fst r1) (fst r2),
    mix System.Numerics.BigInteger.Min (snd r1) (snd r2) )

// Turn an expression about range_var into a range
// Example: (5 <= range_var /\ range_var <= 10) becomes (Some 5, Some 10)
let rec as_range_constant (local_env:Map<string, bigint>) (range_var:string) (e:exp):range option =
  let r = as_range_constant local_env range_var in
  let binary_op (flip:bool) (xop:string) (i:bigint):range option =
    match (xop, flip) with
    | ("Prims.op_LessThanOrEqual", false) -> Some (None, Some i)
    | ("Prims.op_LessThanOrEqual", true) -> Some (Some i, None)
    | ("Prims.op_GreaterThanOrEqual", false) -> Some (Some i, None)
    | ("Prims.op_GreaterThanOrEqual", true) -> Some (None, Some i)
    | ("Prims.op_LessThan", false) -> Some (None, Some (i - bigint.One))
    | ("Prims.op_LessThan", true) -> Some (Some (i + bigint.One), None)
    | ("Prims.op_GreaterThan", false) -> Some (Some (i + bigint.One), None)
    | ("Prims.op_GreaterThan", true) -> Some (None, Some (i - bigint.One))
    | _ -> None
    in
  let binary_op_exp (flip:bool) (xop:string) (e:exp):range option =
    match e with
    | EInt i -> binary_op flip xop i
    | EId {name = Some x} when Map.containsKey x local_env ->
        binary_op flip xop (Map.find x local_env)
    | _ -> None
    in
  match e with
  | EId {name = Some ("true" | "Prims.l_True")} -> Some (None, None)
  | EApp (EId {name = Some "Prims.b2t"}, [(_, e)]) -> r e
  | EApp (EId {name = Some ("Prims.op_AmpAmp" | "Prims.l_and")}, [(_, e1); (_, e2)]) ->
    (
      match (r e1, r e2) with
      | (Some r1, Some r2) -> Some (range_intersect r1 r2)
      | _ -> None
    )
  | EApp (EId {name = Some xop}, [(_, EId {name = Some x}); (_, e)]) when x = range_var ->
      binary_op_exp false xop e
  | EApp (EId {name = Some xop}, [(_, e); (_, EId {name = Some x})]) when x = range_var ->
      binary_op_exp true xop e
  | _ -> None

let to_vale_decl ((env:env), (envs_ds_rev:(env * decl) list)) (d:decl):(env * (env * decl) list) =
  let d = universe0_decl d in
  let bs = d.d_binders in
  let bs_are_Type = List.forall (fun (_, _, e) -> match e with (Some (EType _)) -> true | _ -> false) bs in
  //printfn "examining %s" d.d_name;
  reason := None;
  let typed_binders = List.forall (fun (_, _, t) -> Option.isSome t) in
  let rec add_binders (bs:binder list) (e:exp):exp =
    match bs with
    | [] -> e
    | (a, x, t_opt)::bs -> EArrow (a, x, Option.get t_opt, add_binders bs e)
    in
  let envs_ds =
    match (bs, d.d_typ) with
    | (_, EType _) ->
        let body =
          match (bs, d.d_body) with
          // TODO: handle case with binders
          | ([], Some t) when is_vale_type false false env t -> Some t
          | _ -> None
          in
        let int_refine:(range option * (Map<string, bigint> option * string * exp) option) option =
          // t           --> Some (Some range(t), None)
          // x:t{bounds} --> Some (Some range(t), Some (None, x, bounds))
          if d.d_name = "Prims.int" then Some (Some (None, None), None) else
          let int_type_to_range (e:exp):range option =
            match e with
            | EId {name = Some "int"} -> Some (None, None)
            | EApp (EId {name = Some "int"}, [(_, b1); (_, b2)]) ->
                let get_bound b = match b with | EInt i -> Some i | _ -> None in
                Some (get_bound b1, get_bound b2)
            | _ -> None
            in
          let get_int_type (x:string):range option =
            match Map.tryFind x env with
            | Some {d_category = "type"; d_udecls = []; d_binders = []; d_body = Some e} ->
                int_type_to_range e
            | _ -> None
            in
          match d.d_body with
          | Some (EId {name = Some xt}) -> Some (get_int_type xt, None)
          | Some (EApp (EId {name = Some xt}, args)) ->
              let args = List.map snd args in
              let args = List.map (as_int_constant env) args in
              if List.forall Option.isSome args then
                let args = List.map Option.get args in
                match Map.tryFind xt env with
                | Some {d_category = "int_type_generator"; d_binders = bs; d_body = Some (ERefine ({name = Some xr}, et, bounds))}
                    when List.length bs = List.length args ->
                    let add_x_i env x i = Map.add x i env in
                    let xs = List.map (fun (_, (x:id), _) -> Option.get x.name) bs in
                    let local_env = List.fold2 add_x_i Map.empty xs args in
                    Some (int_type_to_range et, Some (Some local_env, xr, bounds))
                | _ -> None
              else
                None
          | Some (ERefine ({name = Some xr}, EId {name = Some xt}, bounds)) ->
              Some (get_int_type xt, Some (None, xr, bounds))
          | _ -> None
          in
        let range_to_int_type (r:range):exp =
          let eInt = EId {name = Some "int"; index = None} in
          let eIntRange = EId {name = Some "int_range"; index = None} in
          let eNone = EId {name = Some "_"; index = None} in
          match r with
          | (None, None) -> eInt
          | (Some b1, None) -> EApp (eIntRange, [(Explicit, EInt b1); (Explicit, eNone)])
          | (None, Some b2) -> EApp (eIntRange, [(Explicit, eNone); (Explicit, EInt b2)])
          | (Some b1, Some b2) -> EApp (eIntRange, [(Explicit, EInt b1); (Explicit, EInt b2)])
          in
        let int_refine = match int_refine with Some (Some r, z) -> Some (r, z) | _ -> None in
        match (bs, bs_are_Type, int_refine) with
        | (_, true, None) ->
            [(env, {d with d_category = "type"; d_body = body})]
        | (_, false, None) ->
            [(env, {d with d_category = "unsupported"; d_typ = EUnsupported "dependent type"})]
        | ([], _, Some (r, None)) ->
            [(env, {d with d_category = "type"; d_body = Some (range_to_int_type r)})]
        | ([], _, Some (r, Some (local_env_bounds_opt, xr, bounds))) ->
          (
            let local_env_bounds = Option.defaultValue Map.empty local_env_bounds_opt in
            match as_range_constant local_env_bounds xr bounds with
            | None ->
                [(env, {d with d_category = "unsupported"; d_typ = EUnsupported "unsupported integer bounds"})]
            | Some r_bounds ->
                [(env, {d with d_category = "type"; d_body = Some (range_to_int_type (range_intersect r r_bounds))})]
          )
        | (_, false, Some (r, Some (None, xr, bounds))) ->
            let rec resolve_bounds (e:exp):exp =
              match (as_int_constant env e, e) with
              | (Some i, _) -> EInt i
              | (_, EApp (e0, es)) -> EApp (e0, List.map (fun (a, e) -> (a, resolve_bounds e)) es)
              | _ -> e
              in
            let bounds = resolve_bounds bounds in
            let body = ERefine ({name = Some xr; index = None}, range_to_int_type r, bounds) in
            [(env, {d with d_category = "int_type_generator"; d_body = Some body})]
        | _ ->
            [(env, {d with d_category = "unsupported"; d_typ = EUnsupported "unsupported"})]
    | (bs, _) when typed_binders bs && is_vale_type true true env (add_binders bs d.d_typ) ->
        let body =
          match (bs, Option.bind (as_int_constant env) d.d_body) with
          | ([], Some i) -> Some (EInt i)
          | _ -> None
          in
        [(env, {d with d_category = "val"; d_body = body})]
    | _ ->
        let t = match !reason with None -> d.d_typ | Some s -> EUnsupported s in
        [(env, {d with d_category = "unsupported"; d_typ = t})]
    in
  let env = List.fold (fun env (_, d) -> Map.add d.d_name d env) env envs_ds in
  let envs_ds_rev = envs_ds @ envs_ds_rev in
  (env, envs_ds_rev)

let rec trees_of_comma_list (es:string_tree list):string_tree list =
  match es with
  | [] -> []
  | [e] -> [e]
  | e::es -> (st_list [e; st_leaf ","])::(trees_of_comma_list es)

let rec tree_of_vale_name (x:string):string_tree =
  let r = tree_of_vale_name in
  match x with
//  | ("Prop_s.prop0" | "Prims.prop" | "Prims.logical") -> st_leaf "prop"
  | _ when x.EndsWith(".decreases") -> r (x.Replace(".decreases", "._decreases"))
  | _ when x.EndsWith(".modifies") -> r (x.Replace(".modifies", "._modifies"))
  | _ ->
      let x = if x.StartsWith("'") then "_" + x else x in
      st_leaf (x.Replace("#", "_"))

let tree_of_vale_id (id:id):string_tree =
  match id with
  | {name = Some x} -> tree_of_vale_name x
  | _ -> err ("internal error: tree_of_vale_id: " + string_of_id id)

let tree_of_vale_kind (e:exp):string_tree =
  match e with
  | EType (UInt i) -> st_leaf ("Type(" + i.ToString() + ")")
  | _ -> err ("internal error: tree_of_vale_kind: " + string_of_exp e)

let rec tree_of_vale_type (e:exp):string_tree =
  let r = tree_of_vale_type in
  match e with
  | EId id -> tree_of_vale_id id
  | EInt i -> st_leaf (i.ToString())
  | EBool -> st_leaf "bool"
  | EProp -> st_leaf "prop"
  | EComp (EId {name = Some ("Prims.Tot" | "Prims.GTot")}, e, [])
  | EApp (EId {name = Some ("Tot" | "GTot")}, [(_, e)]) -> r e
  | EApp (e, aes) ->
      // TODO: tuples are special case
      st_paren [r e; st_paren (trees_of_comma_list (List.map (snd >> r) aes))]
  | EArrow _ ->
      let (es, e) = take_arrows e in
      st_paren [st_leaf "fun"; st_paren (trees_of_comma_list (List.map r es)); st_leaf "->"; r e]
  | _ -> err ("internal error: tree_of_vale_type: " + string_of_exp e)

let tree_of_vale_type_kind (e:exp):string_tree =
  match e with
  | EType _ -> tree_of_vale_kind e
  | _ -> tree_of_vale_type e

let rec tree_of_vale_exp (env:env) (e:exp):string_tree =
  let r = tree_of_vale_exp env in
  match e with
  | EId x -> tree_of_vale_id x
  | EInt i -> st_leaf (i.ToString())
  | EUnitValue -> st_leaf "tuple()"
  | EApp (e, aes) ->
      let ts =
        match get_vale_exp_id env e with
        | None -> List.map (fun _ -> e) aes // not a top-level decl; no type arguments allowed
        | Some d -> fst (take_arrows d.d_typ)
        in
      let f (t:exp) (e:exp):string_tree =
        match t with
        | EType _ -> tree_of_vale_type e
        | _ -> tree_of_vale_exp env e
        in
      let ss = List.map2 f ts (List.map snd aes) in
      st_paren [r e; st_paren (trees_of_comma_list ss)]
  | ELet ((_, x, Some t), e1, e2) ->
      st_paren [st_list [st_leaf "let"; tree_of_vale_id x; st_leaf ":"; tree_of_vale_type t; st_leaf ":="; r e1; st_leaf "in"]; r e2]
  | _ -> err ("internal error: tree_of_vale_exp: " + string_of_exp e)

// returns parameters, requires, ensures, return type
let rec take_params (e:exp):(binder list * exp list * (id * exp) option * exp) =
  let may_be_refine_req (x:id) (e:exp):(exp list * exp) =
    match e with
    | ERefine (x1, e1, e2) ->
        let req = ELet ((Explicit, x1, Some e1), EId x, e2) in
        ([req], e1)
    | _ -> ([], e)
    in
  let may_be_refine_ens (e:exp):((id * exp) option * exp) =
    match e with
    | ERefine (x1, e1, e2) -> (Some (x1, e2), e1)
    | _ -> (None, e)
    in
  match e with
  | EArrow (a, x, t, e2) ->
      let (req, t) = may_be_refine_req x t in
      let b = (a, x, Some t) in
      let (bs, reqs, enss, e) = take_params e2 in
      (b::bs, req @ reqs, enss, e)
  | EComp (EId {name = Some ("Prims.Pure" | "Prims.Ghost" | "Prims.Lemma")}, e1, [req; EFun ([(_, xens, _)], ens)]) ->
      ([], [req], Some (xens, ens), e1)
  | EComp (EId {name = Some ("Prims.Tot" | "Prims.GTot")}, e, [])
  | EApp (EId {name = Some ("Tot" | "GTot")}, [(_, e)])
  | e ->
      let (ens, e) = may_be_refine_ens e in
      ([], [], ens, e)

let tree_of_vale_decl (env:env) (d:decl):string_tree =
  match d.d_category with
  | "type" ->
    (
      let ps =
        match d.d_binders with
        | [] -> []
        | bs ->
            let f (_, x, k) = st_list [tree_of_vale_id x; st_leaf ":"; tree_of_vale_kind (Option.get k)] in
            [st_paren (trees_of_comma_list (List.map f bs))]
        in
      let typing = [st_leaf ":"; tree_of_vale_kind d.d_typ] in
      let body =
        match d.d_body with
        | None -> [st_leaf "extern"; st_leaf ";"]
        | Some t -> [st_leaf ":="; tree_of_vale_type t; st_leaf ";"]
        in
      st_list ([st_leaf "type"; tree_of_vale_name d.d_name] @ ps @ typing @ body)
    )
  | "val" ->
    (
      let (bs, reqs, enss, t) = take_params d.d_typ in
      let bs = d.d_binders @ bs in
      let (prefix, ps) =
        match bs with
        | [] -> ("const", [])
        | _ ->
            let (bst, bsv) = List.partition (fun (_, _, t) -> match t with Some (EType _) -> true | _ -> false) bs in
            let f (a, x, t) =
              let tree_a = match a with Explicit -> [] | _ -> [st_leaf "#"] in
              st_list (tree_a @ [tree_of_vale_id x; st_leaf ":"; tree_of_vale_type_kind (Option.get t)])
              in
            let tparams = match bst with [] -> [] | _ -> [make_st_list "#[" "]" (trees_of_comma_list (List.map f bst))] in
            ("function", tparams @ [st_paren (trees_of_comma_list (List.map f bsv))])
        in
      let tree_req = List.map (fun e -> st_list [st_leaf "requires"; tree_of_vale_exp env e; st_leaf ";"]) reqs in
      let tree_t = tree_of_vale_type t in
      let (tree_t, tree_ens) =
        match enss with
        | None -> (tree_t, [])
        | Some (x, e) ->
            (st_paren [tree_of_vale_id x; st_leaf ":"; tree_t], [st_list [st_leaf "ensures"; tree_of_vale_exp env e; st_leaf ";"]])
        in
      let typing = [st_leaf ":"; tree_t] @ tree_req @ tree_ens @ [st_leaf "extern"; st_leaf ";"] in
      st_list ([st_leaf prefix; tree_of_vale_name d.d_name] @ ps @ typing)
    )
  | _ -> err ("internal error: tree_of_vale_decl: " + d.d_category)

let main (argv:string array) =
  let in_files_rev = ref ([]:string list) in
  let outfile = ref (None:string option) in
  let lexbufOpt = ref (None:LexBuffer<byte> option)
  let arg_list = argv |> Array.toList in
  let print_err (err:string):unit =
    printfn "Error:";
    match !lexbufOpt with
    | None -> printfn "%s" err;
    | Some lexbuf ->
        printfn "%s" err;
        printfn "\nerror at line %i column %i of string\n%s" (line lexbuf) (col lexbuf) (file lexbuf);
        exit 1
    in
  try
  (
    let parse_argv (args:string list) =
      let rec match_args (arg_list:string list) =
        match arg_list with
        | "-in" :: l ->
          match l with
          | [] -> failwith "Specify input file"
          | f :: l -> in_files_rev := f::!in_files_rev; match_args l
        | "-out" :: l ->
          match l with
          | [] -> failwith "Specify output file"
          | f :: l -> outfile := Some f; match_args l
        | f :: l ->
            failwith ("Unrecognized argument: " + f + "\n")
        | [] -> if List.length !in_files_rev = 0 then failwith "Use -in to specify input file"
        in
        match_args args
      in
    parse_argv (List.tail arg_list);
    let in_files = List.rev (!in_files_rev) in
    let read_file (name:string):string list =
      let rec splitWhereRec (f:'a -> bool) (in1:'a list) (out1:'a list) (outn:'a list list):'a list list =
        match (in1, out1) with
        | ([], []) -> outn
        | ([], _::_) -> out1::outn
        | (h::t, []) when f h -> splitWhereRec f t [h] outn
        | (h::t, _::_) when f h -> splitWhereRec f t [h] (out1::outn)
        | (h::t, _) -> splitWhereRec f t (h::out1) outn
        in
      let splitWhere (f:'a -> bool) (l:'a list):'a list list =
        List.rev (List.map List.rev (splitWhereRec f l [] []))
        in
      let lines = Array.toList (System.IO.File.ReadAllLines(name)) in
      let sModule = "Module after type checking:" in
      let line_is_new_module (x:string):bool = (x = sModule || x.StartsWith("Verified ") || x.StartsWith("All verification")) in
      let modules = splitWhere line_is_new_module lines in
      let modules = List.filter (fun (x:string list) -> match x with s::_ when s = sModule -> true | _ -> false) modules in
      let get_module_blocks (lines:string list):string list list =
        let lines = List.filter (fun (x:string) -> not (x.StartsWith("#") || x.Contains("): (Warning "))) lines in
        match splitWhere (fun (x:string) -> x = "Exports:") lines with
        | [_; (_::lines)] ->
            splitWhere
              (fun (x:string) ->
                // REVIEW: this is to break Sig_bundle or other groups apart; this could be better
                x.StartsWith("(* Sig_bundle *)") ||
                x.StartsWith("[@") ||
                x.StartsWith("val ") ||
                x.StartsWith("assume ") ||
                x.StartsWith("datacon<") ||
                x.StartsWith("unfold let ") ||
                x.StartsWith("sub_effect ") ||
                x.StartsWith("(Discriminator ") ||
                x.StartsWith("visible (Discriminator "))
              lines
        | _ -> []
        in
      let module_blocks = List.map get_module_blocks modules in
      let all_blocks = List.concat module_blocks in
      let all_blocks = List.map (List.map (fun (x:string) -> x.Replace("[set_options \"--z3rlimit 20\"]", "[set_options '--z3rlimit 20']"))) all_blocks in // HACK
      List.map (String.concat "\n") all_blocks
      in
    let blocks = List.collect read_file in_files in
    let parse_block (s:string):decl list =
      //printfn "%s" s;
      let bytes = System.Text.Encoding.UTF8.GetBytes(s) in
      let lexbuf = LexBuffer<byte>.FromBytes bytes in
      setInitialPos lexbuf s;
      lexbufOpt := Some lexbuf;
      let res = Parse.start Lex.lextoken lexbuf in
      lexbufOpt := None;
      //List.iter (fun e -> print_tree "" (tree_of_raw_exp e)) res;
      let res = List.map simplify_raw_exp res in
      let ds = List.map parse_decl res in
      let ds =
        match ds with
        | d::_ when List.exists (fun s -> s = "abstract") d.d_qualifiers -> [d]
        | _ -> ds
        in
      ds
      in
    let ds = List.collect parse_block blocks in
    let ds = filter_decls ds in
    let ds = List.map decl_lift_type_binders ds in
    let ds = List.map decl_unsupported ds in
    let ds = List.map index_to_var_decl ds in
    let (env, envs_ds_rev) = List.fold to_vale_decl (Map.empty, []) ds in
    let envs_ds = List.rev envs_ds_rev in
    let duplicates = ref (Set.empty : Set<string>) in
    List.iter
      (fun (env, d) ->
        if not (Set.contains d.d_name (!duplicates)) then
         (
          // REVIEW: why are there duplicates?
          duplicates := Set.add d.d_name (!duplicates);
          match (d.d_category, d.d_typ) with
          | (_, EUnsupported s) -> printfn "unsupported: %s //(reason: %s)" d.d_name s; printfn ""
          | ("unsupported", _) -> printfn "unsupported: %s" d.d_name; printfn ""
          | ("int_type_generator", _) -> printfn "unsupported (int type generator): %s" d.d_name; printfn ""
          | _ -> print_tree "" (tree_of_vale_decl env d); printfn ""
         )
      )
      envs_ds;
    ()
  )
  with
  | Err err -> print_err err
  | ParseErr err -> print_err err
  | Failure err -> print_err err
  | err -> print_err (err.ToString ())

let () = main (System.Environment.GetCommandLineArgs ())
