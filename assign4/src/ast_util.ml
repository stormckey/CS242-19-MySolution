open Flags
open Core
open Util

exception Unimplemented


module Type = struct
  open Ast.Type

  let rec substitute_map (rename : t String.Map.t) (tau : t) : t =
    let sub1 = substitute_map rename in
    let refresh rename x  = String.Map.change rename x ~f:(function | Some _ | None -> Some( Var (fresh x))) in
    match tau with
    | Num | Bool | Unit -> tau
    | Var x -> 
      ( match String.Map.find rename x with
        | Some x' -> x'
        | None -> Var x)
    | Fn {arg; ret} -> Fn {
      arg = sub1 arg;
      ret = sub1 ret;}
    | Product {left; right} -> Product {
      left = sub1 left;
      right = sub1 right;}
    | Sum {left; right} -> Sum {
      left = sub1 left;
      right = sub1 right;}
    | Rec {a; tau} -> 
      let rename' = refresh rename a in
      Rec {a = fresh a; tau = substitute_map rename' tau}
    | Forall {a; tau} -> 
      let rename' = refresh rename a in 
      Forall {a = fresh a; tau = substitute_map rename' tau}
    | _ -> raise Unimplemented

  let substitute (x : string) (tau' : t) (tau : t) : t =
    substitute_map (String.Map.singleton x tau') tau

  let rec to_debruijn (tau : t) : t =
    let rec aux (index : int String.Map.t) (tau : t) : t =
      let aux1 = aux index in
      match tau with
      | Num | Bool | Unit -> tau
      | Var x ->
        (match String.Map.find index x with 
          | Some depth -> Var (Int.to_string depth)
          | None -> tau)
      | Fn {arg; ret} -> Fn {
        arg = aux1 arg;
        ret = aux1 ret;}
      | Product {left; right} -> Product {
        left = aux1 left;
        right = aux1 right}
      | Sum {left; right} -> Sum {
        left = aux1 left;
        right = aux1 right;}
      | Rec {a; tau} ->
        let new_tau = new_tau_after_increased_depth index a tau in
        Rec {a = "_"; tau = new_tau}
      | Forall {a; tau} -> 
        let new_tau = new_tau_after_increased_depth index a tau in
        Forall {a = "_"; tau = new_tau}
      | _ -> raise Unimplemented
    and new_tau_after_increased_depth index a tau = 
      let increased_index = String.Map.map index ~f:(fun i -> i + 1) in
      let new_index = String.Map.add_exn increased_index ~key:a ~data:0 in
      aux new_index tau

    in
    aux String.Map.empty tau

  let aequiv (tau1 : t) (tau2 : t) : bool =
    let rec aux (tau1 : t) (tau2 : t) : bool =
      match (tau1, tau2) with
      | (Num, Num) -> true
      | (Bool, Bool) | (Unit, Unit) -> true
      | (Var x, Var y) -> x = y
      | (Fn x, Fn y) -> aux x.arg y.arg && aux x.ret y.ret
      | (Sum x, Sum y) -> aux x.left y.left && aux x.right y.right
      | (Product x, Product y) -> aux x.left y.left && aux x.right y.right
      | (Rec x, Rec y) -> aux x.tau y.tau
      | (Forall x, Forall y) -> aux x.tau y.tau
      | (Exists x, Exists y) -> aux x.tau y.tau
      | _ -> false
    in
    aux (to_debruijn tau1) (to_debruijn tau2)

  let inline_tests () =
    let p = Parser.parse_type_exn in

    assert (
      aequiv
        (substitute "a" (p "num") (p "forall b . a"))
        (p "forall a . num"));
    assert (
      aequiv
        (substitute "a" (p "b") (p "forall b . a"))
        (p "forall c . b"));
    assert (
      not (aequiv
        (substitute "a" (p "b") (p "forall b . a"))
        (p "forall b . b")));
    assert (
      aequiv
        (substitute "a" (p "b") (p "forall b . forall b . a"))
        (p "forall q . forall c . b"));
    assert (
      not (aequiv
        (substitute "a" (p "b") (p "forall b . forall b . a"))
        (p "forall a . forall b . a")));

    assert (aequiv (p "forall a . a") (p "forall b . b"));
    assert (not (aequiv (p "forall a . a") (p "forall b . num")));
    assert (aequiv
              (p "forall a . forall b . a -> b")
              (p "forall x . forall y . x -> y"))

  (* Uncomment the line below when you want to run the inline tests. *)
  (* let () = inline_tests () *)
end

module Expr = struct
  open Ast.Expr

  let rec substitute_map (rename : t String.Map.t) (e : t) : t =
    let sub1 = substitute_map rename in
    match e with
    | Num _ | True | False | Unit -> e
    | Binop {binop; left; right} -> Binop {
      binop;
      left = sub1 left;
      right = sub1 right}
    | Relop {relop; left; right} -> Relop {
      relop;
      left = sub1 left;
      right = sub1 right}
    | If {cond; then_; else_;} -> If {
      cond = sub1 cond;
      then_ = sub1 then_;
      else_ = sub1 else_;}
    | And {left; right} -> And {
      left = sub1 left;
      right = sub1 right}
    | Or {left; right} -> Or {
      left = sub1 left;
      right = sub1 right}
    | Lam {x; tau; e} -> 
      let rename' = refresh rename x in
      Lam {x = fresh x; tau; e = substitute_map rename' e}
    | Var x -> (match String.Map.find rename x with 
                | Some x' -> x'
                | None -> Var x)
    | App {lam; arg} -> App {
      lam = sub1 lam;
      arg = sub1 arg} 
    | Pair {left; right} -> Pair {
      left = sub1 left;
      right = sub1 right;}
    | Project {e; d} -> Project {
      e = sub1 e;
      d;}
    | Inject {e; d; tau} -> Inject {
      e = sub1 e;
      d;
      tau;}
    | Case {e; xleft; eleft; xright; eright} ->
        let rename_l = refresh rename xleft in
        let rename_r = refresh rename xright in
        Case {
          e = sub1 e;
          xleft = fresh xleft;
          eleft = substitute_map rename_l eleft;
          xright = fresh xright;
          eright = substitute_map rename_r eright;}
    | Fix {x; tau; e} ->
      let rename' = refresh rename x in
      Fix {
        x = fresh x;
        tau;
        e = substitute_map rename' e;}
    | TyLam {a; e} ->
      let rename' = refresh rename a in
      TyLam {
        a = fresh a;
        e = substitute_map rename' e;}
    | TyApp {e; tau} -> TyApp {
      e = sub1 e;
      tau;}
    | _ -> raise Unimplemented

  let substitute (x : string) (e' : t) (e : t) : t =
    substitute_map (String.Map.singleton x e') e

  let rec to_debruijn (e : t) : t =
    let rec aux (depth : int String.Map.t) (e : t) : t =
      match e with
      | Num _ -> e
      | Binop {binop; left; right} -> Binop {
        binop; left = aux depth left; right = aux depth right}
      (* Add more cases here! *)
      | _ -> raise Unimplemented
    in
    aux String.Map.empty e

  let aequiv (e1 : t) (e2 : t) : bool =
    let rec aux (e1 : t) (e2 : t) : bool =
      match (e1, e2) with
      | (Num n1, Num n2) -> n1 = n2
      | (Var x, Var y) -> x = y
      | (Binop l, Binop r) ->
        l.binop = r.binop && aux l.left r.left && aux l.right r.right
      | (True, True) | (False, False) -> true
      | (If l, If r) ->
        aux l.cond r.cond && aux l.then_ r.then_ && aux l.else_ r.else_
      | (Relop l, Relop r) ->
        l.relop = r.relop && aux l.left r.left && aux l.right r.right
      | (And l, And r) ->
        aux l.left r.left && aux l.right r.right
      | (Or l, Or r) ->
        aux l.left r.left && aux l.right r.right
      | (Lam l, Lam r) ->
        aux l.e r.e
      | (App l, App r) ->
        aux l.lam r.lam && aux l.arg r.arg
      | (Unit, Unit) -> true
      | (Pair l, Pair r) ->
        aux l.left r.left && aux l.right r.right
      | (Project l, Project r) ->
        aux l.e r.e && l.d = r.d
      | (Inject l, Inject r) ->
        aux l.e r.e && l.d = r.d
      | (Case l, Case r) ->
        aux l.e r.e && aux l.eleft r.eleft && aux l.eright r.eright
      | (Fix l, Fix r) -> aux l.e r.e
      | (TyLam l, TyLam r) ->
        aux l.e r.e
      | (TyApp l, TyApp r) -> aux l.e r.e
      | (Fold_ l, Fold_ r) -> aux l.e r.e
      | (Unfold l, Unfold r) -> aux l r
      | (Export l, Export r) -> aux l.e r.e
      | (Import l, Import r) -> aux l.e_mod r.e_mod && aux l.e_body r.e_body
      | _ -> false
    in
    aux (to_debruijn e1) (to_debruijn e2)

  let inline_tests () =
    let p = Parser.parse_expr_exn in
    let t1 = p "(fun (x : num) -> x) y" in
    assert (aequiv (substitute "x" (Num 0) t1) t1);
    assert (aequiv (substitute "y" (Num 0) t1)
              (p "(fun (x : num) -> x) 0"));

    let t2 = p "x + (fun (x : num) -> y)" in
    assert (aequiv
              (substitute "x" (Num 0) t2)
              (p "0 + (fun (x : num) -> y)"));
    assert (aequiv (substitute "y" (Num 0) t2)
              (p "x + (fun (x : num) -> 0)"));

    assert (aequiv (p "fun (x : num) -> x") (p "fun (y : num) -> y"));

    assert (not (aequiv (p "fun (x : num) -> fun (x : num) -> x + x")
                   (p "fun (x : num) -> fun (y : num) -> y + x")));

    assert (
      aequiv
        (p "tyfun a -> fun (x : a) -> x")
        (p "tyfun b -> fun (x : b) -> x"));

    ()

  (* Uncomment the line below when you want to run the inline tests. *)
  (* let () = inline_tests () *)
end
