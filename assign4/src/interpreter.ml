open Flags
open Core
open Util
open Ast

type outcome =
  | Step of Expr.t
  | Val

exception RuntimeError of string

let rec trystep (e : Expr.t) : outcome =
  match e with
  | (Expr.Lam _ | Expr.Num _ | Expr.True | Expr.False | Expr.Pair _ | Expr.Unit
    | Expr.Inject _ | Expr.TyLam _ | Expr.Export _ | Expr.Fold_ _) -> Val

  | Expr.Binop {binop; left; right} ->
    (left, fun left' -> Expr.Binop {left = left'; binop; right;}) |-> fun () ->
    (right, (fun right' -> Expr.Binop {right = right'; binop; left})) |-> fun () ->
			let n1, n2 = expr_expr_to_num_num left right in
				let op = (match binop with
					| Expr.Add -> (+)
					| Expr.Sub -> (-) 
					| Expr.Mul -> ( * )
					| Expr.Div -> (/) )
				in
				Step (Expr.Num (op n1 n2))

	| Expr.And {left; right} ->
		(left, fun left' -> Expr.And {left= left'; right}) |-> fun () ->
		(right, fun right' -> Expr.And {left; right= right'}) |-> fun () ->
			Step( expr_and left right)

	| Expr.Or {left; right} ->
		(left, fun left' -> Expr.Or {left= left'; right}) |-> fun () ->
		(right, fun right' -> Expr.Or {left; right= right'}) |-> fun () ->
			Step( expr_or left right)
	
	| Expr.Relop {relop; left; right} -> 
		(left, fun left' -> Expr.Relop {relop; left= left'; right}) |-> fun () ->
		(right, fun right' -> Expr.Relop {relop; left; right = right'}) |-> fun () ->
			let n1, n2 = expr_expr_to_num_num left right in
			let op = (match relop with
								| Expr.Lt -> (<)
								| Expr.Gt -> (>)
								| Expr.Eq -> (=)) in
			Step(bool_to_expr (op n1 n2))

	| Expr.If {cond; then_; else_ } -> 
		(cond, fun cond' -> Expr.If {cond = cond'; then_; else_}) |-> fun () ->
			(match cond with
				| Expr.True -> Step(then_)
				| Expr.False -> Step(else_)
				| _ -> failwith "If condition not boolean in eval")
		

	| Expr.App {lam; arg} -> 
		(lam, fun lam' -> Expr.App {lam = lam'; arg}) |-> fun () ->
		(match lam with 
			| Lam {x; tau = _; e} -> 
				Step (Ast_util.Expr.substitute x arg e)
			| _ -> failwith "try to call to a non-function")

  | Expr.Project {e; d} -> 
		(e, fun e' -> Expr.Project {e = e'; d}) |-> fun () ->
      ( match e with 
        | Expr.Pair {left; right} -> 
          (match d with 
            | Left -> Step left
            | Right -> Step right)
        | _ -> failwith "the left part of a projection is not a pair")

  | Expr.Case {e; xleft; eleft; xright; eright} ->
		(e, fun e' -> Expr.Case {e = e'; xleft; eleft; xright; eright}) |-> fun () ->
		( match e with
			| Expr.Inject {e; d; _} ->
					let (x, e') = match d with
												| Left -> (xleft, eleft)
												| Right -> (xright, eright) in
					Step (Ast_util.Expr.substitute x e e')			

			| _ -> failwith "try to case over a non-sum type") 

	| Expr.Fix {x; e; _}  as fix -> 
		Step (Ast_util.Expr.substitute x fix e)
	
	| Expr.TyApp {e; tau} ->
			(e, fun e' -> Expr.TyApp {e = e'; tau}) |-> fun () ->
				(match e with
					| Expr.TyLam {e; _} ->
						Step (e)
					| _ -> failwith "the left of a type application is not a polymorphic function")
	
	| Expr.Unfold t ->
			(t, fun t' -> Unfold t') |-> fun () ->
				( match t with 
					| Expr.Fold_ {e; _} ->
							Step (e)
					| _ -> failwith "Try to unfold a non-recursive type")
				
	| Expr.Import {x; a; e_mod; e_body} ->
		(e_mod, fun e_mod' -> Expr.Import {x; a; e_mod = e_mod'; e_body}) |-> fun () ->
			(match e_mod with
				| Expr.Export {e; _} -> 
					Step ( Ast_util.Expr.substitute x e e_body)
				| _ -> failwith "Try to import a non-existential type")
		

  | _ -> raise (RuntimeError (
    sprintf "Reached a stuck state at expression: %s" (Expr.to_string e)))

and (|->) ((e, hole) : Expr.t * (Expr.t -> Expr.t)) (next : unit -> outcome)
  : outcome =
  match trystep e with Step e' -> Step (hole e') | Val -> next ()

let rec eval e =
  match trystep e with
  | Step e' ->
    (if extra_verbose () then
       Printf.printf "Stepped:\n%s\n|->\n%s\n\n"
         (Expr.to_string e) (Expr.to_string e'));
    eval e'
  | Val -> Ok e

(* let inline_tests () =
  let p = Parser.parse_expr_exn in
  let e1 = p "2 + 3" in
  assert (trystep e1 = Step(Expr.Num 5));

  let e2 = p "(fun (x : num) -> x) 3" in
  assert (trystep e2 = Step(Expr.Num 3)) *)

(* Uncomment the line below when you want to run the inline tests. *)
(* let () = inline_tests () *)
