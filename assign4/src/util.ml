open Core
open Ast;;

let expr_to_bool = function 
	| Expr.True -> true
	| Expr.False -> false
	| _ -> failwith "Try to convert non-boolean-value expr to boolean"
	
let bool_to_expr = function
	| true -> Expr.True
	| false -> Expr.False

let expr_and left right = 
  bool_to_expr ((expr_to_bool left ) && (expr_to_bool right))

let expr_or left right = 
  bool_to_expr ((expr_to_bool left ) || (expr_to_bool right))

let expr_type_list_to_string (l : (Expr.t * Type.t) list) =
  String.concat ~sep:"\n" (List.map l ~f:(fun (ex, ty) -> (Expr.to_string ex) ^ " : " ^ (Type.to_string ty))) 
  
let expr_expr_to_num_num left right =
  (match (left, right) with 
    | (Expr.Num n1, Expr.Num n2) -> (n1, n2)
    | _, _ -> failwith ("Not both sides are nums" ^ (Expr.to_string left) ^ (Expr.to_string right)))

let pe s = print_endline (Expr.to_string s)
let pt s = print_endline (Type.to_string s)

let update_ctx ctx x tau= String.Map.change ctx x ~f:(function | Some _ | None -> Some tau)