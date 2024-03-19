open Flags
open Core
open Util
open Result.Monad_infix
open Ast

exception Unimplemented


let rec typecheck_expr (ctx : Type.t String.Map.t) (e : Expr.t)
  : (Type.t, string) Result.t =
  match e with
  | Expr.Num _ -> Ok Type.Num

  | Expr.Binop {left; right; _} ->
    typecheck_expr ctx left >>= fun tau_left ->
    typecheck_expr ctx right >>= fun tau_right ->
    (match (tau_left, tau_right) with
     | (Type.Num, Type.Num) -> Ok Type.Num
     | _ -> Error (
       Printf.sprintf
         "Binary operands have incompatible types: (%s : %s) and (%s : %s)"
         (Expr.to_string left) (Type.to_string tau_left)
         (Expr.to_string right) (Type.to_string tau_right)))

  | Expr.True | Expr.False -> Ok Type.Bool

  | Expr.And {left; right}| Expr.Or {left; right} -> 
    typecheck_expr ctx left >>= fun tau_left ->
    typecheck_expr ctx right >>= fun tau_right ->
      (match (tau_left, tau_right) with
        | (Type.Bool, Type.Bool) -> Ok Type.Bool
        | _, _ -> Error (
            "And/Or operands have imcompatible types:\n"
            ^ (expr_type_list_to_string [(left, tau_left); (right, tau_right)]) ^ "\n"
        ))

  | Expr.Relop {relop = _; left; right} -> 
    typecheck_expr ctx left >>= fun tau_left ->
    typecheck_expr ctx right >>= fun tau_right ->
      (match (tau_left, tau_right) with
        | (Type.Num, Type.Num) -> Ok Type.Bool
        | _, _ -> Error (
          "Relational operand have incompatible types:\n"
          ^ (expr_type_list_to_string [(left, tau_left); (right, tau_right)]) ^ "\n"
        ))
  | Expr.If {cond; then_; else_;} ->
    typecheck_expr ctx cond >>= fun tau_cond ->
    typecheck_expr ctx then_ >>= fun tau_then ->
    typecheck_expr ctx else_ >>= fun tau_else ->
      (match tau_cond with
        | Type.Bool ->  if (Ast_util.Type.aequiv tau_then tau_else) then 
                          Ok tau_then
                        else
                          Error (
                            "The branches of if expression have different types:\n"
                            ^ (expr_type_list_to_string [(then_, tau_then); (else_, tau_else)]) ^ "\n"
                          )
        | _ -> Error(
          "The condition of if is not of type bool\n"
            ^ (expr_type_list_to_string [(cond,tau_cond)]) ^ "\n"
        ))
  | Expr.Lam {x; tau; e} -> 
      let ctx' = update_ctx ctx x tau in
      typecheck_expr ctx' e >>= fun tau_ret ->
        Ok (Type.Fn {arg = tau; ret = tau_ret})
  
  | Expr.Var x ->
      (match String.Map.find ctx x with
      | Some ty -> Ok ty
      | None -> Error (
        "The variable has no type: "
        ^ x
      ))
  
  | Expr.App {lam; arg} ->
    typecheck_expr ctx lam >>= fun tau_lam ->
    typecheck_expr ctx arg >>= fun tau_arg ->
      (match tau_lam with
        | Type.Fn {arg=arg_; ret=ret_} -> if (Ast_util.Type.aequiv arg_ tau_arg) then
                                  Ok ret_
                                else
                                  Error (
                                    "The type of arg doesn't match:\n"
                                    ^ (expr_type_list_to_string [(lam, tau_lam); (arg, tau_arg)]) ^ "\n"
                                  )
        | _ -> Error (
          "Try to apply to non-function"
          ^ (expr_type_list_to_string [(lam, tau_lam); (arg, tau_arg)]) ^ "\n"
        ))
  
  | Expr.Unit -> Ok Type.Unit

  | Expr.Pair {left; right} -> 
    typecheck_expr ctx left >>= fun tau_left ->
    typecheck_expr ctx right >>= fun tau_right ->
      Ok (Type.Product {left= tau_left; right = tau_right})

  | Expr.Project {e; d} -> 
    typecheck_expr ctx e >>= fun tau_pair ->
      ( match tau_pair with 
        | Type.Product {left; right} ->
            ( match d with 
              | Left -> Ok left
              | Right -> Ok right)
        | _ -> Error (
          "The left part of the project is not a pair:"
          ^ (expr_type_list_to_string [(e, tau_pair)]) ^ "\n"
        ))

  | Expr.Inject {e; d; tau} ->
    typecheck_expr ctx e >>= fun tau_e ->
      ( match tau with
        | Type.Sum {left; right} ->
          ( let (tau_expect,dir) =  match d with 
            | Left -> (left, "left ")
            | Right -> (right, "right ") in
            if ( Ast_util.Type.aequiv tau_expect tau_e) then 
                        Ok tau 
                      else Error(
                        "A conflict in the sum type:\n"
                        ^ (expr_type_list_to_string [(e, tau_e)]) ^ " in " ^ dir ^ (Type.to_string tau) ^ "\n"
                      ))
        | _ -> Error ("Try to inject into a non-sum-type:"
                      ^ (Type.to_string tau) ^ "\n"
                ))

  | Expr.Case {e; xleft; eleft; xright; eright;} ->
    typecheck_expr ctx e >>= fun tau_inj ->
      ( match tau_inj with
        | Type.Sum {left; right} -> 
          let ctx_l = update_ctx ctx xleft left in
          typecheck_expr ctx_l eleft >>= fun tau_left ->
            let ctx_r = update_ctx ctx xright right in
            typecheck_expr ctx_r eright >>= fun tau_right ->
              if (Ast_util.Type.aequiv tau_left tau_right) then 
                Ok tau_left
              else
                Error (
                  "The branches have diifernet type:\n"
                  ^ (expr_type_list_to_string [(eleft, tau_left); (eright, tau_right)])
                )
        | _ -> Error (
          "try to case over a non-sum value:\n" ^ ( Expr.to_string e) ^ "\n"
        ))
        
                              

  | _ -> raise Unimplemented

let typecheck t = typecheck_expr String.Map.empty t

(* let inline_tests () =
  let p_ex = Parser.parse_expr_exn in
  let p_ty = Parser.parse_type_exn in
  let e1 = p_ex "fun (x : num) -> x" in
  assert (typecheck e1 = Ok(p_ty "num -> num"));

  let e2 = p_ex "fun (x : num) -> y" in
  assert (Result.is_error (typecheck e2));

  let t3 = p_ex "(fun (x : num) -> x) 3"in
  assert (typecheck t3 = Ok(p_ty "num"));

  let t4 = p_ex "((fun (x : num) -> x) 3) 3" in
  assert (Result.is_error (typecheck t4));

  let t5 = p_ex "0 + (fun (x : num) -> x)" in
  assert (Result.is_error (typecheck t5)) *)

(* Uncomment the line below when you want to run the inline tests. *)
(* let () = inline_tests () *)
