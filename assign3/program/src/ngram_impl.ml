open Core

exception Unimplemented

type ngram = string list
type ngram_map = (ngram, string list) Map.Poly.t
type word_distribution = (string, float) Map.Poly.t

let rec append_n l (n : int) = 
    if n = 0 then l else
      match l with 
      | [] -> failwith "list too short for ngram size"
      | hd :: tl -> hd :: (append_n (tl @ [hd]) (n-1))

let compute_ngrams (l : string list) (n : int) : string list list =
  if List.length l < n then failwith "list too short for ngram size" else
  append_n l (n-1)
  |> List.fold_left ~init:([], []) ~f:(fun (all_grams, cur_gram) (s: string) : (string list list * string list) ->
    if List.length cur_gram < n - 1 then
      ([], cur_gram @ [s])
    else if List.length cur_gram = n - 1 then 
      let new_gram = cur_gram @ [s] in 
      ([new_gram], new_gram)
    else
      let new_gram = match cur_gram with 
                      | _ :: tl -> tl @ [s] 
                      | _ -> failwith "cur_gram too small" in
      (all_grams @ [new_gram], new_gram)
  )
  |> fst
;;

let ngram_map_add (map : ngram_map) (ngram : ngram) : ngram_map =
  let n = List.length ngram in 
  let (hd, tl) = List.split_n ngram ( n-1 ) in
  match (Map.Poly.find map hd ) with 
  | None -> Map.Poly.set map ~key:hd ~data:tl 
  | Some a -> Map.Poly.set map ~key:hd ~data:(a @ tl)
;;

let build_ngram_map (l : string list) (n : int) : ngram_map =
  let ngrams = compute_ngrams l n in
  List.fold_left ngrams ~init:(Map.Poly.empty) ~f:(fun acc ng -> ngram_map_add acc ng)
;;

let ngram_to_string ng =
  Printf.sprintf "[%s]" (String.concat ~sep:", " ng)
;;

let ngram_map_new () : ngram_map =
  Map.Poly.empty
;;

let ngram_map_distribution (map : ngram_map) (ngram : ngram)
  : word_distribution option =
    match Map.Poly.find map ngram with 
    | None -> None
    | Some a -> 
      let count = Float.(1. / of_int (List.length a)) in
      let dist = List.fold_left a ~init:(Map.Poly.empty) ~f:(fun acc s -> 
        match Map.Poly.find acc s with 
        | None -> Map.Poly.set acc ~key:s ~data:(count)
        | Some a -> Map.Poly.set acc ~key:s ~data:(a +. count)
      ) in
      Some dist
;;

let sample_distribution (dist : word_distribution) : string =
  let rand = Random.float 1.0 in
  let lst = Map.Poly.to_alist dist in
  let rec find (lst : (string * float) list) (acc : float) : string =
    match lst with
    | [] -> failwith "no word found"
    | (s, f) :: tl -> if Float.(acc + f > rand) then s else find tl (acc +. f) in
  find lst 0.0
;;

let rec sample_n (map : ngram_map) (ng : ngram) (n : int) : string list =
  let len = List.length ng in
  let take_last_len lst = List.rev lst |> fun reversed ->  List.take reversed len |> List.rev in
  List.fold_left (List.range 1 n) ~init:ng ~f:(fun acc _ -> 
    match ngram_map_distribution map (take_last_len acc) with 
    | None -> failwith "no distribution found for ngram"
    | Some a -> acc @ [sample_distribution a])
;;
