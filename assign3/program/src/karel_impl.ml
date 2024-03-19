open Core
open Option.Monad_infix

exception Unimplemented

(* Set this to true to print out intermediate state between Karel steps *)
let debug = false

type cell =
  | Empty
  | Wall
  | Beeper

type grid = cell list list

type dir =
  | North
  | West
  | South
  | East

type pos = int * int

type state = {
  karel_pos : pos;
  karel_dir : dir;
  grid : grid;
}

let get_cell (grid : grid) ((i, j) : pos) : cell option =
  (List.nth grid j) >>= fun l -> List.nth l i
;;

let set_cell (grid : grid) ((i, j) : pos) (cell : cell) : grid =
  List.mapi grid ~f:(fun j' l ->
    if j = j' then List.mapi l ~f:(fun i' c -> if i = i' then cell else c)
    else l)
;;

let state_to_string (state : state) : string =
  let string_matrix = List.map state.grid ~f:(fun row -> 
    List.map row ~f:(function 
      | Empty -> "."
      | Wall -> "X"
      | Beeper -> "B")) in
  let (x, y) = state.karel_pos in
  let karel_matrix = List.mapi string_matrix ~f:(fun j row -> 
    if j <> y then row else
      List.mapi row ~f:(fun i cell -> 
        if i <> x then cell else
          match cell with 
          | "." | "B" -> "K"
          | "X" -> failwith "K in the wall"
          | _ -> failwith "other char in string_matrix"
      )) in
  List.map karel_matrix ~f:(fun row -> String.concat ~sep:" " row)
  |> String.concat ~sep:"\n"
;;

let empty_grid (m : int) (n : int) : grid =
  List.map (List.range 0 m) ~f:(fun _ ->
    List.map (List.range 0 n) ~f:(fun _ -> Empty))
;;

type predicate =
  | FrontIs of cell
  | NoBeepersPresent
  | Facing of dir
  | Not of predicate

type instruction =
  | Move
  | TurnLeft
  | PickBeeper
  | PutBeeper
  | While of predicate * instruction list
  | If of predicate * instruction list * instruction list

let rec predicate_to_string (pred : predicate) : string =
  match pred with
  | FrontIs c ->
    let cellstr = match c with
      | Empty -> "Empty" | Beeper -> "Beeper" | Wall -> "Wall"
    in
    Printf.sprintf "FrontIs(%s)" cellstr
  | NoBeepersPresent -> "NoBeepersPresent"
  | Facing dir ->
    let dirstr = match dir with
      | North -> "North" | South -> "South" | East -> "East" | West -> "West"
    in
    Printf.sprintf "Facing(%s)" dirstr
  | Not pred' -> Printf.sprintf "Not(%s)" (predicate_to_string pred')

let rec instruction_to_string (instr : instruction) : string =
  match instr with
  | Move -> "Move"
  | TurnLeft -> "TurnLeft"
  | PickBeeper -> "PickBeeper"
  | PutBeeper -> "PutBeeper"
  | While (pred, instrs) ->
    Printf.sprintf "While(%s, [%s])"
      (predicate_to_string pred)
      (instruction_list_to_string instrs)
  | If (pred, then_, else_) ->
    Printf.sprintf "If(%s, [%s], [%s])"
      (predicate_to_string pred)
      (instruction_list_to_string then_)
      (instruction_list_to_string else_)
and instruction_list_to_string (instrs: instruction list) : string =
  String.concat ~sep:", " (List.map ~f:instruction_to_string instrs)


let new_pos state =
  let (x, y) = state.karel_pos in
  let (dx, dy) = match state.karel_dir with
    | North -> (0, -1)
    | West -> (-1, 0)
    | South -> (0, 1)
    | East -> (1, 0) in
  (x + dx, y + dy)
  
let rec eval_pred (state : state) (pred : predicate) : bool =
    match pred with 
    | Not p -> not (eval_pred state p)
    | Facing dir -> state.karel_dir = dir
    | NoBeepersPresent ->  not (get_cell state.grid state.karel_pos = Some Beeper)
    | FrontIs cell -> 
      match get_cell state.grid (new_pos state) with 
      | None -> cell = Wall
      | Some c -> c = cell


let rec step (state : state) (code : instruction) : state =
  match code with 
  | Move ->
    if eval_pred state (FrontIs Wall)
    then 
      state
    else 
      {state with karel_pos = new_pos state}
  | TurnLeft ->
    {state with karel_dir = match state.karel_dir with
    | North -> West
    | West -> South
    | South -> East
    | East -> North}
  | PickBeeper ->
     (match get_cell state.grid state.karel_pos with
      | Some Beeper -> 
        {state with grid = set_cell state.grid state.karel_pos Empty}
      | _ -> state)
  | PutBeeper ->
    {state with grid = set_cell state.grid state.karel_pos Beeper}
  | While (pred, insts) ->
    if eval_pred state pred
    then step (step_list state insts) code
    else state
  | If (pred, then_, else_) ->
    if eval_pred state pred
    then step_list state then_
    else step_list state else_

and step_list (state : state) (instrs : instruction list) : state =
  List.fold instrs ~init:state ~f:(fun state instr ->
    if debug then
       (Printf.printf "Executing instruction %s...\n"
          (instruction_to_string instr);
        let state' = step state instr in
        Printf.printf "Executed instruction %s. New state:\n%s\n"
          (instruction_to_string instr)
          (state_to_string state');
        state')
     else
       step state instr)

;;

let not_wall = Not (FrontIs Wall);;
let check_put = If (not_wall, [Move;PutBeeper], []);;

let to_end = While (not_wall, [Move;check_put])

let checkers_algo=
  [
    PutBeeper;
    to_end;
    TurnLeft;
    TurnLeft;
    TurnLeft;
    While (not_wall, [
      Move; 
      TurnLeft; 
      TurnLeft; 
      TurnLeft; 
      Move;
      PutBeeper;
      to_end;
      TurnLeft;
      If (not_wall, [
        Move; 
        TurnLeft;
        PutBeeper; 
        to_end], []);
      TurnLeft;
      TurnLeft;
      TurnLeft;
    ])
]
