let rec eval_exp st = function
  | Syntax.Lookup l -> List.assoc l st
  | Int n -> n
  | Plus (e1, e2) -> eval_exp st e1 + eval_exp st e2
  | Minus (e1, e2) -> eval_exp st e1 - eval_exp st e2
  | Times (e1, e2) -> eval_exp st e1 * eval_exp st e2

let eval_bool st = function
  | Syntax.Bool b -> b
  | Equal (e1, e2) -> eval_exp st e1 = eval_exp st e2
  | Less (e1, e2) -> eval_exp st e1 < eval_exp st e2
  | Greater (e1, e2) -> eval_exp st e1 > eval_exp st e2

let rec eval_cmd st = function
  | Syntax.Assign (l, e) -> (l, eval_exp st e) :: st
  | IfThenElse (b, c1, c2) ->
      if eval_bool st b then eval_cmd st c1 else eval_cmd st c2
  | Seq (c1, c2) ->
      let st' = eval_cmd st c1 in
      eval_cmd st' c2
  | Skip -> st
  | WhileDo (b, c) ->
      (* eval_cmd st (IfThenElse (b, Seq (c, WhileDo (b, c)), Skip)) *)
      if eval_bool st b then eval_cmd st (WhileDo (b, c)) else st
  | PrintInt e ->
      print_int (eval_exp st e);
      print_newline ();
      st
