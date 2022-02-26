type 'a sez =
  | []
  | (::) of 'a * 'a sez

let rec (++) xs ys =
  match xs with
  | [] -> ys
  | x :: xs -> x :: (xs ++ ys)

let hd =
  function
  | [] -> invalid_arg "hd"
  | x :: _ -> x

let hd =
  function
  | [] -> None
  | x :: _ -> Some x