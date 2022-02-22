type 'a sez =
  | []
  | (::) of 'a * 'a sez

let rec (++) xs ys =
  match xs with
  | [] -> ys
  | x :: xs -> x :: (xs ++ ys)
