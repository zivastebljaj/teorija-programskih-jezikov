type nat =
  | O
  | S of nat

let rec plus m n =
  match m with
  | O -> n
  | S m' -> S (plus m' n)

let rec (+) m n =
  match m with
  | O -> n
  | S m' -> S (m' + n)
  