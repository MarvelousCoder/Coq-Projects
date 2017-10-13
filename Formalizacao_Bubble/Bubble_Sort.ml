type bool =
| True
| False

type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

module Nat =
 struct
  (** val leb : nat -> nat -> bool **)

  let rec leb n m =
    match n with
    | O -> True
    | S n' ->
      (match m with
       | O -> False
       | S m' -> leb n' m')
 end

(** val bubble : nat list -> nat list **)

let rec bubble = function
| Nil -> Nil
| Cons (n1, l0) ->
  (match l0 with
   | Nil -> Cons (n1, Nil)
   | Cons (n2, l') ->
     (match Nat.leb n1 n2 with
      | True -> Cons (n1, (bubble (Cons (n2, l'))))
      | False -> Cons (n2, (bubble (Cons (n1, l'))))))

(** val bubbleSort : nat list -> nat list **)

let rec bubbleSort = function
| Nil -> Nil
| Cons (n, l') -> bubble (Cons (n, (bubbleSort l')))

(** val correcao_comp : nat list -> nat list **)

let correcao_comp l =
  bubbleSort l
