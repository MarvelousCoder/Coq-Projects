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

(** val bubble : nat -> nat list -> nat list **)

let rec bubble n = function
| Nil -> Cons (n, Nil)
| Cons (h, tl) ->
  (match Nat.leb n h with
   | True -> Cons (n, (bubble h tl))
   | False -> Cons (h, (bubble n tl)))

(** val bubbleSort : nat list -> nat list **)

let rec bubbleSort = function
| Nil -> Nil
| Cons (h, tl) -> bubble h (bubbleSort tl)

(** val correcao_comp : nat list -> nat list **)

let correcao_comp l =
  bubbleSort l
