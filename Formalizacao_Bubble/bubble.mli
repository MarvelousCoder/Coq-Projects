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

module Nat :
 sig
  val leb : nat -> nat -> bool
 end

val bubble : nat -> nat list -> nat list

val bubbleSort : nat list -> nat list

val correcao_comp : nat list -> nat list
