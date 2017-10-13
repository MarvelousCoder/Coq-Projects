Require Import Arith Ring.

Theorem plus_swap : forall n m p : nat, (* Teorema do capítulo Induction *)
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  assert (H: n + (m + p) = n + m + p).
  { rewrite -> plus_assoc. reflexivity. }
  { rewrite -> H.
    rewrite -> plus_assoc.
    assert (H': n + m = m + n).
      { rewrite -> plus_comm. reflexivity. }
      rewrite -> H'.
      reflexivity.
  }
Qed.

(*
Exercícios iniciais em Coq
 *)
(*
1. Soma dos n primeiros números naturais

Fixpoint: definição de funções recursivas
 *)

Fixpoint soma (n:nat): nat := 
  match n with
  | 0   => 0
  | S k => n + (soma k)
  end.

Eval compute in (soma 3).

Theorem soma_ate_n: forall (n:nat), 2 * (soma n) = n * (n+1).
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl soma. rewrite <- plus_Sn_m.
    rewrite mult_plus_distr_l.
    rewrite IHn. ring.
Qed.

(*
2. Soma dos n primeiros quadrados
*)

Fixpoint soma_quadrado (n: nat): nat :=
  match n with
  | 0 => 0
  | S n' => n*n + (soma_quadrado n')
  end.

Eval compute in (soma_quadrado 3).

Theorem soma_quadrados_n: forall (n:nat), 
6 * (soma_quadrado n) = n*(n+1)*(2*n + 1).
Proof.
   intros n. induction n as [ | n IHn].
   - simpl. reflexivity.
   - simpl soma_quadrado. 
     rewrite <- plus_Sn_m.
     rewrite -> mult_plus_distr_l.
     rewrite -> IHn. ring. 
(* Nem sei direito o que ring faz, mas só me baseei no que vc fez, professor hehe
*)
Qed.

(*
3. Soma dos n primeiros ímpares
*)

Fixpoint oddb (n:nat) : bool :=
  match n with
  | 0 => false
  | S 0 => true
  | S(S n') => oddb n'
  end.

Fixpoint soma_n_impares (n:nat) : nat :=
  match n with
  | 0 => 0
  | S n' => (2*n' + 1) + soma_n_impares(n')
  end.

Eval compute in (soma_n_impares 5).
Eval compute in (soma_n_impares 10).
Eval compute in (soma_n_impares 3).
Eval compute in (soma_n_impares 4).
Eval compute in (soma_n_impares 6).
Eval compute in (soma_n_impares 2).
Eval compute in (soma_n_impares 7).

Theorem soma_impares: forall (n:nat),
  soma_n_impares n = n*n.
Proof.
  intros n. induction n as [ | n IHn].
  - simpl. reflexivity.
  - simpl soma_n_impares.
    rewrite <- plus_n_O.
    rewrite IHn.
    ring.
Qed.
 
(*
4. Listas de naturais
*)

Inductive lista : Type :=
  | vazia : lista
  | cons : nat -> lista -> lista.

Eval compute in (vazia).
Eval compute in (cons 3 vazia).
Eval compute in (cons 5 (cons 3 vazia)).
Eval compute in (cons 3 (cons 3 (cons 5 vazia))).

Fixpoint tamanho (l:lista) : nat :=
  match l with
  | vazia => 0
  | cons x tl => (tamanho tl) + 1
  end.

Example ex1: tamanho (cons 3 (cons 3 (cons 5 vazia))) = 3.
Proof. simpl. reflexivity. Qed.

Fixpoint concat (l1 l2: lista): lista :=
  match l1 with
  | vazia => l2
  | cons x tl => cons x (concat tl l2)
  end.

Fixpoint rev (l:lista) : lista :=
  match l with
  | vazia => l
  | cons x tl => concat (rev tl) (cons x vazia)
  end.


Lemma soma_concat: forall l1 l2, 
tamanho(concat l1 l2) = (tamanho l1) + (tamanho l2).
Proof.
   intros l1 l2. induction l1 as [ | consx tl1 IHl1].
   - simpl. reflexivity.
   - simpl.
     rewrite <- plus_assoc.
     rewrite -> plus_swap.
     rewrite -> plus_comm.
     rewrite -> IHl1.
     reflexivity.
Qed.

Lemma concat_assoc: forall l1 l2 l3 : lista,
concat(concat l1 l2) (l3) = concat(l1) (concat l2 l3).
Proof.
  intros l1 l2 l3. induction l1.
  - simpl. reflexivity.
  - simpl. rewrite -> IHl1. reflexivity.
Qed.

Fact concat_vazia: forall l1: lista,
concat l1 vazia = l1.
Proof.
  intros l1. induction l1.
  - simpl. reflexivity.
  - simpl. rewrite -> IHl1. reflexivity.
Qed.

Lemma rev_concat: forall l1 l2 : lista,
rev(concat l1 l2) = concat(rev l2) (rev l1).
Proof.
  intros l1 l2. induction l1.
  - simpl. rewrite -> concat_vazia. reflexivity.
  - simpl.
    rewrite -> IHl1.
    rewrite -> concat_assoc.
    reflexivity.
Qed.

Theorem rev_idemp: forall l : lista, rev(rev l) = l.
Proof.
  induction l.
  - simpl. reflexivity.
  - simpl.
    rewrite -> rev_concat.
    rewrite -> IHl.
    simpl.
    reflexivity.
Qed.