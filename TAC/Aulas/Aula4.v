Inductive natural :=
| zero : natural
| sucessor : natural -> natural.

Print nat.
Print and.

Inductive and' : Prop -> Prop -> Prop :=
  conj': forall (A B : Prop), A -> B -> and' A B.

Inductive form :=
| var : form
| abs : form
| neg : form -> form
| conj : form -> form -> form
| disj : form -> form -> form
| impli: form -> form -> form.

Inductive le: natural -> natural -> Prop :=
| le_refl: forall (n : natural), le n n
| le_sucessor  : forall (n m: natural), le n m -> le n (sucessor m).

Inductive le'': natural -> natural -> Prop :=
| le''_zero: forall (n : natural), le'' zero n
| le''_sucessor  : forall (n m: natural), le'' n m -> le'' n (sucessor m).

Lemma le_equi_le'': forall (n m : natural),
  le n m <-> le'' n m.
Proof.
  induction n.
  - intros.
    split.
    + intros.
      apply le''_zero.
    + intros.
      induction m.
      * apply le_refl.
      * apply le_sucessor.
        apply IHm.
        apply le''_zero.
  - intros.
    split.
    + intros.
      inversion H.
      Abort.
      


Notation "m <= n" := (le' m n).

Theorem teste_le1: forall n : natural,
  n <= n.
Proof.
  apply le_refl.
Qed.

Lemma le