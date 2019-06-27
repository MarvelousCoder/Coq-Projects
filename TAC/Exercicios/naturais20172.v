(** 116297 - TÃ³picos AvanÃ§ados em Computadores - 2017/2           **)
(** Provas Formais: Uma IntroduÃ§Ã£o Ã  Teoria de Tipos - Turma B    **)
(** Prof. FlÃ¡vio L. C. de Moura                                   **)
(** Email: contato@flaviomoura.mat.br                             **)
(** Homepage: http://flaviomoura.mat.br                           **)

(** Aluno: Raphael Soares Ramos                                                **)
(** MatrÃ­cula: 14/0160299                                                    **)

(** NÃºmeros naturais: *)

Inductive natural :=
| z: natural 
| s: natural -> natural. 

(** Igualdade proposicional. *)
(* Inductive eq_prop : natural -> natural -> Prop :=
| eq_prop_refl: forall z, eq_prop z z.

Notation "A = B" := (eq_prop A B). *)
  
(** DisjunÃ§Ã£o: *)
Inductive disj (A B: Prop) : Set :=
  | esq : A -> disj A B
  | dir : B -> disj A B.

(** Definimos o absurdo como um tipo indutivo vazio, isto Ã©, sem construtores. Desta maneira podemos representar a negaÃ§Ã£o de A como sendo (A -> falso). *)
Inductive falso: Prop :=.

Fixpoint beq_nat (n m : natural) : bool :=
  match n with
  | z => match m with
         | z => true
         | s m' => false
         end
  | s n' => match m with
            | z => false
            | s m' => beq_nat n' m'
            end
  end.

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> disj P (P -> falso).
Proof.
  intros P [] H.
  - left. apply H. reflexivity.
  - right. unfold not. 
    intros. inversion H.
    apply H1 in H0.
    inversion H0.
Qed.

Theorem beq_nat_true : forall n m,
    beq_nat n m = true -> n = m.
Proof.
    intros n. induction n as [| n' IHn'].
    - intros m H. destruct m.
      + reflexivity.
      + inversion H.
    - intros m H. destruct m.
      + inversion H.
      + apply IHn' in H.
        rewrite -> H.
        reflexivity.
Qed.

Theorem beq_nat_refl : forall n : natural,
  true = beq_nat n n.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. apply IHn'.
Qed.

(** ExercÃ­cio 1: Decidibilidade da igualdade. *)
Lemma eq_dec: forall (n m: natural), disj (n=m) (n=m -> falso).
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (beq_nat n m)).
  split.
  - intros.
    symmetry.
    rewrite -> H.
    apply beq_nat_refl.
  - apply beq_nat_true.
Defined.

Print eq_dec.

Theorem sucessor: forall n m: natural,
  s n = s m -> n = m.
Proof.
  destruct n.
  - intros. inversion H.
    reflexivity.
  - intros.
    destruct m.
    + inversion H.
    + inversion H.
      reflexivity.
Qed.

(** ExercÃ­cio 2: *)
Lemma eq_sn_not_n: forall n, s n = n -> falso.
Proof.
  induction n.
  - intros. inversion H.
  - intros.
    apply sucessor with (n := s n) (m := n) in H.
    apply IHn in H.
    assumption.
Qed.

(** Considere o predicado binÃ¡rio le que define a relaÃ§Ã£o de "menor ou igual que".  *)
Inductive le : natural -> natural -> Prop :=
| le_refl: forall n, le n n
| le_n_sm: forall n m, le n m -> le n (s m).

(** ExercÃ­cio 3: *)
Lemma le_n_z: forall n, le n z -> n = z.
Proof.
  destruct n.
  - intros; reflexivity.
  - intros.
    inversion H.
Qed.

(** ExercÃ­cio 4: O zero Ã© menor ou igual que qualquer natural. *)
Lemma le_z: forall n, le z n.
Proof.
  intros.
  induction n.
  - apply le_refl.
  - apply le_n_sm, IHn.
Qed.

(** ExercÃ­cio 5: *)
Lemma le_trans: forall n m k, le n m -> le m k -> le n k.
Proof.
  intros n m k Hn Hm.
  induction Hm.
  - apply Hn.
  - apply le_n_sm.
    apply IHHm, Hn.
Qed.

(** ExercÃ­cio 6: *)
Lemma le_s: forall n m, le (s n) (s m) <-> le n m.
Proof.
  split.
  - intros.
    inversion H.
    apply le_refl.
    apply le_trans with (m := s n).
    apply le_n_sm; apply le_refl.
    assumption.
  - intros.
    induction H.
    + apply le_refl.
    + apply le_n_sm.
      apply IHle.
Qed.

(** ExercÃ­cio 7: *)
Lemma le_n_sm_eq: forall m n, (le n m -> falso) -> (le n (s m)) -> n = s m.
Proof.
  intros.
  inversion H0.
  - reflexivity.
  - apply H in H3.
    inversion H3.
Qed.

(** Do latim, ex falso quodlibet significa, literalmente, "from falsehood
    follows whatever you like".
*)

Theorem ex_falso_quodlibet : forall (P:Prop),
  falso -> P.
Proof.
  intros P contra.
  destruct contra.  
Qed.

(** ExercÃ­cio 8: *)
Lemma le_nm_falso: forall n m, (le n m -> falso) -> (le m n).
Proof.
  intros n m. generalize dependent n. induction m.
  - intros.
    apply le_z.
  - destruct n.
    + intros.
      apply ex_falso_quodlibet.
      apply H.
      apply le_z.
    + intros.
      apply le_s.
      apply IHm.
      intros.
      apply H.
      apply le_s.
      assumption.
Qed.
      

(** ExercÃ­cio 9: *)
Lemma le_sn_not_n: forall n, le (s n) n -> falso.
Proof.
  induction n.
  - intros.
    inversion H.
  - intros. apply IHn; intros. apply le_s. assumption.
Qed. 

Fixpoint leb (n m : natural) : bool :=
  match n with
  | z => true
  | s n' => match m with
          | z => false
          | s m' => leb n' m'
          end
  end.

Theorem leb_refl : forall n:natural,
  true = leb n n.
Proof.
   intros n.
   induction n as [ | n' IHn'].
   - simpl. reflexivity.
   - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem leb_correct : forall n m,
  le n m ->
  leb n m = true.
Proof.
  induction n.
  - intros.
    unfold leb.
    reflexivity.
  - intros.
    unfold leb.
    destruct m eqn: eq.
    + inversion H.
    + fold leb.
      apply IHn.
      apply le_s.
      assumption.
Qed.

Theorem leb_complete : forall n m,
  leb n m = true -> le n m.
Proof.
  induction n.
  - intros.
    apply le_z.
  - destruct m.
    + intros H. inversion H.
    + intros H. simpl in H.
      apply le_s.
      apply IHn.
      assumption.
Qed.

(** ExercÃ­cio 10: O predicado [le] Ã© decidÃ­vel. *)
Lemma le_dec: forall (n m: natural), disj (le n m) (le n m -> falso). 
Proof.
  intros n m. 
  apply (restricted_excluded_middle (le n m) (leb n m)).
  split.
  - intros.
    apply leb_correct in H.
    assumption.
  - intros.
    apply leb_complete in H.
    assumption.
Defined.