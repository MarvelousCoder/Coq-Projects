(* 116297 - Tópicos Avançados em Computadores *)
(* Provas Formais: Uma Introdução à Teoria de Tipos - Turma B *)
(* Prof. Flávio L.C. de Moura *)
(* Email: contato@flaviomoura.mat.br *)
(* Homepage: http://flaviomoura.mat.br *)

(* Aluno: Raphael Soares Ramos *)
(* Matrícula: 14/0160299 *)

(* Descrição: Esse arquivo contém uma formalização do algoritmo de ordenação Insertion Sort. Foi usado Fixpoint para a definição recursiva do algoritmo. *)

Inductive natural :=
| z: natural 
| s: natural -> natural. 

Inductive lista :=
| nil : lista
| cons : natural -> lista -> lista.

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

Fixpoint num_oc (n:natural) (l:lista) : natural :=
  match l with
    | nil => z
    | cons h tl =>
      match eq_dec n h with
        | esq _ _ _ => s (num_oc n tl)
        | dir _ _ _ => num_oc n tl
      end
  end.

Definition equiv l l' := forall n, num_oc n l = num_oc n l'.

Inductive ordenada : lista -> Prop :=
  | nil_ord : ordenada nil
  | one_ord : forall n:natural, ordenada (cons n nil)
  | mult_ord : forall (x y : natural) (l : lista), ordenada (cons y l) -> le x y -> ordenada (cons x (cons y l)).

(** ExercÃ­cio 1: *)
Lemma ordenada_sub: forall l n, ordenada (cons n l) -> ordenada l.
Proof.
  destruct l.
  - intros.
    apply nil_ord.
  - intros.
    inversion H.
    assumption.
Qed.

Fixpoint insercao_seq (n: natural) l :=
  match l with
    | nil => (cons n nil)
    | cons h tl =>
      match le_dec n h with
        | esq _ _ _  => cons n l
        | dir _ _ _  => cons h (insercao_seq n tl)
      end
  end.

(** ExercÃ­cio 2: *)
Lemma insercao_seq_preserva_ordem : forall l n, 
ordenada l -> ordenada (insercao_seq n l).
Proof.
  induction l.
  - intros.
    unfold insercao_seq.
    apply one_ord.
  - intros.
    generalize dependent l; destruct l eqn: eq.
    + intros.
      simpl.
      destruct (le_dec n0 n).
      * apply mult_ord.
        ** assumption.
        ** assumption.
      * apply mult_ord.
        ** apply one_ord.
        ** apply le_nm_falso in f; apply f.
    + intros.
      inversion H.
      simpl.
      destruct (le_dec n0 n).
      * apply mult_ord.
        ** assumption.
        ** assumption.
      * destruct (le_dec n0 n1).
        ** apply mult_ord.
            *** apply mult_ord.
                **** assumption.
                **** assumption.
            *** apply le_nm_falso in f; apply f.
        ** apply mult_ord.
           *** apply IHl with (n:= n0) in H2.
               simpl in H2.
               generalize H2.
               case (le_dec n0 n1).
               **** intros.
                    apply ex_falso_quodlibet.
                    apply f0; apply l2.
               **** intros.
                    assumption.
           *** assumption.
Qed. 

Lemma sucessor_equal: forall (a b: natural),
a = b -> s a = s b.
Proof.
  destruct a.
  - intros. rewrite -> H; reflexivity.
  - intros.
    rewrite -> H; reflexivity.
Qed.

(** ExercÃ­cio 3: *)
Lemma num_oc_insercao_seq: forall l n n', 
num_oc n (insercao_seq n' l) =  num_oc n (cons n' l).
Proof.
  induction l.
  - unfold insercao_seq.
    reflexivity.
  - intros n' n''.
    simpl insercao_seq.
    destruct (le_dec n'' n).
    + reflexivity.
    + apply le_nm_falso in f.
      simpl.
      destruct (eq_dec n' n).
      * destruct (eq_dec n' n'').
        ** apply sucessor_equal.
           rewrite -> IHl.
           rewrite <- e0.
           simpl num_oc at 1.
           destruct (eq_dec n' n').
           *** reflexivity. 
           *** apply ex_falso_quodlibet.
               apply f0; reflexivity.
       ** rewrite -> IHl.
          simpl num_oc at 1.
          destruct (eq_dec n' n'').
          *** apply ex_falso_quodlibet.
              apply f0; assumption.
          *** reflexivity.
      * destruct (eq_dec n' n'').
        ** rewrite -> IHl.
           rewrite <- e.
           simpl num_oc at 1.
           destruct (eq_dec n' n').
           *** reflexivity.
           *** apply ex_falso_quodlibet.
               apply f1; reflexivity.
        ** rewrite -> IHl.
           simpl num_oc at 1.
           destruct (eq_dec n' n'').
           *** apply ex_falso_quodlibet.
               apply f1; assumption.
           *** reflexivity.
Qed.

Fixpoint insercao (l:lista) :=
  match l with
    | nil => nil
    | cons h tl => insercao_seq h (insercao tl)
  end.

Theorem correcao: forall l, (equiv l (insercao l)) /\ ordenada (insercao l).
Proof.
  induction l.
  - split.
    + simpl.
      unfold equiv.
      intro n.
      reflexivity.
    + simpl.
      apply nil_ord.
  - destruct IHl as [Hequiv Hord]. 
    split.
    + simpl.
      unfold equiv in *.
      intro n'.
      assert (H:  num_oc n' (insercao_seq n (insercao l)) =  num_oc n' (cons n (insercao l))).
      { apply num_oc_insercao_seq. }
      rewrite -> H.
      simpl. destruct (eq_dec n' n).
      rewrite -> Hequiv.
      reflexivity.
      apply Hequiv.
    + simpl.
      apply insercao_seq_preserva_ordem.
      assumption.
Qed.

Theorem correcao_comp: forall (l:lista), {l' | equiv l l' /\ ordenada l'}.
Proof.
  intro l.
  exists (insercao l).
  apply correcao.
Qed.
  
Recursive Extraction correcao_comp.
Extraction "Insertion_Sort.ml" correcao_comp.