(** 116297 - TÃ³picos AvanÃ§ados em Computadores - 2017/2           **)
(** Provas Formais: Uma IntroduÃ§Ã£o Ã  Teoria de Tipos - Turma B    **)
(** Prof. FlÃ¡vio L. C. de Moura                                   **)
(** Email: contato@flaviomoura.mat.br                             **)
(** Homepage: http://flaviomoura.mat.br                           **)

(** Aluno:      Raphael Soares Ramos                                       **)
(** MatrÃ­cula:  14/0160299                                       **)

Require Import naturais20172.

Inductive lista :=
| nil : lista
| cons : natural -> lista -> lista.

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