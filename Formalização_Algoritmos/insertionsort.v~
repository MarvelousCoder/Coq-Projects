(** 116297 - TÃ³picos AvanÃ§ados em Computadores - 2017/2           **)
(** Provas Formais: Uma IntroduÃ§Ã£o Ã  Teoria de Tipos - Turma B    **)
(** Prof. FlÃ¡vio L. C. de Moura                                   **)
(** Email: contato@flaviomoura.mat.br                             **)
(** Homepage: http://flaviomoura.mat.br                           **)

(**                  OrdenaÃ§Ã£o por inserÃ§Ã£o                       **)

Require Import naturais20172.
Require Import listas20172.
  
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
      Check insercao_seq_preserva_ordem.
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
Extraction "insercao.ml" correcao_comp.