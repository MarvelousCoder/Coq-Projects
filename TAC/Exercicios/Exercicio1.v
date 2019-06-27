(** 116297 - TÃ³picos AvanÃ§ados em Computadores - Turma B **)
(** Provas Formais: Uma IntroduÃ§Ã£o Ã  Teoria de Tipos     **)
(** Prof. FlÃ¡vio L. C. de Moura                          **)
(** Email: contato@flaviomoura.mat.br                    **)
(** Homepage: http://flaviomoura.mat.br                  **)

(** Fragmento Implicacional da LÃ³gica Proposicional Intuicionista **)

(** Dicas:

    intro: introduÃ§Ã£o da implicaÃ§Ã£o
    exact H: a hipÃ³tese H corresponde exatamente ao que se quer provar.
    assumption: o que se quer provar Ã© igual a alguma das hipÃ³teses.
    apply H: o tipo alvo de H coincide com o que se quer provar. 
    inversion H: aplica o(s) construtor(es) que permitem gerar a hipÃ³tese H. Se nenhum construtor pode ser aplicado, a prova Ã© concluÃ­da. TambÃ©m permite concluir que a partir do absurdo (False) se prova qualquer coisa.

*)

(**
   Nos exercÃ­cios abaixos remova o comando 'Admitted' e construa uma prova para as proposiÃ§Ãµes apresentadas.
 *)

Section Exercicios.
Variables A B C D: Prop.

Lemma exercicio1 : A -> B -> A.
Proof.
  intros.
  exact H.
Qed.

Lemma exercicio2 : (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
  intros.
  apply H.
  apply H1.
  apply H0.
  apply H1.
Qed.

Lemma exercicio3 : (A -> B) -> (C -> A) -> C -> B.
Proof.
  intros.
  apply H.
  apply H0.
  apply H1.
Qed.

Lemma exercicio4 : (A -> B -> C) -> B -> A -> C.
Proof.
  intros.
  apply H.
  assumption.
  assumption.
Qed.

Lemma exercicio5 : ((((A -> B) -> A) -> A) -> B) -> B. 
Proof.
  (* intros.
  apply H.
  intros.
  apply H0.
  apply exercicio1 in H0.
  intros.
  apply H.
  intros.
  exact H1.
  intros.
  apply H.
  intros.
  exact H1.
  apply H.
  intros.
  apply H0.
  intros.
  apply H.
  intros.
  exact H2. *)
  intros.
  apply H.
  intros.
  apply H0.
  intros.
  apply H.
  intros.
  exact H1.
Qed.

Lemma exercicio6: (A -> B) -> (B -> C) -> A -> C.
Proof.
  intros.
  apply H0.
  apply H.
  apply H1.
Qed.

Lemma exercicio7: (A -> B -> C) -> (B -> A -> C).
Proof.
  intros.
  apply H.
  exact H1.
  exact H0.
Qed.

Lemma exercicio8: (A -> C) -> A -> B -> C.
Proof.
  intros.
  apply H.
  exact H0.
Qed.

Lemma exercicio9: (A -> A -> B) -> A -> B.
Proof.
  intros.
  apply H.
  exact H0.
  exact H0.
Qed.

Lemma exercicio10:  (A -> B) -> (A -> A -> B).
Proof.
  intros.
  apply H.
  exact H0.
Qed.

Lemma exercicio11: (A -> B) -> (A -> C) -> (B -> C -> D) -> A -> D.
Proof.
  intros.
  apply H1.
  apply H.
  exact H2.
  apply H0.
  exact H2.
Qed.

Lemma exercicio12: ((((A -> B) -> A) -> A) -> B) -> B.
Proof.
  apply exercicio5.
Qed.

Lemma exercicio13: False -> A.
Proof.
  intro contra.
  inversion contra.
Qed.

End Exercicios.