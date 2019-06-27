(** 116297 - TÃ³picos AvanÃ§ados em Computadores - Turma B **)
(** Provas Formais: Uma IntroduÃ§Ã£o Ã  Teoria de Tipos     **)
(** Prof. FlÃ¡vio L. C. de Moura                          **)
(** Email: contato@flaviomoura.mat.br                    **)
(** Homepage: http://flaviomoura.mat.br                  **)

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

Lemma exercicio1 : ~ False.
Proof.
  unfold not.
  intros contra.
  inversion contra.
Qed.

Lemma exercicio2 : (A -> B) -> ~ B -> ~ A. 
Proof.
  unfold not.
  intros.
  apply H in H1.
  apply H0 in H1.
  assumption.
Qed.

Lemma exercicio3: A -> ~~A.
Proof.
  unfold not.
  intros.
  apply H0.
  exact H.
Qed.

Lemma exercicio4: ~~~A -> ~A.
Proof.
  unfold not.
  intros.
  apply H.
  intros.
  apply H1.
  exact H0.
Qed.

Lemma exercicio5: A -> ~A -> B.
Proof.
  intros.
  unfold not in H0.
  apply H0 in H.
  inversion H.
Qed.

Lemma exercicio6 : A -> B -> A /\ B. 
Proof.
  intros.
  split.
  - assumption.
  - assumption.
Qed.

Lemma exercicio7 : A /\ B -> B.
Proof.
  intros.
  destruct H.
  assumption.
Qed.

Lemma exercicio8 : A -> A \/ B.
Proof.
  intros H.
  left.
  exact H.
Qed.

Lemma exercicio9 : A \/ B -> (A -> C) -> (B -> C) -> C.
Proof.
  intros.
  destruct H.
  - apply H0; exact H.
  - apply H1; exact H.
Qed.

Lemma exercicio10: ((A /\ B) -> C) <-> (A -> B -> C).
Proof.
  split.
  - intros.
    apply H.
    split.
    + assumption.
    + assumption.
  - intros.
    apply H.
    destruct H0.
    + exact H0.
    + apply exercicio7 in H0; exact H0.
Qed.

Lemma exercicio11: ~~A -> (A \/ ~A) -> A.
Proof.
  unfold not.
  intros.
  destruct H0 as [Ha | Hna].
  - assumption.
  - apply H in Hna; inversion Hna.
Qed.

Lemma exercicio12: ~~(A \/ ~A).
Proof.
  unfold not.
  intros H.
  apply H.
  right.
  intros Ha.
  apply H.
  left.
  exact Ha.
Qed.

Definition LEM := A \/ ~A.
Definition Peirce := ((A -> B) -> A) -> A.
Definition NNeg := ~~A -> A.

Lemma exercicio13: LEM -> NNeg.
Proof.
  unfold LEM, NNeg.
  intros LEM.
  unfold not.
  intros Hneg.
  destruct LEM as [Ha | Hna].
  - exact Ha.
  - unfold not in Hna; apply Hneg in Hna.
    inversion Hna.
Qed.

Lemma exercicio14: NNeg -> Peirce.
Proof.
  unfold NNeg, Peirce.
  intros.
  unfold not in H.
  apply H.
  intros H1.
  apply H1 in H0.
  - inversion H0.
  - intros Ha.
    apply H1 in Ha.
    inversion Ha.
Qed.

Lemma exercicio15: (A -> ~A) -> A -> B.
Proof.
  unfold not.
  intros.
  apply H in H0.
  - inversion H0.
  - assumption.
Qed.

End Exercicios.