(* 116297 - Tópicos Avançados em Computadores *)
(* Provas Formais: Uma Introdução à Teoria de Tipos - Turma B *)
(* Prof. Flávio L.C. de Moura *)
(* Email: contato@flaviomoura.mat.br *)
(* Homepage: http://flaviomoura.mat.br *)

(* Aluno: Raphael Soares Ramos *)
(* Matrícula: 14/0160299 *)

(* Descrição: Esse arquivo contém uma formalização do algoritmo de ordenação Bubble Sort. Foi usado Function para a definição recursiva do algoritmo, que está otimizado. *)

Require Import Recdef.
Require Import List.
Require Import Arith.

Function bubble (l : list nat) {measure length} : list nat :=
  match l with
  | nil => nil
  | n :: nil => n :: nil
  | n1 :: n2 :: l' => if leb n1 n2
                      then n1 :: (bubble (n2 :: l'))
                      else n2 :: (bubble (n1 :: l'))
  end.
Proof.
  auto. auto.
Defined.

Fixpoint bubbleSort (l : list nat) : list nat :=
  match l with
  | nil => nil
  | n :: l' => bubble (n :: (bubbleSort l'))
  end.

Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Eval compute in bubble (1 :: 2 :: 0 :: 3 :: 1 :: nil).
Eval compute in bubbleSort ([1;3;2;4]).
Eval compute in bubble ([1;3;2;4;0;1]).
Eval compute in bubbleSort ([1;3;2;4;0;1]).
Eval compute in bubbleSort (1 :: 2 :: 0 :: 3 :: 1 :: nil).
Eval compute in bubbleSort (1 :: 2 :: 10 :: 3 :: 6 :: nil).

Fixpoint num_oc (n : nat) (l:list nat) : nat :=
  match l with 
    | [] => 0
    | h :: tl =>
      match eq_nat_dec n h with
        | left _  => S (num_oc n tl)
        | right _ => num_oc n tl 
      end
  end.


Definition equiv l l' := forall n, num_oc n l = num_oc n l'.

Inductive ordenada : list nat -> Prop :=
  | nil_ord : ordenada nil
  | one_ord : forall n:nat, ordenada [n]
  | mult_ord : forall (x y : nat) (l : list nat), ordenada (y :: l) -> le x y -> ordenada (x :: (y :: l)).

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  destruct contra.  
Qed.

Fact num_oc_fact: forall l n,
    num_oc n (n :: l) = S (num_oc n l).
Proof.
  induction l.
  - simpl.
    intros n.
    destruct (eq_nat_dec n n).
    + reflexivity.
    + unfold not in n0.
      apply ex_falso_quodlibet.
      apply n0; reflexivity.
  - simpl num_oc.
    intros n.
    destruct (eq_nat_dec n n).
    + reflexivity.
    + apply ex_falso_quodlibet.
      apply n0; reflexivity.
Qed.

Lemma num_oc_comm: forall n n1 n2 l,
    num_oc n2 (n :: n1 :: l) = num_oc n2 (n1 :: n :: l).
Proof.
  intros.
  generalize dependent n1; generalize dependent n.
  generalize dependent n2; induction l.
  - simpl.
    intros.
    destruct (eq_nat_dec n2 n).
    + destruct (Nat.eq_dec n2 n1).
      * reflexivity.
      * reflexivity.
    + reflexivity.
  -  intros.
     simpl.
     destruct (eq_nat_dec n2 n).
     + destruct (eq_nat_dec n2 n1).
       * destruct (eq_nat_dec n2 a).
         ** reflexivity.
         ** reflexivity.
       * reflexivity.
     + reflexivity.
Qed.          

Lemma num_oc_bubble: forall l n,
    num_oc n (bubble l) =  num_oc n l.
Proof.
  intros l.
  functional induction (bubble l).
  - reflexivity.
  - reflexivity.
  - intros n.
    destruct (eq_nat_dec n n1).
    + rewrite e.
      rewrite -> num_oc_fact.
      rewrite -> IHl0.
      rewrite <- num_oc_fact.
      reflexivity.
    + simpl.
      destruct (eq_nat_dec n n1).
      * contradiction.
      * destruct (Nat.eq_dec n n2).
        ** rewrite <- num_oc_fact.
           rewrite <- e in IHl0.
           rewrite <- IHl0.
           rewrite <- e.
           reflexivity.
        ** rewrite IHl0.
           simpl num_oc at 1.
           destruct (eq_nat_dec n n2).
           *** contradiction.
           *** reflexivity.
  - intros.
    remember (n1 :: l') as l eqn: H.
    destruct (eq_nat_dec n n2).
    + rewrite e.
      rewrite -> num_oc_fact.      
      rewrite -> IHl0.
      rewrite <- num_oc_fact.
      rewrite -> H.
      apply num_oc_comm.
    + simpl num_oc at 1.
      destruct (eq_nat_dec n n2).
      * contradiction.
      * rewrite IHl0.
        rewrite <- num_oc_comm.
        rewrite <- H.
        simpl num_oc at 2.
        destruct (eq_nat_dec n n2).
        ** contradiction.
        ** reflexivity.
Qed.
   
Lemma ordenada_sub: forall l n, ordenada (n :: l) -> ordenada l.
Proof.
  destruct l.
  - intros.
    apply nil_ord.
  - intros.
    inversion H.
    assumption.
Qed.

Lemma bubble_leq : forall a b l,
    a <= b -> bubble (a :: (b :: l)) = a :: (bubble (b :: l)).
Proof.
  intros a b l Hle.
  rewrite bubble_equation.
  apply leb_correct in Hle.
  rewrite Hle.
  reflexivity.
Qed. 
    
Lemma leb_nle: forall a b,
    (a <=? b) = false -> b <= a.
Proof.
  intros a b Heq.
  apply Nat.leb_gt in Heq.
  apply Nat.lt_le_incl in Heq.
  assumption.
Qed.

Lemma bubble_preserva_ordem: forall l n, 
    ordenada l -> ordenada (bubble (n :: l)).
Proof.
  induction l.
  - intros.
    rewrite bubble_equation; constructor.
  - intros.
    rewrite bubble_equation.
    destruct (leb n a) eqn: Heq.
    + generalize dependent l; destruct l.
      * intros.
        rewrite bubble_equation.
        constructor.
        ** constructor.
        ** apply leb_complete; assumption.
      * intros.
        rewrite bubble_equation.
        inversion H; subst.
        apply leb_correct in H4.
        rewrite H4.
        constructor.
        ** apply IHl with (n := a) in H2.
           rewrite bubble_equation in H2.
           rewrite H4 in H2.
           assumption.
        ** apply leb_complete; assumption.
    + apply leb_nle in Heq.
      generalize dependent l; destruct l.
      * intros.
        rewrite bubble_equation.
        constructor.
        ** assert(H': ordenada []).
           { constructor. }
           apply (IHl n) in H'.
           rewrite bubble_equation in H'.
           assumption.
        ** assumption.
      * intros.
        rewrite bubble_equation.
        inversion H; subst.
        destruct (leb n n0) eqn: Hleb.
        ** constructor.
           apply (IHl n) in H2.
           rewrite bubble_equation in H2.
           *** rewrite Hleb in H2.
               assumption.
           *** assumption.
        ** constructor.
           *** apply (IHl n) in H2.
               rewrite bubble_equation in H2.
               rewrite Hleb in H2.
               assumption.
           *** assumption.
Qed.

Theorem correcao: forall l,  (equiv l (bubbleSort l)) /\ ordenada (bubbleSort l).
Proof.
  induction l.
  - simpl.
    split.
    + unfold equiv.
      reflexivity.
    + apply nil_ord.
  - split.
    + destruct IHl.
      unfold equiv in *.
      simpl bubbleSort.
      symmetry.
      rewrite -> num_oc_bubble.
      simpl num_oc.
      * destruct eq_nat_dec.
        ** rewrite -> H.
           reflexivity.
        ** symmetry.
           apply H.
    + destruct IHl as [Hequiv Hord].
      simpl bubbleSort in *.
      apply bubble_preserva_ordem; assumption.    
Qed.
      
Theorem correcao_comp: forall (l:list nat), {l' | equiv l l' /\ ordenada l'}.
Proof.
  intro l.
  exists (bubbleSort l).
  apply correcao.
Qed.
  
Recursive Extraction correcao_comp.
Extraction "BubbleSort.ml" correcao_comp.
  
