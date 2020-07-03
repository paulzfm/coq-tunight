(* 3. Formalizing Your Theory *)

Module ToyLang.

(* From codewars:
    https://www.codewars.com/kata/5cfd36be4c60c3001b8fb38a *)

(* terms *)
Inductive tm : Type :=
  | zero : tm
  | succ : tm -> tm
  | plus : tm -> tm -> tm
  | nil  : tm
  | cons : tm -> tm -> tm
  | len  : tm -> tm
  | idx  : tm -> tm -> tm
  | sgt  : tm -> tm.

(* value: natural numbers *)
Inductive num : tm -> Prop :=
  | num_zero : num zero
  | num_succ : forall n, num n -> num (succ n).

Hint Constructors num.

(* value: lists *)
Inductive lst : tm -> Prop :=
  | lst_nil  : lst nil
  | lst_cons : forall n l, num n -> lst l -> lst (cons n l).

Hint Constructors lst.

Definition value (t : tm) := num t \/ lst t.

Hint Unfold value.

Reserved Notation "t1 '-->' t2" (at level 40).

(* small-step operational semantics *)
Inductive step : tm -> tm -> Prop :=
  | ST_succ : forall t1 t1',
      t1 --> t1' ->
      succ t1 --> succ t1'
  | ST_plus_zero : forall n,
      num n ->
      plus zero n --> n
  | ST_plus_succ : forall n1 n2,
      num n1 ->
      num n2 ->
      plus (succ n1) n2 --> succ (plus n1 n2)
  | ST_plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      plus t1 t2 --> plus t1' t2
  | ST_plus2 : forall n t t',
      num n ->
      t --> t' ->
      plus n t --> plus n t'
  | ST_cons1 : forall t1 t1' t2,
      t1 --> t1' ->
      cons t1 t2 --> cons t1' t2
  | ST_cons2 : forall n t t',
      num n ->
      t --> t' ->
      cons n t --> cons n t'
  | ST_len_nil :
      len nil --> zero
  | ST_len_cons : forall n l,
      num n ->
      lst l ->
      len (cons n l) --> succ (len l)
  | ST_len : forall t t',
      t --> t' ->
      len t --> len t'
  | ST_idx_zero : forall n l,
      num n ->
      lst l ->
      idx zero (cons n l) --> n
  | ST_idx_succ : forall i n l,
      num i ->
      num n ->
      lst l ->
      idx (succ i) (cons n l) --> idx i l
  | ST_idx1 : forall t1 t1' t2,
      t1 --> t1' ->
      idx t1 t2 --> idx t1' t2
  | ST_idx2 : forall i t t',
      num i ->
      t --> t' ->
      idx i t --> idx i t'
  | ST_sgt_num : forall n,
      num n ->
      sgt n --> cons n nil
  | ST_sgt : forall t1 t1',
      t1 --> t1' ->
      sgt t1 --> sgt t1'

where "t1 '-->' t2" := (step t1 t2).

Hint Constructors step.

(* binary relation *)
Definition relation (X : Type) := X -> X -> Prop.

(* normal form *)
Definition normal_form {X : Type} (R : relation X) (t : X) : 
  Prop := ~ exists t', R t t'.

Notation step_normal_form := (normal_form step).

Lemma num_is_nf : forall n, num n -> step_normal_form n.
Proof with eauto.
  intros t H. unfold step_normal_form.
  induction H; intros contra; inversion contra.
  - inversion H.
  - inversion H0...
Qed.

Lemma lst_is_nf : forall l, lst l -> step_normal_form l.
Proof with eauto.
  intros t H. unfold step_normal_form.
  induction H; intros contra; inversion contra.
  - inversion H.
  - inversion H1; subst... apply num_is_nf in H...
Qed.

(* deterministic *)
Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

(* Advanced exercise: you may need a few customized tactics *)
Theorem step_deterministic : deterministic step.
Admitted.

(* multi step *)
Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X), 
      R x y -> multi R y z -> multi R x z.

Hint Constructors multi.

Notation "t1 '-->*' t2" := (multi step t1 t2) (at level 40).

Example test : idx (plus zero (succ zero))
  (cons zero (cons (succ zero) nil)) -->* succ zero.
Proof.
  eapply multi_step. apply ST_idx1.
    apply ST_plus_zero. apply num_succ. apply num_zero.
  eapply multi_step. apply ST_idx_succ.
    apply num_zero.
    apply num_zero.
    apply lst_cons. apply num_succ. apply num_zero. apply lst_nil.
  eapply multi_step. apply ST_idx_zero.
    apply num_succ. apply num_zero.
    apply lst_nil.
  apply multi_refl.
Qed.

Example test' : idx (plus zero (succ zero))
  (cons zero (cons (succ zero) nil)) -->* succ zero.
Proof with eauto.
  eapply multi_step...
  eapply multi_step...
Qed.

(* type *)
Inductive ty : Type :=
  | Nat : ty
  | List : ty.

(* a term `t` has type `T` *)
Reserved Notation "'|-' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_zero :
      |- zero \in Nat
  | T_succ : forall t,
      |- t \in Nat ->
      |- succ t \in Nat
  | T_plus : forall t1 t2,
      |- t1 \in Nat ->
      |- t2 \in Nat ->
      |- plus t1 t2 \in Nat
  | T_nil :
      |- nil \in List
  | T_cons : forall t1 t2,
      |- t1 \in Nat ->
      |- t2 \in List ->
      |- cons t1 t2 \in List
  | T_len : forall t1,
      |- t1 \in List ->
      |- len t1 \in Nat
  | T_idx : forall t1 t2,
      |- t1 \in Nat ->
      |- t2 \in List ->
      |- idx t1 t2 \in Nat
  | T_sgt : forall t,
      |- t \in Nat ->
      |- sgt t \in List

where "'|-' t '\in' T" := (has_type t T).

Hint Constructors has_type.

Example test_typing : |- idx (plus zero (succ zero))
  (cons zero (cons (succ zero) nil)) \in Nat.
Proof.
  apply T_idx. apply T_plus. apply T_zero.
  apply T_succ. apply T_zero.
  apply T_cons. apply T_zero.
  apply T_cons. apply T_succ. apply T_zero. apply T_nil.
Qed.

Example test_typing' : |- idx (plus zero (succ zero))
  (cons zero (cons (succ zero) nil)) \in Nat.
Proof with eauto.
  apply T_idx...
Qed.

(* lemmas on canonical forms *)

Ltac auto_inverts n :=
  match goal with | H : ?T |- _ =>
    match type of T with Prop =>
      solve [
        inversion H; eauto;
        match n with 
          S (S (?n')) => subst; auto_inverts (S n') 
        end 
      ]
    end
  end.

Lemma cf_num : forall t,
  |- t \in Nat -> value t -> num t.
Proof.
  intros t HT HVal; try auto_inverts 3.
Qed.

Lemma cf_lst : forall t,
  |- t \in List -> value t -> lst t.
Proof.
  intros t HT HVal; try auto_inverts 3.
Qed.

(* Let's try to show the progress *)
Theorem progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht.
  induction Ht...
  - destruct IHHt.
    + left. 
      assert (H1: num t) by (eapply cf_num; eauto)...
    + right. destruct H...
  - right. destruct IHHt1.
    + assert (H1: num t1) by (eapply cf_num; eauto).
      destruct IHHt2.
      * assert (H2: num t2) by (eapply cf_num; eauto).
      destruct H1...
      * destruct H0...
    + destruct H...
  - destruct IHHt1.
    + assert (H1: num t1) by (eapply cf_num; eauto)...
      destruct IHHt2.
      * assert (H2: lst t2) by (eapply cf_lst; eauto). left...
      * right. destruct H0...
    + destruct H...
  - right. destruct IHHt.
    + assert (H1: lst t1) by (eapply cf_lst; eauto).
      destruct H1...
    + destruct H...
  - right. destruct IHHt1.
    + assert (H1: num t1) by (eapply cf_num; eauto).
      destruct IHHt2.
      * assert (H2: lst t2) by (eapply cf_lst; eauto).
        destruct H1.
Abort.

(* counterexample: *)
Example idx_nil := idx zero nil.

Definition stuck (t : tm) : Prop :=
  step_normal_form t /\ ~ value t.

Lemma idx_nil_stuck : stuck idx_nil.
Proof.
  unfold stuck, idx_nil, step_normal_form, not.
  split; intros H.
  - destruct H. auto_inverts 2.
  - auto_inverts 2.
Qed.

Theorem not_progress : ~ (forall t T,
  |- t \in T ->
  value t \/ exists t', t --> t').
Proof with eauto.
  unfold not.
  intros H.
  destruct (H idx_nil Nat); unfold idx_nil...
  - assert (~ value idx_nil) by apply idx_nil_stuck...
  - assert (step_normal_form idx_nil) by apply idx_nil_stuck...
Qed.

(* Exercise: modify --> so that the progress will be held. *)

(* Type is preserved before and after -->: *)
Theorem type_preservation : forall t t' T,
  |- t \in T ->
  t --> t' ->
  |- t' \in T.
Proof.
  intros t t' T HT.
  generalize dependent t'.
  induction HT; intros t' HE;
    try (inversion HE; subst; eauto);
    try auto_inverts 2.
Qed.

(* Soundness means: well-typed terms never get stuck. *)
Theorem unsound : ~ (forall t t' T,
  |- t \in T ->
  t -->* t' ->
  ~ stuck t').
Proof with eauto.
  unfold not.
  intros H.
  destruct (H idx_nil idx_nil Nat); unfold idx_nil...
  apply idx_nil_stuck.
Qed.

End ToyLang.
