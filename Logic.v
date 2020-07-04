(** 1. Logic & Curry-Howard Correspondence **)

(* Check the type of a term *)
Check 2.
Check nat.
Print nat.
Check Set.
Check Type.

Check True.
Check 1 = 2.
Check forall n : nat, n = 2.
Check Prop.

Module Logic.

(* Conjunction/and *)
Check and.
Print and.

Lemma and_intro : forall P Q : Prop, P -> Q -> P /\ Q.
Proof.
  intros P.
  intros Q.
  intros HP.
  intros HQ.
  (* intros P, Q, HP, HQ. *)
  split.
  - exact HP.
  - exact HQ.
Qed.

Lemma and_proj1 : forall P Q : Prop, P /\ Q -> P.
Proof.
  intros P Q [HP _].
  exact HP.
Qed.

Lemma and_proj2 : forall P Q : Prop, P /\ Q -> Q.
Proof.
  intros P Q [_ HQ].
  exact HQ.
Qed.

Lemma and_commute : forall P Q : Prop, P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
  - exact HQ.
  - exact HP.
Qed.

(** Disjunction/or *)
Check or.

Lemma or_intro1 : forall P Q : Prop, P -> P \/ Q.
Proof.
  intros P Q H.
  left.
  assumption.
Qed.

Lemma or_intro2 : forall P Q : Prop, Q -> P \/ Q.
Proof.
  intros P Q H.
  right.
  assumption.
Qed.

(* Exercise: *)
Theorem or_commute : forall P Q : Prop, P \/ Q -> Q \/ P.
Admitted.

(* True *)
Check True.
Print True.

Proposition True_is_true : True.
Proof.
  exact I.
Qed.

(* False *)
Check False.
Print False.

(* Principle of explosion *)
Theorem ex_falso_quodlibet : forall P: Prop, False -> P.
Proof.
  intros P contra.
  destruct contra.
Qed.

(* Negation *)
Check not.
Print not.

Theorem not_False : ~ False.
Proof.
  unfold not.
  intros H.
  exact H.
Qed.

(* Exercise: *)
Theorem double_neg : forall P : Prop, P -> ~~P.
Admitted.

(* If and only if *)
Check iff.
Print iff.

(* Automation *)
Example auto_example : forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P -> Q) -> (P -> S)) ->
  T ->
  P ->
  U.
Proof.
  (* intuition. *)
  auto.
Qed.

(* Existential quantification *)
Theorem dist_exists_or : forall (X: Type) (p q : X -> Prop),
  (exists x, p x \/ q x) <-> (exists x, p x) \/ (exists x, q x).
Proof.
  intros X p q.
  split.
  - (* -> *)
    intros [x [HP|HQ]].
    + left. exists x. exact HP.
    + right. exists x. exact HQ.
  - (* <- *)
    intros [[x HP]|[x HQ]].
    + exists x. left. exact HP.
    + exists x. right. exact HQ.
Qed.

(* Classical vs. intuitionistic logic *)

(* The law of excluded middle is not provable in intuitionistic
   logic: *)
Definition excluded_middle := forall P : Prop, P \/ ~ P.
(* So you see intuitionistic logic is _not intuitive_, which goes
   against our knowledge based upon classical logic. *)

End Logic.

Module CurryHoward.

(* Example:

  n: nat, s: string
  ---------------------
  (n, s): (nat, string)


  p: P, q: Q
  ---------------
  (p, q): P /\ Q
*)

(* Recall conjunction is commutative *)
Print and.
Check Logic.and_commute.
Print Logic.and_commute.

Definition and_commute_iff P Q : P /\ Q <-> Q /\ P :=
  conj (Logic.and_commute P Q) (Logic.and_commute Q P).

(* Exercise:
Definition or_commute_iff P Q : P \/ Q <-> Q \/ P := ??? *)

(* Equality *)
Print eq.
Check @eq_refl.

Definition four_eq_four : 2 + 2 = 1 + 3 := eq_refl 4.
Check four_eq_four.

Fact four_eq_four' : 2 + 2 = 1 + 3.
Proof. simpl. reflexivity. Qed.

End CurryHoward.
