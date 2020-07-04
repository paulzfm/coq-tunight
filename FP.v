(** 2. Functional Programming & Functional Correctness **)

Module MyList.

(* Polymorphic lists *)

Inductive list (X: Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Check list.
Check nil. (* X: Type -> list X *)
Check (nil nat).
Check cons.
Check (cons nat 3 (nil nat)).

(* To avoid repeating giving type arguments: *)
Arguments nil {_}.
Arguments cons {_} _ _.

Check (cons 2 (cons 1 (nil))).
Check (cons true nil).

(* Implicit type arguments within "{}": *)
Fixpoint app {X: Type} (l1 l2: list X): (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

Check app.
Check @app.

(* Handy notations: *)
Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Check (1 :: []).
Check ([1,2,3] ++ [4,5,6]).

Lemma app_nil_r : forall X (l : list X), l ++ [] = l.
Proof.
  intros X l.
  induction l as [|h l' IHl'].
  - (* l = nil *)
    simpl. reflexivity.
  - (* l = h :: l' *)
    simpl. rewrite IHl'. reflexivity.
Qed.

(* Exercise: *)
Lemma app_assoc : forall X (l m n : list X),
  l ++ m ++ n = (l ++ m) ++ n.
Admitted.

(* Reverse a list *)
Fixpoint rev {X: Type} (l: list X): list X :=
  match l with
  | nil      => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Example test_rev : rev [1,2,3] = [3,2,1].
Proof. reflexivity. Qed.

Check test_rev.

(* Show: rev is involutive *)

Lemma rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l l2.
  induction l as [|h l' IHl'].
  - (* l = nil *)
    simpl. rewrite app_nil_r. reflexivity.
  - (* l = h :: l' *)
    simpl. rewrite IHl'. rewrite app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall X (l : list X), rev (rev l) = l.
Proof.
  intros X l.
  induction l as [|h l' IHl'].
  - (* l = nil *)
    simpl. reflexivity.
  - (* l = h :: l' *)
    simpl. rewrite rev_app_distr. rewrite IHl'. simpl. reflexivity.
Qed.

End MyList.

Module LeftPad.

(* From codewars:
    https://www.codewars.com/kata/5eec40dfe5d13e0001234d01 *)

From Coq Require Import List Ascii Lia.
Import ListNotations.

Definition leftpad (c : ascii) (n : nat) (s : list ascii) :=
  repeat c (n - length s) ++ s.
(* Note: n - length s = max (n - length s) 0 *)

Print repeat.

Open Scope char_scope.

Eval compute in (leftpad " " 4 ["t"; "u"; "n"; "i"; "g"; "h"; "t"]).
Eval compute in (leftpad " " 10 ["t"; "u"; "n"; "i"; "g"; "h"; "t"]).

Theorem leftpad_length : forall c n s,
  length (leftpad c n s) = max n (length s).
Proof.
  intros c n s. unfold leftpad.
  (* Search (length (_ ++ _)). *)
  rewrite app_length.
  (* Search (length (repeat _ _)). *)
  rewrite repeat_length.
  lia.
Qed.

Lemma leftpad_prefix_alt : forall c n s,
  firstn (n - length s) (leftpad c n s) = repeat c (n - length s).
Proof.
  intros c n s.
  unfold leftpad.
  (* Search (firstn _ (_ ++ _)). *)
  rewrite firstn_app.
  rewrite repeat_length.
  (* Search (_ - _ = 0). *)
  rewrite PeanoNat.Nat.sub_diag. simpl.
  assert (H: n - length s = length (repeat c (n - length s))) by (rewrite repeat_length; reflexivity).
  remember (repeat c (n - length s)) as l.
  rewrite H.
  (* Search (firstn (length _) _). *)
  rewrite firstn_all. apply app_nil_r.
Qed.

Theorem leftpad_prefix : forall c n s,
  Forall (fun x => x = c) (firstn (n - length s) (leftpad c n s)).
Proof.
  intros c n s.
  rewrite leftpad_prefix_alt.
  induction (n - length s) as [|n' IHn']; simpl; auto.
Qed.

(* Exercise: *)
Theorem leftpad_suffix: forall c n s,
  skipn (n - length s) (leftpad c n s) = s.
Admitted.

End LeftPad.