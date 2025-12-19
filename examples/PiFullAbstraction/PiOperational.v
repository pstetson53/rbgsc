(** * Operational semantics and labelled transitions
    Small-step rules for the late pi-calculus fragment used in this case study.
    Actions are late-style (inputs expose the channel but abstract over the
    received name) and the transition system follows FMS Section 1. *)

From Coq Require Import Bool.Bool Arith.PeanoNat.
Require Import examples.PiFullAbstraction.PiSyntax.

(** ** Visible actions *)

Inductive action :=
| ActTau : action
| ActOut : name -> name -> action
| ActIn  : name -> name -> action.   (* channel, bound variable *)

(** Substitution on actions follows the same capture-avoiding convention as
    process substitution: bound input variables are left untouched, while free
    occurrences in channels/payloads are rewritten. *)
Definition subst_action (x y : name) (a : action) : action :=
  match a with
  | ActTau => ActTau
  | ActOut c d => ActOut (subst_name x y c) (subst_name x y d)
  | ActIn c b => ActIn (subst_name x y c) b
  end.

(** A restricted name must not appear in a visible action. *)
Definition mentions (x : name) (a : action) : bool :=
  match a with
  | ActTau => false
  | ActOut c d => Nat.eqb x c || Nat.eqb x d
  | ActIn c b => Nat.eqb x c || Nat.eqb x b
  end.

(** ** Transition relation *)

Inductive step : action -> proc -> proc -> Prop :=
| StepTau p :
    step ActTau (PTau p) p
| StepOut a b p :
    step (ActOut a b) (POut a b p) p
| StepIn a x p :
    step (ActIn a x) (PIn a x p) p
| StepSumL a p p' q :
    step a p p' -> step a (PSum p q) p'
| StepSumR a p q q' :
    step a q q' -> step a (PSum p q) q'
| StepParL a p p' q :
    step a p p' -> step a (PPar p q) (PPar p' q)
| StepParR a p q q' :
    step a q q' -> step a (PPar p q) (PPar p q')
| StepCommL a b x p p' q q' :
    step (ActOut a b) p p' ->
    step (ActIn a x) q q' ->
    step ActTau (PPar p q) (PPar p' (subst x b q'))
| StepCommR a b x p p' q q' :
    step (ActIn a x) p p' ->
    step (ActOut a b) q q' ->
    step ActTau (PPar p q) (PPar (subst x b p') q')
| StepNu a x p p' :
    mentions x a = false ->
    step a p p' ->
    step a (PNu x p) (PNu x p')
| StepMatch a b p p' act :
    a = b ->
    step act p p' ->
    step act (PMatch a b p) p'
| StepRep a p p' :
    step a (PPar p (PRep p)) p' ->
    step a (PRep p) p'.

Notation "P =[ a ]=> Q" := (step a P Q) (at level 70, no associativity).

(** ** Substitution compatibility
    These lemmas will be used to show that bisimulation is stable under
    substitutions.  We work under a simple [fresh_bound] hypothesis to
    avoid capture; a full alpha-conversion development would discharge
    this assumption. *)

Lemma subst_name_neq :
  forall x u v n,
    x <> v ->
    x <> n ->
    x <> subst_name u v n.
Proof.
  intros x u v n Hnv Hnn.
  unfold subst_name.
  destruct (Nat.eq_dec n u); subst; auto.
Qed.

Lemma mentions_subst_action :
  forall a u v x,
    mentions x a = false ->
    x <> v ->
    mentions x (subst_action u v a) = false.
Proof.
  intros a u v x Hm Hneq.
  destruct a; cbn in *.
  - assumption.
  - rewrite Bool.orb_false_iff in Hm. destruct Hm as [H1 H2].
    apply Bool.orb_false_iff. split.
    + apply (proj2 (Nat.eqb_neq x (subst_name u v n))).
      apply subst_name_neq; [exact Hneq|].
      apply Nat.eqb_neq in H1. exact H1.
    + apply (proj2 (Nat.eqb_neq x (subst_name u v n0))).
      apply subst_name_neq; [exact Hneq|].
      apply Nat.eqb_neq in H2. exact H2.
  - rewrite Bool.orb_false_iff in Hm. destruct Hm as [H1 H2].
    apply Bool.orb_false_iff. split.
    + apply (proj2 (Nat.eqb_neq x (subst_name u v n))).
      apply subst_name_neq; [exact Hneq|].
      apply Nat.eqb_neq in H1. exact H1.
    + exact H2.
Qed.

Lemma step_subst_action :
  forall a p p' u v,
    fresh_bound u p ->
    fresh_bound v p ->
    step a p p' ->
    step (subst_action u v a) (subst u v p) (subst u v p').
Admitted.
