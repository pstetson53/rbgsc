(** * Late bisimulation and congruence
    This file packages the labelled transition system into the late
    bisimulation of FMS Section 1, together with its substitution-closed
    congruence.  Proofs are intentionally lightweight; the goal is to
    expose the shape of the definitions that the denotational model
    will validate. *)

From Coq Require Import Arith.PeanoNat.
Require Import examples.PiFullAbstraction.PiSyntax.
Require Import examples.PiFullAbstraction.PiOperational.

(** ** Late bisimulation (FMS Section 1)
    A relation [R] is a late bisimulation when it matches all labelled
    transitions, with bound inputs closed under all instantiations. *)

Definition bisimulation (R : proc -> proc -> Prop) : Prop :=
  forall p q,
    R p q ->
    (forall act p',
        step act p p' ->
        match act with
        | ActTau =>
            exists q', step ActTau q q' /\ R p' q'
        | ActOut c d =>
            exists q', step (ActOut c d) q q' /\ R p' q'
        | ActIn c x =>
            exists q' y,
              step (ActIn c y) q q' /\
              forall v, R (subst x v p') (subst y v q')
        end) /\
    (forall act q',
        step act q q' ->
        match act with
        | ActTau =>
            exists p', step ActTau p p' /\ R p' q'
        | ActOut c d =>
            exists p', step (ActOut c d) p p' /\ R p' q'
        | ActIn c y =>
            exists p' x,
              step (ActIn c x) p p' /\
              forall v, R (subst x v p') (subst y v q')
        end).

Definition late_bisim (p q : proc) : Prop :=
  exists R, bisimulation R /\ R p q.

Notation "p ~ q" := (late_bisim p q) (at level 70).

(** Late congruence: closure of bisimilarity under single-name substitutions. *)
Definition late_congruence (p q : proc) : Prop :=
  forall x v, late_bisim (subst x v p) (subst x v q).

Notation "p ~c q" := (late_congruence p q) (at level 70).

Lemma bisimulation_converse R :
  bisimulation R ->
  bisimulation (fun p q => R q p).
Proof.
  intros HR p q HRpq.
  specialize (HR q p HRpq).
  destruct HR as [Hqp Hpq]. split; intros act r Hr.
  - specialize (Hpq _ _ Hr).
    destruct act.
    + destruct Hpq as (p' & Hstep & Hrel). exists p'. split; auto.
    + destruct Hpq as (p' & Hstep & Hrel). exists p'. split; auto.
    + destruct Hpq as (p' & x & Hstep & Hrel).
      exists p', x. split; auto.
  - specialize (Hqp _ _ Hr).
    destruct act.
    + destruct Hqp as (p' & Hstep & Hrel). exists p'. split; auto.
    + destruct Hqp as (p' & Hstep & Hrel). exists p'. split; auto.
    + destruct Hqp as (p' & x & Hstep & Hrel).
      exists p', x. split; auto.
Qed.

Lemma late_bisim_sym :
  forall p q, p ~ q -> q ~ p.
Proof.
  intros p q [R [HR HRpq]].
  exists (fun x y => R y x). split.
  - apply bisimulation_converse, HR.
  - exact HRpq.
Qed.

Lemma bisimulation_compose R1 R2 :
  bisimulation R1 ->
  bisimulation R2 ->
  bisimulation (fun p r => exists q, R1 p q /\ R2 q r).
Proof.
  intros H1 H2 p r [q [Hq1 Hq2]].
  specialize (H1 _ _ Hq1).
  specialize (H2 _ _ Hq2).
  destruct H1 as [H1L H1R].
  destruct H2 as [H2L H2R].
  split; intros act t Hstep.
  - specialize (H1L _ _ Hstep).
    destruct act.
    + destruct H1L as (q' & Hstep1 & HR1).
      specialize (H2L _ _ Hstep1).
      destruct H2L as (r' & Hstep2 & HR2).
      exists r'. split; auto. exists q'. split; auto.
    + destruct H1L as (q' & Hstep1 & HR1).
      specialize (H2L _ _ Hstep1).
      destruct H2L as (r' & Hstep2 & HR2).
      exists r'. split; auto. exists q'. split; auto.
    + destruct H1L as (q' & x & Hstep1 & HR1).
      specialize (H2L _ _ Hstep1).
      destruct H2L as (r' & y & Hstep2 & HR2).
      exists r', y. split; auto. intros v.
      exists (subst x v q'). split; [apply HR1|].
      specialize (HR2 v). exact HR2.
  - specialize (H2R _ _ Hstep).
    destruct act.
    + destruct H2R as (q' & Hstep1 & HR2).
      specialize (H1R _ _ Hstep1).
      destruct H1R as (p' & Hstep2 & HR1).
      exists p'. split; auto. exists q'. split; auto.
    + destruct H2R as (q' & Hstep1 & HR2).
      specialize (H1R _ _ Hstep1).
      destruct H1R as (p' & Hstep2 & HR1).
      exists p'. split; auto. exists q'. split; auto.
    + destruct H2R as (q' & y & Hstep1 & HR2).
      specialize (H1R _ _ Hstep1).
      destruct H1R as (p' & x & Hstep2 & HR1).
      exists p', x. split; auto. intros v.
      exists (subst y v q'). split; [apply HR1|].
      specialize (HR2 v). exact HR2.
Qed.

Lemma late_bisim_trans :
  forall p q r, p ~ q -> q ~ r -> p ~ r.
Proof.
  intros p q r [R1 [HR1 Hpq]] [R2 [HR2 Hqr]].
  exists (fun x z => exists y, R1 x y /\ R2 y z).
  split.
  - apply bisimulation_compose; assumption.
  - now exists q.
Qed.

Lemma late_congruence_intro :
  forall p q,
    (forall x v, subst x v p ~ subst x v q) ->
    p ~c q.
Proof. firstorder. Qed.

Lemma late_bisim_refl :
  forall p, p ~ p.
Proof.
  (* Build the largest bisimulation by taking the identity relation. *)
  exists (@eq proc).
  split.
  - unfold bisimulation.
    intros p0 q0 Heq. subst q0.
    split; intros act r Hstep; destruct act as [|c d|c x];
      try (exists r; split; auto);
      try (exists r, x; split; auto; intros v; reflexivity).
  - reflexivity.
Qed.
