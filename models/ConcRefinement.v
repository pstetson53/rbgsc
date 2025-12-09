Require Import Coq.Relations.Relations.
Require Import Coq.Relations.Relation_Operators.
Require Import models.ConcSignature.
Require Import models.ConcMonad.
Require Import models.ConcStrategy.

(** Refinement scaffold for concurrency: relates abstract concurrent terms
    to concrete scheduler-aware configurations. *)

Section ConcRefinement.
  Context (P : conc_params).
  Variable ThreadState SharedState : Type.
  Variable h : ConcStrategy.handlers P ThreadState SharedState.
  Variable sched : ConcStrategy.scheduler ThreadState SharedState.
  Variable tstrat : ConcStrategy.thread_strategy P ThreadState.

  Notation config := (ConcStrategy.config ThreadState SharedState).
  Notation step := (ConcStrategy.step P ThreadState SharedState h sched tstrat).

  (** Observational refinement: the specification produces some initial configuration
      [c0] which reaches the concrete configuration [c] by repeated scheduler steps. *)
  Definition R_conc (tm : ConcMonad.conc_term P config) (c : config) : Prop :=
    exists c0, tm = ConcMonad.ret (P:=P) c0 /\ clos_refl_trans _ step c0 c.

  Lemma ret_refines (c : config) : R_conc (ConcMonad.ret (P:=P) c) c.
  Proof.
    exists c; split; [reflexivity|apply rt_refl].
  Qed.

  (** Spawn refinements hold trivially for the relational closure. *)
  Lemma spawn_refinement :
    forall (tid : ConcSignature.conc_tid P) (k : ConcSignature.conc_tid P -> ConcMonad.conc_term P config) (t : config),
      R_conc (k tid) t ->
      R_conc (ConcMonad.bind (P:=P) k (ConcMonad.ret (P:=P) tid)) t.
  Proof.
    intros tid k t H.
    rewrite ConcMonad.ret_bind.
    exact H.
  Qed.

  (** Yield refinements hold trivially for the placeholder relation. *)
  Lemma yield_refinement :
    forall (t : config) (k : unit -> ConcMonad.conc_term P config),
      R_conc (k tt) t ->
      R_conc (ConcMonad.bind (P:=P) k (ConcMonad.ret (P:=P) tt)) t.
  Proof.
    intros t k H.
    rewrite ConcMonad.ret_bind.
    exact H.
  Qed.
End ConcRefinement.
