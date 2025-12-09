Require Import Coq.Relations.Relations.
Require Import models.ConcSignature.
Require Import models.ConcMonad.
Require Import models.ConcStrategy.

(** Refinement scaffold for concurrency: relates abstract concurrent terms
    to concrete scheduler-aware configurations. *)

Section ConcRefinement.
  Context (P : conc_params).
  Variable ThreadState SharedState : Type.

  Notation config := (ConcStrategy.config ThreadState SharedState).

  (** A simple observational refinement: the concurrent term must be a pure return of [c]. *)
  Definition R_conc (tm : ConcMonad.conc_term P config) (c : config) : Prop :=
    exists c', tm = ConcMonad.ret (P:=P) c' /\ c' = c.

  Lemma ret_refines (c : config) : R_conc (ConcMonad.ret (P:=P) c) c.
  Proof. exists c; split; reflexivity. Qed.

  (** Spawn refinements hold trivially for the placeholder relation. *)
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
