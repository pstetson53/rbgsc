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
  Import ConcMonad.Notations.
  Local Open Scope conc_scope.
  Local Notation ret := (ConcMonad.ret (P:=P)).
  Local Notation bind := (ConcMonad.bind (P:=P)).
  Local Notation fmap := (ConcMonad.fmap (P:=P)).

  (** A simple total-correctness style refinement: every branch of the term returns [c]. *)
  Inductive returns {X} : ConcMonad.conc_term P X -> X -> Prop :=
  | returns_ret x : returns (ConcMonad.ret (P:=P) x) x
  | returns_cons m k x : (forall a, returns (k a) x) -> returns (ConcMonad.Sig.cons m k) x.

  Definition R_conc (tm : ConcMonad.conc_term P config) (c : config) : Prop := returns tm c.

  Lemma ret_refines (c : config) : R_conc (ConcMonad.ret (P:=P) c) c.
  Proof. constructor. Qed.

  Lemma returns_bind {X Y} (t : ConcMonad.conc_term P X) (k : X -> ConcMonad.conc_term P Y)
        (x : X) (y : Y) :
    returns t x -> (forall x', returns (k x') y) -> returns (ConcMonad.bind (P:=P) k t) y.
  Proof.
    revert k y.
    induction 1; intros k y Hk; cbn.
    - apply Hk.
    - constructor. intro a. apply IHreturns. intro x0. apply Hk.
  Qed.

  Lemma returns_fmap {X Y} (f : X -> Y) (t : ConcMonad.conc_term P X) (x : X) :
    returns t x -> returns (ConcMonad.fmap (P:=P) f t) (f x).
  Proof.
    induction 1; cbn.
    - constructor.
    - constructor. intro a. apply IHreturns.
  Qed.

  Lemma returns_tensor {X Y} (tx : ConcMonad.conc_term P X) (ty : ConcMonad.conc_term P Y) (x : X) (y : Y) :
    returns tx x -> returns ty y -> returns (ConcMonad.tensor (P:=P) tx ty) (x, y).
  Proof.
    intros Hx Hy. unfold ConcMonad.tensor.
    eapply returns_bind; eauto.
    intro x0. eapply returns_bind; eauto. intro y0. constructor.
  Qed.

  (** Spawn and yield refinements propagate along all branches. *)
  Lemma spawn_refinement :
    forall (k : ConcSignature.conc_tid P -> ConcMonad.conc_term P config) (t : config),
      (forall tid, R_conc (k tid) t) ->
      R_conc (ConcMonad.spawn (P:=P) k) t.
  Proof.
    intros k t H.
    unfold R_conc.
    constructor. intro tid. apply H.
  Qed.

  Lemma yield_refinement :
    forall (t : config) (k : unit -> ConcMonad.conc_term P config),
      (forall u, R_conc (k u) t) ->
      R_conc (ConcMonad.yield (P:=P) k) t.
  Proof.
    intros t k H.
    unfold R_conc.
    constructor. intro u. apply H.
  Qed.

  Lemma send_refinement :
    forall (ch : ConcSignature.conc_chan P) (v : ConcSignature.conc_val P)
           (k : unit -> ConcMonad.conc_term P config) (t : config),
      (forall u, R_conc (k u) t) ->
      R_conc (ConcMonad.send (P:=P) ch v k) t.
  Proof.
    intros ch v k t Hk. constructor. intro u. apply Hk.
  Qed.

  Lemma recv_refinement :
    forall (ch : ConcSignature.conc_chan P)
           (k : ConcSignature.conc_val P -> ConcMonad.conc_term P config) (t : config),
      (forall v, R_conc (k v) t) ->
      R_conc (ConcMonad.recv (P:=P) ch k) t.
  Proof.
    intros ch k t Hk. constructor. intro v. apply Hk.
  Qed.

  Lemma join_refinement :
    forall (tid : ConcSignature.conc_tid P)
           (k : ConcSignature.conc_val P -> ConcMonad.conc_term P config) (t : config),
      (forall v, R_conc (k v) t) ->
      R_conc (ConcMonad.join (P:=P) tid k) t.
  Proof.
    intros tid k t Hk. constructor. intro v. apply Hk.
  Qed.
End ConcRefinement.
