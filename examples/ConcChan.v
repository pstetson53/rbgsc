Require Import Coq.Lists.List.
Import ListNotations.
Require Import models.ConcSignature.
Require Import models.ConcMonad.
Require Import models.ConcStrategy.
Require Import models.ConcRefinement.

(** Stub example: two threads communicate over a channel. *)

Section ConcChan.
  Variable Val Tid Chan : Type.
  Let P := {| conc_val := Val; conc_tid := Tid; conc_chan := Chan |}.

  Variable ThreadState SharedState : Type.

  Notation config := (ConcStrategy.config ThreadState SharedState).
  Notation term := (ConcMonad.conc_term P).

  Definition sender (ts : ThreadState) : term ThreadState := ConcMonad.ret ts.
  Definition receiver (ts : ThreadState) : term ThreadState := ConcMonad.ret ts.

  Definition compose_config (t1 t2 : ThreadState) (sh : SharedState) : config :=
    {| ConcStrategy.cfg_threads := [t1; t2];
       ConcStrategy.cfg_shared := sh |}.

  Definition R : term config -> config -> Prop := fun t c => ConcRefinement.R_conc P ThreadState SharedState t c.

  (** Placeholder correctness statement. *)
  Lemma chan_example_refines :
    forall t1 t2 sh, R (ConcMonad.ret (compose_config t1 t2 sh)) (compose_config t1 t2 sh).
  Proof.
    intros t1 t2 sh.
    unfold R.
    apply ConcRefinement.ret_refines.
  Qed.
End ConcChan.
