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
  Definition merge_shared (l r : SharedState) : SharedState := r.
  Variable default_tid : Tid.
  Variable delivered : Val.
  Variable ch : Chan.
  Variable payload : Val.

  Notation config := (ConcStrategy.config ThreadState SharedState).
  Notation term := (ConcMonad.conc_term P).
  Import ConcMonad.Notations.
  Local Open Scope conc_scope.

  Definition chan_handlers : ConcStrategy.handlers P ThreadState SharedState :=
    {|
      ConcStrategy.h_spawn := fun sh => ((default_tid : conc_tid P), sh, None);
      ConcStrategy.h_yield := fun sh => sh;
      ConcStrategy.h_send  := fun _ _ sh => sh;
      ConcStrategy.h_recv  := fun _ sh => (delivered, sh);
      ConcStrategy.h_join  := fun _ sh => (delivered, sh);
    |}.

  Definition pick_head (c : config) : option nat :=
    match ConcStrategy.cfg_threads ThreadState SharedState c with
    | [] => None
    | _ => Some 0
    end.

  (** Thread program: send a payload, then receive on the same channel, keeping the state. *)
  Definition send_then_recv (ts : ThreadState) : term ThreadState :=
    _ <- ConcMonad.send (P:=P) ch payload (fun _ => ConcMonad.ret tt);;
    _ <- ConcMonad.recv (P:=P) ch (fun _ => ConcMonad.ret ts);;
    ConcMonad.ret ts.

  Definition compose_config (t1 t2 : ThreadState) (sh : SharedState) : config :=
    {| ConcStrategy.cfg_threads := [t1; t2];
       ConcStrategy.cfg_shared := sh |}.

  Definition R : term config -> config -> Prop :=
    ConcRefinement.R_conc P ThreadState SharedState
                          chan_handlers pick_head send_then_recv.

  (** The specification that returns its input configuration refines itself. *)
  Lemma chan_example_refines :
    forall t1 t2 sh, R (ConcMonad.ret (compose_config t1 t2 sh)) (compose_config t1 t2 sh).
  Proof.
    intros t1 t2 sh.
    unfold R.
    apply ConcRefinement.ret_refines.
  Qed.

  (** A concrete scheduler step executes the send/recv program without changing the state. *)
  Lemma chan_step_progress :
    forall sh tstate,
      ConcStrategy.step P ThreadState SharedState
        chan_handlers pick_head send_then_recv
        {| ConcStrategy.cfg_threads := [tstate]; ConcStrategy.cfg_shared := sh |}
        {| ConcStrategy.cfg_threads := [tstate]; ConcStrategy.cfg_shared := sh |}.
  Proof.
    intros sh tstate.
    refine (@ConcStrategy.step_run P ThreadState SharedState
              chan_handlers pick_head send_then_recv
              {| ConcStrategy.cfg_threads := [tstate]; ConcStrategy.cfg_shared := sh |}
              0 tstate tstate sh [] _ _ _); simpl; auto.
  Qed.
End ConcChan.
