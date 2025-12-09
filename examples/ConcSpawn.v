Require Import Coq.Lists.List.
Import ListNotations.
Require Import models.ConcSignature.
Require Import models.ConcMonad.
Require Import models.ConcStrategy.
Require Import models.ConcRefinement.

(** Demonstration: a thread that spawns a worker using the concrete scheduler/handlers. *)

Section ConcSpawn.
  Variable Val Tid Chan : Type.
  Let P := {| conc_val := Val; conc_tid := Tid; conc_chan := Chan |}.

  Variable ThreadState SharedState : Type.
  Definition merge_shared (l r : SharedState) : SharedState := r.

  Notation config := (ConcStrategy.config ThreadState SharedState).
  Notation term := (ConcMonad.conc_term P).
  Import ConcMonad.Notations.
  Local Open Scope conc_scope.

  Variable default_val : Val.
  Variable default_tid : Tid.

  (** Handlers that keep shared state unchanged and always spawn [child] with [default_tid]. *)
  Definition spawn_handlers (child : ThreadState) : ConcStrategy.handlers P ThreadState SharedState :=
    {|
      ConcStrategy.h_spawn := fun sh => ((default_tid : conc_tid P), sh, Some child);
      ConcStrategy.h_yield := fun sh => sh;
      ConcStrategy.h_send  := fun _ _ sh => sh;
      ConcStrategy.h_recv  := fun _ sh => (default_val, sh);
      ConcStrategy.h_join  := fun _ sh => (default_val, sh);
    |}.

  (** Always schedule the head thread if available. *)
  Definition pick_head (c : config) : option nat :=
    match ConcStrategy.cfg_threads ThreadState SharedState c with
    | [] => None
    | _ => Some 0
    end.

  (** Thread program: perform [spawn], ignore the tid, and keep the same thread state. *)
  Definition spawn_then_return (ts : ThreadState) : term ThreadState :=
    ConcMonad.spawn (P:=P) (fun _ => ConcMonad.ret ts).

  Definition R (child : ThreadState) : term config -> config -> Prop :=
    ConcRefinement.R_conc P ThreadState SharedState
                          (spawn_handlers child) pick_head spawn_then_return.

  (** The specification that simply returns [c] refines itself under the step closure. *)
  Lemma spawn_example_refines :
    forall c child, R child (ConcMonad.ret c) c.
  Proof.
    intros c child.
    unfold R.
    apply ConcRefinement.ret_refines.
  Qed.

  (** One concrete scheduler step adds the spawned child to the runnable threads. *)
  Lemma spawn_step_adds_child :
    forall sh ts child,
      ConcStrategy.step P ThreadState SharedState
        (spawn_handlers child) pick_head spawn_then_return
        {| ConcStrategy.cfg_threads := [ts]; ConcStrategy.cfg_shared := sh |}
        {| ConcStrategy.cfg_threads := [ts; child]; ConcStrategy.cfg_shared := sh |}.
  Proof.
    intros sh ts child.
    refine (@ConcStrategy.step_run P ThreadState SharedState
              (spawn_handlers child) pick_head spawn_then_return
              {| ConcStrategy.cfg_threads := [ts]; ConcStrategy.cfg_shared := sh |}
              0 ts ts sh [child] _ _ _); simpl; auto.
  Qed.
End ConcSpawn.
