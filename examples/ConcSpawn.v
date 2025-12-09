Require Import Coq.Lists.List.
Import ListNotations.
Require Import models.ConcSignature.
Require Import models.ConcMonad.
Require Import models.ConcStrategy.
Require Import models.ConcRefinement.

(** Stub example: a thread spawns a worker that increments a counter. *)

Section ConcSpawn.
  Variable Val Tid Chan : Type.
  Let P := {| conc_val := Val; conc_tid := Tid; conc_chan := Chan |}.

  Variable ThreadState SharedState : Type.

  Notation config := (ConcStrategy.config ThreadState SharedState).
  Notation term := (ConcMonad.conc_term P).
  Import ConcMonad.Notations.
  Local Open Scope conc_scope.
  #[local] Notation ret := (ConcMonad.ret (P:=P)).

  (** Simple shared-state update and worker identity constructors. *)
  Definition counter_inc (sh : SharedState) : SharedState := sh.
  Definition mk_worker (ts : ThreadState) : ThreadState := ts.

  (** Sketch of the spawned worker program. *)
  Definition worker_body (ts : ThreadState) : term ThreadState :=
    _ <- ConcMonad.yield (P:=P) (fun _ => ret tt);
    ret (mk_worker ts).

  (** Client program: spawn worker, then join (placeholder behavior). *)
  Definition spawn_and_join (c : config) : term config :=
    ConcMonad.spawn (P:=P) (fun tid =>
      ConcMonad.join (P:=P) tid (fun _ =>
        ret
          {| ConcStrategy.cfg_threads := ConcStrategy.cfg_threads c;
             ConcStrategy.cfg_shared := counter_inc (ConcStrategy.cfg_shared c) |})).

  Definition R : term config -> config -> Prop := fun t c => ConcRefinement.R_conc P ThreadState SharedState t c.

  (** Placeholder correctness statement. *)
  Lemma spawn_example_refines :
    forall c, R (spawn_and_join c) c.
  Proof.
    intros c. unfold spawn_and_join, R.
    eapply ConcRefinement.spawn_refinement.
    intro tid. eapply ConcRefinement.join_refinement.
    intro _. apply ConcRefinement.ret_refines.
  Qed.
End ConcSpawn.
