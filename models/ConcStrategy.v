Require Import Coq.Lists.List.
Import ListNotations.
Require Import models.ConcSignature.
Require Import models.ConcMonad.

(** Skeleton for concurrent thread strategies and configurations. *)

Section ConcStrategy.
  Context (P : conc_params).
  Variable ThreadState SharedState : Type.

  Record config :=
    {
      cfg_threads : list ThreadState;
      cfg_shared : SharedState;
    }.

  (** A single-thread strategy produces the next thread state. *)
  Definition thread_strategy := ThreadState -> ConcMonad.conc_term P ThreadState.

  (** A system strategy ranges over whole configurations (scheduler to be plugged later). *)
  Definition system_strategy := config -> ConcMonad.conc_term P config.

  (** Small-step relation placeholder (to be refined with scheduler policy). *)
  Definition step : config -> config -> Prop := fun _ _ => False.

  (** Combine two configurations by concatenating threads and taking the shared state of the second. *)
  Definition combine_config (c1 c2 : config) : config :=
    {| cfg_threads := cfg_threads c1 ++ cfg_threads c2;
       cfg_shared := cfg_shared c2 |}.

  (** Parallel composition uses tensor + fmap to combine the two strategy results. *)
  Definition parallel (s1 s2 : system_strategy) : system_strategy :=
    fun c =>
      let paired := ConcMonad.tensor (s1 c) (s2 c) in
      ConcMonad.fmap (fun '(c1, c2) => combine_config c1 c2) paired.
End ConcStrategy.
