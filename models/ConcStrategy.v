Require Import Coq.Lists.List.
Import ListNotations.
Require Import models.ConcSignature.
Require Import models.ConcMonad.
Require Import models.EffectSignatures.

(** Skeleton for concurrent thread strategies and configurations. *)

Section ConcStrategy.
  Context (P : conc_params).
  Variable ThreadState SharedState : Type.
  Variable merge_shared : SharedState -> SharedState -> SharedState.

  (** A configuration collects runnable thread states and shared state. *)
  Record config :=
    {
      cfg_threads : list ThreadState;
      cfg_shared : SharedState;
    }.

  (** A single-thread strategy produces the next thread state. *)
  Definition thread_strategy := ThreadState -> ConcMonad.conc_term P ThreadState.

  (** A system strategy ranges over whole configurations (scheduler to be plugged later). *)
  Definition system_strategy := config -> ConcMonad.conc_term P config.

  (** Combine two configurations by concatenating threads and merging shared state. *)
  Definition combine_config (c1 c2 : config) : config :=
    {| cfg_threads := cfg_threads c1 ++ cfg_threads c2;
       cfg_shared := merge_shared (cfg_shared c1) (cfg_shared c2) |}.

  (** Parallel composition uses tensor + fmap to combine the two strategy results. *)
  Definition parallel (s1 s2 : system_strategy) : system_strategy :=
    fun c =>
      let paired := ConcMonad.tensor (s1 c) (s2 c) in
      ConcMonad.fmap (fun '(c1, c2) => combine_config c1 c2) paired.

  (** Abstract handlers for the concurrency effects. A spawn can optionally
      introduce a new runnable thread state. *)
  Record handlers :=
    {
      h_spawn : SharedState -> ConcSignature.conc_tid P * SharedState * option ThreadState;
      h_yield : SharedState -> SharedState;
      h_send  : ConcSignature.conc_chan P -> ConcSignature.conc_val P -> SharedState -> SharedState;
      h_recv  : ConcSignature.conc_chan P -> SharedState -> ConcSignature.conc_val P * SharedState;
      h_join  : ConcSignature.conc_tid P -> SharedState -> ConcSignature.conc_val P * SharedState;
    }.

  Definition scheduler := config -> option nat.

  Fixpoint interpret (h : handlers) (t : ConcMonad.conc_term P ThreadState) (sh : SharedState)
    : ThreadState * SharedState * list ThreadState :=
    match t with
    | ConcMonad.Sig.var ts => (ts, sh, [])
    | ConcMonad.Sig.cons (SigBase.mkop (@ConcSignature.e_spawn _)) k =>
        let '(tid, sh', child) := h_spawn h sh in
        let '(ts', sh'', spawned) := interpret h (k tid) sh' in
        let spawned' := match child with
                        | None => spawned
                        | Some ts => ts :: spawned
                        end in
        (ts', sh'', spawned')
    | ConcMonad.Sig.cons (SigBase.mkop (@ConcSignature.e_yield _)) k =>
        let sh' := h_yield h sh in
        interpret h (k tt) sh'
    | ConcMonad.Sig.cons (SigBase.mkop (@ConcSignature.e_send _ ch v)) k =>
        let sh' := h_send h ch v sh in
        interpret h (k tt) sh'
    | ConcMonad.Sig.cons (SigBase.mkop (@ConcSignature.e_recv _ ch)) k =>
        let '(v, sh') := h_recv h ch sh in
        interpret h (k v) sh'
    | ConcMonad.Sig.cons (SigBase.mkop (@ConcSignature.e_join _ tid)) k =>
        let '(v, sh') := h_join h tid sh in
        interpret h (k v) sh'
    end.

  Fixpoint replace_nth {A} (n : nat) (x : A) (l : list A) : list A :=
    match n, l with
    | O, _ :: xs => x :: xs
    | S n', y :: ys => y :: replace_nth n' x ys
    | _, [] => []
    end.

  Inductive step (h : handlers) (sched : scheduler) (ts : thread_strategy) : config -> config -> Prop :=
  | step_run :
      forall cfg idx state state' sh' spawned,
        sched cfg = Some idx ->
        nth_error (cfg_threads cfg) idx = Some state ->
        interpret h (ts state) (cfg_shared cfg) = (state', sh', spawned) ->
        step h sched ts cfg
             {| cfg_threads := replace_nth idx state' (cfg_threads cfg) ++ spawned;
                cfg_shared := sh' |}.
End ConcStrategy.
