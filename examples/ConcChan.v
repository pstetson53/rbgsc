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
  Import ConcMonad.Notations.
  Local Open Scope conc_scope.
  #[local] Notation ret := (ConcMonad.ret (P:=P)).

  Definition sender (ch : Chan) (v : Val) (ts : ThreadState) : term ThreadState :=
    ConcMonad.send (P:=P) ch v (fun _ => ret ts).

  Definition receiver (ch : Chan) (ts : ThreadState) : term ThreadState :=
    ConcMonad.recv (P:=P) ch (fun _ => ret ts).

  Definition compose_config (t1 t2 : ThreadState) (sh : SharedState) : config :=
    {| ConcStrategy.cfg_threads := [t1; t2];
       ConcStrategy.cfg_shared := sh |}.

  Definition two_party_exchange (ch : Chan) (v : Val) (t1 t2 : ThreadState) (sh : SharedState) : term config :=
    _ <- sender ch v t1;;
    _ <- receiver ch t2;;
    ret (compose_config t1 t2 sh).

  Definition R : term config -> config -> Prop := fun t c => ConcRefinement.R_conc P ThreadState SharedState t c.

  (** Placeholder correctness statement. *)
  Lemma chan_example_refines :
    forall ch v t1 t2 sh, R (two_party_exchange ch v t1 t2 sh) (compose_config t1 t2 sh).
  Proof.
    intros ch v t1 t2 sh.
    unfold two_party_exchange, R.
    eapply (ConcRefinement.returns_bind P ThreadState SharedState) with (x:=t1).
    - constructor. intro _. constructor.
    - intro _. eapply (ConcRefinement.returns_bind P ThreadState SharedState) with (x:=t2).
      + constructor. intro _. constructor.
      + intro _. constructor.
  Qed.
End ConcChan.
