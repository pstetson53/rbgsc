Require Import models.EffectSignatures.

(** Concurrency effect signature (operations + arities). *)

Record conc_params :=
  {
    conc_val : Type;
    conc_tid : Type;
    conc_chan : Type;
  }.

Section ConcSignature.
  Context (P : conc_params).

  (** Each constructor indexes an operation by its arity (the type of
      values it returns to the continuation). *)
  Inductive conc_esig : SigBase.esig :=
  | e_spawn : conc_esig (conc_tid P)                  (** spawn returns a thread id *)
  | e_yield : conc_esig unit                          (** yield produces no value *)
  | e_send (ch : conc_chan P) (v : conc_val P) : conc_esig unit
  | e_recv (ch : conc_chan P) : conc_esig (conc_val P) (** recv returns a value *)
  | e_join (t : conc_tid P) : conc_esig (conc_val P).  (** join returns the thread result *)

  Definition conc_sig : SigBase.sig := SigBase.esig_sig conc_esig.
End ConcSignature.

Arguments conc_sig P.
Arguments conc_esig P.
