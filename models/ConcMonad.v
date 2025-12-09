Require Import models.ConcSignature.
Require Import models.EffectSignatures.

(** Free concurrency monad over the [Conc] signature. *)

Module ConcMonad.
  Module Sig := SigBase.

  (** Terms over the concurrency signature. *)
  Definition conc_term (P : conc_params) (X : Type) : Type :=
    Sig.term (ConcSignature.conc_sig P) X.

  (** Functorial action on terms. *)
  Definition fmap {P : conc_params} {X Y} (f : X -> Y) (t : conc_term P X) : conc_term P Y :=
    Sig.tmap f t.

  (** Monad structure inherited from the free monad on the signature. *)
  Definition ret {P : conc_params} {X} (x : X) : conc_term P X :=
    Sig.var x.

  Definition bind {P : conc_params} {X Y} (f : X -> conc_term P Y) (t : conc_term P X) : conc_term P Y :=
    Sig.subst f t.

  Lemma bind_ret {P : conc_params} {X} (t : conc_term P X) :
    bind (P:=P) (@ret P X) t = t.
  Proof.
    unfold bind, ret. apply Sig.subst_var_l.
  Qed.

  Lemma ret_bind {P : conc_params} {X Y} (f : X -> conc_term P Y) (x : X) :
    bind (P:=P) f (ret x) = f x.
  Proof.
    reflexivity.
  Qed.

  Lemma bind_bind {P : conc_params} {X Y Z}
        (f : X -> conc_term P Y) (g : Y -> conc_term P Z) (t : conc_term P X) :
    bind (P:=P) g (bind (P:=P) f t) =
    bind (P:=P) (fun v => bind (P:=P) g (f v)) t.
  Proof.
    unfold bind. apply Sig.subst_subst.
  Qed.

  (** A simple tensor/parallel composition: sequence left then right and pair results. *)
  Definition tensor {P : conc_params} {X Y}
             (tx : conc_term P X) (ty : conc_term P Y) : conc_term P (X * Y) :=
    bind (fun x => bind (fun y => ret (x, y)) ty) tx.

  (** Tensor coherence laws can be added when integrating scheduler/monoidal structure. *)
End ConcMonad.
