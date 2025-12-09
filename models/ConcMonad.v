Require Import models.ConcSignature.
Require Import models.EffectSignatures.

(** Free concurrency monad over the [Conc] signature. *)

Module ConcMonad.
  Module Sig := SigBase.

  (** Terms over the concurrency signature. *)
  Definition conc_term (P : conc_params) (X : Type) : Type :=
    Sig.term (ConcSignature.conc_sig P) X.

  #[global] Arguments conc_term _ _ : clear implicits.

  (** Smart constructors for the effect operations. *)
  Definition spawn {P : conc_params} {X}
             (k : ConcSignature.conc_tid P -> conc_term P X) : conc_term P X :=
    Sig.cons (Sig.mkop (ConcSignature.e_spawn P)) k.

  Definition yield {P : conc_params} {X}
             (k : unit -> conc_term P X) : conc_term P X :=
    Sig.cons (Sig.mkop (ConcSignature.e_yield P)) k.

  Definition send {P : conc_params} {X}
             (ch : ConcSignature.conc_chan P) (v : ConcSignature.conc_val P)
             (k : unit -> conc_term P X) : conc_term P X :=
    Sig.cons (Sig.mkop (ConcSignature.e_send P ch v)) k.

  Definition recv {P : conc_params} {X}
             (ch : ConcSignature.conc_chan P)
             (k : ConcSignature.conc_val P -> conc_term P X) : conc_term P X :=
    Sig.cons (Sig.mkop (ConcSignature.e_recv P ch)) k.

  Definition join {P : conc_params} {X}
             (t : ConcSignature.conc_tid P)
             (k : ConcSignature.conc_val P -> conc_term P X) : conc_term P X :=
    Sig.cons (Sig.mkop (ConcSignature.e_join P t)) k.

  (** Functorial action on terms. *)
  Definition fmap {P : conc_params} {X Y} (f : X -> Y) (t : conc_term P X) : conc_term P Y :=
    Sig.tmap f t.

  (** Monad structure inherited from the free monad on the signature. *)
  Definition ret {P : conc_params} {X} (x : X) : conc_term P X :=
    Sig.var x.

  Definition bind {P : conc_params} {X Y} (f : X -> conc_term P Y) (t : conc_term P X) : conc_term P Y :=
    Sig.subst f t.

  #[global] Arguments spawn {P X} _.
  #[global] Arguments yield {P X} _.
  #[global] Arguments send {P X} _ _ _.
  #[global] Arguments recv {P X} _ _.
  #[global] Arguments join {P X} _ _.
  #[global] Arguments ret {P X} _.
  #[global] Arguments bind {P X Y} _ _.

  Module Notations.
    Declare Scope conc_scope.
    Bind Scope conc_scope with conc_term.

    Notation "x <- t1 ;; t2" := (bind (fun x => t2) t1)
      (at level 100, t1 at next level, right associativity) : conc_scope.
    Notation "t1 ;; t2" := (bind (fun _ => t2) t1)
      (at level 100, right associativity) : conc_scope.
    Notation "'ret!' x" := (ret x)
      (at level 10) : conc_scope.
  End Notations.

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

  Lemma fmap_id {P : conc_params} {X} (t : conc_term P X) :
    fmap (P:=P) (fun x => x) t = t.
  Proof. apply Sig.tmap_id. Qed.

  Lemma fmap_compose {P : conc_params} {X Y Z} (g : Y -> Z) (f : X -> Y) (t : conc_term P X) :
    fmap (P:=P) (fun x => g (f x)) t = fmap (P:=P) g (fmap (P:=P) f t).
  Proof. apply Sig.tmap_compose. Qed.

  Lemma bind_fmap {P : conc_params} {X Y Z} (f : X -> Y) (k : Y -> conc_term P Z) (t : conc_term P X) :
    bind (P:=P) k (fmap (P:=P) f t) = bind (P:=P) (fun x => k (f x)) t.
  Proof. unfold bind, fmap. apply Sig.subst_tmap. Qed.

  (** A simple tensor/parallel composition: sequence left then right and pair results. *)
  Definition tensor {P : conc_params} {X Y}
             (tx : conc_term P X) (ty : conc_term P Y) : conc_term P (X * Y) :=
    bind (fun x => bind (fun y => ret (x, y)) ty) tx.

  (** Tensor coherence laws can be added when integrating scheduler/monoidal structure. *)
End ConcMonad.
