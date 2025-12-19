(** * pi-calculus syntax (structural side)
    This file declares a minimal late-style pi-calculus syntax that will be
    reused by the operational, bisimulation, and denotational layers of the
    case study.  Names are represented by natural numbers to keep substitution
    simple, and constructs follow the presentation in Fiore-Moggi-Sangiorgi
    (2002), Section 1. *)

From Coq Require Import Arith.PeanoNat Bool.Bool.

(** ** Names and processes *)

Definition name := nat.

Inductive proc :=
| PZero : proc
| PTau  : proc -> proc                          (* tau.P *)
| POut  : name -> name -> proc -> proc          (* a!b.P *)
| PIn   : name -> name -> proc -> proc          (* a(x).P *)
| PPar  : proc -> proc -> proc                  (* P | Q *)
| PSum  : proc -> proc -> proc                  (* P + Q *)
| PNu   : name -> proc -> proc                  (* nu x. P *)
| PMatch : name -> name -> proc -> proc         (* [a=b]P *)
| PRep  : proc -> proc.                         (* !P *)

Notation "0" := PZero.
Notation "'tau' ; P" := (PTau P) (at level 40).
Notation "'out' a b ; P" := (POut a b P) (at level 40).
Notation "'inp' a x ; P" := (PIn a x P) (at level 40).
Notation "P ||| Q" := (PPar P Q) (at level 50, left associativity).
Notation "P <+> Q" := (PSum P Q) (at level 50, left associativity).
Notation "'nu' x , P" := (PNu x P) (at level 45, right associativity).
Notation "[ a =? b ] P" := (PMatch a b P) (at level 50).
Notation "'rep' P" := (PRep P) (at level 35).

(** ** Substitution on names and processes *)

Definition subst_name (x y n : name) : name :=
  if Nat.eq_dec n x then y else n.

Fixpoint subst (x y : name) (p : proc) : proc :=
  match p with
  | PZero => PZero
  | PTau p' => PTau (subst x y p')
  | POut a b p' =>
      POut (subst_name x y a) (subst_name x y b) (subst x y p')
  | PIn a b p' =>
      let a' := subst_name x y a in
      if Nat.eq_dec b x then PIn a' b p' else PIn a' b (subst x y p')
  | PPar p1 p2 => PPar (subst x y p1) (subst x y p2)
  | PSum p1 p2 => PSum (subst x y p1) (subst x y p2)
  | PNu n p' =>
      if Nat.eq_dec n x then PNu n p' else PNu n (subst x y p')
  | PMatch a b p' =>
      PMatch (subst_name x y a) (subst_name x y b) (subst x y p')
  | PRep p' => PRep (subst x y p')
  end.

(** ** Finiteness (processes without replication)
    This predicate isolates the fragment considered in the finite model of
    FMS Theorem 6.4.  Replication introduces unbounded behaviour and is
    intentionally ruled out. *)

Inductive finite : proc -> Prop :=
| FinZero : finite PZero
| FinTau p : finite p -> finite (PTau p)
| FinOut a b p : finite p -> finite (POut a b p)
| FinIn a x p : finite p -> finite (PIn a x p)
| FinPar p q : finite p -> finite q -> finite (PPar p q)
| FinSum p q : finite p -> finite q -> finite (PSum p q)
| FinNu x p : finite p -> finite (PNu x p)
| FinMatch a b p : finite p -> finite (PMatch a b p).

Hint Constructors finite : core.

(** ** A simple size measure for well-founded definitions *)

Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Fixpoint proc_size (p : proc) : nat :=
  match p with
  | PZero => 1
  | PTau p' => S (proc_size p')
  | POut _ _ p' => S (proc_size p')
  | PIn _ _ p' => S (proc_size p')
  | PPar p q => S (proc_size p + proc_size q)
  | PSum p q => S (proc_size p + proc_size q)
  | PNu _ p' => S (proc_size p')
  | PMatch _ _ p' => S (proc_size p')
  | PRep p' => S (proc_size p')
  end.

Lemma proc_size_subst x y p :
  proc_size (subst x y p) = proc_size p.
Proof.
  induction p; cbn.
  - reflexivity.
  - rewrite IHp. reflexivity.
  - rewrite IHp. reflexivity.
  - destruct (Nat.eq_dec n0 x); cbn; [reflexivity| rewrite IHp; reflexivity].
  - rewrite IHp1, IHp2. reflexivity.
  - rewrite IHp1, IHp2. reflexivity.
  - destruct (Nat.eq_dec n x); cbn; [reflexivity| rewrite IHp; reflexivity].
  - rewrite IHp. reflexivity.
  - rewrite IHp. reflexivity.
Qed.

Lemma proc_size_par_l p q :
  proc_size p < proc_size (PPar p q).
Proof.
  cbn. lia.
Qed.

Lemma proc_size_par_r p q :
  proc_size q < proc_size (PPar p q).
Proof.
  cbn. lia.
Qed.

Lemma proc_size_sum_l p q :
  proc_size p < proc_size (PSum p q).
Proof.
  cbn. lia.
Qed.

Lemma proc_size_sum_r p q :
  proc_size q < proc_size (PSum p q).
Proof.
  cbn. lia.
Qed.

Lemma proc_size_sub x y p :
  proc_size (subst x y p) < proc_size (PIn x y p).
Proof.
  cbn. rewrite proc_size_subst. lia.
Qed.

(** ** Freshness of bound names
    [fresh_bound x p] states that [x] is not used as a binder in [p].
    This is a lightweight alternative to full alpha-equivalence for
    substitution lemmas. *)

Fixpoint fresh_bound (x : name) (p : proc) : Prop :=
  match p with
  | PZero => True
  | PTau p' => fresh_bound x p'
  | POut _ _ p' => fresh_bound x p'
  | PIn _ b p' => x <> b /\ fresh_bound x p'
  | PPar p1 p2 => fresh_bound x p1 /\ fresh_bound x p2
  | PSum p1 p2 => fresh_bound x p1 /\ fresh_bound x p2
  | PNu b p' => x <> b /\ fresh_bound x p'
  | PMatch _ _ p' => fresh_bound x p'
  | PRep p' => fresh_bound x p'
  end.
