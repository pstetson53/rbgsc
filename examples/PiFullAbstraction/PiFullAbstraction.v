(** * Full abstraction statements
    The key theorems mirroring Fiore-Moggi-Sangiorgi (2002).  Proofs are
    intentionally left as skeletons; the statements make the intended
    connection between late bisimilarity and the RBGS denotation precise. *)

Require Import examples.PiFullAbstraction.PiSyntax.
Require Import examples.PiFullAbstraction.PiOperational.
Require Import examples.PiFullAbstraction.PiBisimulation.
Require Import examples.PiFullAbstraction.PiDenotation.

(** ** Finite fragment (FMS Theorem 6.4) *)

Theorem finite_full_abstraction :
  forall p q,
    finite p ->
    finite q ->
    p ~ q <-> denote p = denote q.
Proof.
  (* Proof outline (FMS 6.4, finite model):
     1. Adequacy: [step] corresponds to a move in [denote], using
        [denote_step_sound_prefix] plus the parallel/communication
        soundness lemmas in [PiDenotation].
     2. Completeness: define a logical relation on the free CDL
        mirroring the up-to-substitution closure of late bisimilarity,
        and show [denote p = denote q -> p ~ q] by structural induction
        on finite processes (replication excluded by [finite]).
     3. Equality is the semantic notion (RBGS lattice equality), so no
        additional observational closure is required. *)
Admitted.

(** ** General model (FMS Theorem 6.1)
    A stronger statement for the full calculus.  This requires domain-theoretic
    reasoning on the RBGS side and coinductive handling of replication; the
    skeleton is left admitted for now. *)

Theorem full_abstraction :
  forall p q,
    p ~ q <-> denote p = denote q.
Proof.
Admitted.
