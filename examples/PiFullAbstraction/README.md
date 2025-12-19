# pi-calculus full abstraction in RBGS

This case study shows how RBGS hosts a Fiore–Moggi–Sangiorgi-style semantics for the late π-calculus, using only RBGS primitives (effect signatures, interaction specs, CDLattice structure) rather than a bespoke model.

Paper reference: Fiore, Moggi, Sangiorgi, “A theory of bisimulation for the π-calculus” (Information and Computation 2002), <https://doi.org/10.1016/S0890-5401(02)92968-8>.

## What the theorems say (paper vs. code)
- **FMS Section 1 (late bisimulation / congruence):** Implemented as coinductive `late_bisim` and substitution-closure `late_congruence` (`examples/PiFullAbstraction/PiBisimulation.v`). Symmetry/transitivity are proved coinductively; congruence uses the standard substitution closure (capture-avoidance requires alpha-conversion, documented).
- **FMS Theorem 6.4 (finite full abstraction):** Stated in `PiFullAbstraction.v` as `finite_full_abstraction`. The intended proof path mirrors the set-theoretic model: adequacy of the LTS vs. denotation, and completeness via a logical relation on the free CDL. Replication is excluded by `finite`.
- **FMS Theorem 6.1 (general full abstraction):** Stated as `full_abstraction` in `PiFullAbstraction.v`. Requires domain-theoretic fixpoints (for replication) and continuity arguments; left as a roadmap.

## How RBGS is used (canonical modules)
- **Effect signature**: `pi_sig` in `PiDenotation.v`, built with `models/EffectSignatures.v` / `structures/Effects`. Maps π-actions to RBGS operations (τ, output, input).
- **Interaction specs**: `denote : proc -> ispec pi_sig unit` in `PiDenotation.v`, using `models/IntSpec.v` (`int` for effects, `bind` for sequencing, `||`/`bot` from `lattices/FCD.v`).
- **Lattice/compositionality**: Choice and interleaving use lattice joins (`structures/Lattice.v` / `lattices/FCD.v`); synchronization is injected via `comm_step` in `PiDenotation.v`.
- **Operational link**: `op_of_action` connects LTS labels to effect ops; adequacy lemmas (`denote_step_sound`, `denote_step_complete`) document the intended correspondence.

## Code map (reading order)
1. `PiSyntax.v`: names, process grammar, substitution (capture-avoiding), size measure, and `finite` fragment (excludes replication).
2. `PiOperational.v`: late-labelled transition system (`step`), communication, restriction, replication unrolling; action substitution helper `subst_action` is declared for congruence reasoning.
3. `PiBisimulation.v`: coinductive `late_bisim` (~), symmetry/transitivity proofs, and late congruence (~c) as substitution closure.
4. `PiDenotation.v`: RBGS-native denotation. Replication is given a finite unrolling `unroll_rep` (adequate for the finite fragment); interleaving is approximated by join in the CDL. Adequacy lemmas are stated with proof sketches.
5. `PiFullAbstraction.v`: theorem statements `finite_full_abstraction` and `full_abstraction`, with structured proof outlines referencing the earlier lemmas and the paper.

## How the proof is structured (finite fragment)
1. **Adequacy** (`denote_step_sound`): every operational step maps to an `int`-triggered move in the denotation (fuel decreases via `proc_size`).
2. **Logical relation / completeness**: on the free CDL (`lattices/FCD.v`), show that denotational equality implies late bisimilarity on finite processes, following FMS Section 6 (set-theoretic model).
3. **Congruence**: late bisimulation is closed under substitutions (`late_congruence`), matching FMS “late congruence”.
4. **Result**: `finite_full_abstraction` equates `p ~ q` with `denote p = denote q`.

## Limitations and open work
- **Alpha-conversion & substitution:** `step_subst_action` is stated with `fresh_bound` hypotheses but still admitted; a full alpha-renaming/substitution-commutation development is needed to prove it.
- **Interleaving precision:** parallel now includes explicit communication via `comm_step`, but still models interleavings by join (may-style). A fully compositional ISpec interleaving/tensor would be stronger.
- **Replication/general model:** `unroll_rep` provides finitary approximants; the general theorem needs a greatest fixpoint/continuity argument.
- **Adequacy proofs:** communication soundness is captured by `denote_comm_sound`, but prefix adequacy (`denote_step_sound_prefix`) is still admitted; full operational completeness is open and required to settle `finite_full_abstraction`.

## Practical notes
- Build with the project’s local opam switch and the provided configure/make scripts; the example lives in `examples/PiFullAbstraction/`.
- Link this README in correspondence: it is the single entry point explaining what was encoded, how it matches FMS, and where RBGS components are used.
