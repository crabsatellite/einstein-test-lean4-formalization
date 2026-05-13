/-
  EinsteinTest/AxiomAudit.lean

  Prints the axiom dependency list for every paper-level theorem.

  Trust policy.  Every `axiom` declaration in the project falls into
  exactly one of three categories (per `feedback_gap_ledger_in_lean4`
  ATOMIC MINIMAL UNITS interpretation):

    Cat 1 — Mathlib-derivable: claim closes via Mathlib + kernel.
            Must be encoded as `theorem`, not `axiom`.  Project has
            no Cat 1 axioms because the Mathlib infrastructure for
            K-complexity, Robinson Q, and Tarski CAD is absent; see
            the three `gapBlocked` entries in `EinsteinTest.Ledger`.

    Cat 2 — External published (textbook / peer-reviewed paper):
            opaque-carrier-bound atomic axiom + precise citation.

    Cat 3 — Paper-novel: typed primitive carrier (`axiom`) or
            paper-stated atomic defining equation (`axiom`).  Cited
            only to Li 2026 `\label{thm:undecidable}` construction
            or other paper-stated atomic clauses.

  Plus the Lean kernel axioms (`propext`, `Classical.choice`,
  `Quot.sound`), provided by Lean / Mathlib core.

  Constraints.  No (E) custom-scaffolding axioms (naked constants,
  abstract-type-inhabitation stipulations).  No composite axioms
  bundling multiple independent textbook results or hybrid Cat 2 +
  Cat 3 steps.

  Inventory by category (live counts: see `lake env lean
  EinsteinTest/Ledger.lean`):

    Cat 2 propositional axioms (Li-Vitányi + Tarski + Smith / HP /
    TMR / Shoenfield / Hodges):
      K_codingTheorem, K_chainRule_pair, K_pairNonDecrease,
      K_condMonotone, K_descLength, Bridge_Tarski_RCF_Correctness,
      Bridge_Q_Sigma01_completeness, Bridge_Q_Sigma01_soundness,
      Bridge_DefExt_Conservative

    Cat 3 propositional defining equations (Li 2026):
      Bridge_Encoding_Sstar_T0, Bridge_H_e_distinct_from_Sstar,
      Bridge_Defining_Biconditional

    Cat 3 carrier axioms (Li 2026):
      DistinguishedObs, H_e_Obs, Bridge1b_T0, Bridge1b_Tstar

  Cat 2 framework opaques (primitive types/functions at the
  inhabited-type level, not axioms in `#print axioms`):
    Li-Vitányi (2008) universal prefix machine framework:
      KObj, encodeTh, encodeData, encodePair, K, Kcond, descLen,
      μAssignsAtLeast
    Tarski 1948 RCF syntax / decision procedure / standard semantics:
      RCFFormula, RCFDecide, RCFSatisfies

  Per-axiom citations live in the corresponding `axiom` docstring in
  the source file.  Round-history (prior retracted citations + atomic
  refactor steps) lives in `gap_*.attackHistory` fields inside
  `EinsteinTest.Ledger`.

  Per-theorem axiom dependency profile (verified by `#print axioms`
  below):

    * Lean kernel only (`propext`, `Classical.choice`, `Quot.sound`):
        thm_floor, tauMin_nonneg, thm_self_verification,
        cor_self_verif_robust_{i,ii,iii,iv}, cor_empirical_necessity,
        cor_bound_interaction_iii, cor_rare, rem_emission_not_impossible,
        thm_decomposition, cor_conditional_feasibility,
        thm_undecidable_sigma02_upper.

    * Lean kernel + Cat 2 KC bridges:
        thm_emission.

    * Lean kernel + Cat 3 carriers + Cat 3 defining equations + Cat 2
      recursion-theoretic textbook axioms:
        thm_undecidable_sigma01_hard, cor_no_universal.

    * Lean kernel + Bridge_Tarski_RCF_Correctness:
        thm_undecidable_tarski_decidable.

  Any axiom outside the inventory above is a RED FLAG — investigate.

  Usage:
    lake exe cache get
    lake env lean EinsteinTest/AxiomAudit.lean
-/

import EinsteinTest

-- Lean-kernel-only theorems.
#print axioms EinsteinTest.thm_floor
#print axioms EinsteinTest.tauMin_nonneg
#print axioms EinsteinTest.thm_self_verification
#print axioms EinsteinTest.cor_self_verif_robust_i
#print axioms EinsteinTest.cor_self_verif_robust_ii
#print axioms EinsteinTest.cor_self_verif_robust_iii
#print axioms EinsteinTest.cor_self_verif_robust_iv
#print axioms EinsteinTest.cor_empirical_necessity
#print axioms EinsteinTest.cor_bound_interaction_iii

-- KC-bridge-dependent theorems.
#print axioms EinsteinTest.thm_emission
#print axioms EinsteinTest.cor_rare
#print axioms EinsteinTest.rem_emission_not_impossible
#print axioms EinsteinTest.thm_decomposition
#print axioms EinsteinTest.cor_conditional_feasibility

-- Recursion-theoretic theorems.
#print axioms EinsteinTest.thm_undecidable_sigma01_hard
#print axioms EinsteinTest.thm_undecidable_tarski_decidable
#print axioms EinsteinTest.thm_undecidable_sigma02_upper
#print axioms EinsteinTest.cor_no_universal

-- Derived theorems composing atomic axioms.
#print axioms EinsteinTest.Bridge_Halt_Iff_Dist
#print axioms EinsteinTest.Bridge_Q_Sigma01_complete_sound
#print axioms EinsteinTest.Bridge_Sstar_iff_Halt
