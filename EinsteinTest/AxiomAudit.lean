/-
  EinsteinTest/AxiomAudit.lean

  Prints the axiom dependency list for every paper-level theorem.

  Trust policy: every `axiom` declaration in the source must fall
  into exactly one of three categories:

    (A) standard kernel:  `propext`, `Classical.choice`, `Quot.sound`
        — provided by Lean / Mathlib, not declared here.
    (C) literature bridge: a single-step textbook claim with explicit
        citation in the axiom's docstring.
    (D) paper-novel axiom: a definitional / structural claim from the
        companion paper "What the Karpowicz Theorem Does Not Prove"
        (Li 2026), tied to a specific `\label{...}`.

  No (E) custom-scaffolding axioms (e.g. naked constants, abstract-
  type-inhabitation stipulations) are permitted.

  Expected axiom dependencies per theorem (post-v0.4):

  * Theorem 1 (`thm_floor`), Theorem 5 (`thm_self_verification`),
    Theorem 4 (`thm_decomposition`), Corollary `cor_empirical_necessity`,
    Corollary `cor_bound_interaction_iii`, Corollary
    `cor_conditional_feasibility`, `tauMin_nonneg`:
    standard kernel only — `propext`, `Classical.choice`, `Quot.sound`.

  * Theorem 2 (`thm_emission`):
    standard kernel + five literature-cited Kolmogorov bridges
    (each a single existential statement; the previously-separate
    naked constants `K_*_const` and `K_chainRule_slack` are now
    `Classical.choose`-derived from these bundles and do not appear
    as axioms; the v0.5 split decomposes the previously-bundled
    chain rule (pair + single LHS) into pure single-step facts):
      `K_codingTheorem`     — Li-Vitányi, 3rd ed. (2008), Thm 4.3.4
      `K_chainRule_pair`    — Li-Vitányi, 3rd ed. (2008), Thm 3.9.1
                              (pair-LHS form only; single-LHS form
                              is now DERIVED via `K_pairNonDecrease`)
      `K_pairNonDecrease`   — Li-Vitányi, 3rd ed. (2008), §3.1
                              (information non-decrease under pairing;
                              v0.5 split out of the previous bundled
                              chain rule)
      `K_condMonotone`      — Li-Vitányi, 3rd ed. (2008), Thm 2.1.8
      `K_descLength`        — Li-Vitányi, 3rd ed. (2008), §2.1
                              (immediate consequence of the Invariance
                              Theorem Thm 2.1.1 via the literal-output
                              universal program; the v0.5 hedge
                              acknowledges the earlier "Thm 2.1.1"
                              citation conflated the invariance result
                              with its description-length corollary)

  * Corollary `cor_rare`, Remark `rem_emission_not_impossible`:
    standard kernel only (the KC bridges are scoped to `thm_emission`
    itself; corollaries that take `K_*` as an abstract real do not
    depend on the bridges).

  * Theorem 3 (`thm_undecidable_sigma01_hard`) / Corollary
    `cor_no_universal`:
    standard kernel + TWO PURE single-category recursion-theoretic
    bridges:
      `Bridge_Tstar_e_Encoding`         — Category 3 paper-novel
                                          (Li 2026 \label{thm:undecidable}
                                          construction; clauses (iii)+(iv))
      `Bridge_Q_DefExt_TextbookFacts`   — Category 1 literature
                                          (BBJ 2007 Ch. 16 §16.4 +
                                          Rogers 1967 Ch.~XII +
                                          Shoenfield 1967 §4.6 with
                                          Hodges 1997 §2.6 as secondary)
    Every axiom is exactly one of {literature theorem, standard
    library, paper-novel claim}; no composite axioms remain.
    The derived accessors `DistinguishedObs`, `Q_proves_He`,
    `Bridge1b_T0`, `Bridge1b_Tstar`, `Bridge_Q_Sigma01_complete_sound`,
    `Bridge_DefExt_Conservative`, `Bridge_Encoding_Sstar_T0`,
    `Bridge_Encoding_Sstar_Tstar` are now `Classical.choose`-derived
    (the encoding ones from `Bridge_Tstar_e_Encoding`, the textbook
    ones from `Bridge_Q_DefExt_TextbookFacts`) and do NOT appear as
    axioms.

  * `thm_undecidable_tarski_decidable`:
    standard kernel + `Bridge_Tarski_RCF_Correctness` (single
    literature citation: Tarski 1948 RAND R-109).  The previous v0.2
    statement (`∃ b, RCFDecide φ = b`) was trivial by `Bool`-typing;
    the v0.3 statement (`∃ b : Bool, b = true ↔ RCFSatisfies φ`)
    captures the substantive content of Tarski's decision procedure.

  * `thm_undecidable_sigma02_upper`:
    standard kernel only / no axioms.

  Any axiom outside this list is a RED FLAG — investigate.

  Trust audit summary (8 axioms total post-v0.5; every axiom PURE
  single-category and citation-tightened):
  ┌─────────────────────────────────┬──────────┬─────────────────────────────────────────────────────────┐
  │ Axiom                           │ Category │ Citation                                                │
  ├─────────────────────────────────┼──────────┼─────────────────────────────────────────────────────────┤
  │ K_codingTheorem                 │ 1        │ Li-Vitányi, 3rd ed. (2008), Thm 4.3.4                   │
  │ K_chainRule_pair                │ 1        │ Li-Vitányi, 3rd ed. (2008), Thm 3.9.1                   │
  │                                 │          │ (pair-LHS form only; v0.5 split)                        │
  │ K_pairNonDecrease               │ 1        │ Li-Vitányi, 3rd ed. (2008), §3.1                        │
  │                                 │          │ (information non-decrease under pairing; v0.5 split     │
  │                                 │          │ out of bundled chain rule so single-LHS variant becomes │
  │                                 │          │ a derived lemma — see K_chainRule_single_apply)         │
  │ K_condMonotone                  │ 1        │ Li-Vitányi, 3rd ed. (2008), Thm 2.1.8                   │
  │ K_descLength                    │ 1        │ Li-Vitányi, 3rd ed. (2008), §2.1                        │
  │                                 │          │ (immediate consequence of Thm 2.1.1 Invariance via the  │
  │                                 │          │ literal-output universal program; v0.5 hedge replaces   │
  │                                 │          │ the prior "Thm 2.1.1" label, which conflated invariance │
  │                                 │          │ K_1-K_2 ≤ c with description-length K(y|z) ≤ |y|+c)     │
  │ Bridge_Tarski_RCF_Correctness   │ 1        │ Tarski 1948 RAND R-109                                  │
  │ Bridge_Q_DefExt_TextbookFacts   │ 1        │ BBJ 2007 Ch. 16 §16.4 + Rogers 1967 Ch.~XII +           │
  │                                 │          │ Shoenfield 1967 §4.6 (primary) / Hodges 1997 §2.6       │
  │                                 │          │ (secondary).  v0.5 hedge: prior "BBJ Thm 16.4"          │
  │                                 │          │ conflated section §16.4 with a theorem number; prior    │
  │                                 │          │ "Hodges Thm 2.6.4" could not be independently verified  │
  │                                 │          │ (index lists conservative extension at p. 58 only) so   │
  │                                 │          │ primary citation moved to Shoenfield 1967 §4.6 which is │
  │                                 │          │ theorem-numbered in the source. Textbook conclusions    │
  │                                 │          │ about ANY structure satisfying paper-novel encoding     │
  │                                 │          │ clauses (iii)+(iv))                                     │
  │ Bridge_Tstar_e_Encoding         │ 3        │ Li 2026 \label{thm:undecidable} construction (paper-    │
  │                                 │          │ novel encoding clauses (iii) S*∉π(T_0) + (iv) S*∈π(T*_e)│
  │                                 │          │ ↔ qHe(e); abstract realization of T*_e := Q ∪ {S*↔H_e}) │
  └─────────────────────────────────┴──────────┴─────────────────────────────────────────────────────────┘

  **Pure single-category split (recursion-theoretic bridges).** The
  recursion-theoretic content is decomposed into two pure
  single-category axioms:

    * `Bridge_Tstar_e_Encoding` (PURE Category 3): an EXISTENTIAL
      witnessing (Sstar, qHe, T0_enc, Tstar_enc) satisfying ONLY the
      paper-novel encoding clauses (iii) `S* ∉ π(T_0)` and (iv)
      `S* ∈ π(T*_e) ↔ qHe(e)`.  No textbook content.

    * `Bridge_Q_DefExt_TextbookFacts` (PURE Category 1): a UNIVERSAL
      claim that for any 4-tuple satisfying the encoding clauses
      (iii)+(iv), the textbook facts (i) `qHe e ↔ Halt(e)` (BBJ +
      Rogers) and (ii) conservativity outside `S*` (Hodges) hold.
      No paper-novel content; pure textbook conclusions.

  Every axiom in the project is now exactly one of {literature
  theorem, standard library, paper-novel claim} — no composite
  axioms remain.

  Opaque declarations (primitive types/functions, not axioms):
    KObj, encodeTh, encodeData, encodePair,   — Li-Vitányi, 3rd ed.
    K, Kcond, descLen, μAssignsAtLeast          (2008), §3.1
                                                (universal prefix
                                                machine framework)
    RCFFormula, RCFDecide, RCFSatisfies       — Tarski 1948 framework
                                                (RCF syntax /
                                                decision procedure /
                                                standard semantics)

  Usage:
    lake exe cache get
    lake env lean EinsteinTest/AxiomAudit.lean
-/

import EinsteinTest

-- Core structural theorems (standard kernel only).
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

-- Recursion-theoretic theorems (split bridges: Bridge_Tstar_e_Encoding
-- = Cat 3 paper-novel, Bridge_Q_DefExt_TextbookFacts = Cat 1 literature,
-- Bridge_Tarski_RCF_Correctness = Cat 1 literature).
#print axioms EinsteinTest.thm_undecidable_sigma01_hard
#print axioms EinsteinTest.thm_undecidable_tarski_decidable
#print axioms EinsteinTest.thm_undecidable_sigma02_upper
#print axioms EinsteinTest.cor_no_universal
