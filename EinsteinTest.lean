/-
  EinsteinTest.lean

  Root module. Machine-checked formalization of the five theorems
  and four corollaries of:

    Li, Alex. "What the Karpowicz Theorem Does Not Prove:
              A Three-Component Decomposition of the LLM Einstein Test."
              2026.

  Submodules:
    EinsteinTest/Basic.lean             Defs 1–4 (observational world,
                                        Einstein-replacement (E1)/(E2)/(E3),
                                        generator+verifier, Einstein Test)
    EinsteinTest/Floor.lean             Theorem~\ref{thm:floor}
    EinsteinTest/Emission.lean          Theorem~\ref{thm:emission} + cor:rare
    EinsteinTest/Undecidable.lean       Theorem~\ref{thm:undecidable} + cor:no-universal
    EinsteinTest/Decomposition.lean     Theorem~\ref{thm:decomposition} + cor:bound-interaction
    EinsteinTest/SelfVerification.lean  Theorem~\ref{thm:self-verification} + cor:self-verif-robust

  Soundness audit:
    EinsteinTest/AxiomAudit.lean — prints axiom dependencies of every
    paper-level theorem. Expected: only `propext`, `Classical.choice`,
    `Quot.sound`, plus the explicitly declared `K_*` Kolmogorov bridges.

  Gap ledger:
    EinsteinTest/Ledger.lean — typed record of every atomic axiom,
    every Cat 3 carrier, every blocked route, and every closed
    top-level result.  Two orthogonal classifications per entry:
      * 6-tier status: gapOpen / gapPartial / gapBlocked / gapDeadEnd /
        gapClosed / gapClosedConditional
      * 4-input-category: cat1Mathlib / cat2External / cat3PaperNovel /
        notInput
    Plus a `conditionalOn` list of `Hyp_*` broken-link predicate names
    for any `gapClosedConditional` entries (currently empty for all
    entries; see v6 §12 broken-link discipline).  Canonical
    attack-history record.
-/

import EinsteinTest.Basic
import EinsteinTest.Floor
import EinsteinTest.Emission
import EinsteinTest.Undecidable
import EinsteinTest.Decomposition
import EinsteinTest.SelfVerification
