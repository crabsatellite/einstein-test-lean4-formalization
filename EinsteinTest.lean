/-
  EinsteinTest.lean

  Root module for the audited formal support of:

    Li, Alex. "What the Karpowicz Theorem Does Not Prove:
              A Three-Resource Theory of the LLM Einstein Test."
              2026.

  Submodules:
    EinsteinTest/Basic.lean             Abstract observational layer,
                                        candidate E1/E2 conditions,
                                        strict verifier, resource vector
    EinsteinTest/Floor.lean             Theorem~\ref{thm:floor}
    EinsteinTest/Emission.lean          Theorem~\ref{thm:emission} + cor:waiting
    EinsteinTest/Undecidable.lean       Broad Dist + E1--E2 candidate recognition
    EinsteinTest/Decomposition.lean     Pareto/scalar resource geometry
    EinsteinTest/Dynamic.lean           Availability--acquisition path and floor
    EinsteinTest/Feasibility.lean       Strict-witness compositional sufficiency
    EinsteinTest/SelfVerification.lean  Strict-refutation no-certification result

  Soundness audit:
    EinsteinTest/AxiomAudit.lean — prints axiom dependencies of every
    retained theorem.  The KC and broad-class recursion layers use
    explicitly inventoried external and construction bridges.

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
import EinsteinTest.Dynamic
import EinsteinTest.Feasibility
import EinsteinTest.SelfVerification
