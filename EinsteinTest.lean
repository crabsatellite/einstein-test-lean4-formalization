/-
  EinsteinTest.lean

  Root module for the Lean companion formalization of:

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

  Axiom-dependency report:
    EinsteinTest/AxiomAudit.lean — prints axiom dependencies of every
    exported theorem.  The KC and broad-class recursion layers use
    explicitly inventoried external and construction bridges.

  Formalization inventory:
    EinsteinTest/Ledger.lean — typed record of every atomic axiom,
    every Cat 3 carrier, and every listed top-level result.  Two
    orthogonal classifications per entry:
      * 6-tier status: gapOpen / gapPartial / gapBlocked / gapDeadEnd /
        gapClosed / gapClosedConditional
      * 4-input-category: cat1Mathlib / cat2External / cat3PaperNovel /
        notInput
    A `conditionalOn` list records any explicit hypotheses on which a
    conditional closure depends.
-/

import EinsteinTest.Basic
import EinsteinTest.Floor
import EinsteinTest.Emission
import EinsteinTest.Undecidable
import EinsteinTest.Decomposition
import EinsteinTest.Dynamic
import EinsteinTest.Feasibility
import EinsteinTest.SelfVerification
