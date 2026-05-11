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
-/

import EinsteinTest.Basic
import EinsteinTest.Floor
import EinsteinTest.Emission
import EinsteinTest.Undecidable
import EinsteinTest.Decomposition
import EinsteinTest.SelfVerification
