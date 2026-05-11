/-
  EinsteinTest/Decomposition.lean

  Theorem~\ref{thm:decomposition} (Three-Component Decomposition),
  Corollary~\ref{cor:bound-interaction}, and
  Corollary~\ref{cor:conditional-feasibility}.

  Companion to: "What the Karpowicz Theorem Does Not Prove" (Li, 2026).

  Statement (informal): on inputs where the system succeeds, the
  expected total Einstein-Test cost decomposes additively:

      E[C_Einstein] ≥ c_sample · 2^{K_*} + E[B_V] + τ_min

  where (a) is the KC-emission floor (Theorem 2), (b) is the verifier
  cost (procedural; only `B_V ≥ 0` is procedure-independent on Θ^N,
  with structural infeasibility on Θ^G), and (c) is the empirical
  floor (Theorem 1).

  Post-R11 honest restatement: `B_V^♭` was removed from the sum
  decomposition as it was derived from a PSPACE upper bound on
  decision complexity, not a matching lower bound on cost.
-/

import EinsteinTest.Basic
import EinsteinTest.Floor
import EinsteinTest.Emission
import EinsteinTest.Undecidable

namespace EinsteinTest

variable {W : ObservationalWorld}

/--
  **Theorem~\ref{thm:decomposition} (cost decomposition, empirical-floor portion).**

  On inputs where the system passes the Einstein Test, the *total* cost
  is bounded below by the empirical floor:

      `𝔖.totalCost ≥ τ_min`.

  This is the unconditional (in-Lean-provable) portion of the
  three-component decomposition.  The full paper-level statement

      `E[C_Einstein] ≥ c_sample · 2^{K_*} + E[B_V] + τ_min`

  factors as:

  * **τ_min term:** discharged here (combination of Theorem 1 and the
     `0 ≤ B_M`, `0 ≤ B_V` non-negativity automatic in `ℝ≥0∞`).
  * **`c_sample · 2^{K_*}` term:** conditional on the Kolmogorov-
     complexity bridges in `Emission.lean` (Theorem 2); see
     `EinsteinTest.thm_emission`.
  * **`E[B_V]` term:** a procedural floor; on `Θ^N` it reduces to
     `B_V ≥ 0` (automatic), on `Θ^G` it is structurally infeasible
     (Theorem 3, `EinsteinTest.thm_undecidable_sigma01_hard`).

  Post-R11 honest restatement: only the τ_min portion is unconditional
  here; the KC-emission and the B_V floor are tracked by their
  respective theorems and axiom bridges.
-/
theorem thm_decomposition (R : EinsteinReplacement W) (𝔖 : System W R)
    (hPass : 𝔖.passes)
    (hCorrect : correctSuccessor R 𝔖.Pi) :
    tauMin R ≤ 𝔖.totalCost := by
  -- Step 1: by Theorem 1, the empirical floor bounds B_Π from below.
  have hFloor : tauMin R ≤ 𝔖.BPi := thm_floor 𝔖 hPass hCorrect
  -- Step 2: in `ℝ≥0∞`, B_Π ≤ B_M + B_V + B_Π = totalCost trivially.
  have hSum : 𝔖.BPi ≤ 𝔖.totalCost := by
    show 𝔖.BPi ≤ 𝔖.BM + 𝔖.BV + 𝔖.BPi
    have h1 : 𝔖.BPi ≤ 𝔖.BV + 𝔖.BPi := le_add_self
    have h2 : 𝔖.BV + 𝔖.BPi ≤ 𝔖.BM + (𝔖.BV + 𝔖.BPi) := le_add_self
    have h3 : 𝔖.BM + (𝔖.BV + 𝔖.BPi) = 𝔖.BM + 𝔖.BV + 𝔖.BPi := (add_assoc _ _ _).symm
    exact h3 ▸ (h1.trans h2)
  exact hFloor.trans hSum

/-! ### Notes on Corollary~\ref{cor:bound-interaction} (i) and (ii).

  Clause (i): Constraining `M`'s output to `Th^N` tightens the
  verifier side (decision moves to the Tarski-decidable class);
  impact on the generator side `B_M` is procedurally non-monotone.
  This is a meta-claim about procedure spaces (verifier classes vs.
  generator distributions), not a single Lean inequality without
  instantiating a procedure model — full formalization belongs to a
  future `EinsteinTest.Procedures` module.

  Clause (ii): Growing the data `D_t` reduces `K(T*|D_t)` and, in the
  regime where the corrected KC-exponent becomes non-positive, the
  Theorem 2 lower bound on `E[B_M]` becomes vacuous; the conditional
  structure is captured by `EinsteinTest.rem_emission_not_impossible`.

  Neither remark contributes a Lean inequality with current content,
  so no placeholder theorem is carried (it would inflate the
  axiom-dependency audit with empty stubs).  The narrative remarks
  stand on their own in the paper. -/

/-- **Corollary~\ref{cor:bound-interaction} (iii).** The empirical
    floor `τ_min` is uncoupled from AI-side interventions (M-changes
    cannot lower `τ_min`); the bound `B_Π ≥ τ_min` still requires
    Theorem~\ref{thm:floor}'s correct-successor hypothesis. -/
theorem cor_bound_interaction_iii (R : EinsteinReplacement W) (𝔖 : System W R)
    (hPass : 𝔖.passes) (hCorrect : correctSuccessor R 𝔖.Pi) :
    tauMin R ≤ 𝔖.BPi :=
  thm_floor 𝔖 hPass hCorrect

/-- **Corollary~\ref{cor:conditional-feasibility} (F3 portion).**
    A necessary condition for the Einstein Test to be passable in
    principle: the strict-refutation set must be technologically
    feasible, `τ_min < +∞`.

    *Lean statement:* if a system passes the test (with correct-
    successor protocol), then `τ_min` cannot be `⊤` (i.e., the
    refutation set is non-trivially in `Tech_t`).  This is the
    one direction provable from Theorem 1 alone.

    Full (F1)+(F2)+(F3) sufficiency is conditional on the KC bridges
    and the Tarski-decidability of `Θ^N`; see `Emission.lean` and
    `Undecidable.lean`. -/
theorem cor_conditional_feasibility (R : EinsteinReplacement W)
    (𝔖 : System W R) (hPass : 𝔖.passes)
    (hCorrect : correctSuccessor R 𝔖.Pi)
    (hCostFinite : 𝔖.BPi ≠ ⊤) :
    tauMin R ≠ ⊤ := by
  -- By Theorem 1, τ_min ≤ B_Π.  If B_Π is finite, then τ_min is finite.
  have hFloor : tauMin R ≤ 𝔖.BPi := thm_floor 𝔖 hPass hCorrect
  intro hTop
  rw [hTop] at hFloor
  exact hCostFinite (top_le_iff.mp hFloor)

end EinsteinTest
