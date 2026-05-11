/-
  EinsteinTest/Floor.lean

  Theorem~\ref{thm:floor} (Empirical Verification Floor) and
  Remark~\ref{rem:floor-corollaries}.

  Companion to: "What the Karpowicz Theorem Does Not Prove" (Li, 2026).

  Statement (informal): for any empirical protocol Π that returns
  evidence sufficient for a sound verifier to certify, the wall-clock
  cost B_Π is bounded below by τ_min, the minimum-decisive-experiment
  time on the strict-refutation set.

  Proof skeleton:
    1. Witness materialisation. Sound certification (clause c) yields
       S† ∈ augmentedData with S† ∈ π(T*) \ π(T_0).
    2. By (E1), S† ∉ D_t (Lemma `data_disjoint_refutationSet` in Basic.lean).
    3. Hence S† ∈ outcomes(E). The experiment e producing S† satisfies
       τ_t(e) ≥ τ_t(S†) ≥ τ_min.
    4. Sum of non-negative terms: B_Π = Σ τ_t(e) ≥ τ_t(e) ≥ τ_min.
-/

import EinsteinTest.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace EinsteinTest

open ObservationalWorld

variable {W : ObservationalWorld}

/-- Definition of `τ_min` for an Einstein-replacement candidate `R`:
    the infimum of `τ_t(s)` over the strict-refutation set intersected
    with `Tech_t`. Returns `+∞` if no such observation is performable
    by time `t`.

    Stated in `ℝ∞ = WithTop ℝ`; the case `τ_min = +∞` corresponds to
    technological infeasibility (Remark on (E2)). -/
noncomputable def tauMin (R : EinsteinReplacement W) : ℝ∞ :=
  ⨅ s ∈ (R.refutationSet ∩ W.Tech R.t), W.tau s R.t

/-- *Correct-successor* condition: `T*` is the correct successor for a
    protocol `Π` (Lean: `Pi`) if every experiment performed yields an
    outcome in `π(T*)`. The paper Theorem~\ref{thm:floor} states this
    as a hypothesis for narrative clarity, but Remark
    `\ref{rem:correct-succ-redundant}` of the paper (added in R13) and
    the proof of `thm_floor` below both show that this hypothesis is
    *logically redundant* given soundness clause (c) of `Verifier`:
    the refuting witness `S†` supplied by `sound_c` already lies in
    `π(T*) \ π(T_0) ⊆ π(T*)`, so the bound goes through without any
    constraint on the other outcomes of `Π`. -/
def correctSuccessor (R : EinsteinReplacement W)
    (Pi : EmpiricalProtocol W R.t) : Prop :=
  Pi.outcomes ⊆ W.predict R.Tstar

/--
  **Theorem~\ref{thm:floor}: Empirical Verification Floor.**

  Suppose `R : EinsteinReplacement W` and a system `𝔖` passes the
  Einstein Test on `R` with `Π = 𝔖.Π`. Then the wall-clock cost of
  `Π` satisfies

  `B_Π ≥ τ_min`.

  (Requires the witness `S†` to lie in `outcomes(E)`, which follows
   from `data_disjoint_refutationSet` under (E1).)

  *Note on `hCorrect`:* The parameter `hCorrect : correctSuccessor R 𝔖.Pi`
  is kept for narrative consistency with paper Theorem~\ref{thm:floor}
  (and Remark~\ref{rem:correct-succ-redundant}), but is *not used* in
  the proof — the refuting witness comes directly from `Verifier.sound_c`,
  which already places it in `π(T*) \ π(T_0)`. We carry the parameter
  with an underscore prefix to suppress the unused-variable linter
  while documenting the narrative role.
-/
theorem thm_floor {R : EinsteinReplacement W} (𝔖 : System W R)
    (hPass : 𝔖.passes)
    (_hCorrect : correctSuccessor R 𝔖.Pi) :
    tauMin R ≤ 𝔖.BPi := by
  -- Extract the three components of `passes`.
  obtain ⟨hMout, _hAugSubPredict, hCert⟩ := hPass
  -- Substitute `Mout = Tstar` to bring `sound_c` into the right form.
  rw [hMout] at hCert
  -- (Step 1) Witness materialisation via Verifier soundness clause (c).
  obtain ⟨Sdag, hS_in_augData, hS_in_Tstar, hS_not_in_T0⟩ := 𝔖.V.sound_c hCert
  -- (Step 2) Show Sdag ∉ data t.  By `data_disjoint_refutationSet` (E1),
  -- the strict-refutation set is disjoint from data t; we re-derive the
  -- single membership statement directly via E1.
  have hS_not_in_data : Sdag ∉ W.data R.t := fun hData =>
    hS_not_in_T0 (R.E1 hData)
  -- (Step 3) Hence Sdag ∈ outcomes (since augData = data t ∪ outcomes).
  have hS_in_outcomes : Sdag ∈ 𝔖.Pi.outcomes := by
    rcases hS_in_augData with hData | hOut
    · exact absurd hData hS_not_in_data
    · exact hOut
  -- (Step 4) Outcomes ⊆ experiments (paper convention; structural field).
  have hS_in_exp : Sdag ∈ 𝔖.Pi.experiments :=
    𝔖.Pi.outcomes_subset_experiments Sdag hS_in_outcomes
  -- (Step 5) Sdag ∈ Tech_t (since experiments ⊆ Tech_t).
  have hS_in_tech : Sdag ∈ W.Tech R.t :=
    𝔖.Pi.experiments_in_tech Sdag hS_in_exp
  -- (Step 6) Sdag ∈ refutationSet ∩ Tech_t.
  have hS_in_refSet : Sdag ∈ R.refutationSet :=
    ⟨hS_in_Tstar, hS_not_in_T0⟩
  have hS_in_target : Sdag ∈ R.refutationSet ∩ W.Tech R.t :=
    ⟨hS_in_refSet, hS_in_tech⟩
  -- (Step 7) tauMin R ≤ W.tau Sdag R.t by infimum-lower-bound.
  have h7 : tauMin R ≤ W.tau Sdag R.t :=
    biInf_le (fun s => W.tau s R.t) hS_in_target
  -- (Step 8) W.tau Sdag R.t ≤ Σ e ∈ experiments, W.tau e R.t.
  -- In `ℝ≥0∞`, every term is ≥ 0 so single_le_sum applies trivially.
  have h8 : W.tau Sdag R.t ≤ ∑ e ∈ 𝔖.Pi.experiments, W.tau e R.t :=
    Finset.single_le_sum (f := fun e => W.tau e R.t)
      (fun _ _ => bot_le) hS_in_exp
  -- Chain h7 and h8.  `𝔖.BPi` is definitionally `𝔖.Pi.cost`, which
  -- unfolds to the Finset sum.
  exact h7.trans h8

/-- **Remark `floor-corollaries` (a).** The floor is generator-independent:
    `τ_min` is a function of `(π, T_0, T*, Tech_t, τ)` alone, not of `M`.
    Two distinct systems on the same candidate produce the same `τ_min`. -/
theorem tauMin_generator_independent {R : EinsteinReplacement W}
    (_𝔖₁ _𝔖₂ : System W R) :
    tauMin R = tauMin R := rfl

/-- **Remark `floor-corollaries` (c).** `τ_min` is non-negative.
    In `ℝ≥0∞`, `0` is the bottom element so this is automatic;
    paper-level it follows from `W.tau_nonneg`. -/
theorem tauMin_nonneg (R : EinsteinReplacement W) :
    (0 : ℝ∞) ≤ tauMin R := bot_le

end EinsteinTest
