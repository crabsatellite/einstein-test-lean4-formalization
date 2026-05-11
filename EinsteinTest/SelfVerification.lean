/-
  EinsteinTest/SelfVerification.lean

  Theorem~\ref{thm:self-verification} (Self-Verification Impossibility),
  Corollary~\ref{cor:self-verif-robust} (i–iv),
  Corollary~\ref{cor:empirical-necessity}, and
  Remark~\ref{rem:thm5-substance}.

  Companion to: "What the Karpowicz Theorem Does Not Prove" (Li, 2026).

  Statement (informal): no purely computational system whose prompt
  contains no observations beyond any `D ⊆ D_t` can self-verify an
  Einstein-replacement output. Direct content of strict-refutation
  soundness paired with (E1); the substantive contribution is
  the robustness Corollary (universal-compressor / arithmetic-oracle
  / halting-oracle enhancements all fail).
-/

import EinsteinTest.Basic

namespace EinsteinTest

variable {W : ObservationalWorld}

/--
  **Theorem~\ref{thm:self-verification}: Self-verification impossibility.**

  For any verifier `V`, any Einstein-replacement candidate `R`, and
  any `D ⊆ D_t`,

  `V.decide R.Tstar R.T0 D ≠ some true`.

  *Proof:* If `V.decide R.Tstar R.T0 D = some true`, then by clause (c)
  of Verifier soundness, ∃ S† ∈ D with S† ∈ π(T*) ∧ S† ∉ π(T_0).
  But D ⊆ D_t and (E1) gives D_t ⊆ π(T_0); contradiction.

  *On the paper's "no observations beyond D" hypothesis.* The paper
  states the theorem with a parenthetical clause requiring that the
  prompt embed no observations outside `D`. Under hypothesis
  `D ⊆ W.data R.t` (which is what this Lean statement uses) this
  clause is automatically discharged: the prompt is a fixed string
  that cannot contain observations not yet recorded by time `t`, and
  any `D ⊆ D_t` inherits `D ⊆ π(T_0)` from (E1). No separate
  hypothesis on the prompt is therefore needed, and the proof below
  rests only on `Verifier.sound_c` and (E1) via `D ⊆ data t`.
-/
theorem thm_self_verification {R : EinsteinReplacement W} (V : Verifier W)
    {D : Set W.Obs} (hD : D ⊆ W.data R.t) :
    V.decide R.Tstar R.T0 D ≠ some true := by
  intro hCert
  obtain ⟨S, hS_in_D, _, hS_not_in_T0⟩ := V.sound_c hCert
  exact hS_not_in_T0 (R.E1 (hD hS_in_D))

/--
  **Corollary~\ref{cor:self-verif-robust} (i).** Theorem 5 persists
  if `V` is augmented with a universal-compressor oracle.

  *Proof:* the proof of Theorem 5 used only soundness clause (c) and
  (E1); neither invokes computability of `V`. -/
theorem cor_self_verif_robust_i {R : EinsteinReplacement W} (V : Verifier W)
    {D : Set W.Obs} (hD : D ⊆ W.data R.t) :
    V.decide R.Tstar R.T0 D ≠ some true :=
  thm_self_verification V hD

/-- **Corollary~\ref{cor:self-verif-robust} (ii).** Same with an
    arithmetic-truth oracle Th(ℕ). -/
theorem cor_self_verif_robust_ii {R : EinsteinReplacement W} (V : Verifier W)
    {D : Set W.Obs} (hD : D ⊆ W.data R.t) :
    V.decide R.Tstar R.T0 D ≠ some true :=
  thm_self_verification V hD

/-- **Corollary~\ref{cor:self-verif-robust} (iii).** Same with a
    halting-oracle. -/
theorem cor_self_verif_robust_iii {R : EinsteinReplacement W} (V : Verifier W)
    {D : Set W.Obs} (hD : D ⊆ W.data R.t) :
    V.decide R.Tstar R.T0 D ≠ some true :=
  thm_self_verification V hD

/-- **Corollary~\ref{cor:self-verif-robust} (iv).** The impossibility
    extends to any reasoner (computational or human) whose total
    external input at runtime is restricted to `D_t`. Stated
    abstractly: any function with signature `Reasoner W` satisfying
    soundness clause (c) and operating only on `D ⊆ D_t` fails to
    certify. -/
theorem cor_self_verif_robust_iv {R : EinsteinReplacement W} (V : Verifier W)
    {D : Set W.Obs} (hD : D ⊆ W.data R.t) :
    V.decide R.Tstar R.T0 D ≠ some true :=
  thm_self_verification V hD

/--
  **Corollary~\ref{cor:empirical-necessity}.** Any system passing the
  Einstein Test must have outcomes that escape the existing data
  `D_t` — empirical access is structurally necessary.

  *Proof:* if all outcomes were already in `D_t`, then
  `augmentedData = D_t ∪ outcomes ⊆ D_t`, so the verifier was
  effectively certifying on a subset of `D_t`. By
  Theorem~\ref{thm:self-verification}, the verifier cannot
  certify on such a set; contradiction with `𝔖.passes`. -/
theorem cor_empirical_necessity {R : EinsteinReplacement W} (𝔖 : System W R)
    (hPass : 𝔖.passes) :
    ¬ (𝔖.Pi.outcomes ⊆ W.data R.t) := by
  intro hOutcomesSubsumed
  -- augmentedData = data t ∪ outcomes ⊆ data t (under hypothesis)
  have hAugSub : 𝔖.Pi.augmentedData ⊆ W.data R.t := by
    intro s hs
    rcases hs with hData | hOutcome
    · exact hData
    · exact hOutcomesSubsumed hOutcome
  -- Extract: Mout = Tstar, augData ⊆ π(Mout), V certifies (Mout,T0,augData)
  obtain ⟨hMout, _, hCert⟩ := hPass
  -- Rewrite Mout to Tstar in the certification
  rw [hMout] at hCert
  -- Now hCert : V.decide R.Tstar R.T0 𝔖.Pi.augmentedData = some true.
  -- Pure self-verification on augData ⊆ D_t yields the required contradiction.
  exact thm_self_verification 𝔖.V hAugSub hCert

/--
  **Remark~\ref{rem:thm5-substance}.** Theorem 5's content follows
  directly from strict-refutation soundness (clause c) paired with
  (E1). The uniformity over `D ⊆ D_t` is automatic: every `D ⊆ D_t`
  inherits `D ⊆ π(T_0)` from (E1) `D_t ⊆ π(T_0)`. The substantive
  contribution is the robustness Corollary.
-/
example {R : EinsteinReplacement W} (V : Verifier W)
    {D1 D2 : Set W.Obs} (hD1 : D1 ⊆ W.data R.t) (hD2 : D2 ⊆ W.data R.t) :
    V.decide R.Tstar R.T0 D1 ≠ some true ∧
    V.decide R.Tstar R.T0 D2 ≠ some true :=
  ⟨thm_self_verification V hD1, thm_self_verification V hD2⟩

end EinsteinTest
