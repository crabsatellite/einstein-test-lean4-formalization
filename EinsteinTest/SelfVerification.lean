/-
  EinsteinTest/SelfVerification.lean

  Formal counterpart of Proposition `prop:no-cert`.  This is a
  strict-refutation certification result, not a computability or oracle
  impossibility theorem.
-/

import EinsteinTest.Basic

namespace EinsteinTest

variable {W : ObservationalWorld}

/-- No strict-refutation-sound verifier can certify using only a subset
    of incumbent-consistent data.  The proof uses only `sound_c` and
    candidate condition (E1-T0). -/
theorem no_strict_refutation_certification
    {R : EinsteinReplacement W} (V : Verifier W)
    {D : Set W.Obs} (hD : D ⊆ W.data R.t) :
    V.decide R.Tstar R.T0 D ≠ some true := by
  intro hCert
  obtain ⟨s, hsD, _, hsNot0⟩ := V.sound_c hCert
  exact hsNot0 (R.E1_T0 (hD hsD))

/-- A passing strict-refutation protocol must contribute at least one
    outcome outside the already recorded data. -/
theorem empirical_access_required
    {R : EinsteinReplacement W} (sys : System W R)
    (hPass : sys.passes) :
    ¬ (sys.Pi.outcomes ⊆ W.data R.t) := by
  intro hOutcomesSubsumed
  have hAugSub : sys.Pi.augmentedData ⊆ W.data R.t := by
    intro s hs
    rcases hs with hData | hOutcome
    · exact hData
    · exact hOutcomesSubsumed hOutcome
  obtain ⟨hMout, _, hCert⟩ := hPass
  rw [hMout] at hCert
  exact no_strict_refutation_certification sys.V hAugSub hCert

end EinsteinTest
