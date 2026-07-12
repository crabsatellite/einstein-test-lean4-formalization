/-
  EinsteinTest/Feasibility.lean

  Non-circular deterministic core of Theorem `thm:feasibility`.
  Positive generation and witness probabilities are paper-level
  stochastic premises.  Here we verify the logical composition step:
  once the target is emitted, successor-consistent data contain a
  strict witness, and the verifier is complete for represented strict
  witnesses, the system passes.
-/

import EinsteinTest.Basic

namespace EinsteinTest

variable {W : ObservationalWorld}

/-- Strict-witness completeness turns a represented witness into an
    accepting verifier decision. -/
theorem strict_witness_accepts
    {R : EinsteinReplacement W} (V : Verifier W)
    (hComplete : V.strictCompleteFor R.Tstar R.T0)
    {D : Set W.Obs} (hConsistent : D ⊆ W.predict R.Tstar)
    {s : W.Obs} (hsD : s ∈ D) (hsRef : s ∈ R.refutationSet) :
    V.decide R.Tstar R.T0 D = some true := by
  exact hComplete D hConsistent ⟨s, hsD, hsRef.1, hsRef.2⟩

/-- Deterministic compositional sufficiency: target emission,
    successor-consistent augmented data, a represented strict witness,
    and verifier completeness imply the Einstein pass predicate. -/
theorem strict_witness_feasibility
    {R : EinsteinReplacement W} (sys : System W R)
    (hMout : sys.Mout = R.Tstar)
    (hConsistent : sys.Pi.augmentedData ⊆ W.predict R.Tstar)
    (hComplete : sys.V.strictCompleteFor R.Tstar R.T0)
    (hWitness : ∃ s ∈ sys.Pi.augmentedData, s ∈ R.refutationSet) :
    sys.passes := by
  obtain ⟨s, hsData, hsRef⟩ := hWitness
  have hCert : sys.V.decide R.Tstar R.T0 sys.Pi.augmentedData = some true :=
    strict_witness_accepts sys.V hComplete hConsistent hsData hsRef
  refine ⟨hMout, ?_, ?_⟩
  · simpa [hMout] using hConsistent
  · simpa [hMout] using hCert

end EinsteinTest
