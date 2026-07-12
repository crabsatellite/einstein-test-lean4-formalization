/-
  EinsteinTest/Decomposition.lean

  Resource-profile layer.  The paper uses the vector

      (B_M, B_V, B_Pi)

  as its primitive resource object.  Unit-bearing scalarisation is used
  only after conversion weights are declared.  The algebra in this module
  supports the deterministic component of the paper's conditional serial
  expected-cost theorem; its probability and expectation layer is not
  formalized here.
-/

import EinsteinTest.Basic
import EinsteinTest.Floor

namespace EinsteinTest

variable {W : ObservationalWorld}

namespace System.ResourceProfile

/-- Coordinatewise (Pareto) resource order. -/
def ParetoLE (B B' : System.ResourceProfile) : Prop :=
  B.generation ≤ B'.generation ∧
  B.computationalVerification ≤ B'.computationalVerification ∧
  B.empiricalTime ≤ B'.empiricalTime

/-- A unit-bearing non-negative scalarisation.  The fields of `w` are
    conversion weights into a declared common reporting unit. -/
noncomputable def scalarise (w B : System.ResourceProfile) : ℝ∞ :=
  w.generation * B.generation +
  w.computationalVerification * B.computationalVerification +
  w.empiricalTime * B.empiricalTime

/-- Non-negative scalarisations preserve Pareto dominance. -/
theorem scalarise_mono {w B B' : System.ResourceProfile}
    (h : ParetoLE B B') :
    scalarise w B ≤ scalarise w B' := by
  rcases h with ⟨hM, hV, hPi⟩
  unfold scalarise
  gcongr

end System.ResourceProfile

/-- Machine-checked portion of Proposition `prop:profile`: on a passing
    system under the strict-refutation protocol, the empirical coordinate
    of the three-resource vector is bounded below by `tauMin`.

    The paper's generation and broad-class distinguishability clauses live
    in their own modules with their own external hypotheses; they are not
    silently bundled into this theorem. -/
theorem resource_profile_empirical_floor
    (R : EinsteinReplacement W) (sys : System W R)
    (hPass : sys.passes) :
    tauMin R ≤ sys.resourceProfile.empiricalTime := by
  exact thm_floor sys hPass

/-- Proposition `prop:resource-geometry`, weighted empirical clause:
    on a passing system, every non-negative scalarisation is at least
    the empirical weight times the strict-witness floor. -/
theorem weighted_resource_empirical_floor
    (R : EinsteinReplacement W) (sys : System W R)
    (w : System.ResourceProfile) (hPass : sys.passes) :
    w.empiricalTime * tauMin R ≤
      System.ResourceProfile.scalarise w sys.resourceProfile := by
  have hFloor : tauMin R ≤ sys.resourceProfile.empiricalTime :=
    resource_profile_empirical_floor R sys hPass
  unfold System.ResourceProfile.scalarise
  have hWeighted : w.empiricalTime * tauMin R ≤
      w.empiricalTime * sys.resourceProfile.empiricalTime := by
    gcongr
  exact hWeighted.trans le_add_self

/-- Fixed-environment invariance is definitional: once the candidate and
    observational world are fixed, changing which system value is supplied
    does not change `tauMin`.  This does not model changes to instruments,
    technology, or the observational world. -/
theorem fixed_environment_invariance
    {R : EinsteinReplacement W} (_sys1 _sys2 : System W R) :
    tauMin R = tauMin R := rfl

end EinsteinTest
