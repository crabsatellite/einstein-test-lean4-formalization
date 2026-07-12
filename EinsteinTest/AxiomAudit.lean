/-
  Axiom-dependency report for the companion formalization.

  The output identifies the assumptions used by each exported result.
  Absence of `sorry` does not remove dependencies on the explicitly
  listed external or construction bridges.
-/

import EinsteinTest

-- Set-theoretic strict-refutation layer.
#print axioms EinsteinTest.EinsteinReplacement.refutationSet_nonempty
#print axioms EinsteinTest.thm_floor
#print axioms EinsteinTest.tauMin_nonneg
#print axioms EinsteinTest.no_strict_refutation_certification
#print axioms EinsteinTest.empirical_access_required
#print axioms EinsteinTest.resource_profile_empirical_floor
#print axioms EinsteinTest.System.ResourceProfile.scalarise_mono
#print axioms EinsteinTest.weighted_resource_empirical_floor
#print axioms EinsteinTest.fixed_environment_invariance
#print axioms EinsteinTest.dynamic_floor_of_witness
#print axioms EinsteinTest.dynamic_tau_mono
#print axioms EinsteinTest.dynamic_tau_congr
#print axioms EinsteinTest.path_completion_mono
#print axioms EinsteinTest.dynamic_path_tau_mono
#print axioms EinsteinTest.strict_witness_accepts
#print axioms EinsteinTest.strict_witness_feasibility

-- Conditional Kolmogorov-complexity layer.
#print axioms EinsteinTest.thm_emission
#print axioms EinsteinTest.cor_rare

-- Broad-class recursion-theoretic layer.
#print axioms EinsteinTest.thm_undecidable_sigma01_hard
#print axioms EinsteinTest.Bridge_Halt_Iff_CandidateE2
#print axioms EinsteinTest.thm_candidate_recognition_sigma01_hard
#print axioms EinsteinTest.thm_undecidable_sigma02_upper
#print axioms EinsteinTest.thm_undecidable_tarski_decidable
#print axioms EinsteinTest.cor_no_universal
#print axioms EinsteinTest.Bridge_Halt_Iff_Dist
