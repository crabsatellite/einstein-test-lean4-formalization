import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Set.Lattice

/-! Literal set-theoretic statements of the submission manuscript.
The elapsed protocol cost is an independent variable; it is not replaced
by the sum-of-experiments carrier of the older companion.
-/
namespace EinsteinTest.SubmissionCore
open scoped ENNReal

def StrictSound {Obs : Type*} (incumbent successor : Set Obs) (V : Set Obs → Prop) : Prop :=
  ∀ data, V data → data ⊆ successor ∧ ∃ s ∈ data, s ∈ successor ∧ s ∉ incumbent

theorem empirical_floor {Obs : Type*}
    (oldData incumbent successor outcomes tech : Set Obs)
    (tau : Obs → ℝ≥0∞) (budget : ℝ≥0∞)
    (V : Set Obs → Prop) (sound : StrictSound incumbent successor V)
    (old_consistent : oldData ⊆ incumbent ∩ successor)
    (outcomes_available : outcomes ⊆ tech)
    (cost_link : ∀ s ∈ outcomes, tau s ≤ budget)
    (accepted : V (oldData ∪ outcomes)) :
    (⨅ s ∈ (successor \ incumbent) ∩ tech, tau s) ≤ budget := by
  obtain ⟨s, hs, hsucc, hnot⟩ := (sound _ accepted).2
  have hout : s ∈ outcomes := hs.resolve_left (fun hd => hnot (old_consistent hd).1)
  exact (iInf₂_le s ⟨⟨hsucc, hnot⟩, outcomes_available hout⟩).trans (cost_link s hout)

theorem dynamic_floor {Obs : Type*}
    (oldData incumbent successor outcomes : Set Obs)
    (completion : Obs → ℝ≥0∞) (budget : ℝ≥0∞)
    (V : Set Obs → Prop) (sound : StrictSound incumbent successor V)
    (old_consistent : oldData ⊆ incumbent ∩ successor)
    (cost_link : ∀ s ∈ outcomes, completion s ≤ budget)
    (accepted : V (oldData ∪ outcomes)) :
    (⨅ s ∈ successor \ incumbent, completion s) ≤ budget := by
  obtain ⟨s, hs, hsucc, hnot⟩ := (sound _ accepted).2
  have hout : s ∈ outcomes := hs.resolve_left (fun hd => hnot (old_consistent hd).1)
  exact (iInf₂_le s ⟨hsucc, hnot⟩).trans (cost_link s hout)

theorem no_certification {Obs : Type*}
    (oldData incumbent successor data : Set Obs)
    (V : Set Obs → Prop) (sound : StrictSound incumbent successor V)
    (old_consistent : oldData ⊆ incumbent) (data_old : data ⊆ oldData) :
    ¬ V data := by
  intro accepted
  obtain ⟨s, hs, _, hnot⟩ := (sound _ accepted).2
  exact hnot (old_consistent (data_old hs))

theorem empirical_access {Obs : Type*}
    (oldData incumbent successor outcomes : Set Obs)
    (V : Set Obs → Prop) (sound : StrictSound incumbent successor V)
    (old_consistent : oldData ⊆ incumbent)
    (accepted : V (oldData ∪ outcomes)) :
    ¬ outcomes ⊆ oldData := by
  intro hout
  apply no_certification oldData incumbent successor (oldData ∪ outcomes) V sound old_consistent
  · exact Set.union_subset (fun _ h => h) hout
  · exact accepted

end EinsteinTest.SubmissionCore
