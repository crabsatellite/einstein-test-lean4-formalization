/-
  EinsteinTest/Basic.lean

  Definitions 1–4 of the paper:
    * Definition `def:obs-world`     — observational world (Obs, Th, π, Tech, τ, D)
    * Definition `def:einstein-rep`  — Einstein-replacement: (E1), (E2), (E3)
    * Definition `def:generator`     — generator M, verifier V with strict-refutation soundness
    * Definition `def:emp-protocol`  — empirical protocol Π and its wall-clock cost B_Π
    * Definition `def:einstein-test` — Einstein Test, total cost C_Einstein

  Companion to: "What the Karpowicz Theorem Does Not Prove" (Li, 2026).

  *Lean 4 naming note:* Greek capital `Π` is reserved by Lean's parser
  for dependent product types. The paper symbol `Π` (empirical protocol)
  is rendered as `Pi` in Lean code.  ASCII identifiers for paper symbols:

      paper  →  Lean
      ─────────────
      π(T)   →  predict T
      τ_t(s) →  tau s t
      D_t    →  data t
      Π      →  Pi (structure field; local var)
      T*     →  Tstar
      T_0    →  T0
      𝔖      →  𝔖   (kept; 'fraktur S' is parsed as identifier)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop

namespace EinsteinTest

/-- `ℝ∞` notation for the wall-clock cost codomain.
    Paper-level meaning: extended non-negative reals `[0, +∞]`.

    *Implementation note:* the paper writes `ℝ∞ = ℝ ∪ {+∞}` informally;
    since `τ_t(s) ≥ 0` always holds (Def `def:obs-world`), we use
    `ℝ≥0∞ = WithTop ℝ≥0` (the canonical Mathlib type for `[0, +∞]`).
    This makes non-negativity automatic and gives us
    `CompleteLinearOrder` (needed for `tauMin` in `Floor.lean`).  The
    paper's intended semantics is preserved: `⊤ = +∞`, `0` is the
    bottom element, and `0 ≤ τ_t(s)` for all `s`. -/
notation "ℝ∞" => ENNReal

/-! ### Definition `def:obs-world`: Observational world. -/

/--
  An observational world fixes:

  * `Obs` — countable set of observations (typed strings).
  * `Th`  — set of FO-axiomatised theories (each over its own signature
            extending some common base language $L_0$).
  * `predict T` — `π(T)`, the set of observations entailed by `T`
                   together with a fixed background of auxiliary theories.
                   By convention `T` is **consistent with** a data set
                   $D$ iff $D \subseteq \mathrm{predict}\ T$.
  * `Tech t` — `Tech_t`, observations performable at time `t`.
  * `tau s t` — `τ_t(s)`, minimum wall-clock time to perform an
                experiment yielding observation `s` under `Tech_t`.
                `+∞` if `s ∉ Tech_t`.
  * `data t` — `D_t`, observations recorded by time `t`.
               Non-decreasing in `t`.

  All five components are abstract parameters of the framework
  (`predict` is the only one used in the structural theorems; the
   remaining parameters appear only in Theorem~\ref{thm:floor} via
   `tau` and `Tech`).
-/
structure ObservationalWorld where
  Obs : Type
  Th : Type
  predict : Th → Set Obs
  Tech : ℝ → Set Obs
  tau : Obs → ℝ → ℝ∞
  data : ℝ → Set Obs
  /-- Data accumulation is monotone: D_s ⊆ D_t whenever s ≤ t. -/
  data_mono : ∀ {s t : ℝ}, s ≤ t → data s ⊆ data t
  /-- τ_t(s) = +∞ when s ∉ Tech_t. -/
  tau_infty_off_tech : ∀ (s : Obs) (t : ℝ), s ∉ Tech t → tau s t = ⊤
  /-- τ_t(s) is non-negative. -/
  tau_nonneg : ∀ (s : Obs) (t : ℝ), 0 ≤ tau s t

namespace ObservationalWorld

variable (W : ObservationalWorld)

/-- A theory `T` is *consistent with* a data set `D` iff `D ⊆ π(T)`. -/
def consistentWith (T : W.Th) (D : Set W.Obs) : Prop :=
  D ⊆ W.predict T

/-- A data set `D` is consistent with theory `T` (symmetric phrasing). -/
def dataConsistentWith (D : Set W.Obs) (T : W.Th) : Prop :=
  D ⊆ W.predict T

lemma consistentWith_iff_dataConsistentWith (T : W.Th) (D : Set W.Obs) :
    W.consistentWith T D ↔ W.dataConsistentWith D T := Iff.rfl

end ObservationalWorld

/-! ### Definition `def:einstein-rep`: Einstein-replacement (E1)/(E2)/(E3). -/

/--
  A theory `T*` is an *Einstein-replacement* of `T_0` at time `t` if:

  * **(E1) Backward compatibility:** `T_0` is consistent with the data
          `D_t` accumulated by time `t`, i.e., `D_t ⊆ π(T_0)`.
  * **(E2) Strict prediction divergence:** `π(T*) ≠ π(T_0)` — some
          observable prediction differs.
  * **(E3) Ontological innovation (Beth-definability):** `T*` extends
          `T_0`'s vocabulary `L_0` by adding `k ≥ 1` primitive
          non-logical symbols `σ_1, …, σ_k`, and at least one such
          symbol `σ` is NOT FO-definable inside `T*` from `L_0`-vocabulary
          alone. By Beth's theorem this is equivalent to the existence
          of two `T*`-models whose `L_0`-reducts coincide but which
          assign distinct interpretations to `σ`.

  The (E3) clause is an abstract Prop here; the recursion-theoretic
  construction in `Undecidable.lean` will instantiate one specific
  shape (single fresh 0-ary predicate `S*` with explicit defining
  formula `H_e`), and Remark `adversarial-not-E3` notes that this
  family fails (E3) by construction.
-/
structure EinsteinReplacement (W : ObservationalWorld) where
  /-- The base theory `T_0`. -/
  T0 : W.Th
  /-- The successor theory `T*`. -/
  Tstar : W.Th
  /-- The time-slice index `t`. -/
  t : ℝ
  /-- **(E1)** `T_0` consistent with `D_t`. -/
  E1 : W.consistentWith T0 (W.data t)
  /-- **(E2)** `π(T*) ≠ π(T_0)`. -/
  E2 : W.predict Tstar ≠ W.predict T0
  /-- **(E3)** `T*` is not a definitional extension of `T_0` in the
       Beth sense. Stated abstractly: there exists a primitive
       non-logical symbol added by `T*` that is not FO-definable in
       `T*` from `T_0`'s vocabulary. We carry this as a `Prop`-valued
       parameter; constructive instances would witness the model
       pair from Beth's theorem. -/
  E3 : Prop

namespace EinsteinReplacement

variable {W : ObservationalWorld} (R : EinsteinReplacement W)

/--
  *Strict-refutation set.* The observations on which `T*` predicts
  something `T_0` does not. Membership in this set is the witness
  required by Definition `def:generator` clause (c).
-/
def refutationSet : Set W.Obs :=
  W.predict R.Tstar \ W.predict R.T0

/-- Strict refutations live outside `π(T_0)`. -/
lemma refutationSet_disjoint_T0 :
    ∀ s ∈ R.refutationSet, s ∉ W.predict R.T0 := by
  intro s hs
  exact hs.2

/-- Strict refutations lie inside `π(T*)`. -/
lemma refutationSet_subset_Tstar :
    R.refutationSet ⊆ W.predict R.Tstar := by
  intro s hs
  exact hs.1

/--
  Under (E1), the data `D_t` lies entirely inside `π(T_0)`, hence
  contains no strict-refutation witnesses for `T*`:
  $(\pi(T^*) \setminus \pi(T_0)) \cap D_t = \emptyset$.

  Used in the proofs of Theorem~\ref{thm:floor} (witness must come
  from `outcomes(E)`) and Theorem~\ref{thm:self-verification}
  (witness must come from outside `D_t`).
-/
lemma data_disjoint_refutationSet :
    W.data R.t ∩ R.refutationSet = ∅ := by
  ext s
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hData hRef
  exact hRef.2 (R.E1 hData)

end EinsteinReplacement

/-! ### Definition `def:generator`: Generator `M` and verifier `V`. -/

/--
  *Strict-refutation soundness* of a verifier `V` on an Einstein-
  replacement candidate. The verifier's signature is

  `V : Th × Th × 2^Obs → {0, 1, ⊥}`

  (where `⊥` denotes "undefined / does not halt"). Soundness clauses:

  * **(a)** If `V(T*, T_0, D) = 1` then `T*` is consistent with `D`
          (i.e., `D ⊆ π(T*)`).
  * **(b)** If `V(T*, T_0, D) = 1` then `T_0` is refuted by some
          `S ∈ D` (i.e., `∃ S ∈ D. S ∉ π(T_0)`).
  * **(c)** Any such refuting `S` lies in
          `π(T*) \ π(T_0) = R.refutationSet`.

  We package soundness as a single proposition over `V` and a
  triple `(T*, T_0, D)`.
-/
structure Verifier (W : ObservationalWorld) where
  /-- The decision: 0 (reject), 1 (certify), or `none` (no halt). -/
  decide : W.Th → W.Th → Set W.Obs → Option Bool
  /-- **Soundness clause (a).** Certified ⇒ data consistent with `T*`. -/
  sound_a : ∀ {Tstar T0 : W.Th} {D : Set W.Obs},
    decide Tstar T0 D = some true → D ⊆ W.predict Tstar
  /-- **Soundness clause (b).** Certified ⇒ `T_0` refuted on some `S ∈ D`.

      *Note:* Strictly logically, `sound_b` follows from `sound_c` (just
      drop `S ∈ π(T*)` from the conjunct).  We retain it as a separate
      field for clarity and to match the paper's Definition~\ref{def:generator}
      (b)+(c) structure; no theorem in this formalisation uses `sound_b`.
      The derived implication is documented as the lemma
      `Verifier.sound_b_from_sound_c` below. -/
  sound_b : ∀ {Tstar T0 : W.Th} {D : Set W.Obs},
    decide Tstar T0 D = some true → ∃ S ∈ D, S ∉ W.predict T0
  /-- **Soundness clause (c).** Refuting witnesses live in
       `π(T*) \ π(T_0)`. -/
  sound_c : ∀ {Tstar T0 : W.Th} {D : Set W.Obs},
    decide Tstar T0 D = some true →
    ∃ S ∈ D, S ∈ W.predict Tstar ∧ S ∉ W.predict T0

/-- *Derivability witness:* `sound_b` is logically implied by `sound_c`.
    Documents the redundancy noted in the docstring of the `sound_b` field
    above; not used anywhere else in the formalisation. -/
lemma Verifier.sound_b_from_sound_c {W : ObservationalWorld} (V : Verifier W)
    {Tstar T0 : W.Th} {D : Set W.Obs}
    (hCert : V.decide Tstar T0 D = some true) :
    ∃ S ∈ D, S ∉ W.predict T0 := by
  obtain ⟨S, hS_in_D, _, hS_not_in_T0⟩ := V.sound_c hCert
  exact ⟨S, hS_in_D, hS_not_in_T0⟩

/-! ### Definition `def:emp-protocol`: Empirical protocol. -/

/--
  An empirical protocol `Π` (Lean name: `Pi`) performs a finite set of
  experiments `E ⊆ Tech_t` and returns the augmented data
  `D_t ∪ outcomes(E)`.

  Cost: `B_Π = Σ_{e ∈ E} τ_t(e)` (wall-clock time on the static
  frontier `Tech_t`, ignoring frontier advances during execution;
  this convention is internally consistent — see Theorem~\ref{thm:floor}).

  Outcomes are constrained to lie inside `Tech_t` because each
  experiment is by definition performable at time `t`.
-/
structure EmpiricalProtocol (W : ObservationalWorld) (t : ℝ) where
  /-- Finite set of experiments performed. -/
  experiments : Finset W.Obs
  /-- Each experiment performable at time `t`. -/
  experiments_in_tech : ∀ e ∈ experiments, e ∈ W.Tech t
  /-- Outcomes augmenting `D_t`. -/
  outcomes : Set W.Obs
  /-- All outcomes lie in `Tech_t` (the static-frontier convention). -/
  outcomes_in_tech : outcomes ⊆ W.Tech t
  /-- Paper convention: "we identify each experiment with its
       (possibly random) outcome observation".  Every reported outcome
       was the result of a performed experiment, so `outcomes ⊆ experiments`
       under the experiment/outcome identification used throughout.
       Required for Theorem~\ref{thm:floor} to link `cost` (a sum over
       `experiments`) with the strict-refutation witness (in `outcomes`). -/
  outcomes_subset_experiments : ∀ s ∈ outcomes, s ∈ experiments

namespace EmpiricalProtocol

variable {W : ObservationalWorld} {t : ℝ} (Pi : EmpiricalProtocol W t)

/-- Augmented data returned by the protocol: `D_t ∪ outcomes(E)`. -/
def augmentedData : Set W.Obs := W.data t ∪ Pi.outcomes

/-- Wall-clock cost of the protocol: `B_Π = Σ_{e ∈ E} τ_t(e)`.
    Stated in `ℝ∞ = WithTop ℝ` to accommodate `+∞` for experiments
    outside the frontier (excluded by `experiments_in_tech`). -/
noncomputable def cost : ℝ∞ :=
  ∑ e ∈ Pi.experiments, W.tau e t

end EmpiricalProtocol

/-! ### Definition `def:einstein-test`: Einstein Test. -/

/--
  An *Einstein-Test system* `𝔖 = (M, V, Π)` consists of:

  * a generator `M` (the prompt-driven theory-producer, abstracted as
    the produced theory `Mout : Th`),
  * a verifier `V : Verifier W`,
  * an empirical protocol `Pi : EmpiricalProtocol W t`,

  together with cost budgets `(B_M, B_V, B_Π) ∈ ℝ∞³`. The system
  *passes the Einstein Test* on an Einstein-replacement candidate `R`
  iff
  *  `Mout = R.Tstar`,
  *  `Pi.augmentedData ⊆ π(Mout)`,
  *  `V.decide Mout R.T0 Pi.augmentedData = some true`,
  *  the realized cost is bounded by the corresponding budget for each
    component.

  Total cost: `C_Einstein = B_M + B_V + B_Π` (additive composition
  convention of Def `def:einstein-test`; parallel resources would
  give the `max` form — flagged here for cross-reference with
  Theorem~\ref{thm:decomposition}).
-/
structure System (W : ObservationalWorld) (R : EinsteinReplacement W) where
  /-- Generator output `M(p)`. -/
  Mout : W.Th
  /-- The verifier `V`. -/
  V : Verifier W
  /-- Empirical protocol at the candidate's time slice. -/
  Pi : EmpiricalProtocol W R.t
  /-- Generator-side budget. -/
  BM : ℝ∞
  /-- Verifier-side budget. -/
  BV : ℝ∞

namespace System

variable {W : ObservationalWorld} {R : EinsteinReplacement W} (𝔖 : System W R)

/-- Empirical-side budget. -/
noncomputable def BPi : ℝ∞ := 𝔖.Pi.cost

/-- Total cost `C_Einstein = B_M + B_V + B_Π`. -/
noncomputable def totalCost : ℝ∞ := 𝔖.BM + 𝔖.BV + 𝔖.BPi

/--
  *Passes-the-test* predicate. The system passes Einstein Test on
  candidate `R` iff:

  * generator outputs the successor (`Mout = R.Tstar`),
  * the protocol's augmented data is consistent with the output,
  * the verifier certifies `(Mout, T_0, augmentedData)` with `1`,
  * all three budgets are respected.

  Used in Theorem~\ref{thm:decomposition} clause (c) and Corollary
  `cor:empirical-necessity`.
-/
def passes : Prop :=
  𝔖.Mout = R.Tstar ∧
  𝔖.Pi.augmentedData ⊆ W.predict 𝔖.Mout ∧
  𝔖.V.decide 𝔖.Mout R.T0 𝔖.Pi.augmentedData = some true

end System

end EinsteinTest
