/-
  EinsteinTest/Basic.lean

  Abstract definitions supporting the revised paper:
    * observational world `(Obs, Th, π, Tech, τ, D)`;
    * model-relative candidate with E1-T0, E1-T*, and positive E2;
    * verifier with strict-refutation soundness;
    * empirical protocol and its elapsed-time coordinate;
    * three-resource vector `(B_M, B_V, B_Π)`.

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

/-! ### Definition `def:candidate`: model-relative Einstein candidate. -/

/--
  A theory `T*` is a model-relative *Einstein candidate* for `T_0` at
  time `t` if:

  * **(E1-T0)** `T_0` is consistent with `D_t`.
  * **(E1-T*)** `T*` is consistent with `D_t`.
  * **(E2)** there is an observation in `π(T*) \ π(T_0)`.

  The paper's optional Beth non-definability novelty screen is not
  represented by an unconstrained proposition.  A genuine encoding
  requires first-order syntax, reducts, expansions, and definability;
  this abstract observational layer intentionally omits it.
-/
structure EinsteinReplacement (W : ObservationalWorld) where
  /-- The base theory `T_0`. -/
  T0 : W.Th
  /-- The successor theory `T*`. -/
  Tstar : W.Th
  /-- The time-slice index `t`. -/
  t : ℝ
  /-- **(E1-T0)** `T_0` is consistent with `D_t`. -/
  E1_T0 : W.consistentWith T0 (W.data t)
  /-- **(E1-T*)** `T*` is consistent with `D_t`. -/
  E1_Tstar : W.consistentWith Tstar (W.data t)
  /-- **(E2)** A positive strict-refutation observation exists. -/
  E2 : ∃ s, s ∈ W.predict Tstar ∧ s ∉ W.predict T0

namespace EinsteinReplacement

variable {W : ObservationalWorld} (R : EinsteinReplacement W)

/--
  *Strict-refutation set.* The observations on which `T*` predicts
  something `T_0` does not. Membership in this set is the witness
  required by Definition `def:generator` clause (c).
-/
def refutationSet : Set W.Obs :=
  W.predict R.Tstar \ W.predict R.T0

/-- Candidate condition (E2) is exactly non-emptiness of the strict
    refutation set. -/
lemma refutationSet_nonempty : R.refutationSet.Nonempty := by
  obtain ⟨s, hsStar, hs0⟩ := R.E2
  exact ⟨s, hsStar, hs0⟩

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
  exact hRef.2 (R.E1_T0 hData)

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

/-- A verifier is complete for represented strict-refutation witnesses
    for a fixed theory pair when every successor-consistent data set
    containing such a witness is accepted.  This is deliberately a
    separate predicate from soundness: a verifier may be sound by never
    accepting, whereas the finite-feasibility theorem needs both. -/
def Verifier.strictCompleteFor {W : ObservationalWorld} (V : Verifier W)
    (Tstar T0 : W.Th) : Prop :=
  ∀ D : Set W.Obs,
    D ⊆ W.predict Tstar →
    (∃ S ∈ D, S ∈ W.predict Tstar ∧ S ∉ W.predict T0) →
    V.decide Tstar T0 D = some true

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

  together with separately reported resource coordinates
  `(B_M, B_V, B_Π) ∈ ℝ∞³`. The system
  *passes the Einstein Test* on a model-relative candidate `R`
  iff
  *  `Mout = R.Tstar`,
  *  `Pi.augmentedData ⊆ π(Mout)`,
  *  `V.decide Mout R.T0 Pi.augmentedData = some true`.

  The coordinates are a vector.  The revised paper does not add raw
  computational resources and elapsed empirical time without an
  explicit scalarisation rule.
-/
structure System (W : ObservationalWorld) (R : EinsteinReplacement W) where
  /-- Generator output `M(p)`. -/
  Mout : W.Th
  /-- The verifier `V`. -/
  V : Verifier W
  /-- Empirical protocol at the candidate's time slice. -/
  Pi : EmpiricalProtocol W R.t
  /-- Reported generator-side resource use. -/
  BM : ℝ∞
  /-- Reported computational-verifier resource use. -/
  BV : ℝ∞

namespace System

variable {W : ObservationalWorld} {R : EinsteinReplacement W} (𝔖 : System W R)

/-- Empirical elapsed-time coordinate. -/
noncomputable def BPi : ℝ∞ := 𝔖.Pi.cost

/-- The paper's primary three-resource vector. -/
structure ResourceProfile where
  generation : ℝ∞
  computationalVerification : ℝ∞
  empiricalTime : ℝ∞

/-- Resource profile reported by a system. -/
noncomputable def resourceProfile : ResourceProfile :=
  ⟨𝔖.BM, 𝔖.BV, 𝔖.BPi⟩

/--
  *Passes-the-test* predicate. The system passes Einstein Test on
  candidate `R` iff:

  * generator outputs the successor (`Mout = R.Tstar`),
  * the protocol's augmented data is consistent with the output,
  * the verifier certifies `(Mout, T_0, augmentedData)` with `1`.

  Resource coordinates are recorded separately and are not part of
  this logical pass predicate.  The predicate is used by the empirical
  floor and no-certification results.
-/
def passes : Prop :=
  𝔖.Mout = R.Tstar ∧
  𝔖.Pi.augmentedData ⊆ W.predict 𝔖.Mout ∧
  𝔖.V.decide 𝔖.Mout R.T0 𝔖.Pi.augmentedData = some true

end System

end EinsteinTest
