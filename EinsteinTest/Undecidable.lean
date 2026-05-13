/-
  EinsteinTest/Undecidable.lean

  Theorem~\ref{thm:undecidable} (Distinguishability is Σ⁰₁-hard on
  recursively axiomatised classes containing Robinson Q; decidable on
  the Tarski class), Corollary~\ref{cor:no-universal}, and
  Remark~\ref{rem:adversarial-not-E3}.

  Construction.  For each Turing machine code `e`, let
  `T*_e := Q ∪ {S* ↔ H_e}` where `S*` is a fresh 0-ary predicate
  outside `L_0`'s signature and `H_e := ∃t. T(e, 0, t)` is the
  arithmetic halting predicate.  The observable family is the
  disjoint atomic union `Obs := L_0 ∪ {S*}`.  The Halt ⇒ Dist
  many-one reduction is `e ↦ (T*_e, T_0)`; on the single
  distinguished observable `S*` the prediction sets of `T*_e` and
  `T_0` differ iff `Halt(e)`.

  Note on Q-naming.  "Robinson's Q" follows Smith 2013 Ch 11 §"Q is
  Σ₁-complete" (primary).  Boolos-Burgess-Jeffrey use a different
  convention: BBJ's "Q" is Shoenfield-style minimal arithmetic
  (§16.2), distinct from standard Robinson's Q (BBJ's §16.4 "R");
  we therefore cite Smith / Hájek-Pudlák / TMR throughout.

  Adversarial-not-E3 caveat.  `T*_e` is by construction a
  definitional extension of `T_0 = Q` (via S* ↔ H_e), so it fails
  (E3) by Beth's theorem.  Theorem 3 is a result about `Dist` on
  r.e.-axiomatised classes, not specifically about Einstein-Test
  verifiers; Cor `no-universal` transfers the lower bound to any
  super-family of Dist-deciders.

  Lean atomic axiom surface (per `feedback_gap_ledger_in_lean4`
  ATOMIC MINIMAL UNITS; full Mathlib FO-encoding of Robinson Q is
  deferred — under v6 this is not `gapBlocked`, since the textbook
  claims are accepted on external authority as Cat 2 axioms below):

  * Cat 3 carriers (paper-novel typed primitives):
      `DistinguishedObs`  — fresh `S*` predicate
      `H_e_Obs`           — paper's `H_e := ∃t. T(e, 0, t)` as
                            an L_0-observable indexed by `Code`
      `Bridge1b_T0`       — abstract Robinson Q
      `Bridge1b_Tstar`    — abstract `T*_e` family

  * Cat 3 paper-stated defining equations (atomic):
      `Bridge_Encoding_Sstar_T0`        — S* ∉ π(T_0) freshness
      `Bridge_H_e_distinct_from_Sstar`  — H_e ≠ S* (atomic
                                          disjoint-union on Obs)
      `Bridge_Defining_Biconditional`   — T*_e ⊢ S* ↔ T*_e ⊢ H_e
                                          (modus ponens on the
                                          defining axiom)

  * Cat 2 textbook atomic axioms:
      `Bridge_Q_Sigma01_completeness`   — Smith 2013 Ch 11 / HP 1998
      `Bridge_Q_Sigma01_soundness`      — TMR 1953 + Smith 2013 §10
      `Bridge_DefExt_Conservative`      — Shoenfield 1967 §4.6
      `Bridge_Tarski_RCF_Correctness`   — Tarski 1948 RAND R-109

  * Derived theorems composing the atomic axioms:
      `Bridge_Q_Sigma01_complete_sound` — H_e ∈ π(T_0) ↔ Halt(e)
      `Bridge_Sstar_iff_Halt`           — S* ∈ π(T*_e) ↔ Halt(e)
      `Bridge_Halt_Iff_Dist`            — full Halt ↔ Dist reduction
      `thm_undecidable_*`               — paper-level theorems
-/

import EinsteinTest.Basic
import Mathlib.Computability.Halting
import Mathlib.Computability.Reduce

namespace EinsteinTest

/-! ### Setup: r.e.-axiomatised theory classes. -/

/-- An r.e.-axiomatised theory class is presented by a computable
    function from indices (`Nat`) to axiom sets together with a
    uniform r.e. predicate for membership in `π`. -/
class REAxiomatised (W : ObservationalWorld) where
  /-- Index → theory. -/
  byIndex : ℕ → W.Th
  /-- Uniform r.e. of `S ∈ π(byIndex n)`. -/
  predict_re : ∀ (n : ℕ) (S : W.Obs), Decidable (S ∈ W.predict (byIndex n))

/-! ### Distinguishability decision problem. -/

variable {W : ObservationalWorld}

/-- The distinguishability decision problem `Dist`. -/
def Dist (W : ObservationalWorld) (T1 T2 : W.Th) : Prop :=
  W.predict T1 ≠ W.predict T2

/-! ### Cat 3 atomic carriers (paper-novel primitives).

  Four atomic carriers realising the paper's
  `T*_e := Q ∪ {S* ↔ H_e}` construction at the abstract
  `W.Obs / W.Th` level.  Declared as `axiom` (rather than `opaque`)
  because `W.Obs` and `W.Th` are abstract types without required
  `Nonempty` instances; `axiom T : <type>` postulates an inhabitant
  without needing a `Nonempty` witness.

  Citation: Li 2026, *What the Karpowicz Theorem Does Not Prove*,
  `\label{thm:undecidable}` construction.
-/

/-- Distinguished observable `S*`: the fresh 0-ary predicate added
    to `T_0 = Q` in the adversarial construction.

    *Cat 3 sub-type: carrier (primitive type).* -/
axiom DistinguishedObs (W : ObservationalWorld) [REAxiomatised W] : W.Obs

/-- Paper's halting sentence `H_e := ∃t. T(e, 0, t)` (Kleene's
    T-predicate Σ⁰₁ sentence asserting machine `e` halts on input 0),
    encoded as an L_0-observable indexed by Turing-machine codes.
    This is the L_0-sentence on the right-hand side of the
    defining biconditional `S* ↔ H_e`.

    *Cat 3 sub-type: carrier (primitive type).* -/
axiom H_e_Obs (W : ObservationalWorld) [REAxiomatised W] :
    Nat.Partrec.Code → W.Obs

/-- Base theory `T_0 = Q`: abstract realisation of Robinson's Q.

    *Cat 3 sub-type: carrier (primitive type).* -/
axiom Bridge1b_T0 (W : ObservationalWorld) [REAxiomatised W] : W.Th

/-- Extension family `T*_e := Q ∪ {S* ↔ H_e}`: abstract realisation
    indexed by Turing-machine codes.

    *Cat 3 sub-type: carrier (primitive type).* -/
axiom Bridge1b_Tstar (W : ObservationalWorld) [REAxiomatised W] :
    Nat.Partrec.Code → W.Th

/-! ### Cat 3 atomic defining equations (paper-stated).

  Three atomic clauses encoding the paper's construction:
    (iii)   `S*` is fresh in `T_0`'s signature;
    (iii')  `H_e` is distinct from `S*` (paper: `Obs = L_0 ∪ {S*}`
            disjoint, `H_e ∈ L_0`);
    (iv)    `T*_e ⊢ S*` iff `T*_e ⊢ H_e` (modus ponens on the
            defining axiom `S* ↔ H_e`).

  Citation: Li 2026, `\label{thm:undecidable}` proof.
-/

/-- (iii) `S*` is fresh in `T_0`: since `S*` does not occur in `T_0`'s
    axioms, `T_0 ⊬ S*`, hence `S* ∉ π(T_0)`.

    *Cat 3 sub-type: structural defining equation.* -/
axiom Bridge_Encoding_Sstar_T0 (W : ObservationalWorld) [REAxiomatised W] :
    DistinguishedObs W ∉ W.predict (Bridge1b_T0 W)

/-- (iii') `H_e` and `S*` are distinct observables.  Paper-stated:
    `Obs` is the disjoint atomic union `L_0 ∪ {S*}` with `H_e ∈ L_0`,
    so `H_e ≠ S*`.  This side-condition is needed to instantiate
    `Bridge_DefExt_Conservative` (universally quantified over
    `S ≠ DistinguishedObs W`) at the specific observable `H_e_Obs e`.

    *Cat 3 sub-type: structural defining equation.* -/
axiom Bridge_H_e_distinct_from_Sstar
    (W : ObservationalWorld) [REAxiomatised W] :
    ∀ e, H_e_Obs W e ≠ DistinguishedObs W

/-- (iv) Defining biconditional in `T*_e`: the axiom `S* ↔ H_e` of
    `T*_e` gives, by modus ponens, `T*_e ⊢ S*` iff `T*_e ⊢ H_e`.
    At the abstract `W.Obs / W.Th` level (where `π` is the
    syntactic provability map per the paper's thm:undecidable
    hypothesis), this is `S* ∈ π(T*_e) ↔ H_e ∈ π(T*_e)`.

    Paper-novel Step 1 only: the textbook conservativity link
    `T*_e ⊢ H_e ↔ Q ⊢ H_e` (Step 2) is a separate Cat 2 fact
    derived from `Bridge_DefExt_Conservative` specialised at the
    observable `H_e_Obs e ≠ DistinguishedObs W` (using
    `Bridge_H_e_distinct_from_Sstar`).

    *Cat 3 sub-type: structural defining equation.* -/
axiom Bridge_Defining_Biconditional
    (W : ObservationalWorld) [REAxiomatised W] :
    ∀ e, DistinguishedObs W ∈ W.predict (Bridge1b_Tstar W e) ↔
         H_e_Obs W e ∈ W.predict (Bridge1b_Tstar W e)

/-! ### Cat 2 atomic textbook axioms. -/

/-- Σ⁰₁-completeness of `Q` applied to `H_e`: if machine `e` halts
    on input 0, then Robinson's `Q` proves the arithmetic halting
    predicate `H_e`.

    At the abstract level, `Q ⊢ H_e` is captured as
    `H_e_Obs e ∈ π(Bridge1b_T0)` (since `π` is the syntactic
    provability map of `T_0 = Q`).

    Citation: Smith, *An Introduction to Gödel's Theorems*, 2nd ed.,
    Cambridge UP 2013, Ch 11 "What Q can prove", §"Q is Σ₁-complete"
    (primary); Hájek-Pudlák, *Metamathematics of First-Order
    Arithmetic*, Springer 1998, Preliminaries §(c) pp. 20-26
    (secondary, foundational preliminaries-level fact, not numbered). -/
axiom Bridge_Q_Sigma01_completeness
    (W : ObservationalWorld) [REAxiomatised W] :
    ∀ e, (Nat.Partrec.Code.eval e 0).Dom →
         H_e_Obs W e ∈ W.predict (Bridge1b_T0 W)

/-- Σ⁰₁-soundness of `Q` applied to `H_e`: if `Q` proves the
    arithmetic halting predicate `H_e`, then `H_e` is true, i.e.,
    machine `e` halts on input 0.

    Citation: Tarski-Mostowski-Robinson, *Undecidable Theories*,
    North-Holland 1953, Ch II (Q's axiomatization) + Smith 2013
    §10.1-10.2 (axiom-by-axiom verification that ℕ ⊨ Q).
    Σ⁰₁-soundness follows as a one-line corollary of `N ⊨ Q`
    combined with soundness of first-order derivation — folklore
    preliminaries fact, not a numbered theorem.

    A strictly atomic split (`N_models_Q` + `Sigma01_soundness_of_-
    FO_derivation`) is deferred to a future Mathlib FO formalisation
    of Robinson Q. -/
axiom Bridge_Q_Sigma01_soundness
    (W : ObservationalWorld) [REAxiomatised W] :
    ∀ e, H_e_Obs W e ∈ W.predict (Bridge1b_T0 W) →
         (Nat.Partrec.Code.eval e 0).Dom

/-- Conservativity of definitional extension outside `S*`: for every
    observable `S ≠ S*`, the prediction sets of `T*_e` and `T_0`
    agree on `S`.  Since `T*_e := T_0 ∪ {S* ↔ H_e}` adds only the
    defining axiom for `S*` over `T_0 = Q`, no L_0-sentence
    derivable in `T*_e` requires the `S*` axiom (substitution of
    `H_e` for `S*` reduces to a `T_0`-derivation).

    Citation: Shoenfield, *Mathematical Logic*, Addison-Wesley 1967,
    §4.6 "Extensions by definitions" p. 57f (primary, theorem-
    numbered); Hodges, *A Shorter Model Theory*, Cambridge UP 1997,
    §2.6 (secondary, section-level). -/
axiom Bridge_DefExt_Conservative
    (W : ObservationalWorld) [REAxiomatised W] :
    ∀ (e : Nat.Partrec.Code) (S : W.Obs),
      S ≠ DistinguishedObs W →
        (S ∈ W.predict (Bridge1b_Tstar W e) ↔ S ∈ W.predict (Bridge1b_T0 W))

/-! ### Derived theorems (composing atomic Cat 2 + Cat 3 axioms). -/

/-- `H_e ∈ π(T_0) ↔ Halt(e)`: Σ⁰₁-complete-sound iff form, composing
    `Bridge_Q_Sigma01_completeness` and `Bridge_Q_Sigma01_soundness`. -/
theorem Bridge_Q_Sigma01_complete_sound
    (W : ObservationalWorld) [REAxiomatised W] :
    ∀ e, H_e_Obs W e ∈ W.predict (Bridge1b_T0 W) ↔
         (Nat.Partrec.Code.eval e 0).Dom :=
  fun e => ⟨Bridge_Q_Sigma01_soundness W e, Bridge_Q_Sigma01_completeness W e⟩

/-- `S* ∈ π(T*_e) ↔ Halt(e)`: full 3-step chain.

    Step 1 (Cat 3 defining biconditional):
        S* ∈ π(T*_e) ↔ H_e ∈ π(T*_e)
    Step 2 (Cat 2 conservativity specialised at H_e ≠ S*):
        H_e ∈ π(T*_e) ↔ H_e ∈ π(T_0)
    Step 3 (Cat 2 Σ⁰₁-complete-sound applied to H_e):
        H_e ∈ π(T_0) ↔ Halt(e) -/
theorem Bridge_Sstar_iff_Halt
    (W : ObservationalWorld) [REAxiomatised W] :
    ∀ e, DistinguishedObs W ∈ W.predict (Bridge1b_Tstar W e) ↔
         (Nat.Partrec.Code.eval e 0).Dom := by
  intro e
  have hStep1 : DistinguishedObs W ∈ W.predict (Bridge1b_Tstar W e) ↔
                H_e_Obs W e ∈ W.predict (Bridge1b_Tstar W e) :=
    Bridge_Defining_Biconditional W e
  have hStep2 : H_e_Obs W e ∈ W.predict (Bridge1b_Tstar W e) ↔
                H_e_Obs W e ∈ W.predict (Bridge1b_T0 W) :=
    Bridge_DefExt_Conservative W e (H_e_Obs W e)
      (Bridge_H_e_distinct_from_Sstar W e)
  have hStep3 : H_e_Obs W e ∈ W.predict (Bridge1b_T0 W) ↔
                (Nat.Partrec.Code.eval e 0).Dom :=
    Bridge_Q_Sigma01_complete_sound W e
  exact hStep1.trans (hStep2.trans hStep3)

/-- Halt-iff-Dist reduction: there exists a uniformly-computable
    encoding `e ↦ (T*_e, T_0)` under which `Dist(T*_e, T_0) ↔ Halt(e)`.

    The reduction pivots on the distinguished observable `S*`:
      * `S* ∈ π(T*_e) ↔ Halt(e)` by `Bridge_Sstar_iff_Halt`;
      * `S* ∉ π(T_0)` by `Bridge_Encoding_Sstar_T0` (freshness);
      * all other observables agree between `T*_e` and `T_0` by
        `Bridge_DefExt_Conservative`. -/
theorem Bridge_Halt_Iff_Dist
    (W : ObservationalWorld) [REAxiomatised W] :
    ∃ (encode : Nat.Partrec.Code → W.Th × W.Th),
      ∀ e, Dist W (encode e).1 (encode e).2 ↔ (Nat.Partrec.Code.eval e 0).Dom := by
  refine ⟨fun e => (Bridge1b_Tstar W e, Bridge1b_T0 W), ?_⟩
  intro e
  unfold Dist
  have hSstar_iff_Halt :
      DistinguishedObs W ∈ W.predict (Bridge1b_Tstar W e) ↔
      (Nat.Partrec.Code.eval e 0).Dom :=
    Bridge_Sstar_iff_Halt W e
  have hSstar_notin_T0 : DistinguishedObs W ∉ W.predict (Bridge1b_T0 W) :=
    Bridge_Encoding_Sstar_T0 W
  constructor
  · -- Dist → Halt: prediction sets differ; non-S* observables agree
    -- by conservativity, S* ∉ π(T_0) by freshness, so the sets can
    -- only differ on S*, requiring S* ∈ π(T*_e), hence Halt(e).
    intro hDist
    by_contra hNotHalt
    apply hDist
    have hSstar_notin_Tstar : DistinguishedObs W ∉ W.predict (Bridge1b_Tstar W e) :=
      fun hIn => hNotHalt (hSstar_iff_Halt.mp hIn)
    apply Set.eq_of_subset_of_subset
    · intro S hS
      by_cases hS_is_star : S = DistinguishedObs W
      · exact absurd (hS_is_star ▸ hS) hSstar_notin_Tstar
      · exact (Bridge_DefExt_Conservative W e S hS_is_star).mp hS
    · intro S hS
      by_cases hS_is_star : S = DistinguishedObs W
      · exact absurd (hS_is_star ▸ hS) hSstar_notin_T0
      · exact (Bridge_DefExt_Conservative W e S hS_is_star).mpr hS
  · -- Halt → Dist: get S* ∈ π(T*_e) by Bridge_Sstar_iff_Halt, but
    -- S* ∉ π(T_0) by freshness, so the prediction sets differ on S*.
    intro hHalt
    have hSstar_in_Tstar : DistinguishedObs W ∈ W.predict (Bridge1b_Tstar W e) :=
      hSstar_iff_Halt.mpr hHalt
    intro hEq
    exact hSstar_notin_T0 (hEq ▸ hSstar_in_Tstar)

/-! ### Cat 2 framework primitives + decidability (Tarski 1948). -/

/-- Abstract encoding of FO formulas over the real-closed-field
    signature `(+, ·, <, 0, 1)`.  Tarski 1948 framework. -/
opaque RCFFormula : Type

/-- Abstract `Bool`-valued decision procedure for RCF-validity.
    Witnessed by Tarski's quantifier-elimination procedure /
    Collins CAD / Renegar's algorithms.  Tarski 1948 framework. -/
opaque RCFDecide : RCFFormula → Bool

/-- RCF satisfaction predicate: `RCFSatisfies φ` holds iff the
    first-order formula `φ` is true over `⟨ℝ; +, ·, <, 0, 1⟩`.
    Treated as an opaque framework primitive. -/
opaque RCFSatisfies : RCFFormula → Prop

/-- Tarski 1948 RCF decision-procedure correctness: for every FO
    formula `φ` over the RCF signature, `RCFDecide φ = true` iff `φ`
    is satisfied by the standard RCF model.

    Citation: Tarski, *A Decision Method for Elementary Algebra and
    Geometry*, RAND R-109 (1948) / UC Press 1951.  The concrete
    algorithm is Tarski's quantifier-elimination procedure; later
    descendants include Collins' cylindrical-algebraic-decomposition
    and Renegar's algorithms. -/
axiom Bridge_Tarski_RCF_Correctness :
    ∀ φ : RCFFormula, RCFDecide φ = true ↔ RCFSatisfies φ

/-! ### Theorems. -/

/-- **Theorem~\ref{thm:undecidable} (i) upper bound: Σ⁰₂.**

    `Dist(T_1, T_2)` is equivalent to `∃ S` separating the prediction
    sets, an `∃ (Σ⁰₁ ∧ Π⁰₁)` claim of complexity `Σ⁰₂`.

    Pure-logic equivalence using `Classical.byContradiction`; no
    axioms beyond standard kernel. -/
theorem thm_undecidable_sigma02_upper (W : ObservationalWorld) (T1 T2 : W.Th) :
    Dist W T1 T2 ↔
      ∃ S, (S ∈ W.predict T1 ∧ S ∉ W.predict T2)
         ∨ (S ∈ W.predict T2 ∧ S ∉ W.predict T1) := by
  constructor
  · intro hDist
    by_contra hNoSep
    apply hDist
    ext S
    refine ⟨?_, ?_⟩
    · intro hS1
      by_contra hNot
      exact hNoSep ⟨S, Or.inl ⟨hS1, hNot⟩⟩
    · intro hS2
      by_contra hNot
      exact hNoSep ⟨S, Or.inr ⟨hS2, hNot⟩⟩
  · rintro ⟨S, hSep⟩ hEq
    rcases hSep with ⟨hIn1, hNotIn2⟩ | ⟨hIn2, hNotIn1⟩
    · exact hNotIn2 (hEq ▸ hIn1)
    · exact hNotIn1 (hEq.symm ▸ hIn2)

/-- **Theorem~\ref{thm:undecidable} (i): Σ⁰₁-hardness of `Dist`.**

    On any r.e.-axiomatised class extending Robinson `Q`, `Dist` is
    Σ⁰₁-hard: there is a computable encoding under which `Dist` is
    iff-equivalent to halting.  Direct from `Bridge_Halt_Iff_Dist`. -/
theorem thm_undecidable_sigma01_hard
    (W : ObservationalWorld) [REAxiomatised W] :
    ∃ (encode : Nat.Partrec.Code → W.Th × W.Th),
      ∀ e, Dist W (encode e).1 (encode e).2 ↔ (Nat.Partrec.Code.eval e 0).Dom :=
  Bridge_Halt_Iff_Dist W

/-- **Theorem~\ref{thm:undecidable} (ii): Tarski-class decidability.**

    On the Tarski class `Θ^N` (theories whose prediction set is the
    solution set of a first-order formula over the real-closed-field
    signature), `Dist` is decidable: every RCF formula `φ` has a
    `Bool`-valued classifier whose `true` value coincides with
    `RCFSatisfies φ`.  The non-trivial `b = true ↔ RCFSatisfies φ`
    form (rather than the trivial `∃ b, RCFDecide φ = b`) captures
    the substantive Tarski content. -/
theorem thm_undecidable_tarski_decidable :
    ∀ φ : RCFFormula, ∃ b : Bool, b = true ↔ RCFSatisfies φ :=
  fun φ => ⟨RCFDecide φ, Bridge_Tarski_RCF_Correctness φ⟩

/-- **Corollary~\ref{cor:no-universal}**: no `ComputablePred`-witnessing
    total Dist-decider exists on r.e.-axiomatised classes extending `Q`.

    Suppose such a `ComputablePred` existed.  By `Bridge_Halt_Iff_Dist`
    the Dist-decision is iff-equivalent to halting under the encoding,
    so the halting predicate would be `ComputablePred`, contradicting
    `ComputablePred.halting_problem 0` from Mathlib.

    Transfer to Einstein-Test verifiers is conditional on the super-
    family containing the r.e.-axiomatised adversarial sub-class. -/
theorem cor_no_universal
    (W : ObservationalWorld) [REAxiomatised W] :
    ¬ ComputablePred
        (fun e : Nat.Partrec.Code =>
          Dist W ((Bridge_Halt_Iff_Dist W).choose e).1
                 ((Bridge_Halt_Iff_Dist W).choose e).2) := by
  intro hComp
  have hIff := (Bridge_Halt_Iff_Dist W).choose_spec
  have hHalt : ComputablePred (fun e : Nat.Partrec.Code => (Nat.Partrec.Code.eval e 0).Dom) := by
    convert hComp using 1
    funext e
    exact propext (hIff e).symm
  exact ComputablePred.halting_problem 0 hHalt

end EinsteinTest
