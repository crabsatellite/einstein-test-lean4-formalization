/-
  EinsteinTest/Ledger.lean

  Gap ledger.  Every atomic axiom, every Cat 3 carrier, every blocked
  route, and every closed top-level result is recorded as a typed
  `GapEntry` with TWO orthogonal classifications:

    * 5-tier status:   gapOpen / gapPartial / gapBlocked / gapDeadEnd / gapClosed
    * 3-input-category: cat1Mathlib / cat2External / cat3PaperNovel / notInput

  Pre-attack discipline.  Scan this ledger before launching new
  attacks.  Re-attempting a `gapBlocked` or `gapDeadEnd` route is a
  context-drift failure mode.

  `attackHistory` is the canonical location for round metadata
  (citation revisions, atomic refactors, prior retractions); docstrings
  and scope fields are kept to current-state content only.
-/

import EinsteinTest

namespace EinsteinTest.Ledger

/-- 5-tier status tag attached to each gap. -/
inductive GapStatus
  | gapOpen
  | gapPartial
  | gapBlocked
  | gapDeadEnd
  | gapClosed
  deriving DecidableEq, Repr

/-- 3-input-category tag attached to each gap.  Orthogonal to status. -/
inductive InputCategory
  /-- Mathlib-derivable theorem (no axiom).  Project has zero such. -/
  | cat1Mathlib
  /-- External published; opaque-carrier-bound axiom + citation. -/
  | cat2External
  /-- Paper-novel: carrier or paper-stated atomic defining equation. -/
  | cat3PaperNovel
  /-- Not an atomic input: derived theorem (gapClosed) or blocked
      Mathlib-derivation route (gapBlocked). -/
  | notInput
  deriving DecidableEq, Repr

/-- Typed record for a single gap. -/
structure GapEntry where
  /-- Identifier matching the underlying axiom / theorem name. -/
  name : String
  /-- 5-tier status (orthogonal to inputCategory). -/
  status : GapStatus
  /-- Input category (orthogonal to status). -/
  inputCategory : InputCategory
  /-- Operative paper / obstacle citation. -/
  paperSource : String
  /-- Per-round attack trace (canonical location for round metadata). -/
  attackHistory : List String
  /-- What content the entry carries; what it does NOT claim. -/
  scope : String

/-! ### Cat 2 atomic KC bridges (Li-Vitányi 3rd ed. 2008 + Vitányi 2013 TCS 501) -/

/-- Conditional coding theorem (universal additive constant). -/
def gap_K_codingTheorem : GapEntry := {
  name := "K_codingTheorem"
  status := GapStatus.gapOpen
  inputCategory := InputCategory.cat2External
  paperSource :=
    "Li-Vitányi 3rd ed. (2008) Thm 4.3.4 (conditional coding theorem); " ++
    "Vitányi, *TCS* 501 (2013), 93–100 (arXiv:1206.0983), Theorem 4 " ++
    "under Definition 1 (lower-semicomputable conditional semi-measure " ++
    "with Σ_x m(x|y) ≤ 1 + multiplicative universality), for the " ++
    "explicit conditional-version proof"
  attackHistory := [
    "v0.6 (2026-05-12): Vitányi 2013 supplementary citation added; " ++
      "Thm 4.3.4 conditional version was non-standard prior to 2013",
    "v0.6.1: H3 patch — docstring committed to Vitányi Definition 1 " ++
      "convention (classical quotient m(x,y)/Σ_z m(z,y) FAILS the " ++
      "conditional coding theorem, Vitányi 2013 Thm 2)"
  ]
  scope :=
    "Universal additive constant `c` for the upper bound " ++
    "`K(x|μDesc) ≤ k + c` when μDesc encodes a Vitányi-Definition-1 " ++
    "conditional lower-semicomputable semi-measure and " ++
    "m(x|y) ≥ 2^(-k); upper bound only"
}

/-- Symmetric-information chain rule, pair-LHS form. -/
def gap_K_chainRule_pair : GapEntry := {
  name := "K_chainRule_pair"
  status := GapStatus.gapOpen
  inputCategory := InputCategory.cat2External
  paperSource :=
    "Li-Vitányi 3rd ed. (2008) Thm 3.9.1 (symmetric-information chain " ++
    "rule, prefix-complexity version); plain-complexity analogue: " ++
    "Li-Vitányi 3rd ed. Eq. (3.21)"
  attackHistory := [
    "v0.5: pair-LHS form only; single-LHS form derived via " ++
      "K_pairNonDecrease (no composite axiom)"
  ]
  scope :=
    "Slack function `slack : ℝ → ℝ` (O(log L) overhead) such that " ++
    "`K((x,y)|z) ≤ K(x|y,z) + K(y|z) + slack L`; pair-LHS only; " ++
    "single-LHS form is the derived lemma `K_chainRule_single_apply`"
}

/-- Information non-decrease under pairing. -/
def gap_K_pairNonDecrease : GapEntry := {
  name := "K_pairNonDecrease"
  status := GapStatus.gapOpen
  inputCategory := InputCategory.cat2External
  paperSource :=
    "Li-Vitányi 3rd ed. (2008) §3.1 (immediate from prefix-free " ++
    "pair-decoding: K(x|z) ≤ K(⟨x,y⟩|z) + c)"
  attackHistory := [
    "v0.5: split out of bundled chain rule so single-LHS variant " ++
      "becomes a derived lemma",
    "v0.6: F5 patch — cite by §3.1 only (any prior 'Thm 2.2.1' " ++
      "label could not be verified)"
  ]
  scope :=
    "Additive constant `c` such that `K(x|z) ≤ K(encodePair x y | z) + c`"
}

/-- Conditioning monotonicity (prefix-`K`). -/
def gap_K_condMonotone : GapEntry := {
  name := "K_condMonotone"
  status := GapStatus.gapOpen
  inputCategory := InputCategory.cat2External
  paperSource :=
    "Li-Vitányi 3rd ed. (2008) §3.1 / §3.4 (prefix-`K` analogue of " ++
    "plain-`C` Ch 2 result; extra conditioning cannot raise prefix " ++
    "complexity by more than a constant; immediate by relativizing " ++
    "the universal prefix machine)"
  attackHistory := [
    "v0.6: F4 patch — Thm 2.1.8 is for plain `C` (Ch 2); Lean axiom " ++
      "is stated for prefix `K`, so cite §3.1/§3.4 (prefix-K analogue)"
  ]
  scope :=
    "Additive constant `c` such that `K(x|y,z) ≤ K(x|y) + c` (prefix `K`)"
}

/-- Description-length bound. -/
def gap_K_descLength : GapEntry := {
  name := "K_descLength"
  status := GapStatus.gapOpen
  inputCategory := InputCategory.cat2External
  paperSource :=
    "Li-Vitányi 3rd ed. (2008) §2.1 (immediate consequence of the " ++
    "Invariance Theorem Thm 2.1.1 via the literal-output universal " ++
    "program)"
  attackHistory := [
    "v0.5: hedged — cite §2.1 (immediate consequence of Thm 2.1.1) " ++
      "instead of Thm 2.1.1 directly",
    "v0.6: F6 patch — self-delimiting hypothesis made explicit in " ++
      "docstring (without prefix-coding the textbook bound carries " ++
      "an extra 2log|y| term)"
  ]
  scope :=
    "Additive constant `c` such that `K(y|z) ≤ descLen y + c` where " ++
    "`descLen y` includes the self-delimiting overhead"
}

/-! ### Cat 3 atomic carriers (paper-novel primitives) -/

/-- Distinguished observable `S*`. -/
def gap_DistinguishedObs_carrier : GapEntry := {
  name := "DistinguishedObs"
  status := GapStatus.gapOpen
  inputCategory := InputCategory.cat3PaperNovel
  paperSource :=
    "Li 2026, `\\label{thm:undecidable}` construction: fresh 0-ary " ++
    "predicate `S*` added to T_0 = Q in the adversarial extension"
  attackHistory := []
  scope :=
    "Typed primitive `DistinguishedObs W : W.Obs`.  Freshness " ++
    "(S* ∉ π(T_0)) is recorded in the separate atomic axiom " ++
    "`Bridge_Encoding_Sstar_T0`"
}

/-- Paper's halting sentence `H_e` as an L_0-observable. -/
def gap_H_e_Obs_carrier : GapEntry := {
  name := "H_e_Obs"
  status := GapStatus.gapOpen
  inputCategory := InputCategory.cat3PaperNovel
  paperSource :=
    "Li 2026, `\\label{thm:undecidable}` construction: paper-stated " ++
    "`H_e := ∃t. T(e, 0, t)` (Kleene's T-predicate Σ⁰₁ sentence " ++
    "asserting machine `e` halts on input 0)"
  attackHistory := []
  scope :=
    "Typed primitive `H_e_Obs W : Code → W.Obs` encoding the paper's " ++
    "L_0-sentence H_e on the right-hand side of the defining " ++
    "biconditional `S* ↔ H_e`.  Consumed by Bridge_Defining_Biconditional " ++
    "(Step 1), Bridge_DefExt_Conservative specialised at H_e (Step 2), " ++
    "and Bridge_Q_Sigma01_complete/sound (Step 3)"
}

/-- Abstract Robinson Q. -/
def gap_Bridge1b_T0_carrier : GapEntry := {
  name := "Bridge1b_T0"
  status := GapStatus.gapOpen
  inputCategory := InputCategory.cat3PaperNovel
  paperSource :=
    "Li 2026, `\\label{thm:undecidable}` construction: abstract " ++
    "realisation of Robinson's Q as the base theory T_0"
  attackHistory := []
  scope :=
    "Typed primitive `Bridge1b_T0 W : W.Th`"
}

/-- Abstract extension family `T*_e`. -/
def gap_Bridge1b_Tstar_carrier : GapEntry := {
  name := "Bridge1b_Tstar"
  status := GapStatus.gapOpen
  inputCategory := InputCategory.cat3PaperNovel
  paperSource :=
    "Li 2026, `\\label{thm:undecidable}` construction: abstract " ++
    "realisation of T*_e := Q ∪ {S* ↔ H_e} indexed by Code"
  attackHistory := []
  scope :=
    "Typed primitive `Bridge1b_Tstar W : Code → W.Th`"
}

/-! ### Cat 3 atomic defining equations (paper-stated) -/

/-- (iii) `S*` is fresh in `T_0`. -/
def gap_Bridge_Encoding_Sstar_T0 : GapEntry := {
  name := "Bridge_Encoding_Sstar_T0"
  status := GapStatus.gapOpen
  inputCategory := InputCategory.cat3PaperNovel
  paperSource :=
    "Li 2026, `\\label{thm:undecidable}` proof: 'since S* does not " ++
    "occur in T_0's axioms, T_0 ⊬ S*, so S* ∉ π(T_0)'"
  attackHistory := []
  scope :=
    "`DistinguishedObs W ∉ W.predict (Bridge1b_T0 W)` — paper-novel " ++
    "freshness (clause iii)"
}

/-- (iii') `H_e ≠ S*`. -/
def gap_Bridge_H_e_distinct_from_Sstar : GapEntry := {
  name := "Bridge_H_e_distinct_from_Sstar"
  status := GapStatus.gapOpen
  inputCategory := InputCategory.cat3PaperNovel
  paperSource :=
    "Li 2026, `\\label{thm:undecidable}` proof: 'Obs := {closed " ++
    "sentences in L_0} ∪ {S*} ... S* not occurring in the language " ++
    "of Q'.  H_e is an L_0-sentence, hence H_e ≠ S*"
  attackHistory := []
  scope :=
    "`∀ e, H_e_Obs W e ≠ DistinguishedObs W`.  Side-condition needed " ++
    "to specialise `Bridge_DefExt_Conservative` (universally " ++
    "quantified over S ≠ DistinguishedObs W) at the observable H_e_Obs e"
}

/-- (iv) Defining biconditional Step 1: `T*_e ⊢ S* ↔ T*_e ⊢ H_e`. -/
def gap_Bridge_Defining_Biconditional : GapEntry := {
  name := "Bridge_Defining_Biconditional"
  status := GapStatus.gapOpen
  inputCategory := InputCategory.cat3PaperNovel
  paperSource :=
    "Li 2026, `\\label{thm:undecidable}` proof: 'In T*_e, the axiom " ++
    "S* ↔ H_e gives T*_e ⊢ S* iff T*_e ⊢ H_e' — paper-novel Step 1 " ++
    "atomic claim (modus ponens on the defining axiom)"
  attackHistory := []
  scope :=
    "`∀ e, S* ∈ π(T*_e) ↔ H_e_Obs e ∈ π(T*_e)`.  Step 1 only; the " ++
    "textbook conservativity link (T*_e ⊢ H_e ↔ Q ⊢ H_e, Step 2) " ++
    "is derived from Bridge_DefExt_Conservative at H_e using " ++
    "Bridge_H_e_distinct_from_Sstar"
}

/-! ### Cat 2 atomic textbook axioms (recursion-theoretic + Tarski) -/

/-- Σ⁰₁-completeness of `Q` applied to `H_e`. -/
def gap_Bridge_Q_Sigma01_completeness : GapEntry := {
  name := "Bridge_Q_Sigma01_completeness"
  status := GapStatus.gapOpen
  inputCategory := InputCategory.cat2External
  paperSource :=
    "Smith, *An Introduction to Gödel's Theorems*, 2nd ed., " ++
    "Cambridge UP 2013, Ch 11 'What Q can prove', §'Q is Σ₁-complete' " ++
    "(PRIMARY; chapter title + section locator verified by direct CUP " ++
    "frontmatter match, in-chapter theorem number unverified so cited " ++
    "at section level only); Hájek-Pudlák, *Metamathematics of " ++
    "First-Order Arithmetic*, Springer 1998, Preliminaries §(c) " ++
    "pp. 20-26 (SECONDARY, foundational preliminaries-level fact)"
  attackHistory := [
    "v0.6: F1 FATAL — BBJ §16.4 → Hájek-Pudlák 1998 Ch I (primary) " ++
      "+ Smith 2013 Ch 11 (secondary); BBJ §16.4 is an optional " ++
      "appendix and BBJ uses 'Q' for minimal arithmetic (distinct " ++
      "from standard Robinson Q)",
    "v0.6.1: H1 FATAL — HP Ch I §1.4 was MISCITED (HP uses two-level " ++
      "numbering; §1.4 does not exist).  PRIMARY/SECONDARY reversed: " ++
      "Smith 2013 Ch 11 PRIMARY; HP Preliminaries §(c) SECONDARY"
  ]
  scope :=
    "`∀ e, Halt(e) → H_e_Obs W e ∈ W.predict (Bridge1b_T0 W)`.  " ++
    "Halt(e) implies Q proves H_e, applied to the abstract carrier"
}

/-- Σ⁰₁-soundness of `Q` applied to `H_e`. -/
def gap_Bridge_Q_Sigma01_soundness : GapEntry := {
  name := "Bridge_Q_Sigma01_soundness"
  status := GapStatus.gapOpen
  inputCategory := InputCategory.cat2External
  paperSource :=
    "Tarski-Mostowski-Robinson, *Undecidable Theories*, North-Holland " ++
    "1953, Ch II (Q's axiomatization) + Smith 2013 §10.1-10.2 " ++
    "(axiom-by-axiom verification of N ⊨ Q).  Σ⁰₁-soundness follows " ++
    "as a one-line corollary of N ⊨ Q combined with soundness of FO " ++
    "derivation — folklore preliminaries fact, not numbered theorem"
  attackHistory := [
    "v0.6: F2 FATAL — Rogers Ch XII → TMR 1953 Ch II + Smith 2013 " ++
      "§10.1-10.2; Rogers Ch XII is RE/reducibilities territory",
    "v0.6.1: H2 hedge — TMR 1953 does not contain a numbered 'N ⊨ Q' " ++
      "theorem; Smith 2013 §10.1-10.2 added as supplementary for the " ++
      "axiom-by-axiom verification"
  ]
  scope :=
    "`∀ e, H_e_Obs W e ∈ W.predict (Bridge1b_T0 W) → Halt(e)`.  " ++
    "Strictly atomic split (`N_models_Q` + `Sigma01_soundness_of_-" ++
    "FO_derivation`) deferred to Mathlib FO formalisation; see " ++
    "`gap_FOTheory_encoding_BLOCKED`"
}

/-- Conservativity of definitional extension outside `S*`. -/
def gap_Bridge_DefExt_Conservative : GapEntry := {
  name := "Bridge_DefExt_Conservative"
  status := GapStatus.gapOpen
  inputCategory := InputCategory.cat2External
  paperSource :=
    "Shoenfield, *Mathematical Logic*, Addison-Wesley 1967, §4.6 " ++
    "'Extensions by definitions' (p. 57f) — PRIMARY (theorem-numbered); " ++
    "Hodges, *A Shorter Model Theory*, Cambridge UP 1997, §2.6 " ++
    "(SECONDARY, section-level)"
  attackHistory := []
  scope :=
    "`∀ e S, S ≠ DistinguishedObs W → " ++
    "(S ∈ W.predict (Bridge1b_Tstar W e) ↔ S ∈ W.predict (Bridge1b_T0 W))`.  " ++
    "Conservativity of T*_e over T_0 outside the fresh symbol S*"
}

/-- Tarski 1948 RCF decision-procedure correctness. -/
def gap_Bridge_Tarski_RCF_Correctness : GapEntry := {
  name := "Bridge_Tarski_RCF_Correctness"
  status := GapStatus.gapOpen
  inputCategory := InputCategory.cat2External
  paperSource :=
    "Tarski, *A Decision Method for Elementary Algebra and Geometry*, " ++
    "RAND R-109, 1948 / UC Press 1951; quantifier-elimination " ++
    "procedure for the FO theory of real-closed fields"
  attackHistory := [
    "v0.3: strengthened from trivial `∃ b, RCFDecide φ = b` to " ++
      "substantive `∃ b : Bool, b = true ↔ RCFSatisfies φ` (captures " ++
      "Tarski content, not just Bool-typing)"
  ]
  scope :=
    "`∀ φ : RCFFormula, RCFDecide φ = true ↔ RCFSatisfies φ`.  " ++
    "Stipulates correctness of a Tarski-style quantifier-elimination " ++
    "procedure as an opaque framework primitive"
}

/-! ### gapBlocked entries — Mathlib derivations deferred -/

/-- Full Mathlib derivation of Kolmogorov complexity `K`. -/
def gap_K_Mathlib_full_derivation_BLOCKED : GapEntry := {
  name := "K_Mathlib_full_derivation"
  status := GapStatus.gapBlocked
  inputCategory := InputCategory.notInput
  paperSource :=
    "Mathlib has no `Mathlib.InformationTheory.Kolmogorov` module; " ++
    "building one (universal prefix Turing machine + invariance " ++
    "theorem + conditional coding theorem) is a substantial " ++
    "separate project"
  attackHistory := []
  scope :=
    "Full Lean proofs of the 5 KC bridges as theorems against a " ++
    "concrete prefix-machine framework.  Deferred; the bridges " ++
    "remain Cat 2 atomic external-published axioms"
}

/-- Full FO theory encoding via `Mathlib.ModelTheory`. -/
def gap_FOTheory_encoding_BLOCKED : GapEntry := {
  name := "FOTheory_encoding_Mathlib"
  status := GapStatus.gapBlocked
  inputCategory := InputCategory.notInput
  paperSource :=
    "Mathlib.ModelTheory does not yet contain a formalisation of " ++
    "Robinson's Q with its Σ⁰₁-completeness theorem, or the framework " ++
    "for r.e.-axiomatised FO theories with conservativity of " ++
    "definitional extension"
  attackHistory := []
  scope :=
    "Full FO-encoding of T*_e := Q ∪ {S* ↔ H_e} as a Mathlib " ++
    "FirstOrder.Language theory, with Σ⁰₁-completeness of Q, " ++
    "soundness of FO derivation, conservativity of def-ext, and " ++
    "Beth definability proved inside Mathlib.  Deferred; the three " ++
    "atomic textbook bridges remain Cat 2 axioms"
}

/-- Full Tarski CAD algorithm in Lean. -/
def gap_Tarski_CAD_Mathlib_BLOCKED : GapEntry := {
  name := "Tarski_CAD_Mathlib"
  status := GapStatus.gapBlocked
  inputCategory := InputCategory.notInput
  paperSource :=
    "Mathlib does not contain a constructive Tarski / Collins " ++
    "quantifier-elimination procedure for the FO theory of real- " ++
    "closed fields with a machine-checked correctness proof.  See " ++
    "Basu-Pollack-Roy 2006 for the algorithmic content"
  attackHistory := []
  scope :=
    "Full constructive Tarski CAD inside Lean with machine-checked " ++
    "correctness against standard RCF semantics.  Deferred; " ++
    "`Bridge_Tarski_RCF_Correctness` remains a Cat 2 atomic axiom"
}

/-! ### gapClosed entries — top-level theorems proven without `sorry` -/

/-- Theorem 1: empirical-verification wall-clock floor. -/
def gap_thm_floor_CLOSED : GapEntry := {
  name := "thm_floor"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{thm:floor}`"
  attackHistory := []
  scope :=
    "Empirical-verification protocol Π requires wall-clock " ++
    "`B_Π ≥ τmin = inf {τ_t(S) : S ∈ (π(T*) \\ π(T_0)) ∩ Tech_t}`; " ++
    "generator-independent.  Proof uses Verifier.sound_c and (E1) " ++
    "directly; standard kernel only"
}

/-- Theorem 2: generator KC emission lower bound. -/
def gap_thm_emission_CLOSED : GapEntry := {
  name := "thm_emission"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{thm:emission}`"
  attackHistory := []
  scope :=
    "`K(T*|D_t) ≤ k + |M| + |p| + slack constants`, where " ++
    "`k = -log Pr[M(p)=T*]`; depends on the Cat 2 atomic KC bridges; " ++
    "proof is a linear chain via `linarith` over the bridge inequalities"
}

/-- Corollary: geometric waiting-time `2^K_* ≤ 1/p`. -/
def gap_cor_rare_CLOSED : GapEntry := {
  name := "cor_rare"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{cor:rare}`"
  attackHistory := []
  scope :=
    "For `p ≤ 2^(-K_*)` with `K_* > 0`, `E[N] = 1/p ≥ 2^(K_*)`; " ++
    "pure real-arithmetic, no atomic axioms"
}

/-- Remark: vacuous when `K_* ≤ 0`. -/
def gap_rem_emission_not_impossible_CLOSED : GapEntry := {
  name := "rem_emission_not_impossible"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{rem:emission-not-impossible}`"
  attackHistory := []
  scope :=
    "Three escape routes push `K_* ≤ 0`, making the cor_rare " ++
    "bound vacuous"
}

/-- Theorem 3(i): Σ⁰₁-hardness of `Dist`. -/
def gap_thm_undecidable_sigma01_hard_CLOSED : GapEntry := {
  name := "thm_undecidable_sigma01_hard"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{thm:undecidable}` clause (i)"
  attackHistory := []
  scope :=
    "Existence of a computable encoding `e ↦ (T*_e, T_0)` under " ++
    "which `Dist(T*_e, T_0) ↔ Halt(e)`.  Depends on the Cat 3 " ++
    "carriers, Cat 3 paper-stated defining equations, and Cat 2 " ++
    "recursion-theoretic textbook atomics via the derived theorem " ++
    "`Bridge_Halt_Iff_Dist`"
}

/-- Theorem 3(i) Σ⁰₂-upper bound: pure logic. -/
def gap_thm_undecidable_sigma02_upper_CLOSED : GapEntry := {
  name := "thm_undecidable_sigma02_upper"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{thm:undecidable}` clause (i) upper bound"
  attackHistory := []
  scope :=
    "`Dist(T_1, T_2) ↔ ∃ S` separating observation; pure-logic " ++
    "equivalence, no axioms beyond standard kernel + " ++
    "Classical.byContradiction"
}

/-- Theorem 3(ii): Tarski-class decidability. -/
def gap_thm_undecidable_tarski_decidable_CLOSED : GapEntry := {
  name := "thm_undecidable_tarski_decidable"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{thm:undecidable}` clause (ii)"
  attackHistory := [
    "v0.3: strengthened from trivial `∃ b, RCFDecide φ = b` to " ++
      "substantive `∃ b : Bool, b = true ↔ RCFSatisfies φ`"
  ]
  scope :=
    "For every RCFFormula φ, `∃ Bool-valued classifier b` with " ++
    "`b = true ↔ RCFSatisfies φ`; depends on " ++
    "`Bridge_Tarski_RCF_Correctness` only"
}

/-- Corollary: no `ComputablePred` witness for the Dist-decider. -/
def gap_cor_no_universal_CLOSED : GapEntry := {
  name := "cor_no_universal"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{cor:no-universal}`"
  attackHistory := []
  scope :=
    "Structural negation: no `ComputablePred` for " ++
    "`e ↦ Dist(enc(e).1, enc(e).2)` where `enc` is the Bridge_Halt_-" ++
    "Iff_Dist reduction; contradicts Mathlib's " ++
    "`ComputablePred.halting_problem 0`"
}

/-- Theorem 5: self-verification impossibility. -/
def gap_thm_self_verification_CLOSED : GapEntry := {
  name := "thm_self_verification"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{thm:self-verification}`"
  attackHistory := []
  scope :=
    "For any D ⊆ D_t consistent with T_0, no sound verifier V_M can " ++
    "return 1 on (p, T*, T_0, D) for an Einstein-replacement T*; " ++
    "robust to universal-compressor, true-arithmetic, halting-oracle, " ++
    "and any-reasoner enhancements"
}

/-- Corollary: empirical access is structurally necessary. -/
def gap_cor_empirical_necessity_CLOSED : GapEntry := {
  name := "cor_empirical_necessity"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{cor:empirical-necessity}`"
  attackHistory := []
  scope :=
    "A system (M, V_M) with no empirical protocol Π cannot pass the " ++
    "Einstein Test on any Einstein-replacement T*"
}

/-- Theorem 4: three-component cost decomposition. -/
def gap_thm_decomposition_CLOSED : GapEntry := {
  name := "thm_decomposition"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{thm:decomposition}`"
  attackHistory := []
  scope :=
    "`C_Einstein = B_M + B_V + B_Π` with structurally distinct " ++
    "floors (emission KC bound, computational class-dependent " ++
    "obstruction, empirical wall-clock floor)"
}

/-- Corollary: conditional feasibility. -/
def gap_cor_conditional_feasibility_CLOSED : GapEntry := {
  name := "cor_conditional_feasibility"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{cor:conditional-feasibility}`"
  attackHistory := []
  scope :=
    "(F1) ∧ (F2) ∧ (F3) sufficient for Einstein-Test feasibility " ++
    "within finite budget"
}

/-- Corollary: bound interaction. -/
def gap_cor_bound_interaction_CLOSED : GapEntry := {
  name := "cor_bound_interaction"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{cor:bound-interaction}`"
  attackHistory := []
  scope :=
    "AI-side interventions can lower (a) + (b) but not (c); " ++
    "τmin is uncoupled from any AI-side intervention"
}

/-! ### Aggregated ledger inventory -/

/-- All gap entries in canonical order. -/
def allGaps : List GapEntry := [
  -- Cat 2 atomic KC bridges
  gap_K_codingTheorem,
  gap_K_chainRule_pair,
  gap_K_pairNonDecrease,
  gap_K_condMonotone,
  gap_K_descLength,
  -- Cat 3 atomic carriers
  gap_DistinguishedObs_carrier,
  gap_H_e_Obs_carrier,
  gap_Bridge1b_T0_carrier,
  gap_Bridge1b_Tstar_carrier,
  -- Cat 3 atomic defining equations
  gap_Bridge_Encoding_Sstar_T0,
  gap_Bridge_H_e_distinct_from_Sstar,
  gap_Bridge_Defining_Biconditional,
  -- Cat 2 atomic textbook axioms (recursion-theoretic + Tarski)
  gap_Bridge_Q_Sigma01_completeness,
  gap_Bridge_Q_Sigma01_soundness,
  gap_Bridge_DefExt_Conservative,
  gap_Bridge_Tarski_RCF_Correctness,
  -- gapBlocked
  gap_K_Mathlib_full_derivation_BLOCKED,
  gap_FOTheory_encoding_BLOCKED,
  gap_Tarski_CAD_Mathlib_BLOCKED,
  -- gapClosed top-level results
  gap_thm_floor_CLOSED,
  gap_thm_emission_CLOSED,
  gap_cor_rare_CLOSED,
  gap_rem_emission_not_impossible_CLOSED,
  gap_thm_undecidable_sigma01_hard_CLOSED,
  gap_thm_undecidable_sigma02_upper_CLOSED,
  gap_thm_undecidable_tarski_decidable_CLOSED,
  gap_cor_no_universal_CLOSED,
  gap_thm_self_verification_CLOSED,
  gap_cor_empirical_necessity_CLOSED,
  gap_thm_decomposition_CLOSED,
  gap_cor_conditional_feasibility_CLOSED,
  gap_cor_bound_interaction_CLOSED
]

/-- Status-keyed counts: `(open, partial, blocked, deadEnd, closed)`. -/
def gapCounts : Nat × Nat × Nat × Nat × Nat :=
  let countWhere (s : GapStatus) : Nat :=
    (allGaps.filter (fun g => g.status = s)).length
  ( countWhere GapStatus.gapOpen
  , countWhere GapStatus.gapPartial
  , countWhere GapStatus.gapBlocked
  , countWhere GapStatus.gapDeadEnd
  , countWhere GapStatus.gapClosed )

/-- InputCategory-keyed counts: `(cat1Mathlib, cat2External, cat3PaperNovel, notInput)`. -/
def inputCategoryCounts : Nat × Nat × Nat × Nat :=
  let countWhere (c : InputCategory) : Nat :=
    (allGaps.filter (fun g => g.inputCategory = c)).length
  ( countWhere InputCategory.cat1Mathlib
  , countWhere InputCategory.cat2External
  , countWhere InputCategory.cat3PaperNovel
  , countWhere InputCategory.notInput )

#eval s!"EinsteinTest gap-ledger inventory (status):  open={(gapCounts).1} partial={(gapCounts).2.1} blocked={(gapCounts).2.2.1} deadEnd={(gapCounts).2.2.2.1} closed={(gapCounts).2.2.2.2}"

#eval s!"EinsteinTest gap-ledger inventory (input):   cat1Mathlib={(inputCategoryCounts).1} cat2External={(inputCategoryCounts).2.1} cat3PaperNovel={(inputCategoryCounts).2.2.1} notInput={(inputCategoryCounts).2.2.2}"

#eval s!"Total entries: {allGaps.length}"

/-! ### Inventory summary

  The live status counts and input-category counts are printed by the
  `#eval` calls above (run `lake env lean EinsteinTest/Ledger.lean` to
  see them).  The axiom names by category:

    Cat 2 propositional (external published textbook):
      K_codingTheorem, K_chainRule_pair, K_pairNonDecrease,
      K_condMonotone, K_descLength, Bridge_Tarski_RCF_Correctness,
      Bridge_Q_Sigma01_completeness, Bridge_Q_Sigma01_soundness,
      Bridge_DefExt_Conservative

    Cat 3 propositional defining equations (paper-stated atomic):
      Bridge_Encoding_Sstar_T0, Bridge_H_e_distinct_from_Sstar,
      Bridge_Defining_Biconditional

    Cat 3 carrier axioms (paper-novel typed primitives):
      DistinguishedObs, H_e_Obs, Bridge1b_T0, Bridge1b_Tstar

  Lean kernel (not declared here): propext, Classical.choice, Quot.sound.
-/

end EinsteinTest.Ledger
