/-
  EinsteinTest/Ledger.lean

  Gap ledger.  Every atomic axiom and every closed top-level result is
  recorded as a typed `GapEntry` with three orthogonal classifications
  plus a broken-link dependency list:

    * 6-tier status:    gapOpen / gapPartial / gapBlocked / gapDeadEnd /
                        gapClosed / gapClosedConditional
    * 4-input-category: cat1Mathlib / cat2External / cat3PaperNovel / notInput
    * Cat 3 sub-type:   carrier / hypothesisPredicate / structuralEquation /
                        workingAssumption / conditionalHypothesis / notCat3
    * conditionalOn :   list of `Hyp_*` broken-link predicate names
                        (non-empty iff status is `gapClosedConditional`;
                        see v6 §12)

  Pre-attack discipline.  Scan this ledger before launching new
  attacks.  Re-attempting a `gapBlocked` or `gapDeadEnd` route is a
  context-drift failure mode.

  `attackHistory` is the canonical location for round metadata
  (citation revisions, atomic refactors, prior retractions, Cat 3
  reductionism check outcomes); docstrings and scope fields are kept
  to current-state content only.

  Note on Mathlib gaps.  Per the v6 ATOMIC MINIMAL UNITS spec, "Mathlib
  infra absence ALONE is NOT BLOCKED" — if a paper's conclusion is
  published externally, encode as a plain Cat 2 axiom + paper-citation
  docstring (status `gapOpen`).  The `gapBlocked` tier is reserved for
  genuine no-acceptance-possible cases (folkloric with no specific
  paper, externally-conjectured-unproven, or no source at all).  This
  ledger therefore has zero `gapBlocked` entries: K-complexity,
  Robinson-Q FO encoding, and Tarski CAD are all covered by external
  textbook Cat 2 axioms with `gapOpen` status.
-/

import EinsteinTest

namespace EinsteinTest.Ledger

/-- 6-tier status tag attached to each gap.  `gapClosedConditional`
    is used when Phase 4 catches a defect breaking a typed-bridge
    chain: the downstream closure is preserved as conditional on a
    named `Hyp_*` broken-link hypothesis (recorded in the entry's
    `conditionalOn` field) pending repair or independent derivation.
    See `feedback_gap_ledger_in_lean4` §12. -/
inductive GapStatus
  | gapOpen
  | gapPartial
  | gapBlocked
  | gapDeadEnd
  | gapClosed
  | gapClosedConditional
  deriving DecidableEq, Repr

/-- 4-input-category tag attached to each gap.  Orthogonal to status.
    (Cat 0 = Lean kernel axioms — `propext` / `Classical.choice` /
    `Quot.sound` — is the always-present system layer and is not
    tracked here per v6 §3.1.) -/
inductive InputCategory
  /-- Mathlib-derivable theorem (no axiom).  Project has zero such. -/
  | cat1Mathlib
  /-- External published; opaque-carrier-bound axiom + citation. -/
  | cat2External
  /-- Paper-novel: carrier, hypothesis predicate, structural defining
      equation, working assumption, or conditional hypothesis.
      Refine via the `cat3SubType` field. -/
  | cat3PaperNovel
  /-- Not an atomic input: derived theorem (gapClosed) or genuine
      no-acceptance-possible route (gapBlocked / gapDeadEnd). -/
  | notInput
  deriving DecidableEq, Repr

/-- Cat 3 paper-novel sub-types per v6 §3.4.  Orthogonal to status and
    input-category; only meaningful when `inputCategory = cat3PaperNovel`. -/
inductive Cat3SubType
  /-- Paper-introduced primitive type or typed-primitive value
      (e.g., paper 5-tuple carriers).  Definitional atom; 永不 close. -/
  | carrier
  /-- Paper-introduced scope/regime predicate (e.g., `Conditions_C1_C2_C3`,
      `IsBlackwellOrdered`).  Definitional atom; 永不 close. -/
  | hypothesisPredicate
  /-- Paper-stated definitional equation on its primitives (e.g., paper
      Def 2.6 `V_dyn(v|H,ω) = max{r(w) : w ∈ R(v|H,ω)}`).  Definitional
      atom; 永不 close — these constitute the paper's commitments to
      how its primitives behave. -/
  | structuralEquation
  /-- Higher-level claim temporarily axiomatized while derivation is
      developed.  必须 close before paper submission. -/
  | workingAssumption
  /-- Paper's conclusion conditional on an external open problem (RH,
      BSD, Hodge, P≠NP).  永不 close; encoded as theorem-signature
      antecedent `theorem T (hRH : RiemannHypothesis) : ...`, NOT as
      an axiom.  Listed here only for completeness; project has none. -/
  | conditionalHypothesis
  /-- This entry is not Cat 3 paper-novel. -/
  | notCat3
  deriving DecidableEq, Repr

/-- Typed record for a single gap. -/
structure GapEntry where
  /-- Identifier matching the underlying axiom / theorem name. -/
  name : String
  /-- 6-tier status. -/
  status : GapStatus
  /-- Input category (orthogonal to status). -/
  inputCategory : InputCategory
  /-- Cat 3 sub-type (orthogonal; `notCat3` unless `inputCategory =
      cat3PaperNovel`). -/
  cat3SubType : Cat3SubType
  /-- Operative paper / obstacle citation. -/
  paperSource : String
  /-- Per-round attack trace (canonical location for round metadata).
      For Cat 3 entries, MUST include ≥2 reductionism check outcomes
      (Cat 1? Cat 2?) per v6 §5. -/
  attackHistory : List String
  /-- What content the entry carries; what it does NOT claim. -/
  scope : String
  /-- Names of `Hyp_*` broken-link predicates this entry's proof
      depends on.  Invariant: non-empty iff `status =
      gapClosedConditional`.  See v6 §12. -/
  conditionalOn : List String := []

/-! ### Cat 2 atomic KC bridges (Li-Vitányi 3rd ed. 2008 + Vitányi 2013 TCS 501) -/

/-- Conditional coding theorem (universal additive constant). -/
def gap_K_codingTheorem : GapEntry := {
  name := "K_codingTheorem"
  status := GapStatus.gapOpen
  inputCategory := InputCategory.cat2External
  cat3SubType := Cat3SubType.notCat3
  paperSource :=
    "Li-Vitányi 3rd ed. (2008) Thm 4.3.4 (conditional coding theorem); " ++
    "Vitányi, *TCS* 501 (2013), 93–100 (arXiv:1206.0983), Theorem 4 " ++
    "under Definition 1 (lower-semicomputable conditional semi-measure " ++
    "with Σ_x m(x|y) ≤ 1 + multiplicative universality), for the " ++
    "explicit conditional-version proof"
  attackHistory := [
    "v0.6: Vitányi 2013 supplementary citation added; Thm 4.3.4 " ++
      "conditional version was non-standard prior to 2013",
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
  cat3SubType := Cat3SubType.notCat3
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
  cat3SubType := Cat3SubType.notCat3
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
  cat3SubType := Cat3SubType.notCat3
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
  cat3SubType := Cat3SubType.notCat3
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

/-! ### Cat 3 atomic carriers (paper-novel primitives, sub-type: carrier) -/

/-- Distinguished observable `S*`. -/
def gap_DistinguishedObs_carrier : GapEntry := {
  name := "DistinguishedObs"
  status := GapStatus.gapOpen
  inputCategory := InputCategory.cat3PaperNovel
  cat3SubType := Cat3SubType.carrier
  paperSource :=
    "Li 2026, `\\label{thm:dist}` construction: fresh 0-ary " ++
    "predicate `S*` added to T_0 = Q in the adversarial extension"
  attackHistory := [
    "v6 reductionism Cat 1?: CLEAR-NO — Mathlib has no `W.Obs` " ++
      "abstraction nor any directly-imported 'fresh 0-ary predicate' " ++
      "primitive at this level of abstraction",
    "v6 reductionism Cat 2?: CLEAR-NO — `S*` is the paper's specific " ++
      "construction-internal fresh symbol; it is not the subject of any " ++
      "external textbook theorem, only of paper-local stipulation"
  ]
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
  cat3SubType := Cat3SubType.carrier
  paperSource :=
    "Li 2026, `\\label{thm:dist}` construction: paper-stated " ++
    "`H_e := ∃t. T(e, 0, t)` (Kleene's T-predicate Σ⁰₁ sentence " ++
    "asserting machine `e` halts on input 0)"
  attackHistory := [
    "v6 reductionism Cat 1?: CLEAR-NO — Mathlib has " ++
      "`Nat.Partrec.Code` but no `W.Obs`-embedded representation of " ++
      "the H_e sentence at this abstraction level",
    "v6 reductionism Cat 2?: CLEAR-NO — the SENTENCE H_e is standard " ++
      "(Kleene's T-predicate) but its embedding as a member of the " ++
      "paper's specific `W.Obs` is paper-novel, not external"
  ]
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
  cat3SubType := Cat3SubType.carrier
  paperSource :=
    "Li 2026, `\\label{thm:dist}` construction: abstract " ++
    "realisation of Robinson's Q as the base theory T_0"
  attackHistory := [
    "v6 reductionism Cat 1?: CLEAR-NO — Mathlib.ModelTheory does not " ++
      "yet contain Robinson's Q as a concrete first-order theory at " ++
      "the level this paper consumes",
    "v6 reductionism Cat 2?: CLEAR-NO — Robinson's Q exists in external " ++
      "literature (Smith 2013, TMR 1953, etc.) but the paper's `W.Th`- " ++
      "level abstraction is paper-stipulated, not a direct import"
  ]
  scope :=
    "Typed primitive `Bridge1b_T0 W : W.Th`"
}

/-- Abstract extension family `T*_e`. -/
def gap_Bridge1b_Tstar_carrier : GapEntry := {
  name := "Bridge1b_Tstar"
  status := GapStatus.gapOpen
  inputCategory := InputCategory.cat3PaperNovel
  cat3SubType := Cat3SubType.carrier
  paperSource :=
    "Li 2026, `\\label{thm:dist}` construction: abstract " ++
    "realisation of T*_e := Q ∪ {S* ↔ H_e} indexed by Code"
  attackHistory := [
    "v6 reductionism Cat 1?: CLEAR-NO — no Mathlib import for `T*_e`; " ++
      "the construction T_0 ∪ {single defining axiom} is paper-stipulated",
    "v6 reductionism Cat 2?: CLEAR-NO — the construction itself is " ++
      "Li 2026's adversarial encoding; not an external named theorem"
  ]
  scope :=
    "Typed primitive `Bridge1b_Tstar W : Code → W.Th`"
}

/-! ### Cat 3 atomic defining equations (paper-stated, sub-type: structuralEquation) -/

/-- (iii) `S*` is fresh in `T_0`. -/
def gap_Bridge_Encoding_Sstar_T0 : GapEntry := {
  name := "Bridge_Encoding_Sstar_T0"
  status := GapStatus.gapOpen
  inputCategory := InputCategory.cat3PaperNovel
  cat3SubType := Cat3SubType.structuralEquation
  paperSource :=
    "Li 2026, `\\label{thm:dist}` proof: 'since S* does not " ++
    "occur in T_0's axioms, T_0 ⊬ S*, so S* ∉ π(T_0)'"
  attackHistory := [
    "v6 reductionism Cat 1?: CLEAR-NO — Mathlib cannot derive " ++
      "`DistinguishedObs W ∉ W.predict (Bridge1b_T0 W)` since both " ++
      "operands are Cat 3 paper-novel primitives",
    "v6 reductionism Cat 2?: CLEAR-NO — this is the paper's specific " ++
      "construction stipulation, not a standalone external theorem"
  ]
  scope :=
    "`DistinguishedObs W ∉ W.predict (Bridge1b_T0 W)` — paper-novel " ++
    "freshness (clause iii)"
}

/-- (iii') `H_e ≠ S*`. -/
def gap_Bridge_H_e_distinct_from_Sstar : GapEntry := {
  name := "Bridge_H_e_distinct_from_Sstar"
  status := GapStatus.gapOpen
  inputCategory := InputCategory.cat3PaperNovel
  cat3SubType := Cat3SubType.structuralEquation
  paperSource :=
    "Li 2026, `\\label{thm:dist}` proof: 'Obs := {closed " ++
    "sentences in L_0} ∪ {S*} ... S* not occurring in the language " ++
    "of Q'.  H_e is an L_0-sentence, hence H_e ≠ S*"
  attackHistory := [
    "v6 reductionism Cat 1?: CLEAR-NO — distinctness of paper-novel " ++
      "Cat 3 carriers cannot be derived in Mathlib",
    "v6 reductionism Cat 2?: CLEAR-NO — this is the paper's atomic-" ++
      "disjoint-union structure on `Obs = L_0 ∪ {S*}`, a paper-specific " ++
      "stipulation"
  ]
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
  cat3SubType := Cat3SubType.structuralEquation
  paperSource :=
    "Li 2026, `\\label{thm:dist}` proof: 'In T*_e, the axiom " ++
    "S* ↔ H_e gives T*_e ⊢ S* iff T*_e ⊢ H_e' — paper-novel Step 1 " ++
    "atomic claim (modus ponens on the defining axiom)"
  attackHistory := [
    "v6 reductionism Cat 1?: CLEAR-NO — `S* ∈ π(T*_e) ↔ H_e ∈ π(T*_e)` " ++
      "is a property of the paper-novel `Bridge1b_Tstar` carrier; not " ++
      "Mathlib-derivable",
    "v6 reductionism Cat 2?: CLEAR-NO — modus ponens on a defining " ++
      "biconditional is a standard FO inference, but its application to " ++
      "the paper-specific S*-↔-H_e construction is paper-novel; the " ++
      "abstract claim at the `W.Obs / W.Th` level cannot be 'imported' " ++
      "from an external theorem"
  ]
  scope :=
    "`∀ e, S* ∈ π(T*_e) ↔ H_e_Obs e ∈ π(T*_e)`.  Step 1 only; the " ++
    "textbook conservativity link (T*_e ⊢ H_e ↔ Q ⊢ H_e, Step 2) " ++
    "is derived from Bridge_DefExt_Conservative at H_e using " ++
    "Bridge_H_e_distinct_from_Sstar"
}

/-- Strengthened optional novelty screen: genuine FO syntax, an ablation
    operator, and prediction relevance are not yet represented in Lean. -/
def gap_E3_ablation_relevance : GapEntry := {
  name := "E3_ablation_relevance"
  status := GapStatus.gapOpen
  inputCategory := InputCategory.cat3PaperNovel
  cat3SubType := Cat3SubType.hypothesisPredicate
  paperSource :=
    "Li 2026, Definition `def:candidate` clauses E3a--E3b"
  attackHistory := [
    "2026-07-12 contribution-maximisation revision: added prediction " ++
      "relevance to block novelty-by-idle-symbol; no fake `E3 : Prop` restored"
  ]
  scope :=
    "Requires first-order syntax, declared sigma-ablation, and a proof " ++
      "that ablation removes at least one strict new prediction"
}

/-! ### Cat 2 atomic textbook axioms (recursion-theoretic + Tarski) -/

/-- Σ⁰₁-completeness of `Q` applied to `H_e`. -/
def gap_Bridge_Q_Sigma01_completeness : GapEntry := {
  name := "Bridge_Q_Sigma01_completeness"
  status := GapStatus.gapOpen
  inputCategory := InputCategory.cat2External
  cat3SubType := Cat3SubType.notCat3
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
  cat3SubType := Cat3SubType.notCat3
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
    "FO_derivation`) deferred to Mathlib FO formalisation"
}

/-- Conservativity of definitional extension outside `S*`. -/
def gap_Bridge_DefExt_Conservative : GapEntry := {
  name := "Bridge_DefExt_Conservative"
  status := GapStatus.gapOpen
  inputCategory := InputCategory.cat2External
  cat3SubType := Cat3SubType.notCat3
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
  cat3SubType := Cat3SubType.notCat3
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

/-- Adaptive sequential-testing change-of-measure inequality. -/
def gap_Bayesian_change_of_measure : GapEntry := {
  name := "Bayesian_change_of_measure"
  status := GapStatus.gapOpen
  inputCategory := InputCategory.cat2External
  cat3SubType := Cat3SubType.notCat3
  paperSource :=
    "Kaufmann, Cappe, and Garivier, Journal of Machine Learning " ++
      "Research 16 (2016), Lemma 1: for an almost-surely finite " ++
      "adaptive stopping time, expected sample counts times armwise " ++
      "KL divergence dominate binary relative entropy of every " ++
      "terminal event"
  attackHistory := [
    "2026-07-12 ambition-preserving reconstruction: replaced the " ++
      "underspecified generic KL slogan by a cited adaptive testing theorem"
  ]
  scope :=
    "External bridge used by paper Theorem thm:bayes-floor; not yet " ++
      "encoded as a Lean probability theorem in this project"
}

/-! ### gapClosed entries — top-level theorems proven without `sorry` -/

/-- Theorem 1: empirical-verification wall-clock floor. -/
def gap_thm_floor_CLOSED : GapEntry := {
  name := "thm_floor"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
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
  cat3SubType := Cat3SubType.notCat3
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
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{cor:waiting}`"
  attackHistory := []
  scope :=
    "For `p ≤ 2^(-K_*)` with `K_* > 0`, `E[N] = 1/p ≥ 2^(K_*)`; " ++
    "pure real-arithmetic, no atomic axioms"
}

/-- Theorem 3(i): Σ⁰₁-hardness of `Dist`. -/
def gap_thm_undecidable_sigma01_hard_CLOSED : GapEntry := {
  name := "thm_undecidable_sigma01_hard"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:dist}` clause (i)"
  attackHistory := []
  scope :=
    "Existence of a computable encoding `e ↦ (T*_e, T_0)` under " ++
    "which `Dist(T*_e, T_0) ↔ Halt(e)`.  Depends on the Cat 3 " ++
    "carriers, Cat 3 paper-stated defining equations, and Cat 2 " ++
    "recursion-theoretic textbook atomics via the derived theorem " ++
    "`Bridge_Halt_Iff_Dist`"
}

/-- E1--E2 candidate recognition at the empty snapshot is Sigma01-hard. -/
def gap_thm_candidate_recognition_CLOSED : GapEntry := {
  name := "thm_candidate_recognition_sigma01_hard"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:candidate-recognition}`"
  attackHistory := [
    "2026-07-12: salvaged a candidate-domain result without reviving the " ++
      "invalid promised-verification transfer"
  ]
  scope :=
    "At D=empty, E1 is vacuous and E2 for the adversarial pair is iff " ++
      "halting; does not include E3 or promised-candidate verification"
}

/-- Theorem 3(i) Σ⁰₂-upper bound: pure logic. -/
def gap_thm_undecidable_sigma02_upper_CLOSED : GapEntry := {
  name := "thm_undecidable_sigma02_upper"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:dist}` clause (i) upper bound"
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
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:dist}` clause (ii)"
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
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{cor:no-universal}`"
  attackHistory := []
  scope :=
    "Structural negation: no `ComputablePred` for " ++
    "`e ↦ Dist(enc(e).1, enc(e).2)` where `enc` is the Bridge_Halt_-" ++
    "Iff_Dist reduction; contradicts Mathlib's " ++
    "`ComputablePred.halting_problem 0`"
}

/-- Proposition: no certification from incumbent-consistent data under
    the strict-refutation rule. -/
def gap_no_strict_refutation_certification_CLOSED : GapEntry := {
  name := "no_strict_refutation_certification"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{prop:no-cert}`"
  attackHistory := [
    "2026-07-12 solidity audit: demoted from computability/oracle " ++
      "impossibility to the exact strict-refutation data-set claim"
  ]
  scope :=
    "For D ⊆ D_t ⊆ π(T_0), no verifier satisfying sound_c can " ++
    "certify on D.  No computability or oracle claim is made"
}

/-- Derived protocol consequence: a passing protocol contributes an
    outcome outside the already recorded data. -/
def gap_empirical_access_required_CLOSED : GapEntry := {
  name := "empirical_access_required"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{cor:empirical-access}`"
  attackHistory := []
  scope :=
    "If a strict-refutation system passes, Pi.outcomes is not a subset " ++
    "of D_t"
}

/-- Machine-checked empirical coordinate of the resource-profile
    proposition. -/
def gap_resource_profile_empirical_floor_CLOSED : GapEntry := {
  name := "resource_profile_empirical_floor"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{prop:profile}` clause (iii)"
  attackHistory := [
    "2026-07-12 solidity audit: deleted scalar decomposition and false " ++
      "feasibility sufficiency; retained only the matching empirical coordinate"
  ]
  scope :=
    "tauMin bounds the empiricalTime field of the vector resource " ++
    "profile on a passing strict-refutation system"
}

/-- Fixed-environment invariance, explicitly scoped to one world and
    candidate. -/
def gap_fixed_environment_invariance_CLOSED : GapEntry := {
  name := "fixed_environment_invariance"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{cor:invariance}`"
  attackHistory := []
  scope :=
    "Definitional equality for two system values sharing the same " ++
    "world and candidate; no technology-change claim"
}

/-- Pareto dominance is preserved by non-negative scalarisation. -/
def gap_scalarise_mono_CLOSED : GapEntry := {
  name := "System.ResourceProfile.scalarise_mono"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{prop:resource-geometry}`"
  attackHistory := []
  scope :=
    "Coordinatewise resource dominance implies dominance under every " ++
      "non-negative unit-bearing scalarisation"
}

/-- Weighted empirical clause of the reconstructed resource theorem. -/
def gap_weighted_resource_floor_CLOSED : GapEntry := {
  name := "weighted_resource_empirical_floor"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{prop:resource-geometry}`"
  attackHistory := []
  scope :=
    "For a passing system, w_Pi * tauMin is at most the declared " ++
      "weighted scalar cost; no raw heterogeneous-unit addition"
}

/-- Dynamic witness lower bound. -/
def gap_dynamic_floor_CLOSED : GapEntry := {
  name := "dynamic_floor_of_witness"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:dynamic-floor}`"
  attackHistory := []
  scope :=
    "A realised strict witness whose completion time is bounded by " ++
      "elapsed protocol time yields dynamicTauMin <= elapsed"
}

/-- Technology dominance and frontier congruence. -/
def gap_dynamic_monotonicity_CLOSED : GapEntry := {
  name := "dynamic_tau_mono / dynamic_tau_congr"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{prop:technology-dominance}`"
  attackHistory := []
  scope :=
    "Pointwise improvement on the strict-witness set weakly lowers the " ++
      "dynamic floor; agreement on that set gives equality"
}

/-- Microfounded availability--acquisition technology dominance. -/
def gap_dynamic_path_monotonicity_CLOSED : GapEntry := {
  name := "path_completion_mono / dynamic_path_tau_mono"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{prop:technology-dominance}`"
  attackHistory := [
    "2026-07-12: replaced black-box completion comparison by explicit " ++
      "availability preservation plus acquisition-time dominance"
  ]
  scope :=
    "Every old feasible delayed start remains feasible and no slower; " ++
      "therefore induced completion times and dynamicTauMin weakly fall"
}

/-- Verifier completeness converts a represented witness into acceptance. -/
def gap_strict_witness_accepts_CLOSED : GapEntry := {
  name := "strict_witness_accepts"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, Definition `def:feasibility-certificate` clause F3"
  attackHistory := []
  scope :=
    "Successor-consistent represented strict witness plus explicit " ++
      "strictCompleteFor predicate implies verifier acceptance"
}

/-- Non-circular deterministic core of conditional feasibility. -/
def gap_strict_witness_feasibility_CLOSED : GapEntry := {
  name := "strict_witness_feasibility"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:feasibility}` deterministic core"
  attackHistory := [
    "2026-07-12: replaces the old false F1-F3 shadow with an explicit " ++
      "completeness predicate and represented-witness hypothesis"
  ]
  scope :=
    "Target emission, successor-consistent augmented data, a represented " ++
      "strict witness, and verifier completeness imply System.passes"
}

/-- Paper theorem is only partially machine-bound: probability amplification
    and the union-bound confidence layer are not encoded in this project. -/
def gap_thm_feasibility_PARTIAL : GapEntry := {
  name := "thm_feasibility_probability_layer"
  status := GapStatus.gapPartial
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:feasibility}`"
  attackHistory := []
  scope :=
    "Lean checks the deterministic composition core; the finite-N/K " ++
      "probability and coordinatewise-budget statement is paper-proved only"
}

/-- The Bayesian information-rate theorem is sourced and paper-proved but
    not formalised in this Lean project. -/
def gap_thm_bayes_floor_PARTIAL : GapEntry := {
  name := "thm_bayes_floor"
  status := GapStatus.gapPartial
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:bayes-floor}`"
  attackHistory := []
  scope :=
    "Derives expected empirical time >= binary evidence / best information " ++
      "rate from the external adaptive change-of-measure bridge"
}


/-- Full serial expected-cost decomposition is paper-proved; Lean checks
    the deterministic weighted component aggregation but not expectation. -/
def gap_thm_serial_decomposition_PARTIAL : GapEntry := {
  name := "thm_serial_decomposition"
  status := GapStatus.gapPartial
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:serial-decomposition}`"
  attackHistory := []
  scope :=
    "Serial iid until-hit pipeline: E[C_w] >= w_M c_M/q + w_V L_V + " ++
      "w_Pi tauMin; scalarise_mono checks only the deterministic algebra"
}

/-- Non-stationary independent search law is paper-proved but not encoded
    in the current Lean probability layer. -/
def gap_thm_nonstationary_search_PARTIAL : GapEntry := {
  name := "thm_nonstationary_search"
  status := GapStatus.gapPartial
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:nonstationary-search}`"
  attackHistory := []
  scope :=
    "Independent changing generators: finite no-hit probability is a " ++
      "product; divergent sum q_i is sufficient for eventual hit a.s."
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
  gap_E3_ablation_relevance,
  -- Cat 2 atomic textbook axioms (recursion-theoretic + Tarski)
  gap_Bridge_Q_Sigma01_completeness,
  gap_Bridge_Q_Sigma01_soundness,
  gap_Bridge_DefExt_Conservative,
  gap_Bridge_Tarski_RCF_Correctness,
  gap_Bayesian_change_of_measure,
  -- gapClosed top-level results
  gap_thm_floor_CLOSED,
  gap_thm_emission_CLOSED,
  gap_cor_rare_CLOSED,
  gap_thm_undecidable_sigma01_hard_CLOSED,
  gap_thm_candidate_recognition_CLOSED,
  gap_thm_undecidable_sigma02_upper_CLOSED,
  gap_thm_undecidable_tarski_decidable_CLOSED,
  gap_cor_no_universal_CLOSED,
  gap_no_strict_refutation_certification_CLOSED,
  gap_empirical_access_required_CLOSED,
  gap_resource_profile_empirical_floor_CLOSED,
  gap_fixed_environment_invariance_CLOSED,
  gap_scalarise_mono_CLOSED,
  gap_weighted_resource_floor_CLOSED,
  gap_dynamic_floor_CLOSED,
  gap_dynamic_monotonicity_CLOSED,
  gap_dynamic_path_monotonicity_CLOSED,
  gap_strict_witness_accepts_CLOSED,
  gap_strict_witness_feasibility_CLOSED,
  gap_thm_feasibility_PARTIAL,
  gap_thm_bayes_floor_PARTIAL,
  gap_thm_serial_decomposition_PARTIAL,
  gap_thm_nonstationary_search_PARTIAL
]

/-- Status-keyed counts:
    `(open, partial, blocked, deadEnd, closed, closedConditional)`. -/
def gapCounts : Nat × Nat × Nat × Nat × Nat × Nat :=
  let countWhere (s : GapStatus) : Nat :=
    (allGaps.filter (fun g => g.status = s)).length
  ( countWhere GapStatus.gapOpen
  , countWhere GapStatus.gapPartial
  , countWhere GapStatus.gapBlocked
  , countWhere GapStatus.gapDeadEnd
  , countWhere GapStatus.gapClosed
  , countWhere GapStatus.gapClosedConditional )

/-- InputCategory-keyed counts: `(cat1Mathlib, cat2External, cat3PaperNovel, notInput)`. -/
def inputCategoryCounts : Nat × Nat × Nat × Nat :=
  let countWhere (c : InputCategory) : Nat :=
    (allGaps.filter (fun g => g.inputCategory = c)).length
  ( countWhere InputCategory.cat1Mathlib
  , countWhere InputCategory.cat2External
  , countWhere InputCategory.cat3PaperNovel
  , countWhere InputCategory.notInput )

/-- Cat3SubType-keyed counts:
    `(carrier, hypothesisPredicate, structuralEquation, workingAssumption, conditionalHypothesis, notCat3)`. -/
def cat3SubTypeCounts : Nat × Nat × Nat × Nat × Nat × Nat :=
  let countWhere (s : Cat3SubType) : Nat :=
    (allGaps.filter (fun g => g.cat3SubType = s)).length
  ( countWhere Cat3SubType.carrier
  , countWhere Cat3SubType.hypothesisPredicate
  , countWhere Cat3SubType.structuralEquation
  , countWhere Cat3SubType.workingAssumption
  , countWhere Cat3SubType.conditionalHypothesis
  , countWhere Cat3SubType.notCat3 )

#eval s!"EinsteinTest gap-ledger inventory (status):    open={(gapCounts).1} partial={(gapCounts).2.1} blocked={(gapCounts).2.2.1} deadEnd={(gapCounts).2.2.2.1} closed={(gapCounts).2.2.2.2.1} closedConditional={(gapCounts).2.2.2.2.2}"

#eval s!"EinsteinTest gap-ledger inventory (input):     cat1Mathlib={(inputCategoryCounts).1} cat2External={(inputCategoryCounts).2.1} cat3PaperNovel={(inputCategoryCounts).2.2.1} notInput={(inputCategoryCounts).2.2.2}"

#eval s!"EinsteinTest gap-ledger inventory (Cat 3 sub): carrier={(cat3SubTypeCounts).1} hypothesisPredicate={(cat3SubTypeCounts).2.1} structuralEquation={(cat3SubTypeCounts).2.2.1} workingAssumption={(cat3SubTypeCounts).2.2.2.1} conditionalHypothesis={(cat3SubTypeCounts).2.2.2.2.1} notCat3={(cat3SubTypeCounts).2.2.2.2.2}"

#eval s!"Total entries: {allGaps.length}"

/-! ### Inventory summary

  The live status / input-category / Cat 3 sub-type counts are printed
  by the `#eval` calls above (run `lake env lean
  EinsteinTest/Ledger.lean` to see them).  Axiom names by category:

    Cat 2 propositional (external published textbook):
      K_codingTheorem, K_chainRule_pair, K_pairNonDecrease,
      K_condMonotone, K_descLength, Bridge_Tarski_RCF_Correctness,
      Bridge_Q_Sigma01_completeness, Bridge_Q_Sigma01_soundness,
      Bridge_DefExt_Conservative, Bayesian_change_of_measure

    Cat 3 carriers (paper-novel typed primitives):
      DistinguishedObs, H_e_Obs, Bridge1b_T0, Bridge1b_Tstar

    Cat 3 structural defining equations (paper-stated atomic):
      Bridge_Encoding_Sstar_T0, Bridge_H_e_distinct_from_Sstar,
      Bridge_Defining_Biconditional

    Cat 3 open hypothesis predicate (not declared as a fake axiom):
      E3_ablation_relevance

  Cat 3 sub-types not used in this project: `workingAssumption`
  (no provisional bundles), `conditionalHypothesis`
  (no open-problem-conditional results).

  Lean kernel (Cat 0; not declared here): propext, Classical.choice,
  Quot.sound.
-/

end EinsteinTest.Ledger
