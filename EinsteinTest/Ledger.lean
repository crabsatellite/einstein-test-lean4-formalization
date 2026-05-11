/-
  EinsteinTest/Ledger.lean

  Gap ledger per `feedback_gap_ledger_in_lean4.md`.

  Every axiom + every BLOCKED route + every CLOSED top-level result
  recorded as a typed declaration with explicit status.  This module
  is the canonical cross-session record of the project's attack history,
  citation provenance, and scope verdicts.

  Status taxonomy:
    gapOpen       — postulated; Mathlib derivation not yet attempted
                    (or attempt in progress)
    gapPartial    — partially closed; remaining content explicit
    gapBlocked    — route obstructed by known no-go theorem (cited)
    gapDeadEnd    — ≥N attempts collapsed to same bottleneck
    gapClosed     — proven (theorem with no `sorry`)
    gapPaperNovel — paper's own construction (not literature; not Mathlib)

  Pre-attack review: orchestrator scans this ledger before launching new
  attacks.  Re-attempting a BLOCKED or DEAD-END route is a context-drift
  failure mode — flag and skip.
-/

import EinsteinTest

namespace EinsteinTest.Ledger

/-- Status tag attached to each gap. -/
inductive GapStatus
  | gapOpen
  | gapPartial
  | gapBlocked
  | gapDeadEnd
  | gapClosed
  | gapPaperNovel
  deriving DecidableEq, Repr

/-- Typed record for a single gap. -/
structure GapEntry where
  /-- Identifier (matches the underlying axiom / theorem name where applicable). -/
  name : String
  /-- Current status. -/
  status : GapStatus
  /-- Operative paper source(s) (and/or no-go obstacle citation for `gapBlocked`). -/
  paperSource : String
  /-- Per-round attack trace (canonical location for round metadata;
      docstrings are Phase-5-cleaned, so the round trace lives here). -/
  attackHistory : List String
  /-- Scope of the gap: what content it carries, and what it deliberately
      does NOT claim. -/
  scope : String

/-! ### KC bridges (Li-Vitányi 3rd ed. 2008 + Vitányi 2013 TCS 501)

  Five single-step prefix-Kolmogorov bridges, each a Category-1 literature
  axiom, decomposed per `feedback_lean_axiom_decomposition` (no composite
  axioms).  Citations updated 2026-05-12 per Phase-0 hostile full-theorem-
  survey (F3/F4/F5/F6 defects).
-/

/-- `K_codingTheorem` — conditional coding theorem.  Universal additive
    constant `c` for `K(x|y) ≤ k + c` when `μ(x|y) ≥ 2^(-k)`.  Only the
    upper-bound direction. -/
def gap_K_codingTheorem : GapEntry := {
  name := "K_codingTheorem"
  status := GapStatus.gapOpen
  paperSource :=
    "Li-Vitányi 3rd ed. (2008) Thm 4.3.4 (conditional coding theorem); " ++
    "Vitányi, *Theoretical Computer Science* 501 (2013), 93–100 " ++
    "(arXiv:1206.0983) for the explicit conditional-version proof"
  attackHistory := [
    "v0.1: writer added composite",
    "v0.2: existential form",
    "v0.4: citation tightened to Li-Vit 3rd ed",
    "v0.5: hedged after hostile Phase-0",
    "v0.6 (2026-05-12): F3 fix — added Vitányi 2013 supplementary citation; " ++
      "conditional version (Thm 4.3.4) was non-standard in literature prior " ++
      "to Vitányi 2013, which establishes the conditional convention used here"
  ]
  scope :=
    "Universal additive constant c for the upper bound K(x|y) ≤ k + c " ++
    "when μ(x|y) ≥ 2^(-k); upper bound only, no matching lower bound; " ++
    "treats μ as encoded via opaque `μDesc` parameter"
}

/-- `K_chainRule_pair` — symmetric-information chain rule, pair-LHS form. -/
def gap_K_chainRule_pair : GapEntry := {
  name := "K_chainRule_pair"
  status := GapStatus.gapOpen
  paperSource :=
    "Li-Vitányi 3rd ed. (2008) Thm 3.9.1 (symmetric-information chain " ++
    "rule, prefix-complexity version); plain-complexity analogue: " ++
    "Li-Vitányi 3rd ed. Eq. (3.21)"
  attackHistory := [
    "v0.1: writer added composite",
    "v0.4: explicit Thm 3.9.1 citation",
    "v0.5: pair-LHS form ONLY; single-LHS form derived via " ++
      "K_pairNonDecrease (no composite axiom)",
    "v0.6 (2026-05-12): no change (already correctly cited)"
  ]
  scope :=
    "Slack function `slack : ℝ → ℝ` (O(log L) overhead) such that " ++
    "K((x,y)|z) ≤ K(x|y,z) + K(y|z) + slack L; pair-LHS form only; " ++
    "single-LHS form is a DERIVED lemma `K_chainRule_single_apply`"
}

/-- `K_pairNonDecrease` — information non-decrease under pairing. -/
def gap_K_pairNonDecrease : GapEntry := {
  name := "K_pairNonDecrease"
  status := GapStatus.gapOpen
  paperSource :=
    "Li-Vitányi 3rd ed. (2008) §3.1 (immediate from prefix-free pair-" ++
    "decoding: K(x|z) ≤ K(⟨x,y⟩|z) + c)"
  attackHistory := [
    "v0.5: split out of bundled chain rule so single-LHS variant " ++
      "becomes a derived lemma (no composite axiom)",
    "v0.6 (2026-05-12): F5 fix — dropped any 'Thm 2.2.1' label that " ++
      "could not be verified; cite by §3.1 only"
  ]
  scope :=
    "Additive constant c such that K(x|z) ≤ K(encodePair x y | z) + c " ++
    "(equivalently: pairing cannot decrease information about the first " ++
    "component, modulo additive constant)"
}

/-- `K_condMonotone` — conditioning monotonicity (prefix-`K`). -/
def gap_K_condMonotone : GapEntry := {
  name := "K_condMonotone"
  status := GapStatus.gapOpen
  paperSource :=
    "Li-Vitányi 3rd ed. (2008) §3.1 / §3.4 (prefix-`K` analogue of the " ++
    "plain-`C` Ch 2 result; extra conditioning cannot raise prefix " ++
    "complexity by more than a constant; immediate by relativizing the " ++
    "universal prefix machine)"
  attackHistory := [
    "v0.1: writer cited Thm 2.1.8",
    "v0.4: same",
    "v0.6 (2026-05-12): F4 fix — Thm 2.1.8 is for plain `C` (Ch 2), but " ++
      "the Lean axiom is stated for prefix `K`; result transfers via §3.1/§3.4 " ++
      "by relativizing the universal prefix machine; citation corrected"
  ]
  scope :=
    "Additive constant c such that K(x|y,z) ≤ K(x|y) + c (prefix `K`); " ++
    "the analogous plain-`C` statement is Thm 2.1.8 but the Lean axiom is " ++
    "stated for prefix `K`"
}

/-- `K_descLength` — description-length bound. -/
def gap_K_descLength : GapEntry := {
  name := "K_descLength"
  status := GapStatus.gapOpen
  paperSource :=
    "Li-Vitányi 3rd ed. (2008) §2.1 (immediate consequence of the " ++
    "Invariance Theorem Thm 2.1.1 via the literal-output universal program)"
  attackHistory := [
    "v0.1: writer cited Thm 2.1.1 (invariance) directly — wrong: Thm 2.1.1 " ++
      "is invariance |K_1 - K_2| ≤ c, not description-length K(y|z) ≤ |y| + c",
    "v0.5: hedged — cite §2.1 (immediate consequence of Thm 2.1.1) instead " ++
      "of Thm 2.1.1 directly",
    "v0.6 (2026-05-12): F6 fix — made the self-delimiting hypothesis " ++
      "EXPLICIT in docstring.  REQUIRES `descLen y` to include prefix-coding " ++
      "overhead; without it the textbook bound is K(y|z) ≤ |y| + 2log|y| + c"
  ]
  scope :=
    "Additive constant c such that K(y|z) ≤ descLen y + c, where descLen y " ++
    "INCLUDES the self-delimiting overhead (i.e., descLen y is the length " ++
    "of a prefix-free code for y, not raw |y|); without self-delimiting " ++
    "overhead the bound carries an extra 2log|y| term"
}

/-! ### Recursion-theoretic bridges (post-v0.4 PURE single-category split) -/

/-- `Bridge_Tstar_e_Encoding` — paper-novel encoding construction.
    PURE Category 3 (no literature content). -/
def gap_Bridge_Tstar_e_Encoding : GapEntry := {
  name := "Bridge_Tstar_e_Encoding"
  status := GapStatus.gapPaperNovel
  paperSource :=
    "Li 2026, *What the Karpowicz Theorem Does Not Prove*, " ++
    "`\\label{thm:undecidable}` proof construction T*_e := Q ∪ {S* ↔ H_e}"
  attackHistory := [
    "v0.1: bundled in HaltDistBundle",
    "v0.3: HaltDistBundle 4-conjunct mixed-category axiom flagged",
    "v0.4: split into PURE Category-3 paper-novel encoding axiom " ++
      "(clauses (iii) S* ∉ π(T_0) + (iv) S* ∈ π(T*_e) ↔ qHe(e))",
    "v0.6 (2026-05-12): no change (no defect on paper-novel side)"
  ]
  scope :=
    "Existential witnessing (Sstar : W.Obs, qHe : Nat.Partrec.Code → Prop, " ++
    "T0_enc : W.Th, Tstar_enc : Nat.Partrec.Code → W.Th) satisfying ONLY " ++
    "the paper-novel encoding properties (iii) `S* ∉ π(T_0)` and " ++
    "(iv) `S* ∈ π(T*_e) ↔ qHe(e)`.  No textbook content bundled in."
}

/-- `Bridge_Q_DefExt_TextbookFacts` — textbook conclusions for any
    structure satisfying the paper-novel encoding.  PURE Category 1. -/
def gap_Bridge_Q_DefExt_TextbookFacts : GapEntry := {
  name := "Bridge_Q_DefExt_TextbookFacts"
  status := GapStatus.gapOpen
  paperSource :=
    "Σ⁰₁-completeness of Q: Hájek-Pudlák, *Metamathematics of First-Order " ++
    "Arithmetic*, Springer 1998, Chapter I (PRIMARY, numbered theorem); " ++
    "Smith, *An Introduction to Gödel's Theorems*, 2nd ed., Cambridge UP " ++
    "2013, Ch 11 'What Q can prove' (SECONDARY).  " ++
    "Σ⁰₁-soundness of Q (via N ⊨ Q): Tarski-Mostowski-Robinson, " ++
    "*Undecidable Theories*, North-Holland, 1953 (one-line corollary " ++
    "combined with Σ⁰₁-completeness).  " ++
    "Conservativity outside `S*`: Shoenfield, *Mathematical Logic*, " ++
    "Addison-Wesley 1967, §4.6 'Extensions by definitions' (p. 57f) " ++
    "PRIMARY; Hodges, *A Shorter Model Theory*, Cambridge UP 1997, §2.6 " ++
    "(SECONDARY, section-level only)"
  attackHistory := [
    "v0.3: HaltDistBundle bundled-category axiom flagged",
    "v0.4: split into PURE Category-1 literature axiom (Σ⁰₁-completeness/" ++
      "soundness of Q + conservativity outside `S*`)",
    "v0.5: hedged on 'BBJ Thm 16.4' (conflated section §16.4 with theorem " ++
      "number) and 'Hodges Thm 2.6.4' (could not be independently verified)",
    "v0.6 (2026-05-12): F1+F2 FATAL fix.  (F1) BBJ §16.4 is the WRONG " ++
      "section for the operative Σ⁰₁-completeness fact (BBJ §16.4 is an " ++
      "optional appendix; representability is §16.2), AND BBJ uses 'Q' for " ++
      "minimal arithmetic (§16.2), distinct from standard Robinson's Q " ++
      "(which BBJ label 'R' in §16.4) — citing BBJ as operative source " ++
      "propagates this Q-vs-R naming hazard.  Operative source moved to " ++
      "Hájek-Pudlák 1998 Ch I (cleanest theorem-numbered statement; " ++
      "uncontroversial; widely cited).  Accessible secondary: Smith 2013 " ++
      "Ch 11.  (F2) Rogers Ch XII is RE/reducibilities territory, NOT " ++
      "Σ⁰₁-soundness; arithmetical hierarchy is Rogers Ch XIV but Σ⁰₁-" ++
      "soundness of Q is folklore (one-line corollary of N ⊨ Q + " ++
      "Σ⁰₁-completeness), not in Rogers as a numbered theorem.  Operative " ++
      "source moved to Tarski-Mostowski-Robinson 1953 for N ⊨ Q + " ++
      "Hájek-Pudlák for Σ⁰₁-completeness."
  ]
  scope :=
    "Universal claim over any 4-tuple (Sstar, qHe, T0_enc, Tstar_enc) " ++
    "satisfying paper-novel encoding properties (iii)+(iv): " ++
    "(i) qHe e ↔ Halt(e) (Σ⁰₁-completeness × Σ⁰₁-soundness of Robinson Q); " ++
    "(ii) S ≠ S* → (S ∈ π(T*_e) ↔ S ∈ π(T_0)) (conservativity outside S*).  " ++
    "No paper-novel content; purely textbook conclusions"
}

/-- `Bridge_Tarski_RCF_Correctness` — Tarski 1948 RCF decidability. -/
def gap_Bridge_Tarski_RCF_Correctness : GapEntry := {
  name := "Bridge_Tarski_RCF_Correctness"
  status := GapStatus.gapOpen
  paperSource :=
    "Tarski, *A Decision Method for Elementary Algebra and Geometry*, " ++
    "RAND R-109, 1948 / UC Press 1951; quantifier-elimination procedure " ++
    "for the FO theory of real-closed fields"
  attackHistory := [
    "v0.1: writer added as opaque framework axiom",
    "v0.3: strengthened from trivial `∃ b, RCFDecide φ = b` " ++
      "(true by Bool-typing) to `∃ b : Bool, b = true ↔ RCFSatisfies φ` " ++
      "(captures substantive Tarski content)",
    "v0.6 (2026-05-12): no change (Tarski 1948 citation uncontroversial)"
  ]
  scope :=
    "For every FO formula φ over the RCF signature (RCFFormula), the " ++
    "Bool-valued procedure RCFDecide returns `true` iff φ is satisfied " ++
    "by the standard RCF model `⟨ℝ; +, ·, <, 0, 1⟩` (RCFSatisfies φ).  " ++
    "Stipulates correctness of a Tarski-style quantifier-elimination " ++
    "decision procedure as an opaque framework primitive"
}

/-! ### gapBlocked entries — Mathlib derivations DEFERRED (out-of-scope) -/

/-- BLOCKED: full Mathlib derivation of Kolmogorov complexity `K`.

    Obstacle: Mathlib currently has NO `Mathlib.InformationTheory.Kolmogorov`
    module.  Building one would require (a) a universal prefix Turing
    machine formalisation, (b) the invariance theorem proof, (c) the full
    conditional-coding-theorem proof — all on the order of a substantial
    paper-grade formalization project.  Out of scope for the present
    companion paper; the KC bridges are axiomatised against opaque types
    instead. -/
def gap_K_Mathlib_full_derivation_BLOCKED : GapEntry := {
  name := "K_Mathlib_full_derivation"
  status := GapStatus.gapBlocked
  paperSource :=
    "no-go obstacle: Mathlib currently has no " ++
    "`Mathlib.InformationTheory.Kolmogorov` module; building one is a " ++
    "substantial separate project.  See `Mathlib.Computability` for the " ++
    "computability-side framework available, but no K-complexity primitive"
  attackHistory := [
    "v0.1: writer decided to axiomatise K against opaque types rather " ++
      "than build the full universal-prefix-machine framework"
  ]
  scope :=
    "Full proof of the five KC bridges (K_codingTheorem, K_chainRule_pair, " ++
    "K_pairNonDecrease, K_condMonotone, K_descLength) inside Lean as " ++
    "theorems against a concrete prefix-machine framework.  Deferred; the " ++
    "five bridges remain Category-1 literature axioms"
}

/-- BLOCKED: full FO theory encoding via `Mathlib.ModelTheory`.

    Obstacle: `Mathlib.ModelTheory` is incomplete for r.e.-axiomatised
    theories.  In particular, the framework needed to encode `T*_e` as
    a uniformly computable family of FO theories (Robinson `Q` plus a
    fresh predicate plus one additional axiom, decoded from the Turing
    machine index `e`) and to formalise the Σ⁰₁-completeness of `Q`
    as a Mathlib theorem is not yet available.  The recursion-theoretic
    Bridge_Q_DefExt_TextbookFacts is axiomatised against the encoding
    realisations instead. -/
def gap_FOTheory_encoding_BLOCKED : GapEntry := {
  name := "FOTheory_encoding_Mathlib"
  status := GapStatus.gapBlocked
  paperSource :=
    "no-go obstacle: `Mathlib.ModelTheory` does not yet contain " ++
    "a formalisation of Robinson's Q with its Σ⁰₁-completeness theorem; " ++
    "the framework for r.e.-axiomatised FO theories (axiom enumeration, " ++
    "uniform-r.e.\\ derivability, conservativity-of-definitional-extension " ++
    "lemma) is not yet at the level needed.  See Mathlib issues tracking " ++
    "Robinson arithmetic formalisation."
  attackHistory := [
    "v0.1: writer decided to abstract `W.Th` over concrete FO theories " ++
      "and axiomatise the recursion-theoretic facts about Robinson Q",
    "v0.3-v0.4: split bundled HaltDistBundle into pure Category-1 + " ++
      "Category-3 axioms so the Mathlib-derivation gap is cleanly isolated"
  ]
  scope :=
    "Full FO-encoding of T*_e := Q ∪ {S* ↔ H_e} as a Mathlib " ++
    "FirstOrder.Language theory, with the textbook lemmas (Σ⁰₁-" ++
    "completeness of Q; conservativity of definitional extension; " ++
    "Beth definability for the (E3) clause) proved inside Mathlib.  " ++
    "Deferred; the two recursion-theoretic bridges remain axioms"
}

/-- BLOCKED: full Tarski CAD algorithm in Lean.

    Obstacle: `Mathlib.FieldTheory` real-closed-fields decidability is
    incomplete.  Tarski's quantifier-elimination procedure (and Collins'
    cylindrical-algebraic-decomposition) have not been formalised in
    Mathlib; the closest available framework is the abstract decidability
    of o-minimal structures, which is not yet at the level needed for a
    concrete Boolean-valued `RCFDecide` procedure with a Lean proof of
    correctness.  Hence the abstract opaque `RCFDecide` + axiom pattern. -/
def gap_Tarski_CAD_Mathlib_BLOCKED : GapEntry := {
  name := "Tarski_CAD_Mathlib"
  status := GapStatus.gapBlocked
  paperSource :=
    "no-go obstacle: Mathlib does not contain a constructive Tarski / " ++
    "Collins quantifier-elimination procedure for the FO theory of " ++
    "real-closed fields with a machine-checked correctness proof.  See " ++
    "Basu-Pollack-Roy, *Algorithms in Real Algebraic Geometry* (2nd ed., " ++
    "Springer 2006) for the algorithmic content; no Lean port available"
  attackHistory := [
    "v0.1: writer added abstract `RCFFormula`, `RCFDecide`, `RCFSatisfies` " ++
      "opaque types + correctness axiom",
    "v0.3: strengthened axiom statement from trivial `∃ b, RCFDecide φ = b` " ++
      "to substantive `∃ b : Bool, b = true ↔ RCFSatisfies φ`"
  ]
  scope :=
    "Full constructive Tarski CAD algorithm inside Lean with a " ++
    "machine-checked correctness proof against the standard RCF semantics.  " ++
    "Deferred; `Bridge_Tarski_RCF_Correctness` remains a Category-1 axiom"
}

/-! ### gapClosed entries — top-level theorems proven without `sorry` -/

/-- CLOSED: Theorem 1 — empirical-verification wall-clock floor. -/
def gap_thm_floor_CLOSED : GapEntry := {
  name := "thm_floor"
  status := GapStatus.gapClosed
  paperSource :=
    "Li 2026, *What the Karpowicz Theorem Does Not Prove*, " ++
    "`\\label{thm:floor}`"
  attackHistory := [
    "v0.1: theorem stated + proved",
    "v0.4: `_hCorrect` parameter flagged as redundant (does not invoke " ++
      "correct-successor hypothesis); Remark `correct-succ-redundant` " ++
      "documents this in the paper"
  ]
  scope :=
    "Empirical-verification protocol Π requires wall-clock ≥ τmin = " ++
    "inf {τ_t(S) : S ∈ (π(T*) \\ π(T_0)) ∩ Tech_t}; generator-independent.  " ++
    "Proof uses soundness clause (c) directly; no KC bridges needed"
}

/-- CLOSED: Theorem 2 — generator KC emission lower bound. -/
def gap_thm_emission_CLOSED : GapEntry := {
  name := "thm_emission"
  status := GapStatus.gapClosed
  paperSource :=
    "Li 2026, *What the Karpowicz Theorem Does Not Prove*, " ++
    "`\\label{thm:emission}`"
  attackHistory := [
    "v0.1: theorem stated + axioms added",
    "v0.4: explicit chain-rule constants",
    "v0.5: bundled chain rule split into pair-LHS axiom + " ++
      "pairNonDecrease axiom + derived single-LHS lemma"
  ]
  scope :=
    "K(T*|D_t) ≤ k + |M| + |p| + slack constants, where k = -log Pr[M(p)=T*]; " ++
    "depends on 5 KC bridge axioms (K_codingTheorem, K_chainRule_pair, " ++
    "K_pairNonDecrease, K_condMonotone, K_descLength); proof: 6-step " ++
    "linear chain via `linarith` over the bridge inequalities"
}

/-- CLOSED: Corollary — geometric waiting time `2^K_*` ≤ 1/p. -/
def gap_cor_rare_CLOSED : GapEntry := {
  name := "cor_rare"
  status := GapStatus.gapClosed
  paperSource :=
    "Li 2026, *What the Karpowicz Theorem Does Not Prove*, " ++
    "`\\label{cor:rare}`"
  attackHistory := [
    "v0.1: corollary stated + proved (pure real-arithmetic)"
  ]
  scope :=
    "For p ≤ 2^(-K_*) with K_* > 0, expected sample count " ++
    "E[N] = 1/p ≥ 2^(K_*); pure real-arithmetic, no KC bridges"
}

/-- CLOSED: Remark — vacuous when `K_* ≤ 0`. -/
def gap_rem_emission_not_impossible_CLOSED : GapEntry := {
  name := "rem_emission_not_impossible"
  status := GapStatus.gapClosed
  paperSource :=
    "Li 2026, *What the Karpowicz Theorem Does Not Prove*, " ++
    "`\\label{rem:emission-not-impossible}`"
  attackHistory := [
    "v0.1: remark proved as `2^K_* ≤ 1` when K_* ≤ 0"
  ]
  scope :=
    "Three escape routes (test-time search, ripe innovations, continual " ++
    "training) push K_* ≤ 0, making the cor_rare bound vacuous"
}

/-- CLOSED: Theorem 3(i) Σ⁰₁-hardness — depends on the two split bridges. -/
def gap_thm_undecidable_sigma01_hard_CLOSED : GapEntry := {
  name := "thm_undecidable_sigma01_hard"
  status := GapStatus.gapClosed
  paperSource :=
    "Li 2026, *What the Karpowicz Theorem Does Not Prove*, " ++
    "`\\label{thm:undecidable}` clause (i)"
  attackHistory := [
    "v0.1: stub statement",
    "v0.2: `HaltDistBundle` packed all four conjuncts (mixed-category)",
    "v0.4: split into PURE Category-1 (Bridge_Q_DefExt_TextbookFacts) + " ++
      "PURE Category-3 (Bridge_Tstar_e_Encoding) axioms; theorem proved " ++
      "from the two bridges via Bridge_Halt_Iff_Dist"
  ]
  scope :=
    "Existence of a computable encoding e ↦ (T*_e, T_0) under which " ++
    "Dist(T*_e, T_0) ↔ Halt(e); depends on Bridge_Tstar_e_Encoding + " ++
    "Bridge_Q_DefExt_TextbookFacts"
}

/-- CLOSED: Theorem 3(i) Σ⁰₂-upper bound — pure logic. -/
def gap_thm_undecidable_sigma02_upper_CLOSED : GapEntry := {
  name := "thm_undecidable_sigma02_upper"
  status := GapStatus.gapClosed
  paperSource :=
    "Li 2026, *What the Karpowicz Theorem Does Not Prove*, " ++
    "`\\label{thm:undecidable}` clause (i) upper bound"
  attackHistory := [
    "v0.1: theorem stated + proved (pure logic equivalence)"
  ]
  scope :=
    "Dist(T_1,T_2) iff ∃ S. separating observation; pure-logic equivalence, " ++
    "no axioms beyond Lean kernel + Classical.byContradiction"
}

/-- CLOSED: Theorem 3(ii) Tarski-class decidability. -/
def gap_thm_undecidable_tarski_decidable_CLOSED : GapEntry := {
  name := "thm_undecidable_tarski_decidable"
  status := GapStatus.gapClosed
  paperSource :=
    "Li 2026, *What the Karpowicz Theorem Does Not Prove*, " ++
    "`\\label{thm:undecidable}` clause (ii)"
  attackHistory := [
    "v0.1: trivial Bool-typing statement",
    "v0.3: strengthened to substantive `∃ b : Bool, b = true ↔ RCFSatisfies φ`; " ++
      "depends on Bridge_Tarski_RCF_Correctness"
  ]
  scope :=
    "For every RCFFormula φ, ∃ Bool-valued classifier b with b = true ↔ " ++
    "RCFSatisfies φ; depends on Bridge_Tarski_RCF_Correctness only"
}

/-- CLOSED: Corollary — no `ComputablePred` witness for the Dist-decider. -/
def gap_cor_no_universal_CLOSED : GapEntry := {
  name := "cor_no_universal"
  status := GapStatus.gapClosed
  paperSource :=
    "Li 2026, *What the Karpowicz Theorem Does Not Prove*, " ++
    "`\\label{cor:no-universal}`"
  attackHistory := [
    "v0.6 (R6): post-R6 honest restatement — structural negation only " ++
      "(no `ComputablePred` for the Dist-decider), reduced from a stronger " ++
      "earlier claim caught by hostile review"
  ]
  scope :=
    "Structural negation: no `ComputablePred` for the predicate " ++
    "e ↦ Dist(enc(e).1, enc(e).2) where enc is the Bridge_Halt_Iff_Dist " ++
    "reduction; transports to a contradiction with Mathlib's " ++
    "`ComputablePred.halting_problem 0`"
}

/-- CLOSED: Theorem 5 — self-verification impossibility. -/
def gap_thm_self_verification_CLOSED : GapEntry := {
  name := "thm_self_verification"
  status := GapStatus.gapClosed
  paperSource :=
    "Li 2026, *What the Karpowicz Theorem Does Not Prove*, " ++
    "`\\label{thm:self-verification}`"
  attackHistory := [
    "v0.1: stated + proved (uses soundness clause (c) + E1 directly)",
    "v0.4: Robustness corollaries `cor_self_verif_robust_{i,ii,iii,iv}` " ++
      "established without computability assumption on V_M"
  ]
  scope :=
    "For any D ⊆ D_t consistent with T_0, no sound verifier V_M can " ++
    "return 1 on (p, T*, T_0, D) for an Einstein-replacement T*; " ++
    "uniform over data-restriction lattice {D : D ⊆ D_t}; robust to " ++
    "universal-compressor, true-arithmetic, halting-oracle, and any-" ++
    "reasoner enhancements"
}

/-- CLOSED: Corollary — empirical access is structurally necessary. -/
def gap_cor_empirical_necessity_CLOSED : GapEntry := {
  name := "cor_empirical_necessity"
  status := GapStatus.gapClosed
  paperSource :=
    "Li 2026, *What the Karpowicz Theorem Does Not Prove*, " ++
    "`\\label{cor:empirical-necessity}`"
  attackHistory := [
    "v0.1: stated + proved"
  ]
  scope :=
    "A system (M, V_M) with no empirical protocol Π cannot pass the " ++
    "Einstein Test on any Einstein-replacement T*; structural " ++
    "consequence of `thm_self_verification`"
}

/-- CLOSED: Theorem 4 — three-component cost decomposition. -/
def gap_thm_decomposition_CLOSED : GapEntry := {
  name := "thm_decomposition"
  status := GapStatus.gapClosed
  paperSource :=
    "Li 2026, *What the Karpowicz Theorem Does Not Prove*, " ++
    "`\\label{thm:decomposition}`"
  attackHistory := [
    "v0.1: stated + proved (additive composition of thm_floor, " ++
      "thm_emission, thm_undecidable bounds)"
  ]
  scope :=
    "C_Einstein = B_M + B_V + B_Π with structurally distinct floors " ++
    "(emission KC bound, computational class-dependent obstruction, " ++
    "empirical wall-clock floor)"
}

/-- CLOSED: Corollary — conditional feasibility. -/
def gap_cor_conditional_feasibility_CLOSED : GapEntry := {
  name := "cor_conditional_feasibility"
  status := GapStatus.gapClosed
  paperSource :=
    "Li 2026, *What the Karpowicz Theorem Does Not Prove*, " ++
    "`\\label{cor:conditional-feasibility}`"
  attackHistory := [
    "v0.1: stated + proved"
  ]
  scope :=
    "(F1)∧(F2)∧(F3) sufficient for Einstein-Test feasibility within " ++
    "finite budget; (F1) K(T*|D_t) ≤ |M|+|p|+log_2 N, (F2) T* ∈ Th^N, " ++
    "(F3) τmin < ∞"
}

/-- CLOSED: Corollary — bound interaction. -/
def gap_cor_bound_interaction_CLOSED : GapEntry := {
  name := "cor_bound_interaction"
  status := GapStatus.gapClosed
  paperSource :=
    "Li 2026, *What the Karpowicz Theorem Does Not Prove*, " ++
    "`\\label{cor:bound-interaction}`"
  attackHistory := [
    "v0.1: stated + proved (AI-side coupling between generation and " ++
      "computational verification, uncoupling from τmin)"
  ]
  scope :=
    "AI-side interventions can lower (a)+(b) but not (c); generator " ++
    "constraint to Th^N tightens (b); training-data extension lowers (a); " ++
    "no AI-side intervention lowers τmin"
}

/-! ### Aggregated ledger inventory -/

/-- All gap entries in canonical order (axioms first, then BLOCKED routes,
    then CLOSED top-level results). -/
def allGaps : List GapEntry := [
  -- KC bridges (Category 1)
  gap_K_codingTheorem,
  gap_K_chainRule_pair,
  gap_K_pairNonDecrease,
  gap_K_condMonotone,
  gap_K_descLength,
  -- Recursion-theoretic bridges (post-v0.4 PURE single-category split)
  gap_Bridge_Tstar_e_Encoding,
  gap_Bridge_Q_DefExt_TextbookFacts,
  gap_Bridge_Tarski_RCF_Correctness,
  -- BLOCKED routes (Mathlib derivations deferred)
  gap_K_Mathlib_full_derivation_BLOCKED,
  gap_FOTheory_encoding_BLOCKED,
  gap_Tarski_CAD_Mathlib_BLOCKED,
  -- CLOSED top-level results
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

/-- Status-keyed counts: `(open, partial, blocked, deadEnd, closed, paperNovel)`. -/
def gapCounts : Nat × Nat × Nat × Nat × Nat × Nat :=
  let countWhere (s : GapStatus) : Nat :=
    (allGaps.filter (fun g => g.status = s)).length
  ( countWhere GapStatus.gapOpen
  , countWhere GapStatus.gapPartial
  , countWhere GapStatus.gapBlocked
  , countWhere GapStatus.gapDeadEnd
  , countWhere GapStatus.gapClosed
  , countWhere GapStatus.gapPaperNovel )

-- Inventory printout (run with `lake env lean EinsteinTest/Ledger.lean`).
#eval s!"EinsteinTest gap-ledger inventory: open={(gapCounts).1} partial={(gapCounts).2.1} blocked={(gapCounts).2.2.1} deadEnd={(gapCounts).2.2.2.1} closed={(gapCounts).2.2.2.2.1} paperNovel={(gapCounts).2.2.2.2.2}"

#eval s!"Total entries: {allGaps.length}"

/-! ### Trust audit summary (post Phase-2+4+5, 2026-05-12)

  Total: 8 axioms + 3 gapBlocked deferred-Mathlib routes + 13 gapClosed
  top-level results (= 24 entries).

  Axiom counts by category:
    - Category 1 (literature, prefix-K): 5 (KC bridges)
    - Category 1 (literature, recursion-theoretic): 2
      (Bridge_Q_DefExt_TextbookFacts, Bridge_Tarski_RCF_Correctness)
    - Category 3 (paper-novel): 1 (Bridge_Tstar_e_Encoding)
    - Category 2 (standard kernel: propext, Classical.choice, Quot.sound):
      provided by Lean / Mathlib, not declared here.

  No (E) custom-scaffolding axioms.  No composite axioms.  Each Category-1
  axiom carries a precise paper citation; the Category-3 axiom is tied to
  Li 2026 `\label{thm:undecidable}`.

  Post-Phase-0 citation defects fixed (2026-05-12):
    F1 (FATAL): BBJ Ch 16 §16.4 → Hájek-Pudlák 1998 Ch I (primary) +
               Smith 2013 Ch 11 (secondary).  Rationale: BBJ §16.4 is an
               optional appendix; representability is §16.2; AND BBJ
               uses "Q" for minimal arithmetic (their §16.2), distinct
               from standard Robinson's Q.
    F2 (FATAL): Rogers Ch XII → Tarski-Mostowski-Robinson 1953
               (operative source for N ⊨ Q) + Hájek-Pudlák for
               Σ⁰₁-completeness.  Rationale: Rogers Ch XII is RE/
               reducibilities territory, not Σ⁰₁-soundness of Q.
    F3 (PARTIAL): K_codingTheorem citation augmented with Vitányi 2013
                  TCS 501 (arXiv:1206.0983) for explicit conditional-
                  version proof.
    F4 (MINOR): K_condMonotone cite-by-section §3.1/§3.4 (prefix-K
                analogue) instead of plain-C Thm 2.1.8.
    F5 (MINOR): K_pairNonDecrease dropped any "Thm 2.2.1" reference,
                cite by §3.1 only.
    F6 (MINOR): K_descLength self-delimiting hypothesis made explicit.
-/

end EinsteinTest.Ledger
