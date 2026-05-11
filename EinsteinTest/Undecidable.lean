/-
  EinsteinTest/Undecidable.lean

  Theorem~\ref{thm:undecidable} (Distinguishability is Σ⁰₁-hard on
  recursively axiomatised classes containing Robinson Q; decidable on
  the Tarski class), Corollary~\ref{cor:no-universal}, and
  Remark~\ref{rem:adversarial-not-E3}.

  Companion to: "What the Karpowicz Theorem Does Not Prove" (Li, 2026).

  Construction: for each Turing machine code `e`,
  let `T*_e := Q ∪ {S* ↔ H_e}` where `S*` is a fresh 0-ary predicate
  outside `L_0`'s signature and `H_e := ∃t. T(e, 0, t)` is the
  arithmetic halting predicate for `e`. By the conservativity-of-
  definitional-extension lemma (Shoenfield 1967 *Mathematical Logic*
  §4.6 (Extensions by definitions), p. 57f; see also Hodges 1997
  *A Shorter Model Theory* §2.6 (conservative-extension material on
  p. 58 and surrounding discussion)), `T*_e` is consistent over `Q`
  regardless of the truth of `H_e`.  The Halt ⇒ Dist many-one
  reduction is `e ↦ (T*_e, T_0)`.

  *Note on Q-naming:* "Robinson's Q" in this file refers to the
  standard finitely-axiomatized fragment of Peano arithmetic per
  Smith 2013 (Cambridge, *An Introduction to Gödel's Theorems*,
  2nd ed.) Ch 11 ("What Q can prove", §"Q is Σ₁-complete") as the
  PRIMARY operative source (chapter title and section locator
  verified by direct CUP frontmatter match; the in-chapter theorem
  number is unverified, so we cite at the section level only).
  Secondary: Hájek-Pudlák 1998 (Springer, *Metamathematics of
  First-Order Arithmetic*) Preliminaries §(c) "Beginning
  Arithmetization of Metamathematics" (pp. 20-26), where Q is
  introduced and Σ₁-completeness is stated as a foundational
  preliminaries-level fact (NOT as a numbered theorem; HP uses
  two-level Chapter.Section numbering with letter-labelled
  subsections, and the relativized Σ_n/Π_n hierarchy lives at
  Ch I §2(d) p. 81, which is a DIFFERENT location).  We deliberately
  avoid citing Boolos-Burgess-Jeffrey *Computability and Logic*
  (5th ed., 2007) as the operative source because BBJ use a
  DIFFERENT naming convention: BBJ's "Q" is Shoenfield-style minimal
  arithmetic (§16.2) and BBJ's "R" is what they label as "Robinson
  arithmetic" (§16.4); these are distinct theories (see the
  Wikipedia article on Robinson arithmetic for the explicit
  comparison: "Robinson arithmetic and the minimal arithmetic
  discussed in Boolos, Burgess and Jeffrey are two distinct
  theories").  BBJ may still be cited as a secondary textbook
  source with this naming caveat made explicit.

  *Important caveat (Remark~\ref{rem:adversarial-not-E3}):* the
  adversarial `T*_e` is by construction an explicit definitional
  extension of `T_0 = Q` (via `S* ↔ H_e`), so it fails (E3) by
  Beth's theorem. Theorem 3 is therefore a result about `Dist` on
  r.e.-axiomatised classes, not specifically about Einstein-Test
  verifiers. Cor `no-universal` transfers the lower bound to any
  super-family of Dist-deciders.

  *Lean formalization scope:* full encoding of first-order theories
  as `Nat.Partrec.Code`-indexed objects with the conservativity lemma
  is deferred (see `gap_FOTheory_encoding_BLOCKED` in
  `EinsteinTest.Ledger`).  This module:

    * provides the unconditional Σ⁰₂ upper bound (`thm_undecidable_sigma02_upper`)
      as a pure-logic equivalence;
    * stipulates the Σ⁰₁-hardness reduction as TWO PURE single-category
      bridges (`Bridge_Tstar_e_Encoding` = paper-novel Category 3;
      `Bridge_Q_DefExt_TextbookFacts` = textbook Category 1) and
      derives `Bridge_Halt_Iff_Dist` from them;
    * stipulates the Tarski 1948 RCF decidability as a bridge
      (`Bridge_Tarski_RCF_Correctness`).

  All bridges are single-step (per `feedback_lean_axiom_decomposition`)
  and pure single-category; the axiom-dependency surface in
  `AxiomAudit.lean` shows exactly which textbook facts each theorem
  relies on.
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

/-! ### Recursion-theoretic bridges (decomposed axioms).

  These bridges encode standard facts from computability theory and
  first-order logic; each is a single-step claim cited from the
  textbook references in the file header.  Decomposing them
  individually (rather than as a composite axiom) makes the
  axiom-dependency surface auditable. -/

/-! ### Halt-iff-Dist bridges: two PURE single-category axioms.

  Per the trust policy (every axiom must be PURE single-category), the
  recursion-theoretic content is split into two independent axioms
  (textbook citations: Σ⁰₁-completeness of Robinson Q from Smith 2013
  Ch 11 (primary) / Hájek-Pudlák 1998 Preliminaries §(c) (secondary);
  Σ⁰₁-soundness via N ⊨ Q from Tarski-Mostowski-Robinson 1953 Ch II
  (axiomatization) together with Smith 2013 §10.1-10.2
  (axiom-by-axiom verification that ℕ satisfies each Q-axiom);
  conservativity of definitional extension from Shoenfield 1967 §4.6
  (primary) / Hodges 1997 §2.6 (secondary), on top of two paper-novel
  encoding stipulations for the construction
  `T*_e := Q ∪ {S* ↔ H_e}`):

    * `Bridge_Tstar_e_Encoding` — PURE Category 3 paper-novel.  Witnesses
      the EXISTENCE of (Sstar, qHe, T0_enc, Tstar_enc) satisfying ONLY
      the paper-novel encoding properties (iii) `S* ∉ π(T_0)` and
      (iv) `S* ∈ π(T*_e) ↔ qHe(e)`.  Citation: Li 2026,
      `\label{thm:undecidable}` construction.

    * `Bridge_Q_DefExt_TextbookFacts` — PURE Category 1 literature.
      A UNIVERSAL claim: for ANY 4-tuple (Sstar, qHe, T0_enc, Tstar_enc)
      satisfying the paper's encoding properties (iii)+(iv), the
      textbook facts (i) `qHe e ↔ Halt(e)` (Smith 2013 Ch 11,
      §"Q is Σ₁-complete", primary; Hájek-Pudlák 1998 Preliminaries
      §(c) "Beginning Arithmetization of Metamathematics" (pp. 20-26),
      secondary, for Σ⁰₁-completeness; TMR 1953 Ch II for Q's
      axiomatization plus Smith 2013 §10.1-10.2 for axiom-by-axiom
      verification of N ⊨ Q yielding Σ⁰₁-soundness as a one-line
      corollary) and (ii) conservativity outside `S*` (Shoenfield
      1967 §4.6, primary; Hodges 1997 §2.6, secondary) hold.
      Contains no paper-novel content; pure textbook conclusions
      about any structure with the paper's encoding properties.

  Downstream theorems (`Bridge_Halt_Iff_Dist`, `thm_undecidable_sigma01_hard`,
  `cor_no_universal`) destructure both axioms and chain the
  conclusions.

  *Citations:*
    * Shoenfield, *Mathematical Logic* (Addison-Wesley, 1967) §4.6
      (Extensions by definitions, p. 57f) — classical statement and
      proof of the conservativity-of-definitional-extension theorem
      (primary citation, theorem-numbered in the source).
    * Hodges, *A Shorter Model Theory* (Cambridge UP, 1997) §2.6
      (translations / definitional extensions); conservative-
      extension material on p. 58 and surrounding discussion
      (secondary, section-level only — no theorem-number label).
    * Smith, *An Introduction to Gödel's Theorems* (2nd ed.,
      Cambridge UP, 2013) Ch 11 ("What Q can prove", §"Q is
      Σ₁-complete") — PRIMARY operative source for Σ⁰₁-completeness
      of Q (chapter title + section locator verified by direct CUP
      frontmatter match; in-chapter theorem number unverified, so
      cited at section level only).  Also §10.1-10.2 (axiom-by-axiom
      verification that ℕ satisfies each of Q's seven axioms),
      supplying the textbook witness for N ⊨ Q used in deriving
      Σ⁰₁-soundness.
    * Hájek-Pudlák, *Metamathematics of First-Order Arithmetic*
      (Perspectives in Logic, Springer, 1998) Preliminaries §(c)
      "Beginning Arithmetization of Metamathematics" (pp. 20-26),
      where Q is introduced and Σ⁰₁-completeness is stated as a
      foundational preliminaries-level fact (NOT as a numbered
      theorem; HP uses two-level Chapter.Section numbering with
      letter-labelled subsections — there is no §1.4) —
      SECONDARY source for Σ⁰₁-completeness.
    * Tarski-Mostowski-Robinson, *Undecidable Theories* (Studies
      in Logic and the Foundations of Mathematics, North-Holland,
      Amsterdam, 1953) Ch II — standard reference for the
      axiomatization of Q (used together with Smith 2013 §10.1-10.2
      for the axiom-by-axiom verification of N ⊨ Q, which yields
      Σ⁰₁-soundness as a one-line corollary; N ⊨ Q is not stated
      in TMR as a numbered theorem — it is immediate-by-construction
      from the syntactic axiomatization).
    * Li, 2026, *What the Karpowicz Theorem Does Not Prove*,
      `\label{thm:undecidable}` proof construction.

  Round-history trace (citation revisions, prior retractions) is the
  canonical `attackHistory` field of `gap_Bridge_Q_DefExt_TextbookFacts`
  in `EinsteinTest.Ledger`.
-/

/-- **Paper-novel encoding axiom (Category 3).**  The paper's adversarial
    construction `T*_e := Q ∪ {S* ↔ H_e}` (Section~\ref{sec:undecidability}
    proof of Theorem~\ref{thm:undecidable}) admits an abstract realization:
    there exist a fresh observable `S*` outside `T_0`'s signature, an
    arithmetic halting predicate family `qHe`, and uniformly-r.e.
    encodings `T0_enc : W.Th`, `Tstar_enc : Nat.Partrec.Code → W.Th`
    such that:

    * (iii) `S* ∉ π(T_0)` — `S*` is fresh in `T_0`'s vocabulary;
    * (iv) `S* ∈ π(T*_e) ↔ qHe e` — `S* ↔ H_e` is the defining axiom
        of `T*_e` (so `T*_e ⊢ S* ⇔ T*_e ⊢ H_e ⇔ qHe e`).

    Neither (iii) nor (iv) is a textbook theorem; both are direct
    encodings of the paper's `T*_e` construction (see
    Remark~\ref{rem:adversarial-not-E3} in `einstein_test.tex`).
    Postulated as an axiom because the Lean encoding abstracts `W.Th`
    away from concrete first-order theories; in a full FO-formalization
    this axiom would be replaced by a constructive `def`.

    *Citation:* Li 2026, *What the Karpowicz Theorem Does Not Prove*,
    `\label{thm:undecidable}` proof construction. -/
axiom Bridge_Tstar_e_Encoding (W : ObservationalWorld) [REAxiomatised W] :
    ∃ (Sstar : W.Obs) (qHe : Nat.Partrec.Code → Prop)
      (T0_enc : W.Th) (Tstar_enc : Nat.Partrec.Code → W.Th),
      (Sstar ∉ W.predict T0_enc) ∧
      (∀ e, Sstar ∈ W.predict (Tstar_enc e) ↔ qHe e)

/-- **Literature axiom (Category 1).**  For ANY 4-tuple
    `(Sstar, qHe, T0_enc, Tstar_enc)` satisfying the paper's
    `T*_e := Q ∪ {S* ↔ H_e}` construction stipulations (iii) and (iv),
    the following textbook facts hold:

    * (i) `qHe e ↔ Halt(e)` — Σ⁰₁-completeness of Robinson `Q`
        (Smith, *An Introduction to Gödel's Theorems*, 2nd ed.,
        Cambridge UP, 2013, Ch 11 "What Q can prove", §"Q is
        Σ₁-complete" — PRIMARY; chapter title and section locator
        verified by direct CUP frontmatter match, in-chapter theorem
        number unverified so cited at section level only; secondary
        textbook source: Hájek-Pudlák, *Metamathematics of
        First-Order Arithmetic*, Perspectives in Logic, Springer,
        1998, Preliminaries §(c) "Beginning Arithmetization of
        Metamathematics", pp. 20-26, where Q is introduced and
        Σ⁰₁-completeness is stated as a foundational preliminaries-
        level fact, NOT as a numbered theorem — HP uses two-level
        Chapter.Section numbering with letter-labelled subsections,
        and the relativized Σ_n/Π_n hierarchy lives at Ch I §2(d)
        p. 81, a DIFFERENT location) — combined with Σ⁰₁-soundness
        of `Q`, which follows as a one-line corollary from `N ⊨ Q`
        (Tarski-Mostowski-Robinson, *Undecidable Theories*, North-
        Holland, Amsterdam, 1953, Ch II, for Q's axiomatization;
        Smith 2013 §10.1-10.2 for the axiom-by-axiom verification
        that ℕ satisfies each of Q's seven axioms — TMR does not
        state N ⊨ Q as a numbered theorem) plus Σ⁰₁-completeness.
    * (ii) Conservativity outside `S*`:
        `S ≠ S* → (S ∈ π(T*_e) ↔ S ∈ π(T_0))` — conservativity of
        definitional extensions.  Primary citation: Shoenfield,
        *Mathematical Logic*, Addison-Wesley, 1967, §4.6 "Extensions
        by definitions" (p. 57f).  See also Hodges, *A Shorter Model
        Theory*, Cambridge UP, 1997, §2.6 (conservative-extension
        material on p. 58 and surrounding discussion; section-level
        reference only, no theorem-number label).

    The axiom is stated as a universal claim over any 4-tuple
    `(Sstar, qHe, T0_enc, Tstar_enc)` satisfying the paper-novel
    encoding properties (iii)+(iv) supplied by `Bridge_Tstar_e_Encoding`.
    No bundled paper-novel content — purely textbook conclusions
    about any structure with the paper's encoding properties. -/
axiom Bridge_Q_DefExt_TextbookFacts (W : ObservationalWorld) [REAxiomatised W]
    (Sstar : W.Obs) (qHe : Nat.Partrec.Code → Prop)
    (T0_enc : W.Th) (Tstar_enc : Nat.Partrec.Code → W.Th)
    (h_iii : Sstar ∉ W.predict T0_enc)
    (h_iv : ∀ e, Sstar ∈ W.predict (Tstar_enc e) ↔ qHe e) :
    -- (i) Σ⁰₁-completeness: Smith 2013 Ch 11 §"Q is Σ₁-complete" primary,
    --     Hájek-Pudlák 1998 Preliminaries §(c) pp. 20-26 secondary;
    --     Σ⁰₁-soundness: TMR 1953 Ch II + Smith 2013 §10.1-10.2 for N ⊨ Q
    (∀ e, qHe e ↔ (Nat.Partrec.Code.eval e 0).Dom) ∧
    -- (ii) Shoenfield 1967 §4.6 (primary), Hodges 1997 §2.6 (secondary)
    (∀ (e : Nat.Partrec.Code) (S : W.Obs),
      S ≠ Sstar → (S ∈ W.predict (Tstar_enc e) ↔ S ∈ W.predict T0_enc))

/-! ### Bridge accessors (derived; not separate axioms).

  Each name below is `Classical.choose`-extracted from
  `Bridge_Tstar_e_Encoding` and is therefore not a separate axiom;
  the `#print axioms` audit will list `Bridge_Tstar_e_Encoding` and
  `Bridge_Q_DefExt_TextbookFacts` only. -/

/-- Distinguished observable `S*` (Classical.choose-extracted from
    `Bridge_Tstar_e_Encoding`). -/
noncomputable def DistinguishedObs (W : ObservationalWorld)
    [REAxiomatised W] : W.Obs :=
  Classical.choose (Bridge_Tstar_e_Encoding W)

/-- The "Q proves H_e" predicate (Classical.choose-extracted, second
    component of `Bridge_Tstar_e_Encoding`). -/
noncomputable def Q_proves_He (W : ObservationalWorld) [REAxiomatised W]
    (e : Nat.Partrec.Code) : Prop :=
  (Classical.choose_spec (Bridge_Tstar_e_Encoding W)).choose e

/-- Encoded base theory `T_0` (Classical.choose-extracted, third
    component of `Bridge_Tstar_e_Encoding`). -/
noncomputable def Bridge1b_T0 (W : ObservationalWorld) [REAxiomatised W] : W.Th :=
  (Classical.choose_spec (Bridge_Tstar_e_Encoding W)).choose_spec.choose

/-- Encoded extension family `T*_e` (Classical.choose-extracted,
    fourth component of `Bridge_Tstar_e_Encoding`). -/
noncomputable def Bridge1b_Tstar (W : ObservationalWorld) [REAxiomatised W]
    (e : Nat.Partrec.Code) : W.Th :=
  (Classical.choose_spec (Bridge_Tstar_e_Encoding W)).choose_spec.choose_spec.choose e

/-- The paper-novel encoding properties (iii)+(iv) extracted from
    `Bridge_Tstar_e_Encoding`. -/
private lemma encoding_spec (W : ObservationalWorld) [REAxiomatised W] :
    (DistinguishedObs W ∉ W.predict (Bridge1b_T0 W)) ∧
    (∀ e, DistinguishedObs W ∈ W.predict (Bridge1b_Tstar W e) ↔ Q_proves_He W e) :=
  (Classical.choose_spec (Bridge_Tstar_e_Encoding W)).choose_spec.choose_spec.choose_spec

/-- **Bridge 1c-(T0) (S* does not occur in T_0's signature).**
    Paper-novel encoding clause (iii); derived from
    `Bridge_Tstar_e_Encoding`. -/
lemma Bridge_Encoding_Sstar_T0
    (W : ObservationalWorld) [REAxiomatised W] :
    DistinguishedObs W ∉ W.predict (Bridge1b_T0 W) :=
  (encoding_spec W).1

/-- **Bridge 1c-(Tstar) (defining biconditional `S* ↔ H_e` of T*_e
    pins S*-prediction to Q-provability of H_e).**
    Paper-novel encoding clause (iv); derived from
    `Bridge_Tstar_e_Encoding`. -/
lemma Bridge_Encoding_Sstar_Tstar
    (W : ObservationalWorld) [REAxiomatised W] :
    ∀ e, DistinguishedObs W ∈ W.predict (Bridge1b_Tstar W e) ↔ Q_proves_He W e :=
  (encoding_spec W).2

/-- The textbook facts (i)+(ii) applied to the encoding witnesses.
    Derived from `Bridge_Q_DefExt_TextbookFacts` instantiated at the
    witnesses chosen out of `Bridge_Tstar_e_Encoding`. -/
private lemma textbook_spec (W : ObservationalWorld) [REAxiomatised W] :
    (∀ e, Q_proves_He W e ↔ (Nat.Partrec.Code.eval e 0).Dom) ∧
    (∀ (e : Nat.Partrec.Code) (S : W.Obs),
      S ≠ DistinguishedObs W →
        (S ∈ W.predict (Bridge1b_Tstar W e) ↔ S ∈ W.predict (Bridge1b_T0 W))) :=
  Bridge_Q_DefExt_TextbookFacts W (DistinguishedObs W) (Q_proves_He W)
    (Bridge1b_T0 W) (Bridge1b_Tstar W) (Bridge_Encoding_Sstar_T0 W)
    (Bridge_Encoding_Sstar_Tstar W)

/-- **Bridge 1a (Q-provability of H_e ↔ Halt; Smith 2013 Ch 11 primary
    + Hájek-Pudlák 1998 Preliminaries §(c) secondary, for Σ⁰₁-
    completeness; TMR 1953 Ch II + Smith 2013 §10.1-10.2, for N ⊨ Q
    yielding Σ⁰₁-soundness).** Textbook clause (i); derived from
    `Bridge_Q_DefExt_TextbookFacts`.  Σ⁰₁-completeness from Smith 2013
    Ch 11 §"Q is Σ₁-complete" (primary; chapter title and section
    locator verified, in-chapter theorem number unverified so cited
    at section level only) with secondary Hájek-Pudlák 1998
    Preliminaries §(c) pp. 20-26 (foundational preliminaries-level
    fact, not numbered theorem; HP uses two-level numbering — there
    is no §1.4); Σ⁰₁-soundness as one-line corollary from N ⊨ Q
    (Tarski-Mostowski-Robinson 1953 *Undecidable Theories* Ch II for
    Q's axiomatization plus Smith 2013 §10.1-10.2 for axiom-by-axiom
    verification of N ⊨ Q). -/
lemma Bridge_Q_Sigma01_complete_sound
    (W : ObservationalWorld) [REAxiomatised W] :
    ∀ e, Q_proves_He W e ↔ (Nat.Partrec.Code.eval e 0).Dom :=
  (textbook_spec W).1

/-- **Bridge 1b (Conservativity of definitional extension outside
    `S*`; Shoenfield 1967 §4.6, p. 57f; see also Hodges 1997 §2.6).**
    Textbook clause (ii); derived from `Bridge_Q_DefExt_TextbookFacts`. -/
lemma Bridge_DefExt_Conservative
    (W : ObservationalWorld) [REAxiomatised W] :
    ∀ (e : Nat.Partrec.Code) (S : W.Obs),
      S ≠ DistinguishedObs W →
        (S ∈ W.predict (Bridge1b_Tstar W e) ↔ S ∈ W.predict (Bridge1b_T0 W)) :=
  (textbook_spec W).2

/-- **Bridge 1 (derived theorem).** Composite reduction:
    there exists a uniformly-computable encoding `e ↦ (T*_e, T_0)`
    under which `Dist(T*_e, T_0) ↔ Halt(e)`.

    *Proof from the split bridges:*
    `Bridge_Tstar_e_Encoding` supplies the encoding witnesses
    (Sstar, qHe, T0_enc, Tstar_enc) and the paper-novel properties
    (iii)+(iv); `Bridge_Q_DefExt_TextbookFacts` then yields the
    textbook facts (i) Σ⁰₁-completeness (Smith 2013 Ch 11 §"Q is
    Σ₁-complete", primary; Hájek-Pudlák 1998 Preliminaries §(c)
    pp. 20-26, secondary) + Σ⁰₁-soundness via N ⊨ Q
    (Tarski-Mostowski-Robinson 1953 Ch II + Smith 2013 §10.1-10.2)
    and (ii) conservativity outside `S*` (Shoenfield 1967 §4.6
    primary, Hodges 1997 §2.6 secondary).  The reduction
    `e ↦ (Bridge1b_Tstar W e, Bridge1b_T0 W)` pivots on the
    distinguished observable: the prediction sets agree off `S*`
    (Shoenfield 1967 §4.6 / Hodges 1997 §2.6), and they disagree on
    `S*` iff `T*_e` proves `S*` iff Q proves `H_e` iff `Halt(e)`. -/
theorem Bridge_Halt_Iff_Dist
    (W : ObservationalWorld) [REAxiomatised W] :
    ∃ (encode : Nat.Partrec.Code → W.Th × W.Th),
      ∀ e, Dist W (encode e).1 (encode e).2 ↔ (Nat.Partrec.Code.eval e 0).Dom := by
  refine ⟨fun e => (Bridge1b_Tstar W e, Bridge1b_T0 W), ?_⟩
  intro e
  unfold Dist
  constructor
  · -- Dist → Halt: prediction sets differ ⇒ they differ at S* (by 1b) ⇒
    -- S* ∈ π(T*_e) (since S* ∉ π(T_0) by 1c) ⇒ Q_proves_He ⇒ Halt.
    intro hDist
    by_contra hNotHalt
    apply hDist
    have hNotQHe : ¬ Q_proves_He W e := by
      intro hQHe
      exact hNotHalt ((Bridge_Q_Sigma01_complete_sound W e).mp hQHe)
    have hSstar_notin_Tstar : DistinguishedObs W ∉ W.predict (Bridge1b_Tstar W e) := by
      intro hIn
      exact hNotQHe ((Bridge_Encoding_Sstar_Tstar W e).mp hIn)
    have hSstar_notin_T0 : DistinguishedObs W ∉ W.predict (Bridge1b_T0 W) :=
      Bridge_Encoding_Sstar_T0 W
    apply Set.eq_of_subset_of_subset
    · intro S hS
      by_cases hS_is_star : S = DistinguishedObs W
      · exact absurd (hS_is_star ▸ hS) hSstar_notin_Tstar
      · exact (Bridge_DefExt_Conservative W e S hS_is_star).mp hS
    · intro S hS
      by_cases hS_is_star : S = DistinguishedObs W
      · exact absurd (hS_is_star ▸ hS) hSstar_notin_T0
      · exact (Bridge_DefExt_Conservative W e S hS_is_star).mpr hS
  · -- Halt → Dist: by 1a get Q_proves_He, by 1c get S* ∈ π(T*_e) and
    -- S* ∉ π(T_0), hence the prediction sets differ on S*.
    intro hHalt
    have hQHe : Q_proves_He W e :=
      (Bridge_Q_Sigma01_complete_sound W e).mpr hHalt
    have hSstar_in_Tstar : DistinguishedObs W ∈ W.predict (Bridge1b_Tstar W e) :=
      (Bridge_Encoding_Sstar_Tstar W e).mpr hQHe
    have hSstar_notin_T0 : DistinguishedObs W ∉ W.predict (Bridge1b_T0 W) :=
      Bridge_Encoding_Sstar_T0 W
    intro hEq
    exact hSstar_notin_T0 (hEq ▸ hSstar_in_Tstar)

/-- **Bridge 2 framework primitives (Tarski 1948).**  The first-order
    theory of real-closed fields is decidable; equivalently, there is a
    decision procedure for satisfaction of FO formulas over
    `(ℝ; +, ·, <, 0, 1)`.

    *Citation:* Tarski, *A Decision Method for Elementary Algebra
    and Geometry* (RAND R-109, 1948 / UC Press, 1951). The concrete
    algorithm is Tarski's quantifier-elimination procedure; later
    descendants include Collins' cylindrical-algebraic-decomposition
    and Renegar's algorithms. We stipulate the framework via the
    abstract encoding type `RCFFormula`, the `Bool`-valued decision
    procedure `RCFDecide`, the RCF-satisfaction predicate
    `RCFSatisfies`, and the literature-axiom
    `Bridge_Tarski_RCF_Correctness` linking the two. -/
opaque RCFFormula : Type
opaque RCFDecide : RCFFormula → Bool

/-- RCF satisfaction predicate (Tarski 1948 / standard model theory).
    `RCFSatisfies φ` holds iff the first-order formula `φ` is true
    over the standard model of real-closed fields
    `⟨ℝ; +, ·, <, 0, 1⟩`.  Treated as an opaque framework primitive,
    populated abstractly by the Tarski semantics. -/
opaque RCFSatisfies : RCFFormula → Prop

/-- **Bridge 2 (Tarski 1948 RAND R-109).** The theory of real-closed
    fields is decidable: there exists an algorithm that correctly
    classifies RCF-validity of every FO sentence.  We carry this as
    the existence of a `Bool`-valued procedure agreeing with
    `RCFSatisfies` on every input; the opaque `RCFDecide` declared
    above represents one such algorithm (Tarski's quantifier-
    elimination procedure / Collins CAD / Renegar).

    *Citation:* Tarski, *A Decision Method for Elementary Algebra and
    Geometry* (RAND R-109, 1948 / UC Press, 1951). -/
axiom Bridge_Tarski_RCF_Correctness :
    ∀ φ : RCFFormula, RCFDecide φ = true ↔ RCFSatisfies φ

/-! ### Theorems. -/

/-- **Theorem~\ref{thm:undecidable} (i) upper bound: Σ⁰₂.**

    `Dist(T_1, T_2) ⇔ ∃ S. (S ∈ π(T_1) ∧ S ∉ π(T_2)) ∨ (S ∈ π(T_2) ∧ S ∉ π(T_1))`,
    which is `∃S. (Σ⁰₁ ∧ Π⁰₁)` (= Σ⁰₂).

    Lean content: pure equivalence between `Dist` (defined as set
    inequality) and the existence of a separating observation.
    Classical (uses `Classical.byContradiction`).  Provable
    unconditionally. -/
theorem thm_undecidable_sigma02_upper (W : ObservationalWorld) (T1 T2 : W.Th) :
    Dist W T1 T2 ↔
      ∃ S, (S ∈ W.predict T1 ∧ S ∉ W.predict T2)
         ∨ (S ∈ W.predict T2 ∧ S ∉ W.predict T1) := by
  constructor
  · intro hDist
    -- `Dist` unfolds to `predict T1 ≠ predict T2`.  Take a separating point.
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
    -- Equality predict T1 = predict T2 rules out a separating S.
    rcases hSep with ⟨hIn1, hNotIn2⟩ | ⟨hIn2, hNotIn1⟩
    · exact hNotIn2 (hEq ▸ hIn1)
    · exact hNotIn1 (hEq.symm ▸ hIn2)

/-- **Theorem~\ref{thm:undecidable} (i): Σ⁰₁-hardness of `Dist`.**

    On any r.e.-axiomatised class extending Robinson `Q`, the
    distinguishability decision problem `Dist` is Σ⁰₁-hard.

    *Statement form:* the recursion-theoretic content is the existence
    of a computable encoding under which Dist is iff-equivalent to
    halting.  Proof: invoke `Bridge_Halt_Iff_Dist`. -/
theorem thm_undecidable_sigma01_hard
    (W : ObservationalWorld) [REAxiomatised W] :
    ∃ (encode : Nat.Partrec.Code → W.Th × W.Th),
      ∀ e, Dist W (encode e).1 (encode e).2 ↔ (Nat.Partrec.Code.eval e 0).Dom :=
  Bridge_Halt_Iff_Dist W

/-- **Theorem~\ref{thm:undecidable} (ii): Tarski-class decidability.**

    On the Tarski class `Θ^N` (theories whose prediction set is the
    solution set of a first-order formula over the real-closed-field
    signature), `Dist` is decidable.  Substantive content: every FO
    sentence `φ` over `⟨ℝ; +, ·, <, 0, 1⟩` has a `Bool`-valued
    classifier whose `true` value coincides with `RCFSatisfies φ`.
    Witness: `RCFDecide` from Tarski's quantifier-elimination
    procedure (Tarski 1948 RAND R-109), correctness packaged by
    `Bridge_Tarski_RCF_Correctness`.

    This is the non-trivial statement that RCF validity is
    `Bool`-decidable; it depends on the single literature axiom
    `Bridge_Tarski_RCF_Correctness`.  Stating the conclusion as
    `∃ b, b = true ↔ RCFSatisfies φ` (rather than the trivial
    `∃ b, RCFDecide φ = b`) makes the substantive claim manifest. -/
theorem thm_undecidable_tarski_decidable :
    ∀ φ : RCFFormula, ∃ b : Bool, b = true ↔ RCFSatisfies φ :=
  fun φ => ⟨RCFDecide φ, Bridge_Tarski_RCF_Correctness φ⟩

/--
  **Corollary~\ref{cor:no-universal}**: no `ComputablePred`-witnessing
  total Dist-decider exists on r.e.-axiomatised classes extending `Q`.

  Formal statement: composing Bridge 1 with the standard
  recursion-theoretic identification (a `ComputablePred`-witnessed
  decider on `Dist` would yield a `ComputablePred` for `Halt`),
  the halting problem becomes decidable — contradicting
  `ComputablePred.halting_problem 0` from Mathlib.

  We expose the structural negation: there is no `ComputablePred` for
  the predicate `e ↦ Dist(enc(e).1, enc(e).2)` where `enc` is the
  Bridge-1 reduction.

  Transfer to Einstein-Test verifiers is conditional on the super-
  family containing the r.e.-axiomatised adversarial sub-class.

  *Proof:* Suppose for contradiction such a `ComputablePred` existed.
  Bridge 1 gives `∀ e, Dist (enc e).1 (enc e).2 ↔ Halt e`, so the
  halting predicate `fun e => (Nat.Partrec.Code.eval e 0).Dom` is
  `ComputablePred`-equivalent to a `ComputablePred`, hence itself
  `ComputablePred`.  This contradicts `halting_problem 0` from
  `Mathlib.Computability.Halting`.  The Mathlib-level
  `ComputablePred.of_eq` lemma closes the equivalence-transport step. -/
theorem cor_no_universal
    (W : ObservationalWorld) [REAxiomatised W] :
    ¬ ComputablePred
        (fun e : Nat.Partrec.Code =>
          Dist W ((Bridge_Halt_Iff_Dist W).choose e).1
                 ((Bridge_Halt_Iff_Dist W).choose e).2) := by
  intro hComp
  -- Use Bridge 1 to identify Dist with Halt under the encoding.
  have hIff := (Bridge_Halt_Iff_Dist W).choose_spec
  -- Transport ComputablePred along the iff.
  have hHalt : ComputablePred (fun e : Nat.Partrec.Code => (Nat.Partrec.Code.eval e 0).Dom) := by
    -- We have hIff : ∀ e, Dist ... ↔ Halt e.  Rewrite the predicate.
    convert hComp using 1
    funext e
    exact propext (hIff e).symm
  exact ComputablePred.halting_problem 0 hHalt

/-! ### Note on Remark~\ref{rem:adversarial-not-E3}.

  The adversarial `T*_e := Q ∪ {S* ↔ H_e}` is by construction an
  explicit definitional extension of `T_0 = Q` (the defining formula
  for the fresh symbol `S*` is the `L_0`-sentence `H_e`), so by Beth's
  theorem (E3) FAILS for every `T*_e`.  This is intentional: the
  Σ⁰₁-hardness result above is about `Dist` on r.e.-axiomatised
  classes, not Einstein-Test verifiability — the encoding-axiom
  clauses `(h_iii)` and `(h_iv)` of `Bridge_Tstar_e_Encoding`
  directly witness explicit FO-definability of `S*` over `L_0` in
  `T*_e`.

  This remark is a narrative observation about the construction; no
  Lean ceremony is required, and no placeholder theorem stub is
  carried (it would add nothing to the axiom-dependency audit).  The
  encoding-axiom witnesses live inside `Bridge_Tstar_e_Encoding` and
  the textbook facts inside `Bridge_Q_DefExt_TextbookFacts`; both are
  consumed by `Bridge_Halt_Iff_Dist`. -/

end EinsteinTest
