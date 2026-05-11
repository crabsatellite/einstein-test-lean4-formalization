/-
  EinsteinTest/Emission.lean

  Theorem~\ref{thm:emission} (Generator KC Emission Lower Bound),
  Corollary~\ref{cor:rare}, and Remark~\ref{rem:emission-not-impossible}.

  Companion to: "What the Karpowicz Theorem Does Not Prove" (Li, 2026).

  Statement (informal): for any computable generator `M` and prompt `p`,
  the probability of emitting an Einstein-replacement `T*` is bounded
  above by `2^{-K_*}` where

      K_* := K(T*|D_t) - |M| - |p| - O(log L)

  and `L := K(T*|D_t) + |M| + |p|` is the dominant complexity scale.

  Axioms: Kolmogorov complexity `K` is introduced via a small set of
  single-step typed bridges (universality, conditional coding theorem,
  chain rule, monotonicity-under-conditioning).  Each bridge is a
  textbook lemma; primary citation Li & Vitányi, 3rd ed. (2008), with
  Vitányi 2013 (TCS 501) added for the conditional coding theorem
  where the conditional convention was non-standard prior to 2013:

    * `K_codingTheorem`     ←  Li-Vitányi Thm 4.3.4 (conditional coding theorem);
                                supplementary: Vitányi, *Theoretical Computer
                                Science* 501 (2013), 93–100 (arXiv:1206.0983),
                                explicit conditional-version proof
    * `K_chainRule_pair`    ←  Li-Vitányi Thm 3.9.1 (symmetric-information chain rule, pair-LHS)
    * `K_pairNonDecrease`   ←  Li-Vitányi §3.1 (information non-decrease under pairing;
                                immediate from prefix-free pair-decoding)
    * `K_condMonotone`      ←  Li-Vitányi §3.1 / §3.4 (prefix-`K` analogue of plain-
                                complexity Thm 2.1.8 / Ch 2: extra conditioning cannot
                                raise prefix complexity by more than a constant;
                                immediate by relativizing the universal prefix machine)
    * `K_descLength`        ←  Li-Vitányi §2.1 (immediate consequence of the
                                Invariance Theorem (Thm 2.1.1) via the literal-
                                output universal program: `K(y|z) ≤ |y| + c`;
                                REQUIRES `descLen y` to include self-delimiting
                                overhead — see axiom docstring for convention)

  The single-LHS variant of the chain rule (`K_chainRule_single`) is *derived*
  as a Lean lemma from `K_chainRule_pair`, `K_condMonotone`, and `K_descLength`,
  and is therefore not a separate axiom (per `feedback_lean_axiom_decomposition`:
  no composite axioms).

  *Design choice:* `K` is a single abstract real-valued function on
  an opaque encoding type.  The chain rule and friends are stated as
  inequalities between real numbers over this type; the algebraic
  combination is then a pure-arithmetic chain.  This matches
  `feedback_lean_axiom_decomposition` (single-step typed bridges, no
  composite axioms).
-/

import EinsteinTest.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace EinsteinTest

/-! ### Kolmogorov-complexity bridges. -/

/-- *Universal description object* — the abstract type of strings /
    programs / objects whose Kolmogorov complexity we measure.

    Implementation: `ℕ` is used as a concrete (Gödel-numbering style)
    realisation of the abstract object type.  The bridges below remain
    abstract over `KObj`; only the inhabitation instance and the type
    constructor are concrete.  A more refined formalisation could
    instantiate `KObj` as `List Bool` (binary strings) or
    `Nat.Partrec.Code` without invalidating the algebraic chain in
    `thm_emission`. -/
def KObj : Type := ℕ

instance : Inhabited KObj := ⟨(0 : ℕ)⟩

/-- Encoding of an Einstein-replacement object as a `KObj`.
    Represents a fixed Gödel-numbering / standard FO-formula encoding
    (Li-Vitányi, 3rd ed. (2008), §3.1: every object has a unique
    self-delimiting binary description; the choice of universal prefix
    machine affects the encoding only up to an additive constant). -/
opaque encodeTh : ∀ {W : ObservationalWorld}, W.Th → KObj

/-- Encoding of a data set as a `KObj` (prefix-free concatenation of
    its (countably many) elements, each itself prefix-coded;
    Li-Vitányi, 3rd ed. (2008), §3.1). -/
opaque encodeData : ∀ {W : ObservationalWorld}, Set W.Obs → KObj

/-- Pairing of two encoding objects (used for joint conditioning).
    Represents the standard prefix-free pairing function of
    Li-Vitányi, 3rd ed. (2008), §1.4 / Eq.~(1.7); pair-decoding
    overhead is absorbed into the additive `O(log L)` slack of the
    chain rule. -/
opaque encodePair : KObj → KObj → KObj

/-- *Universal prefix Kolmogorov complexity* `K(x)`
    (Li-Vitányi, 3rd ed. (2008), §3.1; standard notation). The
    length of the shortest binary program for a fixed universal prefix
    machine that outputs `x` and halts. Defined up to an additive
    constant (invariance theorem; Li-Vitányi, 3rd ed. (2008),
    Thm 2.1.1). -/
opaque K : KObj → ℝ

/-- *Conditional prefix Kolmogorov complexity* `K(x | y)`
    (Li-Vitányi, 3rd ed. (2008), §3.1, conditional version of the
    universal prefix complexity). The length of the shortest binary
    program that outputs `x` given `y` as an auxiliary input. -/
opaque Kcond : KObj → KObj → ℝ

@[inherit_doc Kcond]
notation:max "K[" x "|" y "]" => Kcond x y

/-- *Description length* `|y|` of an object `y` (Li-Vitányi, 3rd ed.
    (2008), §1.4: the length of the binary code representing `y`; an
    upper bound on `K(y)` since the literal-output program of length
    `|y| + O(1)` always exists). -/
opaque descLen : KObj → ℝ

/-- *Probability-mass predicate* `μAssignsAtLeast μDesc x k`:
    the conditional semi-measure encoded by `μDesc` assigns
    conditional probability at least `2^{-k}` to `x`.

    *Vitányi Definition 1 convention (commitment).*  Here `μDesc`
    encodes a lower-semicomputable conditional semi-measure
    `m(·|·)` satisfying (a) `Σ_x m(x|y) ≤ 1` for every `y`, (b)
    lower-semicomputability uniformly in `(x, y)`, and (c)
    multiplicative universality among lower-semicomputable
    conditional semi-measures.  Concretely, `μAssignsAtLeast μDesc x k`
    holds iff `m(x|y) ≥ 2^{-k}` where `(x, y)` are the conditioning
    pair encoded into `μDesc` (Vitányi, *Theoretical Computer
    Science* 501 (2013), 93–100, Definition 1).  We deliberately
    do NOT use the classical quotient `m(x,y) / Σ_z m(z,y)`:
    Vitányi 2013 Theorem 2 shows that the conditional coding
    theorem `K(x|y) ≤ -log m(x|y) + O(1)` FAILS under that
    convention.  The Definition-1 convention is mandatory for
    the conditional coding theorem `K_codingTheorem` below to hold;
    every use of `μAssignsAtLeast` in this file presupposes it. -/
opaque μAssignsAtLeast : KObj → KObj → ℝ → Prop

/-- **Bridge 1 (Conditional coding theorem; Li-Vitányi, 3rd ed. (2008),
    Thm 4.3.4; explicit conditional-version proof in Vitányi 2013
    under the Vitányi-Definition-1 conditional convention).**
    There exists a universal additive constant `c` (depending only on
    the universal prefix machine, not on `(x, μDesc, k)`) such that
    `K(x | μDesc) ≤ k + c` whenever `μDesc` encodes a
    Vitányi-Definition-1 conditional lower-semicomputable
    semi-measure `m(·|·)` (i.e. `Σ_x m(x|y) ≤ 1`, lower-semicomputable
    uniformly in `(x, y)`, multiplicatively universal) and the
    encoded `m` assigns `m(x|y) ≥ 2^{-k}` (captured here by
    `μAssignsAtLeast μDesc x k`).

    *Critical convention note.*  The bound `K(x|y) ≤ -log m(x|y) + O(1)`
    is proved in Vitányi 2013 (Theorem 4) ONLY under Definition 1
    (lower-semicomputable conditional semi-measure with
    `Σ_x m(x|y) ≤ 1` and multiplicative universality), NOT under
    the classical quotient `m(x,y) / Σ_z m(z,y)`.  Vitányi 2013
    Theorem 2 explicitly shows that the conditional coding theorem
    FAILS under the classical-quotient convention.  This Lean axiom
    is committed to the Vitányi Definition 1 convention as encoded
    by `μAssignsAtLeast` (see its docstring); under the classical
    quotient the axiom would be unsound.

    *Citation:* Li & Vitányi, *An Introduction to Kolmogorov Complexity
    and Its Applications* (3rd ed., 2008), Theorem 4.3.4 (conditional
    version).  Note: the unconditional coding theorem appears as
    Thm 4.3.3; the conditional version (Thm 4.3.4) was non-standard
    in the literature prior to Vitányi, *Theoretical Computer Science*
    **501** (2013), 93–100 (arXiv:1206.0983), which supplies the
    explicit conditional-version proof (Theorem 4) under Definition 1.
    Cited here as the operative source for the conditional bound. -/
axiom K_codingTheorem :
    ∃ c : ℝ, ∀ (x μDesc : KObj) (k : ℝ),
      μAssignsAtLeast μDesc x k → K[x|μDesc] ≤ k + c

/-- The universal additive constant of the conditional coding theorem,
    extracted via `Classical.choose` from the existential statement
    `K_codingTheorem`. Not a separate axiom — fully derived. -/
noncomputable def K_codingTheorem_const : ℝ := Classical.choose K_codingTheorem

/-- Application form of Bridge 1: the specification given by the
    `Classical.choose_spec` of `K_codingTheorem`. -/
lemma K_codingTheorem_apply (x μDesc : KObj) (k : ℝ)
    (h : μAssignsAtLeast μDesc x k) :
    K[x|μDesc] ≤ k + K_codingTheorem_const :=
  Classical.choose_spec K_codingTheorem x μDesc k h

/-- **Bridge 2 (Symmetric-information chain rule, pair-LHS; Li-Vitányi,
    3rd ed. (2008), Thm 3.9.1).**
    There exists a *slack function* `slack : ℝ → ℝ` (`O(log L)` overhead
    from pair-encoding and chain-decomposition) such that, for every
    pair `(x, y)` conditioned on `z`, the chain-rule decomposition

    `K((x, y) | z) ≤ K(x | y, z) + K(y | z) + slack L`

    holds.

    *Citation:* Li & Vitányi, *An Introduction to Kolmogorov Complexity
    and Its Applications* (3rd ed., 2008), Theorem 3.9.1
    (symmetric-information chain rule, prefix-complexity version);
    plain-complexity version: Li & Vitányi, 3rd ed. (2008), Eq. (3.21). -/
axiom K_chainRule_pair :
    ∃ slack : ℝ → ℝ,
      ∀ (x y z : KObj) (L : ℝ),
        K[encodePair x y | z]
          ≤ K[x | encodePair y z] + K[y | z] + slack L

/-- The chain-rule slack function, extracted via `Classical.choose`
    from the existential `K_chainRule_pair`. Not a separate axiom. -/
noncomputable def K_chainRule_slack : ℝ → ℝ := Classical.choose K_chainRule_pair

/-- Application form of the pair-LHS chain rule. -/
lemma K_chainRule_apply (x y z : KObj) (L : ℝ) :
    K[encodePair x y | z]
      ≤ K[x | encodePair y z] + K[y | z] + K_chainRule_slack L :=
  Classical.choose_spec K_chainRule_pair x y z L

/-- **Bridge 2' (Information non-decrease under pairing; Li-Vitányi,
    3rd ed. (2008), §3.1).**
    There exists an additive constant `c` such that

    `K(x | z) ≤ K(encodePair x y | z) + c`.

    *Citation:* Li & Vitányi, 3rd ed. (2008), §3.1: immediate from
    prefix-free pair-decoding, `K(x|z) ≤ K(⟨x,y⟩|z) + c`.  A universal
    prefix program for `x` is obtained from a program for `(x, y)` by
    appending a fixed projection routine (extract first component,
    length `O(1)`), yielding the additive overhead `c`.  Equivalently:
    information cannot decrease under pairing, since the first component
    is recoverable from the pair via the standard `encodePair` decoder.

    *Decomposition rationale (per `feedback_lean_axiom_decomposition`):*
    This is a single-step typed bridge separate from `K_chainRule_pair`;
    decomposed out so that the single-LHS variant of the chain rule
    can be DERIVED inside Lean (see `K_chainRule_single_apply`) rather
    than axiomatized as a composite. -/
axiom K_pairNonDecrease :
    ∃ c : ℝ, ∀ (x y z : KObj),
      K[x | z] ≤ K[encodePair x y | z] + c

/-- The pair-non-decrease constant, extracted via `Classical.choose`
    from `K_pairNonDecrease`.  Not a separate axiom. -/
noncomputable def K_pairNonDecrease_const : ℝ :=
  Classical.choose K_pairNonDecrease

/-- Application form of Bridge 2'. -/
lemma K_pairNonDecrease_apply (x y z : KObj) :
    K[x | z] ≤ K[encodePair x y | z] + K_pairNonDecrease_const :=
  Classical.choose_spec K_pairNonDecrease x y z

/-- **Derived single-LHS chain rule.**  From the pair-LHS chain rule
    `K_chainRule_pair` (Thm 3.9.1) and information non-decrease under
    pairing `K_pairNonDecrease` (§3.1 corollary), we obtain

    `K(x | z) ≤ K(x | (y, z)) + K(y | z) + (slack L + c_pair)`.

    NOT a separate axiom — derived via `linarith` from
    `K_pairNonDecrease_apply` (gives `K[x|z] ≤ K[(x,y)|z] + c_pair`) and
    `K_chainRule_apply` (gives `K[(x,y)|z] ≤ K[x|(y,z)] + K[y|z] + slack L`).
    The total slack is `K_chainRule_slack L + K_pairNonDecrease_const`. -/
lemma K_chainRule_single_apply (x y z : KObj) (L : ℝ) :
    K[x | z]
      ≤ K[x | encodePair y z] + K[y | z]
        + (K_chainRule_slack L + K_pairNonDecrease_const) := by
  have h1 : K[x | z] ≤ K[encodePair x y | z] + K_pairNonDecrease_const :=
    K_pairNonDecrease_apply x y z
  have h2 :
      K[encodePair x y | z]
        ≤ K[x | encodePair y z] + K[y | z] + K_chainRule_slack L :=
    K_chainRule_apply x y z L
  linarith

/-- **Bridge 3 (Conditioning monotonicity; prefix-`K` analogue of
    Li-Vitányi Ch 2 plain-complexity result, 3rd ed. (2008), §3.1 / §3.4).**
    There exists an additive constant `c` such that adding side-
    information `z` cannot raise the conditional complexity by more
    than `c`:

    `K(x | y, z) ≤ K(x | y) + c`.

    *Citation:* Li & Vitányi, *An Introduction to Kolmogorov Complexity
    and Its Applications* (3rd ed., 2008), §3.1 / §3.4: the prefix-`K`
    analogue of the Ch 2 plain-`C` result Thm 2.1.8 (extra conditioning
    cannot raise prefix complexity by more than a constant; immediate
    by relativizing the universal prefix machine). -/
axiom K_condMonotone :
    ∃ c : ℝ, ∀ (x y z : KObj),
      K[x|encodePair y z] ≤ K[x|y] + c

/-- The conditioning-monotonicity constant, extracted via
    `Classical.choose` from `K_condMonotone`. Not a separate axiom. -/
noncomputable def K_condMonotone_const : ℝ := Classical.choose K_condMonotone

/-- Application form of Bridge 3. -/
lemma K_condMonotone_apply (x y z : KObj) :
    K[x|encodePair y z] ≤ K[x|y] + K_condMonotone_const :=
  Classical.choose_spec K_condMonotone x y z

/-- **Bridge 4 (Description-length bound; Li-Vitányi, 3rd ed. (2008),
    §2.1).**
    There exists an additive constant `c` (universal-machine overhead
    for the print-y program) such that the conditional complexity of
    `y` given any context `z` is bounded by `|y| + c`:

    `K(y | z) ≤ |y| + c`.

    *Citation:* Li & Vitányi, *An Introduction to Kolmogorov Complexity
    and Its Applications* (3rd ed., 2008), §2.1.  Immediate consequence
    of the Invariance Theorem (Thm 2.1.1): the universal prefix machine
    `U` simulates the literal-output program `y ↦ y` (length `|y| + O(1)`),
    giving `K(y | z) ≤ |y| + c` for a universal additive constant `c`
    depending only on `U`.  (Note: Thm 2.1.1 itself is the invariance
    claim `∀ universal K_1, K_2, ∃ c, |K_1 - K_2| ≤ c`; the description-
    length corollary is the standard immediate-consequence application
    of Thm 2.1.1 and appears throughout §2.1 / §3.1 as a basic
    upper bound.)

    *REQUIRES `descLen y` to include self-delimiting overhead*: i.e.,
    `descLen y` must be the length of a prefix-free code for `y`, not
    raw `|y|`.  Without self-delimiting overhead the textbook bound is
    `K(y | z) ≤ |y| + 2 log |y| + c` (the `2 log |y|` term is the
    self-delimiting encoding of the length prefix).  The
    `descLen`-includes-prefix-coding convention is the standard
    interpretation in this formalization and matches §3.1's
    self-delimiting binary description; under that convention the
    bound `K(y|z) ≤ descLen y + c` is exact. -/
axiom K_descLength :
    ∃ c : ℝ, ∀ (y z : KObj),
      K[y|z] ≤ descLen y + c

/-- The description-length constant, extracted via `Classical.choose`
    from `K_descLength`. Not a separate axiom. -/
noncomputable def K_descLength_const : ℝ := Classical.choose K_descLength

/-- Application form of Bridge 4. -/
lemma K_descLength_apply (y z : KObj) :
    K[y|z] ≤ descLen y + K_descLength_const :=
  Classical.choose_spec K_descLength y z

/-! ### Theorem statements. -/

variable {W : ObservationalWorld}

/-- The *KC-corrected emission exponent* `K_*` for an Einstein-
    replacement candidate `Tstar` against a generator `M` and prompt
    `p`, observed at time `t` (with data `D_t`).

    `K_*(T*, M, p, D_t, L) := K(T* | D_t) - |M| - |p|
                              - 2·K_chainRule_slack L
                              - K_pairNonDecrease_const
                              - K_codingTheorem_const
                              - 2·K_condMonotone_const
                              - 2·K_descLength_const`.

    The two `K_chainRule_slack L` terms reflect two chain-rule
    applications; the single `K_pairNonDecrease_const` reflects the
    one outer use of the derived single-LHS chain rule (which absorbs
    one information-non-decrease application); the doubled
    `condConst`/`descConst` reflect that the inner chain decomposition
    `K((M,p)|D_t)` involves a separate conditioning-monotonicity and
    description-length pair. -/
noncomputable def KStar (Tstar : W.Th) (M p : KObj) (Dt : Set W.Obs)
    (L : ℝ) : ℝ :=
  K[encodeTh Tstar | encodeData Dt]
    - descLen M
    - descLen p
    - 2 * K_chainRule_slack L
    - K_pairNonDecrease_const
    - K_codingTheorem_const
    - 2 * K_condMonotone_const
    - 2 * K_descLength_const

/-- **Theorem~\ref{thm:emission}: Generator KC emission lower bound.**

    For any computable generator `M`, prompt `p`, and Einstein-
    replacement `R`, the negative log-probability of emitting `R.Tstar`
    is bounded below:

    `-log₂ Pr[M(p) = R.Tstar] ≥ K_*`.

    Formal Lean content: the chained-bridges inequality
    `K(T* | D_t) ≤ k + |M| + |p| + 2·chainSlack + codingConst + condConst + descConst`
    where `k = -log₂ Pr[M(p) = T*]`.  Rearranging:
    `k ≥ K_*`.

    Proof: chain `K_chainRule_pair` (once for `(M, p | D_t)` directly,
    and once via the derived `K_chainRule_single_apply` for the outer
    `(T*, (M,p) | D_t)`) with `K_condMonotone`, `K_codingTheorem`,
    `K_descLength`, and `K_pairNonDecrease` (the latter absorbed into
    the derived single-LHS lemma).

    *Lean statement:* `K(T* | D_t) ≤ k + (descLen M + descLen p) + ...`
    where `k` is the witness probability-exponent satisfying
    `μAssignsAtLeast (generator-desc) (encodeTh T*) k`. -/
theorem thm_emission
    (Tstar : W.Th) (M p : KObj) (Dt : Set W.Obs) (L k : ℝ)
    (hCoding : μAssignsAtLeast (encodePair M p) (encodeTh Tstar) k) :
    K[encodeTh Tstar | encodeData Dt]
      ≤ k + descLen M + descLen p
        + 2 * K_chainRule_slack L
        + K_pairNonDecrease_const
        + K_codingTheorem_const
        + 2 * K_condMonotone_const
        + 2 * K_descLength_const := by
  -- Apply derived single-LHS chain rule with (x, y, z) =
  --   (encodeTh Tstar, encodePair M p, encodeData Dt).
  -- Get: K(T*|D_t) ≤ K(T*|(M,p), D_t) + K((M,p)|D_t)
  --              + (chainSlack L + pairNonDecreaseConst).
  have h_chain1 :
      K[encodeTh Tstar | encodeData Dt]
        ≤ K[encodeTh Tstar | encodePair (encodePair M p) (encodeData Dt)]
          + K[encodePair M p | encodeData Dt]
          + (K_chainRule_slack L + K_pairNonDecrease_const) :=
    K_chainRule_single_apply (encodeTh Tstar) (encodePair M p) (encodeData Dt) L
  -- Apply conditioning monotonicity:
  -- K(T*|(M,p), D_t) ≤ K(T*|(M,p)) + condConst.
  have h_cond :
      K[encodeTh Tstar | encodePair (encodePair M p) (encodeData Dt)]
        ≤ K[encodeTh Tstar | encodePair M p] + K_condMonotone_const :=
    K_condMonotone_apply (encodeTh Tstar) (encodePair M p) (encodeData Dt)
  -- Apply conditional coding theorem with witness k:
  -- K(T*|(M,p)) ≤ k + codingConst.
  have h_coding :
      K[encodeTh Tstar | encodePair M p] ≤ k + K_codingTheorem_const :=
    K_codingTheorem_apply (encodeTh Tstar) (encodePair M p) k hCoding
  -- For K(M,p | D_t), apply chain-rule (pair LHS variant):
  -- K((M,p) | D_t) ≤ K(M | p, D_t) + K(p | D_t) + chainSlack L.
  have h_chain2 :
      K[encodePair M p | encodeData Dt]
        ≤ K[M | encodePair p (encodeData Dt)]
          + K[p | encodeData Dt]
          + K_chainRule_slack L :=
    K_chainRule_apply M p (encodeData Dt) L
  -- K(M | (p, D_t)) ≤ K(M | p) + condConst ≤ |M| + descConst + condConst.
  have h_desc_M_via_cond :
      K[M | encodePair p (encodeData Dt)]
        ≤ descLen M + K_descLength_const + K_condMonotone_const := by
    have h1 : K[M | encodePair p (encodeData Dt)] ≤ K[M|p] + K_condMonotone_const :=
      K_condMonotone_apply M p (encodeData Dt)
    have h2 : K[M|p] ≤ descLen M + K_descLength_const := K_descLength_apply M p
    linarith
  have h_desc_p : K[p | encodeData Dt] ≤ descLen p + K_descLength_const :=
    K_descLength_apply p (encodeData Dt)
  -- Combine: chain the six inequalities.  The arithmetic is purely
  -- linear in the bridge-constants and the chain-rule slack, so
  -- `linarith` closes it.
  --
  -- Trace:
  --   K(T*|D_t)
  --     ≤ K(T*|(M,p),D_t) + K((M,p)|D_t) + chainSlack L                 [h_chain1]
  --     ≤ K(T*|(M,p)) + condConst + K((M,p)|D_t) + chainSlack L         [h_cond]
  --     ≤ k + codingConst + condConst + K((M,p)|D_t) + chainSlack L     [h_coding]
  --     ≤ k + codingConst + condConst + chainSlack L
  --         + K(M|(p,D_t)) + K(p|D_t) + chainSlack L                    [h_chain2]
  --     ≤ k + codingConst + condConst + 2·chainSlack L
  --         + (descLen M + descConst + condConst)
  --         + (descLen p + descConst)                                   [h_desc_M_via_cond + h_desc_p]
  --     = k + descLen M + descLen p + 2·chainSlack L
  --         + codingConst + 2·condConst + 2·descConst.
  linarith [h_chain1, h_cond, h_coding, h_chain2, h_desc_M_via_cond, h_desc_p]

/-- **Corollary~\ref{cor:rare}.** If `Pr[M(p) = T*] ≤ 2^{-K_*}` with
    `K_* > 0`, then the expected number of i.i.d. samples `N` before
    the first emission satisfies `E[N] ≥ 2^{K_*}` (geometric waiting).

    *Lean statement:* given `0 < p ≤ 2^{-K_*}` (the per-sample
    probability), the geometric expectation `1/p ≥ 2^{K_*}`. -/
theorem cor_rare (KStarVal p : ℝ) (hp_pos : 0 < p)
    (hp_le : p ≤ (2 : ℝ) ^ (-KStarVal)) :
    (2 : ℝ) ^ KStarVal ≤ 1 / p := by
  -- 1/p ≥ 1/(2^{-K_*}) = 2^{K_*}.
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ KStarVal := Real.rpow_pos_of_pos h2pos _
  rw [le_div_iff₀ hp_pos]
  have h_add : (2 : ℝ) ^ KStarVal * (2 : ℝ) ^ (-KStarVal) = 1 := by
    rw [← Real.rpow_add h2pos, add_neg_cancel, Real.rpow_zero]
  calc (2 : ℝ) ^ KStarVal * p
      ≤ (2 : ℝ) ^ KStarVal * (2 : ℝ) ^ (-KStarVal) :=
        mul_le_mul_of_nonneg_left hp_le hpow_pos.le
    _ = 1 := h_add

/-- **Remark~\ref{rem:emission-not-impossible}.** Three escape routes
    make `K_*` non-positive (bound vacuous):
    (i) test-time search: the sampling exponent in `cor_rare` becomes
        finite once `N ≥ 2^{K_*}` is afforded;
    (ii) ripe innovations: `K(T*|D_t)` is small (e.g., the data
         already encodes `T*` up to a short pointer);
    (iii) continual training: growing `D_t` reduces `K(T*|D_t)`.

    *Lean-level witness:* for `KStarVal ≤ 0`, `2 ^ KStarVal ≤ 1` so
    the `cor_rare` bound is vacuous (every protocol with a single
    sample trivially satisfies `1/p ≥ 1 ≥ 2^{K_*}` when `K_* ≤ 0`). -/
theorem rem_emission_not_impossible (KStarVal : ℝ) (hKneg : KStarVal ≤ 0) :
    (2 : ℝ) ^ KStarVal ≤ 1 := by
  have h0 : (2 : ℝ) ^ (0 : ℝ) = 1 := Real.rpow_zero 2
  rw [← h0]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hKneg

end EinsteinTest
