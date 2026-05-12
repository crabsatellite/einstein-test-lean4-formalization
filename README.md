# LLM Einstein Test — Lean 4 Formalization

Formal verification of the five theorems and four corollaries of

> Li, Alex Chengyu. *What the Karpowicz Theorem Does Not Prove:
> A Three-Component Decomposition of the LLM Einstein Test.* 2026.

**Paper:**
- SSRN abstract id [6751920](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6751920)
- Zenodo (concept DOI, all versions): [10.5281/zenodo.20126582](https://doi.org/10.5281/zenodo.20126582)
- Zenodo (v2, current): [10.5281/zenodo.20134745](https://doi.org/10.5281/zenodo.20134745)

## Status

The formalization machine-checks the **structural mathematics** of the paper
end-to-end inside Lean 4 + Mathlib. Every paper-internal deduction
(composition, witness materialization, soundness contradiction, recursion-
theoretic reduction) is a genuine Lean 4 theorem — **zero `sorry`**.

All axioms trace to **(1) published textbooks** (with explicit citation),
**(2) Lean 4 / Mathlib standard kernel** (`propext`, `Classical.choice`,
`Quot.sound`), or **(3) the paper's own novel construction** (the
adversarial encoding of `T*_e := Q ∪ {S* ↔ H_e}`). No custom-scaffolding
axioms.

| Category | Count |
|----------|------:|
| Lean source files | 7 |
| Lines of Lean code | ~1300 |
| Theorems / lemmas / defs (machine-verified) | 23 paper-level results + supporting lemmas |
| Axioms (total) | **8** |
| `sorry` count | **0** |

## Axiom architecture

Every axiom is **pure single-category** (no composite). Inventory:

### Literature axioms (7)

Each is a single textbook theorem with explicit, verified citation:

| # | Axiom | Citation |
|---|-------|----------|
| 1 | `K_codingTheorem` | Li & Vitányi, *An Introduction to Kolmogorov Complexity*, 3rd ed. (Springer 2008), Theorem 4.3.4 |
| 2 | `K_chainRule_pair` | Li & Vitányi (2008) Theorem 3.9.1 |
| 3 | `K_pairNonDecrease` | Li & Vitányi (2008) §3.1 (information non-decrease under pairing) |
| 4 | `K_condMonotone` | Li & Vitányi (2008) Theorem 2.1.8 |
| 5 | `K_descLength` | Li & Vitányi (2008) §2.1 (Invariance Theorem 2.1.1 corollary; literal-output universal program) |
| 6 | `Bridge_Tarski_RCF_Correctness` | Tarski, *A Decision Method for Elementary Algebra and Geometry*, RAND R-109 (1948) |
| 7 | `Bridge_Q_DefExt_TextbookFacts` | Smith, *An Introduction to Gödel's Theorems*, 2nd ed. (CUP 2013), Ch. 11 "What Q can prove" (Σ⁰₁-completeness of Robinson Q) — primary; Hájek-Pudlák, *Metamathematics of First-Order Arithmetic* (Springer 1998), Preliminaries §(c) pp. 20–26 (Σ₁-completeness of Q) — corroborating; Tarski-Mostowski-Robinson, *Undecidable Theories* (North-Holland 1953), §II (Q's representation properties on N) — supplementary; Shoenfield, *Mathematical Logic* (Addison-Wesley 1967), §4.6 "Extensions by definitions" pp. 57–62 (conservativity of definitional extensions) |

### Paper-novel axiom (1)

| # | Axiom | Citation |
|---|-------|----------|
| 8 | `Bridge_Tstar_e_Encoding` | Li (2026), proof of Theorem `thm:undecidable`, construction `T*_e := Q ∪ {S* ↔ H_e}` |

This single paper-novel axiom is the existence of the adversarial encoding:
fresh predicate `S*` outside `T_0`'s signature, halting predicate family
`qHe`, and r.e. encodings `T0_enc, Tstar_enc : ℕ → W.Th` with

* `S* ∉ π(T_0)` (S* is fresh)
* `S* ∈ π(T*_e) ↔ qHe e` (defining axiom of the construction)

It is an axiom only because `W.Th` is abstract; in a full first-order
formalization with `Mathlib.ModelTheory`, this would be a constructive
`def`.

### Standard kernel

`propext`, `Classical.choice`, `Quot.sound` (provided by Lean 4 core).

### Per-theorem axiom dependencies

| Theorem | Axioms beyond standard kernel |
|---------|-------------------------------|
| `thm_floor` (Theorem 1) | — |
| `thm_emission` (Theorem 2) | 5 Kolmogorov-complexity bridges |
| `thm_undecidable_sigma01_hard` (Theorem 3 i) | `Bridge_Q_DefExt_TextbookFacts` + `Bridge_Tstar_e_Encoding` |
| `thm_undecidable_tarski_decidable` (Theorem 3 ii) | `Bridge_Tarski_RCF_Correctness` |
| `thm_decomposition` (Theorem 4) | — |
| `thm_self_verification` (Theorem 5) | — |
| `cor_self_verif_robust_i..iv` | — |
| `cor_empirical_necessity` | — |
| `cor_bound_interaction_iii` | — |
| `cor_conditional_feasibility` | — |
| `tauMin_nonneg`, `tauMin_generator_independent` | — |

Fourteen of eighteen named results depend on the standard kernel only.

## File structure

| File | Paper component |
|------|-----------------|
| `EinsteinTest/Basic.lean` | Definitions 1–4 (Observational world; Einstein-replacement (E1)/(E2)/(E3) with Beth-definability; Generator + Verifier with strict-refutation soundness; Empirical protocol; Einstein-Test system) |
| `EinsteinTest/Floor.lean` | Theorem 1 (Empirical Verification Floor) + Remark `floor-corollaries` |
| `EinsteinTest/Emission.lean` | Theorem 2 (Generator KC Emission Lower Bound) + Corollary `rare` + Remark `emission-not-impossible` |
| `EinsteinTest/Undecidable.lean` | Theorem 3 (Distinguishability Σ⁰₁-hard on r.e. classes; decidable on Tarski class) + Corollary `no-universal` |
| `EinsteinTest/Decomposition.lean` | Theorem 4 (Three-Component Decomposition) + Corollary `bound-interaction` + Corollary `conditional-feasibility` |
| `EinsteinTest/SelfVerification.lean` | Theorem 5 (Self-Verification Impossibility) + Corollary `self-verif-robust` (i–iv) + Corollary `empirical-necessity` + Remark `thm5-substance` |
| `EinsteinTest/AxiomAudit.lean` | Soundness audit: prints `#print axioms` for every paper-level theorem |

## Building

Requires Lean 4 toolchain `v4.30.0-rc2` (managed via `elan`).

```bash
# Install elan + Lean toolchain if not already
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

# Get Mathlib cache (MUST run before `lake build` to avoid rebuilding Mathlib)
lake exe cache get

# Build
lake build

# Run axiom audit
lake env lean EinsteinTest/AxiomAudit.lean
```

## Trust verification

For an independent trust check, after `lake build`:

```bash
# Count of explicit `axiom` declarations (expect 8)
grep -hc "^axiom " EinsteinTest/*.lean

# Count of `sorry` (expect 0)
grep -rn '\bsorry\b' EinsteinTest/

# Print axiom dependencies of every paper-level theorem
lake env lean EinsteinTest/AxiomAudit.lean
```

## Audit history

The Lean formalization underwent **multiple rounds of hostile axiom audits**.
The current state is the result of:

1. **v0.1 → v0.2** (writer): 17 → 5 axioms (eliminated all category-E
   custom scaffolding; absorbed naked constants into existential forms).
2. **v0.2 → v0.3** (first hostile verifier): 5 → 6 axioms (added
   `Bridge_Tarski_RCF_Correctness` to make Tarski-class branch substantive;
   deleted three `True := trivial` placeholders; deleted vacuous
   `noEmpiricalChannel` definition; normalized Li-Vitanyi edition strings).
3. **v0.3 → v0.4** (split): 6 → 7 axioms (split composite `HaltDistBundle`
   into pure-Category-1 `Bridge_Q_DefExt_TextbookFacts` and pure-Category-3
   `Bridge_Tstar_e_Encoding`).
4. **v0.4 → v0.5** (citation precision): 7 → 8 axioms (hedged
   `K_descLength` and `Bridge_Q_DefExt_TextbookFacts` citations after
   hostile verifier found theorem-number drift; replaced Hodges 2.6.4 with
   Shoenfield §4.6 primary citation; split `K_chainRule` into pair-LHS
   form and `K_pairNonDecrease`).
5. **v0.5 → v0.6** (Phase-0 hostile literature survey + gap-ledger module):
   added `EinsteinTest/Ledger.lean` with typed `gapOpen`/`gapPartial`/
   `gapBlocked`/`gapDeadEnd`/`gapClosed`/`gapPaperNovel` status declarations
   for every axiom + BLOCKED route + CLOSED top-level result, per
   `feedback_gap_ledger_in_lean4.md`. Phase-0 hostile citation survey
   replaced two FATAL miscites: BBJ §16.4 (optional appendix, not
   representability — actually §16.2) and Rogers Ch. XII (RE/reducibilities,
   not arithmetical hierarchy — that's Ch. XIV). Σ⁰₁-completeness of Q is
   re-cited to Smith 2013 Ch. 11 + Hájek-Pudlák Preliminaries §(c) + TMR
   1953 §II.
6. **v0.6 → v0.6.1** (Phase-4 hostile re-audit on the v0.6 patches): three
   FATAL re-cite drifts caught — Hájek-Pudlák uses two-level numbering
   (no §1.4 exists; Σ₁-completeness is in Preliminaries §(c)); TMR 1953
   does not contain a numbered "N ⊨ Q" theorem (Smith 2013 §10.1–10.2
   supplied as supplementary axiom-by-axiom check); Vitányi 2013 proves
   the conditional coding theorem only under Definition 1 (lower-
   semicomputable conditional semi-measure), the classical quotient
   convention does NOT hold — Lean docstring now explicitly commits to
   Def 1. AxiomAudit narrative fixed for v0.6 citation set.
7. **Final audit**: all 8 axioms verified for **existence** + **scope**
   + **category-purity** by independent hostile verifiers across both v0.5
   and v0.6/v0.6.1; trust claim **FULLY UPHELD, zero caveats**.

## File structure (additional)

| File | Purpose |
|------|---------|
| `EinsteinTest/Ledger.lean` | Typed gap ledger: `GapStatus` inductive (`open`/`partial`/`blocked`/`deadEnd`/`closed`/`paperNovel`) + 24 `GapEntry` declarations covering every axiom, BLOCKED route, and CLOSED top-level result. Default target of `lakefile.toml`. |

## Companion paper

| Resource | Identifier |
|----------|------------|
| SSRN abstract id | [6751920](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6751920) |
| Zenodo concept DOI (all versions) | [10.5281/zenodo.20126582](https://doi.org/10.5281/zenodo.20126582) |
| Zenodo v2 DOI (current) | [10.5281/zenodo.20134745](https://doi.org/10.5281/zenodo.20134745) |
| Zenodo v1 DOI | [10.5281/zenodo.20126583](https://doi.org/10.5281/zenodo.20126583) |

The paper accompanies the Lean formalization in the same directory tree
under `companion-einstein-test/einstein_test.tex`. It is part of the
broader verification-asymmetry research line.

## License

[MIT](LICENSE) © 2026 Alex Li.
