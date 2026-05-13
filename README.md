# LLM Einstein Test — Lean 4 Formalization

Formal verification of the five theorems and four corollaries of

> Li, Alex Chengyu. *What the Karpowicz Theorem Does Not Prove:
> A Three-Component Decomposition of the LLM Einstein Test.* 2026.

**Paper:**
- SSRN abstract id [6751920](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6751920)
- Zenodo (concept DOI, all versions): [10.5281/zenodo.20126582](https://doi.org/10.5281/zenodo.20126582)
- Zenodo (v2, current): [10.5281/zenodo.20134745](https://doi.org/10.5281/zenodo.20134745)

## Status

The formalization machine-checks the **structural mathematics** of the
paper end-to-end inside Lean 4 + Mathlib.  Every paper-internal
deduction is a genuine Lean 4 theorem — **zero `sorry`**.

All axioms are atomic minimal units, classified as one of:

* **Cat 2** — external published textbook results (opaque-carrier-bound
  + precise citation).
* **Cat 3** — paper-novel: typed primitive carriers or paper-stated
  atomic defining equations from Li 2026 `\label{thm:undecidable}`.
* **Lean kernel** — `propext`, `Classical.choice`, `Quot.sound`.

The project has **zero Cat 1 axioms** because the Mathlib infrastructure
needed for Mathlib-derivability (K-complexity, Robinson Q, Tarski CAD)
is absent; the three corresponding `gapBlocked` entries in
[`EinsteinTest/Ledger.lean`](EinsteinTest/Ledger.lean) record the
deferred Mathlib derivations.

Every axiom is an atomic minimal unit (no composite bundles).  The
authoritative current inventory of axiom names, citations, and per-
theorem dependencies is the `lake env lean EinsteinTest/AxiomAudit.lean`
output combined with the `#eval` printout at the bottom of
[`EinsteinTest/Ledger.lean`](EinsteinTest/Ledger.lean); see those
sources for the live counts and per-axiom citations.

The paper-level theorems most commonly depend only on the Lean
kernel; `thm_emission` adds the Kolmogorov-complexity bridges, and
`thm_undecidable_sigma01_hard` adds the recursion-theoretic carriers,
defining equations, and textbook bridges.

## File structure

| File | Paper component |
|------|-----------------|
| [`EinsteinTest/Basic.lean`](EinsteinTest/Basic.lean) | Definitions 1–4 (Observational world; Einstein-replacement (E1)/(E2)/(E3) with Beth-definability; Generator + Verifier with strict-refutation soundness; Empirical protocol; Einstein-Test system) |
| [`EinsteinTest/Floor.lean`](EinsteinTest/Floor.lean) | Theorem 1 (Empirical Verification Floor) + Remark `floor-corollaries` |
| [`EinsteinTest/Emission.lean`](EinsteinTest/Emission.lean) | Theorem 2 (Generator KC Emission Lower Bound) + Corollary `rare` + Remark `emission-not-impossible` |
| [`EinsteinTest/Undecidable.lean`](EinsteinTest/Undecidable.lean) | Theorem 3 (Distinguishability Σ⁰₁-hard on r.e. classes; decidable on Tarski class) + Corollary `no-universal` |
| [`EinsteinTest/Decomposition.lean`](EinsteinTest/Decomposition.lean) | Theorem 4 (Three-Component Decomposition) + Corollary `bound-interaction` + Corollary `conditional-feasibility` |
| [`EinsteinTest/SelfVerification.lean`](EinsteinTest/SelfVerification.lean) | Theorem 5 (Self-Verification Impossibility) + Corollary `self-verif-robust` (i–iv) + Corollary `empirical-necessity` + Remark `thm5-substance` |
| [`EinsteinTest/AxiomAudit.lean`](EinsteinTest/AxiomAudit.lean) | Trust audit: prints `#print axioms` for every paper-level theorem |
| [`EinsteinTest/Ledger.lean`](EinsteinTest/Ledger.lean) | Typed gap ledger: `GapStatus` × `InputCategory` orthogonal classification, with one `GapEntry` per atomic axiom, blocked route, and closed top-level result |

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
# Count of `sorry` (expect 0)
grep -rn '\bsorry\b' EinsteinTest/

# Print axiom dependencies of every paper-level theorem
lake env lean EinsteinTest/AxiomAudit.lean

# Print live gap-ledger inventory (status counts, input-category counts)
# — this is the authoritative inventory of atomic axioms, blocked
# routes, and closed top-level results
lake env lean EinsteinTest/Ledger.lean
```

## Audit history

The formalization has been through multiple hostile audit rounds.
The attack history of each axiom (citation revisions, atomic refactors,
prior retractions) is preserved in the `attackHistory` field of the
corresponding `GapEntry` in
[`EinsteinTest/Ledger.lean`](EinsteinTest/Ledger.lean); release-level
milestones are recorded in commit history and git tags.

## Companion paper

| Resource | Identifier |
|----------|------------|
| SSRN abstract id | [6751920](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6751920) |
| Zenodo concept DOI (all versions) | [10.5281/zenodo.20126582](https://doi.org/10.5281/zenodo.20126582) |
| Zenodo v2 DOI (current) | [10.5281/zenodo.20134745](https://doi.org/10.5281/zenodo.20134745) |
| Zenodo v1 DOI | [10.5281/zenodo.20126583](https://doi.org/10.5281/zenodo.20126583) |

The paper accompanies the Lean formalization in the same directory tree
under `companion-einstein-test/einstein_test.tex`.  It is part of the
broader verification-asymmetry research line.

## License

[MIT](LICENSE) © 2026 Alex Li.
