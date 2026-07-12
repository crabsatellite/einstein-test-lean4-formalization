# LLM Einstein Test - Lean 4 companion formalization

This project accompanies:

> Alex Chengyu Li, *What the Karpowicz Theorem Does Not Prove: A
> Three-Resource Theory of the LLM Einstein Test* (2026).

Paper: [SSRN abstract 6751920](https://papers.ssrn.com/abstract=6751920)

## Formalization scope

The project contains no `sorry` declarations in its derived theorem proofs.
It provides machine-checked support for the paper results identified below;
it does not represent an end-to-end formalization of every result in the paper.

- The strict-refutation set proofs, empirical-floor deduction, and
  no-certification contradiction are checked at an abstract set-theoretic
  level using the Lean kernel and Mathlib.
- Pareto/scalar resource monotonicity, the weighted empirical floor,
  availability--acquisition path monotonicity, E1--E2 candidate-recognition
  hardness, and the deterministic strict-witness feasibility core are
  machine checked.
- The Kolmogorov-complexity theorem is a conditional algebraic derivation
  from five explicitly declared external KC bridge axioms and opaque
  encodings.  The predicate connecting a generator description to a
  probability exponent is an explicit trust boundary.
- The broad-class distinguishability reduction uses abstract carriers,
  paper-construction equations, and external recursion-theoretic bridges.
  It is **not** a formal hardness theorem for the paper's Einstein-candidate
  subclass.
- The optional novelty screen (Beth non-definability plus prediction
  relevance under a declared ablation operator) is not formalised.
- The stochastic confidence layer of the feasibility theorem, the serial
  expected-cost decomposition, the non-stationary search law, and the
  sequential change-of-measure theorem are not formalised here.
  The latter is sourced to Kaufmann, Cappe, and Garivier (2016), Lemma 1,
  and represented as an explicit external assumption in `Ledger.lean`.

The theorem dependencies and formalization inventory are printed by:

```text
lake env lean EinsteinTest/AxiomAudit.lean
lake env lean EinsteinTest/Ledger.lean
```

## Complete manuscript result map

This table covers every numbered theorem, proposition, and corollary in the
paper.  `Exact` means that the Lean statement has the
same direction, scope, and hypotheses in the abstract model.  `Conditional`
means that the derivation is kernel checked but depends on the external or
paper-construction bridges printed by the dependency report.  `Partial`
identifies the portion that is formalized without extending the claim to the
full paper result.

| Paper result | Lean declaration or boundary | Status |
|---|---|---|
| `prop:resource-geometry` | `System.ResourceProfile.scalarise_mono`, `weighted_resource_empirical_floor` | Exact |
| `prop:karpowicz-nonimplication` | Elementary propositional countervaluation in the paper | Paper only |
| `prop:symmetry` | Computability-scope argument in the paper | Paper only |
| `thm:floor` | `thm_floor` | Exact |
| `cor:invariance` | `fixed_environment_invariance` | Exact |
| `thm:dynamic-floor` | `dynamic_floor_of_witness` | Exact in the abstract dynamic model |
| `prop:technology-dominance` | `dynamic_tau_mono`, `dynamic_tau_congr`, `path_completion_mono`, `dynamic_path_tau_mono` | Exact |
| `thm:bayes-floor` | External `Bayesian_change_of_measure` ledger bridge; no Lean probability theorem | Partial |
| `thm:emission` | `thm_emission` | Conditional on five KC bridges and opaque encodings |
| `cor:waiting` | `cor_rare` | Exact real-arithmetic consequence |
| `prop:amplification` | Fixed-search formula and support boundary proved in the paper | Paper only |
| `prop:corpus-shift` | Algebraic comparative static proved in the paper | Paper only |
| `thm:nonstationary-search` | No Lean probability theorem | Partial |
| `thm:dist` | `thm_undecidable_sigma01_hard`, `thm_undecidable_sigma02_upper`, `thm_undecidable_tarski_decidable` | Conditional on the listed recursion, construction, and RCF bridges |
| `thm:candidate-recognition` | `thm_candidate_recognition_sigma01_hard` | Conditional E1--E2 recognition result |
| `prop:no-transfer` | Scope proof in the paper; no promised-verification Lean claim | Paper only |
| `thm:feasibility` | `strict_witness_accepts`, `strict_witness_feasibility` | Partial: deterministic core exact; finite-budget probability layer unformalised |
| `cor:feasibility-boundaries` | Consequences of the paper's quantitative bound | Paper only |
| `thm:serial-decomposition` | Deterministic weighted aggregation only | Partial: expectation layer unformalised |
| `cor:kc-serial-decomposition` | Uses the conditional KC result plus the paper-only expectation layer | Partial |
| `prop:profile` | `resource_profile_empirical_floor` supports clause (iii) only | Partial meta-map |
| `prop:no-cert` | `no_strict_refutation_certification` | Exact |
| `cor:resource-invariance` | Follows directly from `prop:no-cert`; no separate Lean declaration | Paper only |
| `cor:empirical-access` | `empirical_access_required` | Exact |

## Scope boundaries

- The conditional emission bound does not imply positive target support or
  finite discovery time.
- Broad-class distinguishability hardness does not establish hardness for
  verification promised to remain inside the E1--E3 candidate class.
- The optional E3 novelty screen requires a first-order syntax and represented
  ablation operator that are outside the present Lean model.
- The probability and expectation layers marked `Partial` in the table are
  proved in the paper but are not claimed as Lean theorems here.

## Build

Requires the toolchain specified in `lean-toolchain`.

```text
lake exe cache get
lake build
lake env lean EinsteinTest/AxiomAudit.lean
lake env lean EinsteinTest/Ledger.lean
```

## License

MIT, 2026 Alex Li.
