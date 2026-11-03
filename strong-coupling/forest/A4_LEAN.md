# Finite Dobrushin comparison and the coupling interface (G1)

**Proved / kernel checked (Lean and Mathlib v4.33.0).** Four modules
formalise finite comparison arithmetic, its cost-minimality argument,
the measure-level update interface and existence of a global continuous-cost
minimum on compact metric spaces. They are imported by `YangMills.lean`.
The target is Lemma `comparison` of `main.tex`.

## Implemented results

- `YangMills/StrongCoupling/DobrushinComparison.lean` proves the weighted
  column comparison, its zero-source uniqueness consequence, exponentially
  weighted row decay and the uniform supremum bound for finite index sets.
- `YangMills/StrongCoupling/CouplingMinimality.lean` derives the discrepancy
  recurrence from a minimum of weighted coupling cost when an update fixes
  all other discrepancies. Approximate minimality contributes exactly
  epsilon_i/w_i; simultaneous invariance under all updates is unnecessary.
- `YangMills/StrongCoupling/WassersteinBridge.lean` proves preservation of
  coupling marginals by coupled kernels, integrated update estimates,
  conversion of finite extended integrals to real comparison inequalities,
  observable bounds and decay with an additive floor. The added
  `local_nonimprovement_of_cost` and `cost_minimal_comparison` instantiate
  the finite cost argument with actual discrepancy integrals. The
  measure-level lemmas adapt James Montgomery Lockwood's supplied trimmed
  bridge; the finite arithmetic and cost connection were developed on
  the research fork.
- `YangMills/StrongCoupling/CouplingMinimizer.lean` proves that probability
  couplings with fixed marginals form a nonempty compact set on a compact
  metric space, and that the integral of any continuous real cost attains
  its minimum there. It identifies these couplings with the marginal-based
  predicate of `WassersteinBridge`.

## Remaining specification and limit arguments

**Sketch / open formalisation.** Instantiate the continuous cost with
weighted coordinate distances and identify its ordinary integral with the
finite extended-integral cost. Construct conditional coupled updates
measurably in the boundary data, prove their marginal identities and
specification-dependent one-step estimates, and establish the required
infinite-volume limit. Existence of a global minimiser does not prove a
measurable selection of conditional optimal couplings.

The finite update-to-comparison chain retains positive weights, finiteness
of coordinate discrepancies and preservation of other coordinate
expectations where needed. G1 as a specification-level theorem remains
open. None of these modules establishes a new SU(2) coupling estimate,
a continuum-uniform cube contraction, or continuum existence.

## Validation and scope

**Validation.** The four modules compiled from source in dependency order
against the repository's pinned Lean/Mathlib v4.33.0. The compact minimiser
module emitted only unused-section-variable linter warnings. No `sorry`
or additional axioms were introduced. The entire repository default target
was not rebuilt during this verification pass. The upstream PR changes
only a comment in the checked bridge to remove references to fork-only
research notes; proof declarations are unchanged.

To reproduce the module checks in a checkout with its Mathlib dependencies:

```sh
lake build YangMills.StrongCoupling.DobrushinComparison
lake build YangMills.StrongCoupling.CouplingMinimality
lake build YangMills.StrongCoupling.WassersteinBridge
lake build YangMills.StrongCoupling.CouplingMinimizer
```

The paper sources, release metadata, PDFs and numerical certificates are
outside this contribution's scope.
