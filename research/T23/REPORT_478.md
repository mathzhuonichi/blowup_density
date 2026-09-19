# Lane 478 — T23 U7 partial report

## 1. Statements

**U7 is not closed.** Seven lemmas are proved: coordinate-box faces lie in the
frontier; zero-boundary-flux divergence integrates to zero; scalar no-slip box
integration by parts; ordinary spatial slice smoothness from the slab convention;
finite difference energy for the original solution records; zero energy implies
pointwise equality on an open domain; and a uniform spatial derivative bound on
compact subslabs. Each theorem prints exactly
`[propext, Classical.choice, Quot.sound]`.

The domain vocabulary and `ClassicalSolutionOmega` block are byte-identical to
`research/T23/Spec.lean`, including every raw field. No pressure equality,
connectedness, new analytic inputs or substitute uniqueness theorem was added.

## 2. Files

- `formalization/NSFormalization/Section3/T23/NoSlipUniqueness.lean`: canonical
  vocabulary/record and four analytic lemmas. No `noSlip_uniqueness` declaration.
- `formalization/NSFormalization/Section3/T23/BoxIntegration.lean`: three proved
  coordinate-box boundary lemmas.
- `research/T23/probes/noslip_uniqueness_closes.lean`: explicitly partial probe.
- `research/T23/probes/box_integration_by_parts_closes.lean`: separate box IBP probe.
- `research/T23/axioms_u7.lean`: audit of all seven theorems.
- `research/T23/ATTEMPTS_U7.md`: every failed Lean approach with exact diagnostics,
  supplier searches, and precise residual propositions.
- `research/T23/T23_SPLIT.md`: U7 partial status line.

Initial skeleton committed as `16ee8e1c`; each closed lemma was committed
incrementally. Work stayed in the assigned worktree; no push, merge or rebase.

## 3. Gaps and error text

**Neither full box uniqueness nor smooth-domain uniqueness is proved.** The
box IBP theorem uses `Icc a b : Set (Fin 3 → ℝ)`; transfer to the Spec's open
Euclidean box remains. A regular-level-domain IBP theorem was not found by the
recorded Mathlib search; its exact residual is in ATTEMPTS. The difference-energy
identity, convection integral estimate, differential inequality and Grönwall
application also remain. These are mathematical obligations, not implemented
claims with suppressed Lean errors.

All errors encountered in implemented lemmas were fixed. Representative exact
diagnostics (full contexts in ATTEMPTS):

```text
Invalid field `mul`: The environment does not contain `HasFDerivAtFilter.mul`
Invalid dotted identifier notation: The name `continuousAt.continuousWithinAt` must be atomic
Unknown identifier `pow_eq_zero`
```

Fixes: import `Mathlib.Analysis.Calculus.FDeriv.Mul`; attach chained dot notation
to its receiver; use `sq_eq_zero_iff.mp`. Other recorded failures involved
product-rule summand order, finite-sum simplification, an underconstrained
integration direction, composition spelling in `rw`, and explicit `norm_inr`.
No failed proof remains in a delivered Lean file.

## 4. Commands and results

Every Lean command sourced `. scripts/lean-env.sh`, ran from `verification/`,
and used `LEAN_NUM_THREADS=6`.

| Command | Result |
|---|---|
| `lake build NSFormalization.Section4.A02.SolutionClass Mathlib.MeasureTheory.Integral.DivergenceTheorem` | Exit 0; dependency closure built first |
| `lake build NSFormalization.Section3.T23.NoSlipUniqueness` | Exit 0; 8816 jobs, dependency warnings only |
| `lake env lean ../formalization/NSFormalization/Section3/T23/NoSlipUniqueness.lean` | Exit 0, zero output |
| `lake env lean ../research/T23/probes/noslip_uniqueness_closes.lean` | Exit 0, zero output |
| `lake env lean ../research/T23/probes/box_integration_by_parts_closes.lean` | Exit 0, zero output |
| `lake env lean ../research/T23/axioms_u7.lean` | Exit 0; all seven lists exactly the standard three axioms |
| `make check` (worktree root) | Exit 0; 52 registered contracts, 45 consistent work items |
| `lake test` | Exit 0; registered Lean tests pass |
| `make test-mutations` (worktree root) | Exit 0; refactor accepted, all three invalid mutations rejected |

The copied Spec block passed a byte-for-byte comparison. Source import traversal
found no path to `Paper1.BoundaryCorollary`. `make check` reports the existing
repository-wide historical admission and source-manifest mismatch but exits 0;
these are not additions in this lane. The literal word `sorry` in the new
module occurs only in a copied Spec provenance comment, not in a proof.

The passing gates certify the partial modules, not the absent uniqueness theorem.
