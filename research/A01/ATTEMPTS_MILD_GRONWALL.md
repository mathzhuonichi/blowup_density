# Lane 196: finite-order mild energy

## Outcome and scope

This lane does **not** close the general-data analytic input. It proves a
conditional reduction with ONE analytic predicate, `FiniteMildEnergy`, whose
complete Lean statement is in `MildGronwall.lean` and `REPORT_196.md`.
The review fix makes the permitted solenoidal-interface re-cut in
`AprioriFamily.lean`; no other pre-existing Lean module is modified. No
all-order constructor or classical-solution energy theorem is applied to a
mild competitor.

## Positive results

* Full finite word family: `SobolevWord (q+1)` contains every ordered cylinder
  derivative through order `q+1`. The constant Euclidean metric is the identity
  on `LiftL2 1`. Its scalar root energy is exactly
  `sqrt (sum W, norm (u.val W)^2)`.
* The cylinder norm is the maximum of the word norms. Thus the concrete root
  energy majorizes it and is at most
  `mildNormConstant q * norm u`, where
  `mildNormConstant q = sqrt (Fintype.card (SobolevWord (q+1)))`.
  This is a proved explicit nonnegative norm-comparison constant, independent
  of all data and times. It is not asserted to supply the energy hypothesis.
* `euclidean_full_word_limit` instantiates
  `regularizedValueFamily_tendsto` and `metricPath_tendsto` at exactly that
  complete word family and the identity metric. This is uniform convergence
  on the entire closed time window, including its endpoints and zero norms.
* `quadratic_regularized_word` obtains the actual top-order regularized word
  PDE from `regularized_word_hasDerivAt`. The nonlinear source is the existing
  `sourcePath (D.comp (timeInclusion hTS)) u`. Its Duhamel equation is
  definitionally the quadratic fixed-point equation. No derivative of the
  unregularized top-order path is assumed.
* `outer_tame_low` consumes `A04.outerSobolevNormAt_le`, which consumes
  `A03.outerProductTame`. The field's low-order comparison is explicitly a
  premise; this is not a proof of the finite-order descent bridge.
* `inner_mild_energy` uses only the Hilbert-space algebraic theorem
  `A04.inner_energy_Rhigh`, followed by `young_high_real`. These are generic
  carrier theorems, not classical-solution energy lemmas.
* Exact arithmetic: the unabsorbed cross term is
  `A*(16*l)*sqrt(x)*g`. Absorbing `nu*g^2` yields
  `d <= 2*((A^2/(4*nu))*(256*l^2)*x + b*sqrt(x))`.
  Hence no discrepancy in the factor 256 is introduced.
* The scalar square-root lemma, continuity of the lowered driver, and the
  clamped-path bookkeeping give exactly the original `MildGronwall` conclusion.
  Both base-family corollaries then follow from lane 193. They remain conditional.

## Vendor audit and the residual

Read `Euler/MildMajorantEnergy.lean`, its `PDEMajorantLimit`,
`RegularizedMetricPaths`, `RegularizedEnergyFamily`, `RegularizedWordEquation`,
`RegularizedWordTime` prerequisites, `WeightedCylinderEnergy`'s metric growth
coefficient, and the `CorrectionMildEnergy` consumer. Searched all of
`Section4/{D01,A03,A04,A01,C01}` for mild/regularized/metric/energy interfaces.
The proof does not treat the already proved word PDE as a missing fact.

`mild_majorized_energy_subinterval` has additional substantive inputs:

1. `hu`, `hp`, `hz`: divergence/gradient constraints;
2. `U`, `F`, `P`: higher Bochner-time state, source and pressure representatives,
   with approximation convergence and truncation identities;
3. a bound on its **forcing family**, not merely its metric growth coefficient.

It concludes a root-energy integral inequality containing the norm of that
forcing family. It is not an unabsorbed dissipative tensor inequality. Setting
the metric to identity does not identify or bound the differentiated nonlinear
forcing by itself. In particular, a simple norm estimate on the top-order
source leaves a derivative to absorb; the theorem's displayed conclusion has
already dropped dissipation.

At full cutoff `q+1`, choose external order `N = q − 5`, so `N + 6 = q + 1`;
the wrapper remains unusable directly because it is specific to
`CorrectionData`/`SpatialBudget`.

The review re-cut makes solenoidality explicit in both `MildGronwall` and
`FiniteMildEnergy` and threads it through the family helpers. This resolves the
datum-interface mismatch; it does not supply the remaining regularized/Bochner
energy construction.

The residual is therefore the construction of the scalar envelope in
`FiniteMildEnergy`, with data-independent quantitative constants. Its `x` is
an **envelope**, not asserted to be the actual word energy or norm squared.
It is continuous on the closed interval and differentiable only in its
interior, with an unabsorbed energy estimate. This allows using a differentiable
scalar majorant after a regularized/Bochner energy argument; it does not assert
that a raw finite-Sobolev energy is everywhere differentiable. No time extension
is required to be differentiable at or beyond the endpoint.

`E` and `A` in the conditional theorem are fixed parameters; only `0 <= E` is
needed for the scalar argument and `C=A^2/(4*nu)` is automatically nonnegative.
The explicit word comparison constant is available, but no general-data
choice of `E,A` satisfying the residual is proved. This is a substantial
analytic residual, not a claim that only numerical simplification remains.

## Satisfiability and negative examples

The conformance file proves `FiniteMildEnergy` for zero initial datum and zero
force, every order, every competitor and every subwindow of `[0,1]`, without
assuming the predicate. Uniqueness identifies any competitor with zero; the
witnesses are `x=d=g=0`. The example actually applies `hb_of_base'` with
`E(q)=1`, `A(q)=0`, `C(q)=0`, and base radius zero.

A separate nonzero scalar check uses `x(t)=(1+t)^2`, `d(t)=2*(1+t)`, `g=0`,
`A=0`, `b=1` for `t>=0`. Its unabsorbed bound is equality. This demonstrates
that the scalar requirements do not impose stationarity. It is **not** a
nonzero Navier–Stokes witness for the full quantified hypothesis; that witness
has not been constructed.

A kernel-checked negative example disproves unrestricted monotonicity of
`ENNReal.toReal`: take `1 <= top`, while `toReal 1 = 1 > 0 = toReal top`.
Thus the finiteness assumptions of the real tame transport were retained.

Rejected routes:

* A03's field-side tensor inequality alone is not a cylinder mild-energy
  estimate; it does not supply the pairing/descent/source identities.
* Classical `highOrder_bddAbove_of_kbnd` cannot consume a finite-order mild
  path. No such application is used.
* Constructing an all-order classical path from `hb` before proving `hb` is
  circular. The delivered import/proof uses no such constructor.
* Forcing is at order `q+1`, exactly as lane 193 states it. No order-`q` norm
  is substituted for it.

## Diagnostics, including resolved attempts

The requested review is absent in this worktree:

```
sed: can't read research/A01/REVIEW_193-A01-a3-m2-bounds.md: No such file or directory
```

The route was reconstructed from the supplied task, lane-193 report, and
vendor statements. No files outside this worktree were used to substitute a
possibly different review version.

Initial scalar endpoint simplification produced:

```
Type mismatch: After simplification, term hh has type
  sqrt (x (projIcc 0 T hT t)) <= sqrt (x (projIcc 0 T hT 0)) + ...
but is expected to have type
  sqrt (x t) <= sqrt (x <0, ...>) + ...
```

Resolved by passing the explicit membership proofs to `projIcc_of_mem`.

A direct continuity proof through joint metric/operator continuity produced:

```
(deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached
```

Resolved by using the proved finite sum-of-squares formula and continuity of
each `wordOperator`; no heartbeat option was added.

The zero derivative's initial `simpa` encountered different inferred real
module presentations. `change HasDerivAt (fun _ : Real => 0) 0 t` followed by
`exact hasDerivAt_const t 0` checked. The final audit has no placeholder
axioms. All reported transient compiler errors are resolved; the remaining
analytic gap is an explicit theorem premise, not an unreported compiler error.

## Final validation

Module build passed (inherited dependency warnings are replayed); direct Lean
check of the module emitted zero bytes. The conformance file passed with 19
exact three-axiom reports and all examples. `make check`, `lake test`, and
`make test-mutations` passed; the latter accepted the implementation refactor
and rejected the three invalid mutations. No heartbeat options or forbidden
proof tokens occur in the new Lean files. See `REPORT_196.md` for commands.
