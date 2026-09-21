# Lane 503 — P21 Route B unit B0 report

Status: **B0 closed; P6 remains Partial.**  This lane supplies norm/energy
bridges, fixed-force compact-window caps, and type-checked target statements.
It does not prove H¹-uniform restart or change article coverage.

## 1. Statements

The whole-space module proves, for every smooth compactly supported real
three-vector field `z`,

```text
(sobolevENorm 1 z).toReal²
  = l2EnergyR z + gradientEnergyR z

(sobolevENorm 2 z).toReal²
  = l2EnergyR z + 2 * gradientEnergyR z + hessianEnergyR z
  = (sobolevENorm 1 z).toReal² + gradientEnergyR z + hessianEnergyR z.
```

The periodic module proves the identical formulas with
`periodicSobolevENorm`, normalized cube integrals, and all ordered first and
second partials.  Both modules first prove a generic exact Fourier-energy
identity; the coefficient `2` at order two is forced by the registered
inhomogeneous weight `(1+|ξ|²)²`.

For each domain, `forceL2CapR/T f S` is the actual supremum of the spatial
`L²` slice norm on `[0,S+1]`.  A force in the corresponding fixed-force class
has finite cap for `S ≥ 0`, and every restart window
`t₀ ∈ [0,S]`, `t ∈ [0,1]` is bounded by it, both pointwise and as a literal
iterated supremum.  The shifted-force statements use the same cap.  On the
torus, `timeShiftT` is proved smooth and periodic; no false shifted
`forceClassT` membership is asserted.

`Targets.lean` defines, without proof, the exact registered-vocabulary Props
`h1RestartR`, `h1RestartT`, `h1UniformEndpointR`, and
`h1UniformEndpointT`.  In both restart targets one positive `δ` precedes the
restart time and datum.  The whole-space endpoint has the strict maximal
lifespan conclusion; the periodic endpoint returns a larger classical
solution with exact velocity and normalized-pressure overlap.

## 2. Files

New formalization modules:

- `formalization/NSFormalization/Section4/A04/H1Bridges.lean`
- `formalization/NSFormalization/Section3/T11/H1Bridges.lean`

New research deliverables:

- `research/P21/Targets.lean`
- `research/P21/probes/b0_closes.lean`
- `research/P21/axioms_b0.lean`
- `research/P21/ATTEMPTS_B0.md`
- `research/P21/P6_SPLIT.md`
- `research/P21/REPORT_503.md`

Existing files changed:

- `formalization/blueprint/entrypoints.json`: both proof modules added.
- `formalization/blueprint/AXIOM_AUDIT.json`: refreshed source hash/count after
  a successful article audit.

No contract, binding, test, proof-graph status, guide coverage, or registry
entry is changed.  The pre-existing untracked collaboration brief is left
untouched.

## 3. Gaps and compile findings

B1–B5 remain pending, so P6 remains Partial.  In particular, this lane does
not prove the general convection interpolation/Young estimate, the ODE
barrier, endpoint monotone-limit integrability, the maximal-lifespan
contradiction, or the final restart/registration statements.  It does not use
T20's critical-smallness absorption and does not claim a lower bound for
`A01.localHorizon'`.

The meaningful compile findings were:

- opening `D01.Homogeneous` wholesale produced
  `Ambiguous term SpatialField` (and analogous datum/force ambiguities); only
  the compact-component declarations are now opened;
- an unparenthesized integral binder caused the Hessian sum to be parsed inside
  the preceding integral; explicit parentheses fixed the exact H² formula;
- natural-zero force paths needed explicit `Nat.cast_zero` conversions at the
  duplicate A02/D01 and periodic datum seams;
- the first external probe reported
  `object file '.../H1Bridges.olean' ... does not exist` because direct Lean
  checking does not install the object; `lake build` resolved it;
- the final probe typo was
  `Unknown identifier timeShiftT`; the consumer now uses the canonical
  `Section3.T11.timeShiftT` qualification.

All residual implementation details and carrier choices are recorded in
`ATTEMPTS_B0.md`.

## 4. Commands and results

- `lake build NSFormalization.Section4.A04.H1Bridges
  NSFormalization.Section3.T11.H1Bridges`: exit 0,
  `Build completed successfully (10072 jobs)`; only pre-existing replayed
  upstream warnings.
- Direct `lake env lean` on both new formalization modules: exit 0, zero output.
- Direct `lake env lean ../research/P21/Targets.lean`: exit 0, zero output.
- Direct `lake env lean ../research/P21/probes/b0_closes.lean`: exit 0, zero
  output.
- `lake env lean ../research/P21/axioms_b0.lean`: exit 0; all 23 printed
  declarations depend on exactly `[propext, Classical.choice, Quot.sound]`.
- `python3 experiments/audit_article_axioms.py --build --output-dir
  tmp/article-audit --workers 2`: exit 0; `56 declarations; 27 article
  entries; 0 forbidden-axiom results`.  The reviewed report differed from the
  tracked audit only in source hash and source-file count, which were updated.
- `make check`: exit 0.  Blueprint check reports 41 proof nodes, 27
  article/guide mappings, and 2241 source modules; contract policy ran 11 tests,
  all passing.
- `git diff --check`: passed before documentation assembly and is rerun at
  final handoff.
