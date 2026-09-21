# Lane 189 third fix — landed pressure supply and A01 constructor pipeline

## 1. Result and scope

Rebased onto `origin/erenup/integration` at `509bc12`. Lane 180's
`ConstructorAssembly.lean` is now imported by `PressureRegularity.lean`; the
temporary local copy of `PressureSupply` was deleted. Its binder order already
matches `pressureSupply_of_pieces` exactly (`hpairs` then `hpaths`), so the
theorem proves the landed definition without an adapter or weakened contract.

The pressure theorem still has no extra projector, residual-agreement, or
endpoint-time hypothesis. It accepts the smooth velocity representative with
its a.e. slice equality and slab smoothness, and supplies the pressure-gradient
representative required by lane 180. No pre-existing module other than
`PressureRegularity.lean` was edited; no `sorry` or `axiom` was introduced.

## 2. Four pieces and representative transport

* P4a / lane 194 supplies the complement carrier, all-order datum paths, joint
  smooth complement representative, and a.e. slice identity.
* P4b / lane 195 supplies bounded-evaluation temporal differentiation and
  `interior_momentum_identity_of_datums`.
* P4c / lane 197 supplies `hprojected_of_cylinder''` and
  `residualDatum_jointRepresentative`, closing the canonical projector and
  physical-residual comparisons.
* P4d / lane 189 supplies zero-order `MemLp`, the Fourier Helmholtz converse,
  representative transport, and `pressureSupply_of_pieces`.

`pressureGradientOfVelocity_eq_of_slices` upgrades a.e. slice equality using
spatial continuity. Spatial derivatives agree on whole slices, while ambient
time derivatives agree locally only at interior times. Thus `MemLp` and
`HasSymmetricJacobian` hold on `Ico 0 S`, and the momentum identity is required
only on `Ioo 0 S`.

## 3. A01 milestone probe and exact hypotheses

`probes/a01_constructor_pipeline.lean` imports the landed constructor and the
pressure module. It contains three positive checks:

* `pressure_pipeline` produces the canonical `PressureSupply` field.
* `local_constructor_pipeline` destructs that supply and applies
  `carrierConstructor_of_localTheory` directly.
* `a01_constructor_pipeline` passes `pressureSupply_of_pieces` as the pressure
  argument of `rows_from_constructor_full`, producing a classical solution and
  both comparison rows.

The milestone theorem's exact hypotheses are:

```lean
{q : ℕ} (hq : 6 ≤ q)
{f : A02.SpaceTimeField} (hf : D01.MemForceR f)
{ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
(a : SmoothL2Field Space)
(ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
(R : ℕ → ℝ)
(hb : ∀ p (hp : 6 ≤ p), HasAprioriBound hp hν a
  (C01.forcePath (S := S) hf)
  (C01.forcePath_jetLp_continuous (S := S) hf) (R p))
```

Consequently `hb` is the only analytic premise beyond order selection,
positive viscosity/horizon, force regularity, and the smooth solenoidal initial
datum. The conclusion provides `u`, `a'`, `f'`, and
`w : ClassicalSolutionR ν a' f' S`, with `‖u‖ ≤ R q` and the two landed
closed-horizon Sobolev comparison inequalities. The retained zero-data probe
also constructs `hb` at radius zero and applies the pressure pipeline without
assuming it.

## 4. Gates

* `lake build NSFormalization.Section4.A01.PressureRegularity`: PASS.
* `lake env lean NSFormalization/Section4/A01/PressureRegularity.lean`: PASS.
* `lake env lean ../research/A01/axioms_pressure_regularity.lean`: PASS; every
  audited declaration uses only `propext`, `Classical.choice`, and `Quot.sound`.
* `maxHeartbeats`: the only explicit cap in the module/audit/probe set is
  `400000` on `pressureSupply_of_pieces`.
* `lake env lean ../research/A01/probes/a01_constructor_pipeline.lean`: PASS;
  all three declarations use only the same standard axioms.
* Positive lane-189 regressions `rev189_assembly_400k.lean`,
  `rev189_definition_axioms.lean`, and `rev189_endpoint_htime.lean`: PASS.
* `make check`: PASS, including 13 contract-policy tests.
* `lake test` from the configured `verification/` test-driver package: PASS
  (10573 jobs).

No push performed.
