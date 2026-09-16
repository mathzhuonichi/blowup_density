# Lane 189 — pressure-gradient regularity attempts

## Review correction

The previous `hpg_of_slab` was rejected and has been removed, together with
`ProjectedMomentumDatumOn` and the theorems accepting `htime`. P4 remains open.
The accepted Helmholtz converse is unchanged.

## Negative endpoint example

`temporalDerivative` uses the ambient, two-sided `fderiv`. Relative smoothness
on `[0,S)` does not control that derivative at zero. The reviewer probe
`probes/rev189_endpoint_htime.lean` is retained unchanged: `u(t,x)=|t|e₀`
agrees with `t e₀` on the slab, but its ambient temporal derivative is zero
at zero and `e₀` at positive times. Thus the old `htime` premise does not
follow from `hc3`. The constant-in-space example is a counterexample to that
regularity implication, not a claimed finite-energy Navier–Stokes solution.
The new `pressureGradient_contDiffOn_interior` uses only the open slab.

## Complement route implemented so far

* `unprojectedResidualPath` reuses lane 178's restricted Laplacian and
  `reducedAdvectionPath`, omitting the source projection.
* `unprojectedResidualPath_contDiffOn` proves finite-order time smoothness
  with the same two-spatial-order loss. Lane 178's `reducedResidualPath` and
  `residualPath_hasDerivAt` concern the **projected** residual; taking its
  complement cannot substitute for constructing the unprojected datum.
* `lerayComplement_contDiffOn` transfers smoothness through the datum CLM.
* `exists_smooth_lerayComplement_representative` applies lane 190 to a
  supplied complement carrier. Its slices are L² and have symmetric Jacobian,
  including at zero, by the retained Helmholtz converse. This is an auxiliary
  theorem, not the requested carrier-to-pressure export.
* `carrierDatum_physicalSlice` explicitly applies `IsSobolevDatum.congr_field`
  using `hslice`; it does not identify spatial operators or Leray symbols.

`EulerMeanSolenoidal.L2` is defined as plain `Lp Space 2 volume` in
`Euler/MeanSolenoidalSpace.lean:22`. No generalization of lane 190 is needed.

## Remaining proof obligations

1. Descend the unprojected cylinder residual, prove compatibility across
   spatial orders, and construct the all-order complement datum paths of one
   continuous ordinary L² carrier.
2. Identify the descended cylinder projection with the physical datum Leray
   projection. `projectedResidualPath_eq` is the cylinder formula, not this
   transport theorem.
3. Derive the interior time derivative of the chosen smooth representative
   from `datumPath_hasDerivAt` and bounded evaluation. The conditional
   `residualDatum_is_timeDerivative` requires a pointwise `HasDerivAt` premise;
   `hslice` alone does not supply it for the arbitrary Lp representative.
4. Combine these identifications and continuity to obtain the pointwise
   interior identity and export `pressureGradientField_of_carrier`.

These obligations have not been replaced with another momentum assumption.
The zero satisfiability check exercises only the new auxiliary representative
result, and must not be reported as pipeline closure.

## Dependency snapshot

The requested fetch and rebase succeeded onto integration `34c928b`.
That tree contains `JointRepresentative.lean`, but not `CylinderWiring.lean`.
The latter was inspected read-only from local branch
`erenup/192-A01-wiring-hsob`; its `cylinderPair_of_bounds` export has the
expected Duhamel, divergence, invariance, carrier, and all-order datum clauses.
The local lane-180 fix4 consumer was also inspected. No dependency branch was
merged and no pre-existing Lean module was edited.

## Second fix: pressure supply assembly (2026-09-15)

Rebased on integration 5666c27. Lane 180 ConstructorAssembly is absent, so
PressureRegularity copies its exact fix6 PressureSupply definition (actual
binder order hpairs, hpaths). No pre-existing upstream module is modified.

* 194 supplies the fixed complement carrier, all-order datum paths, smooth
  joint G, and its a.e. slices. Its canonical complement datum is transported
  to G with IsSobolevDatum.congr_field.
* 195 supplies jointRepresentative_temporalDerivative_of_cylinder and
  interior_momentum_identity_of_datums. The assembly uses this datum-level
  core of the complement-path adapter to avoid rechoosing its existential A.
* 197 supplies hprojected_of_cylinder'' and residualDatum_jointRepresentative.
  The lowered order-two time derivative datum is therefore A - complement A,
  without a bridge or residual-agreement assumption.
* 189 supplies the Helmholtz converse, zero-order MemLp, and final assembly.
  D01.contDiff_slice on Ico includes zero: the spatial factor is unrestricted.

The arbitrary-velocity issue is resolved by
pressureGradientOfVelocity_eq_of_slices. Continuous spatial slices turn
a.e. agreement into pointwise equality. Spatial derivatives agree globally
on each slice; time derivatives agree by eventual equality on the open
interior. No conclusion about the ambient derivative at zero is needed.

Removed superseded local residual-path, residual-smoothness, and complement
smoothness helpers. Retained the Fourier converse and representative helpers.
The pipeline probe imports CylinderWiring and JointRepresentative, checks
the exact copied PressureSupply contract, and derives its witnesses with hb
as the only extra analytic premise. Its positive-horizon zero example proves
hb using zero Duhamel uniqueness, reusing lane 192's zero-bound argument.

Final gates: module build and direct Lean check PASS; axiom audit PASS with
only propext/Classical.choice/Quot.sound; pipeline and positive-horizon zero
instance PASS; endpoint regression PASS; make check PASS; diff whitespace
check PASS. The pipeline theorem's axiom audit is standard as well.
