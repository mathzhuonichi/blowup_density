# Lane 180 — B2 constructor assembly attempts

## Final interface

The constructor must be parameterized by the representative selected by B1 R4:

```lean
velocity : SpaceTimeField
hslice : ∀ t : Icc (0 : ℝ) S,
  (fun x => velocity (↑t,x)) =ᵐ[volume] ⇑(U t)
hc3 : ContDiffOn ℝ ∞ velocity (Ico (0 : ℝ) S ×ˢ univ)
```

The pressure is built from a separate supplier field whose identity with the
velocity-derived expression is required only on the open time interior.  The
existential is named `PressureSupply`; its arguments retain the selected
carrier, the complete same-carrier family of mild solutions at every order,
all-order paths, canonical solenoidal datum/force premises, and lane-190
representative evidence:

```lean
G : SpaceTimeField
hG_int : ∀ t ∈ Ioo (0 : ℝ) S, ∀ x,
  G (t,x) = pressureGradientOfVelocity ν f velocity (t,x)
hG : ContDiffOn ℝ ∞ G (Ico (0 : ℝ) S ×ˢ univ) ∧
  ∀ t ∈ Ico 0 S,
    MemLp (fun x => G (t,x)) 2 volume ∧
    RadialPotential.HasSymmetricJacobian (fun x => G (t,x))
```

The fixed-pair conclusion is

```lean
∃ w : ClassicalSolutionR ν (fun x => velocity (0,x)) f S,
  w.velocity = velocity ∧
  ∀ t : Icc (0 : ℝ) S,
    (fun x => w.velocity (↑t,x)) =ᵐ[volume] ⇑(U t)
```

The all-order datum input remains stated for the abstract `L²` carrier.
`velocitySobolev_of_hslice` transfers it to `velocity` with the existing
`IsSobolevDatum.congr_field` lemma. Its result is deliberately the
`ContinuousOn (Icc 0 S)` plus `∀ t ∈ Ico 0 S` shape consumed by lane 189.

## Negative example 1: a strictly longer clamped horizon

The original attempt chose `T := S+1` and used

```lean
constructedVelocity hS.le U (t,x) =
  (U (projIcc 0 S hS.le t) : Space → Space) x.
```

This is constant for `t ≥ S`. At a non-stationary endpoint the left time
derivative is the Navier–Stokes evolution while the right derivative is zero,
so joint smoothness across `S` is false. The same defect affects the
zero-extended force when its endpoint value is nonzero. The classical horizon
therefore has to be `S`; its fields require regularity only on `Ico 0 S`.

## Negative example 2: smoothness of the raw `Lp` coercion

The second attempt fixed the horizon but set

```lean
velocity := constructedVelocity hS.le U
```

and assumed `ContDiffOn` of that exact function. This is also not a satisfiable
supplier interface. `⇑(U t)` is the arbitrary pointwise representative chosen
by the `Lp` coercion of an a.e. equivalence class. Even when the class has a
smooth representative, that coercion is in general not continuous. Lane 190
therefore proves only

```lean
∃ velocity : SpaceTimeField,
  (∀ t : Icc 0 S, (fun x => velocity (↑t,x)) =ᵐ[volume] ⇑(U t)) ∧
  ContDiffOn ℝ ∞ velocity (Ico 0 S ×ˢ univ)
```

and cannot provide smoothness of `constructedVelocity`. A.e. equality cannot
transport `ContDiffOn`; assuming an additional pointwise `EqOn` merely hides
the same obstruction. The raw construction is now used only for the zero
witness and historical negative documentation.

## Negative example 3: ambient `fderiv` at `t = 0`

The third attempt set

```lean
G := pressureGradientOfVelocity ν f velocity
```

and required this exact field to be `ContDiffOn` on `Ico 0 S ×ˢ univ`.
This is generically false even when `velocity` is smooth relative to that
half-open slab. `temporalDerivative` is the ambient two-sided

```lean
fderiv ℝ (fun s : ℝ => velocity (s,x)) t 1
```

not a within-derivative. For `velocity(t,x) = |t| e₀`, Mathlib assigns the
junk value zero at the nondifferentiable endpoint, while the interior
derivative has first coordinate one. Consequently the raw pressure-gradient
field for `ν=0`, `f=0` is discontinuous at zero.

`probes/rev180_pressure_gradient_representative.lean` formalizes both facts:
the velocity satisfies `hc3`, and the old `ContDiffOn` premise is false. The
constructor therefore accepts a supplier field `G` smooth up to zero and asks
for equality with the raw expression only on `Ioo 0 S`, exactly where the
momentum record field is stated.

## Negative example 4: unscoped supplier quantifiers

The fourth rejected consumer asked lane 190 for

```lean
∀ U : C(Icc 0 S, EulerMeanSolenoidal.L2),
  ∃ velocity, hslice U velocity ∧ hc3 velocity
```

but the landed theorem is

```lean
exists_joint_smooth_representative hS U hpaths
```

and requires the all-order paths of the selected `U`.  The mismatch is real:
`probes/rev180_rows_supplier_mismatch.lean` applies the landed theorem to the
rejected type and Lean reports the missing `hpaths` argument.

The same attempt stated lane 189 as a supplier for every smooth velocity,
without the carrier, mild solution, all-order paths, descent, divergence,
projected Duhamel equation, or slice identity.  That statement is false, not
merely stronger than needed.  `probes/rev180_h189_unsat.lean` takes
`velocity(t,x)=t e₀` and `f=0`; its raw pressure gradient is the nonzero
spatial constant `-e₀`, which cannot be an `L²` slice.

The corrected quantifier order is: lane 192 first selects `U`, `hpairs`, and
`hpaths`; lane 190 selects `velocity` using those paths; only then does the
pressure pipeline receive the complete context and return `PressureSupply`.
No arbitrary velocity or arbitrary continuous carrier is quantified without
the premises used to produce it.

## Negative example 5: one order cannot supply all-order consumers

The fifth attempt kept only one selected cylinder realization:

```lean
u : C(Icc 0 S, SobolevSpace 1 (q+1))
hU : ∀ t, ordinaryLift (U t) = value 1 (u t)
hdiv : ∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0
hduh : ∀ t, u t = quadraticDuhamel ... q ... u t
```

This is insufficient for lane 194.  Its fixed residual carrier specializes at
order seven, while its `C^j_t H^m_x` residual paths specialize at
`max 6 m + 2 + 2*j`.  Even at the selected order, the rejected interface had
discarded angular invariance.  Since `constructorInputs_of_bounds` had already
chosen an opaque `U`, a second call to the outer bound family could not recover
an identifiably equal carrier with the missing family.

The fifth-review probe recorded the concrete type mismatch: an order-`q`
`SobolevSpace 1 (q+1)` witness cannot inhabit the required order-`p`
`SobolevSpace 1 (p+1)` existential.  The fix is structural, not a coercion:
`PressureSupply`, `CarrierConstructorFull`, and `rows_from_constructor_full`
now retain

```lean
hpairs : ∀ p (hp : 6 ≤ p), ∃ u,
  hU ∧ hdiv ∧ hinv ∧ hduh
```

for the same `U`.  Production selects it with `cylinderPair_of_bounds`; only
the final constructor and comparison rows specialize `hpairs q hq`.  The
historically named `rev180_pressure_supply_hpairs_mismatch.lean` is now a
positive typecheck of that exact handoff.

## Field-by-field closure for the chosen representative

- `horizon_pos` is `hS`.
- `velocity_smooth` is the lane-190 `hc3` restriction.
- `initial` is reflexive because the initial datum is defined as
  `fun x => velocity (0,x)`.
- `divergence` first specializes `hpairs q hq`; `velocity_divergence` then
  lifts `hslice` through
  `ordinaryProjection_measurePreserving` and applies
  `EulerClassicalDivergence.divergenceFree_classical_divergence_zero` directly
  to the cylinder `hdiv` clause.
- `sobolev` comes from lane 192's all-order path and
  `IsSobolevDatum.congr_field` along `hslice`.
- `momentum` is `momentum_of_supplied_gradient`, using `hc3`, the derived
  divergence, radial recovery `∇p = G`, and `hG_int` only on `Ioo 0 S`.
- `pressure_smooth` is `pressurePotential_contDiffOn_slab G hG.1`.
- `pressure_gradient` uses `pressureGradient_pressurePotential` and the
  per-time `MemLp` clause of `hG`.

Thus there is no remaining record-field hole in lane 180.

## Supplier composition

The positive interface probe `probes/rev180_actual_supplier_pipeline.lean`
uses the landed theorem shapes directly:

- lane 192: call `cylinderPair_of_bounds` on `hb` to obtain one `U`, its full
  same-carrier `hpairs`, and the all-`j,m` paths;
- lane 190: call `exists_joint_smooth_representative hS U hpaths` and open
  `⟨velocity, hslice, hc3⟩`;
- pressure pipeline: obtain its scoped `PressureSupply`, then open
  `⟨G, hG_int, hG_smooth, hG_slices⟩`;
- lane 180: specialize `hpairs q hq` internally and apply
  `carrierConstructor_of_localTheory` to the lane-190 velocity and supplied
  gradient representative.

The cross-lane probe `probes/rev180_194_195_197_pressure_supply.lean` additionally
opens lane 194's real complement exports and calls lane 195's landed interior
identity with the current lane-197 projector-equality conclusion as a named
hypothesis.

The independent satisfiability probe shows that if velocity and force extend
smoothly to `Ioo (-1) S ×ˢ univ`, then the raw pressure-gradient field itself
is a valid `G`: its smoothness restricts from the open neighbourhood,
`hG_int` is reflexive, and the standard slice properties restrict directly.
