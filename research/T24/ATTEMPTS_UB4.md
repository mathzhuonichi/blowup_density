# Ub4 attempts

## A1: initial finite-sum elaboration

Explicit unfolding and sum index annotations are needed; pressure_smooth collides with the raw packet field. The cross-transport local-zero proof itself elaborated.

```text
../formalization/NSFormalization/Section3/T24/MultipleAssembled.lean:31:24: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (fun z => ∑ i ∈ s, F i z) (t, x + coordinateVector i)
in the target expression
  F a (t, x) + ∑ i_1 ∈ s, F i_1 (t, x + coordinateVector i) = F a (t, x) + ∑ i ∈ s, F i (t, x)

case insert.refine_1
ι : Type u_1
F : ι → SpaceTimeField
a : ι
s : Finset ι
ha : a ∉ s
ih : (∀ i ∈ s, F i ∈ forceClassT) → (fun z => ∑ i ∈ s, F i z) ∈ forceClassT
hF : ∀ i ∈ insert a s, F i ∈ forceClassT
hfs : ContDiff ℝ ∞ (F a)
hfp : IsPeriodicOn univ (F a)
K : Set ℝ
hK : IsCompact K
hKpos : K ⊆ Ioi 0
hfK : tsupport (F a) ⊆ K ×ˢ univ
hgs : ContDiff ℝ ∞ fun z => ∑ i ∈ s, F i z
hgp : IsPeriodicOn univ fun z => ∑ i ∈ s, F i z
L : Set ℝ
hL : IsCompact L
hLpos : L ⊆ Ioi 0
hgL : (tsupport fun z => ∑ i ∈ s, F i z) ⊆ L ×ˢ univ
t : ℝ
ht : t ∈ univ
x : Space
i : Fin 3
⊢ F a (t, x) + ∑ i_1 ∈ s, F i_1 (t, x + coordinateVector i) = F a (t, x) + ∑ i ∈ s, F i (t, x)
../formalization/NSFormalization/Section3/T24/MultipleAssembled.lean:55:2: error: Type mismatch
  ContDiffOn.sum fun j x => (d.component j).velocity_smooth
has type
  ContDiffOn ℝ ∞ (fun x => ∑ i ∈ ?m.44, (d.component i).velocity x) (Ico 0 d.T ×ˢ univ)
but is expected to have type
  ContDiffOn ℝ ∞ d.assembledVelocity (Ico 0 d.T ×ˢ univ)
../formalization/NSFormalization/Section3/T24/MultipleAssembled.lean:56:8: error: invalid declaration name `pressure_smooth`, structure `NSFormalization.Section3.T24.RegionsData` has field `pressure_smooth`
../formalization/NSFormalization/Section3/T24/MultipleAssembled.lean:61:2: error: Type mismatch
  Finset.sum_congr rfl fun j x_1 => (d.component j).velocity_periodic t ht x i
has type
  ∑ j ∈ ?m.37, (d.component j).velocity (t, x + coordinateVector i) = ∑ j ∈ ?m.37, (d.component j).velocity (t, x)
but is expected to have type
  d.assembledVelocity (t, x + coordinateVector i) = d.assembledVelocity (t, x)
../formalization/NSFormalization/Section3/T24/MultipleAssembled.lean:64:2: error: Type mismatch
  Finset.sum_congr rfl fun j x_1 => (d.component j).pressure_periodic t ht x i
has type
  ∑ j ∈ ?m.37, (d.component j).pressure (t, x + coordinateVector i) = ∑ j ∈ ?m.37, (d.component j).pressure (t, x)
but is expected to have type
  d.assembledPressure (t, x + coordinateVector i) = d.assembledPressure (t, x)
../formalization/NSFormalization/Section3/T24/MultipleAssembled.lean:67:2: error: Type mismatch
  Finset.sum_eq_zero fun j x_1 => (d.component j).initial x
has type
  ∑ x_1 ∈ ?m.20, (d.component x_1).velocity (0, x) = 0
but is expected to have type
  d.assembledVelocity (0, x) = 0
../formalization/NSFormalization/Section3/T24/MultipleAssembled.lean:85:10: error: typeclass instance problem is stuck
  NormedAddCommGroup ?m.129

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `NormedAddCommGroup` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
```

## A2: sum calculus and field assembly

Fix coordinate coercions, explicit Sobolev order, neighbourhood type annotation, and transpose the cross-term indices. Replace deprecated lemma names.

```text
../formalization/NSFormalization/Section3/T24/MultipleAssembled.lean:126:13: warning: `ContinuousLinearMap.sum_apply` has been deprecated: Use `sum_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sum_apply` to `sum_apply x`).
../formalization/NSFormalization/Section3/T24/MultipleAssembled.lean:126:44: error(lean.unknownIdentifier): Unknown constant `PiLp.sum_apply`
../formalization/NSFormalization/Section3/T24/MultipleAssembled.lean:127:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ∑ x ∈ ?m.48, ∑ y ∈ ?m.49, ?m.50 x y
in the target expression
  ∑ x_1, (∑ i, (spatialDerivative (d.component i).velocity t x) (coordinateVector x_1)).ofLp x_1 = 0

ν : ℝ
u f : VelocityField
p : PressureField
K : Set Space
M E : ℝ
d : RegionsData ν u p f K M E
t : ℝ
ht : t ∈ Ico 0 d.T
x : Space
⊢ ∑ x_1, (∑ i, (spatialDerivative (d.component i).velocity t x) (coordinateVector x_1)).ofLp x_1 = 0
../formalization/NSFormalization/Section3/T24/MultipleAssembled.lean:140:6: error: Application type mismatch: The argument
  ContDiffOn.comp_contDiff (assembled_velocity_smooth d) (ContDiff.prodMk contDiff_const contDiff_id) fun x =>
    ⟨ht, mem_univ x⟩
has type
  ContDiff ℝ ∞ (d.assembledVelocity ∘ fun x => (t, id x))
of sort `Prop` but is expected to have type
  ℝ
of sort `Type` in the application
  @T11.exists_periodicDatum_smooth
    (ContDiffOn.comp_contDiff (assembled_velocity_smooth d) (ContDiff.prodMk contDiff_const contDiff_id) fun x =>
      ⟨ht, mem_univ x⟩)
../formalization/NSFormalization/Section3/T24/MultipleAssembled.lean:172:6: warning: `MeasureTheory.integral_finset_sum` has been deprecated: Use `MeasureTheory.integral_finsetSum` instead
../formalization/NSFormalization/Section3/T24/MultipleAssembled.lean:181:68: error: Application type mismatch: The argument
  ht
has type
  t ∈ Ioo 0 d.T
but is expected to have type
  ?m.156.1 ∈ Ioo 0 d.T
in the application
  And.intro ht
../formalization/NSFormalization/Section3/T24/MultipleAssembled.lean:191:8: warning: `ContinuousLinearMap.sum_apply` has been deprecated: Use `sum_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sum_apply` to `sum_apply x`).
../formalization/NSFormalization/Section3/T24/MultipleAssembled.lean:198:45: warning: `ContinuousLinearMap.sum_apply` has been deprecated: Use `sum_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sum_apply` to `sum_apply x`).
../formalization/NSFormalization/Section3/T24/MultipleAssembled.lean:203:47: warning: `ContinuousLinearMap.sum_apply` has been deprecated: Use `sum_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sum_apply` to `sum_apply x`).
../formalization/NSFormalization/Section3/T24/MultipleAssembled.lean:215:13: warning: `ContinuousLinearMap.sum_apply` has been deprecated: Use `sum_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sum_apply` to `sum_apply x`).
../formalization/NSFormalization/Section3/T24/MultipleAssembled.lean:225:13: warning: `ContinuousLinearMap.sum_apply` has been deprecated: Use `sum_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sum_apply` to `sum_apply x`).
../formalization/NSFormalization/Section3/T24/MultipleAssembled.lean:229:20: error: Type mismatch
  crossTransport_eq_zero d hij ht x
has type
  (spatialDerivative (d.component j).velocity t x) ((d.component i).velocity (t, x)) = 0
but is expected to have type
  (spatialDerivative (d.component i).velocity t x) ((d.component j).velocity (t, x)) = 0
```

## A3: closed implementation

Direct elaboration now exits 0 with zero output. No analytic residual remains.
The support argument uses a common floor-lattice representative to prove
pointwise non-overlap. If the advecting velocity is nonzero, continuity makes
it nonzero on a neighbourhood, forcing the other velocity to vanish there;
`Filter.EventuallyEq.fderiv_eq` makes its derivative zero. If the advecting
velocity is zero, linearity of the derivative closes immediately. This avoids
needing the stronger assertion that at most one *support* meets every point:
disjoint open balls can have touching closures, while the nonzero-neighbourhood
argument proves exactly the cross transport required by the equation.

The derivative of the finite sum is expanded by `fderiv_fun_sum`; the
Laplacian uses differentiability of each first spatial directional derivative.
The advection double sum reduces to the diagonal. The registered residual
is temporal derivative + advection − viscosity times Laplacian + pressure
gradient, and therefore equals the sum of the component momentum equations.

Sobolev paths and pressure-gradient integrability are obtained from the
proved smooth finite sums using the existing T11 datum-path theorem and the
compact-torus smooth-gradient integrability theorem. This proves the exact
fields without introducing additional inputs or importing T18. The Haar
pressure gauge uses integrability of each smooth component pressure and
`integral_finsetSum`. `forceClassT` has no zero-mean requirement; its compact
positive-time carriers are combined by finite unions.
