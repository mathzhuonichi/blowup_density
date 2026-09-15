# ATTEMPTS — R43 row S1 first-layer pairing identities (lane 175)

Date: 2026-09-15.  Module:
`formalization/NSFormalization/Section4/R43/CriticalPairing.lean`.

## 1. Outcome

The identity layer closes without placeholders.

- `critical_laplacian_pairing` proves the residual-first identity
  `⟪L,A⟫ = -‖Z‖²` directly on `RealVectorSobolev`, assuming exactly the a.e.
  homogeneous symbols `Z_i(ξ)=|ξ|A_i(ξ)` and
  `L_i(ξ)=-|ξ|²A_i(ξ)`.
- `critical_pressure_pairing` proves `⟪P,A⟫=0` when the velocity datum is
  transverse and the pressure datum is in the range of the Leray complement.
- `critical_force_pairing` proves
  `|⟪F,A⟫| ≤ ‖F‖‖A‖` by real Hilbert-space Cauchy--Schwarz.
- Homogeneous-datum uniqueness identifies these datum norms with
  `criticalNormAt`, `criticalDissipationAt`, and `criticalForceAt`.
- `criticalEnergyPath` is the requested explicit datum path
  `t ↦ ‖A_{1/2}(t)‖²`; `criticalEnergyPath_eq` identifies it with `y(t)²`, and
  `criticalEnergyPath_hasDerivAt` / `criticalEnergyDerivative_hasDerivAt` prove
  the requested weighted norm-square derivative shape from the smooth
  half-order path field of `hcrit`.
- `rcritical1_of_trilinear` combines the lifted momentum equation, all three
  identities, and the separately named `htri` estimate into the literal scalar
  `henergy` inequality used by `R43.criticalNormBound_radius`.

There is no remaining Lean goal or compiler error in these identities.  S1b is
intentionally not proved in this lane.

## 2. Existing tree lemmas used

Homogeneous realization and norm:

- `D01.Homogeneous.isHomogeneousSliceDatum_unique` turns the datum-infimum
  `D01.dotHomogeneousENorm` into the norm of any supplied datum.
- `D01.Homogeneous.IsSliceDistribution`,
  `IsHomogeneousVectorDatum`, and `IsHomogeneousDatum` give the concrete zero
  datum used by the non-vacuity check.

Fourier-side Laplacian pairing:

- `Paper3.realSobolev_inner_eq_ambient` and
  `Paper3.real_inner_eq_re_complex` expose each real component as the real part
  of its complex `L²` inner product.
- `MeasureTheory.L2.inner_def`, `PiLp.inner_apply`, and
  `PiLp.norm_sq_eq_of_L2` reduce the vector identity to a componentwise
  integral identity.  Substitution of the two supplied symbols then closes by
  ring normalization.
- `D01/LaplacianPairing.lean` was audited.  Its exported results are
  skew-adjointness for the inhomogeneous angular directional-derivative carrier;
  its own docstring says the Laplacian datum assembly/order reconciliation is a
  later step.  It therefore does not directly state the homogeneous
  `1/2`--`3/2` identity needed here, so the present proof works from the exact
  homogeneous symbols.

Pressure and force:

- `D01.Leray.lerayComplement` is the Fourier-side longitudinal projection on
  `RealVectorSobolev`.
- `A04.inner_lerayComplement_eq_zero_of_eq_zero` supplies orthogonality between
  a transverse velocity datum and every longitudinal datum.
- `abs_real_inner_le_norm` supplies the force Cauchy--Schwarz estimate.

Time derivative and scalar assembly:

- `A04.hasDerivAt_datumNormSq_of_contDiffOn` gives
  `(‖A(t)‖²)'=2⟪A(t),A'(t)⟫`.
- `C01.momentum_split_toLp` was audited as the integer/unweighted precedent.
  Its conclusion is an equality of carrier-B `toLp` values; it does not lift
  that equality to homogeneous order-`1/2` data.  The lifted equality is thus
  exactly the `CriticalDatumPath.momentum` field.

## 3. The exact carrier residual (`hcrit`)

`D01/HalfOrder.lean:40-50` explicitly records the missing homogeneous half: the
tree does not yet construct a homogeneous datum for a general `H^∞` slice from
the integer-order datum supplied by `MemForceR`/`ClassicalSolutionR`.  The
search covered all of
`Section4/{D01,A03,A04,A05,B02,C01,R43}`, `Source/`, and `Paper1/` before this
absence was recorded.

Accordingly, `CriticalDatumPath w hf` is the exact named residual.  It supplies:

1. paths `velocityHalf`, `velocityThreeHalf`, `laplacianHalf`,
   `advectionHalf`, `pressureHalf`, and `forceHalf`;
2. the corresponding `IsHomogeneousSliceDatum` witnesses at orders `1/2` or
   `3/2`;
3. `velocityHalf_smooth : ContDiffOn ℝ ∞ velocityHalf (Ico 0 T)`;
4. the homogeneous lifted momentum equality
   `deriv velocityHalf t = ν • laplacianHalf t - advectionHalf t -
   pressureHalf t + forceHalf t`;
5. the order-shift and Laplacian a.e. Fourier symbols; and
6. transverse velocity plus a longitudinal pressure witness.

No pairing equality, norm estimate, or scalar energy inequality is a field of
`hcrit`.  The separate exact S1b residual is

```lean
CriticalTrilinearEstimate (C₀ := C₀) hcrit :=
  ∀ t ∈ Ioo (0 : ℝ) T,
    |⟪hcrit.advectionHalf t, hcrit.velocityHalf t⟫| ≤
      C₀ * ‖hcrit.velocityHalf t‖ * ‖hcrit.velocityThreeHalf t‖ ^ 2
```

## 4. Failed proof/elaboration attempts (error text preserved)

The first residual-first orientation edit instantiated Mathlib's symmetric
inner-product lemma in the wrong argument order.  Lean reported:

```text
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ⟪A, L⟫
in the target expression
  ⟪L, A⟫ = -‖Z‖ ^ 2
```

and analogously:

```text
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ⟪A, P⟫
in the target expression
  ⟪P, A⟫ = 0
```

`real_inner_comm x y` is stated as `⟪y,x⟫ = ⟪x,y⟫`; instantiating it as
`real_inner_comm A L` and `real_inner_comm A P` fixed both statements.

The first zero-carrier proof also exposed function-zero eta and `PiLp`
coordinate issues.  The useful exact diagnostic was:

```text
Type mismatch: After simplification, term
  isHomogeneousSliceDatum_zero (1 / 2)
has type
  D01.Homogeneous.IsHomogeneousSliceDatum (1 / 2) 0 0
but is expected to have type
  D01.Homogeneous.IsHomogeneousSliceDatum (1 / 2) (fun x => 0) 0
```

The physical fields are now rewritten explicitly by function extensionality,
and `PiLp.zero_apply` exposes the zero Fourier coordinate before
`Lp.coeFn_zero` proves the a.e. symbol relations.

## 5. Conformance

`research/R43/axioms_s1.lean` prints every theorem in the module.  Each prints
exactly `[propext, Classical.choice, Quot.sound]`.  Its non-vacuity example uses
`A04.zeroSol 1 2` and `A04.memForceR_zero`, constructs all six zero homogeneous
datum paths, proves `htri`, and instantiates `rcritical1_of_trilinear` on
the explicit interior time `1 ∈ Ioo 0 2`.
