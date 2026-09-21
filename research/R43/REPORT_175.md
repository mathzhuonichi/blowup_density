# Lane 175 report — R43 S1 critical pairing identities

Date: 2026-09-15.  Branch: `erenup/175-R43-s1-pairing`.

## 1. Theorems proved

The new module is
`formalization/NSFormalization/Section4/R43/CriticalPairing.lean`, in namespace
`NSFormalization.Section4.R43`.

Datum realization and the weighted energy path:

- `dotHomogeneousENorm_eq_of_isHomogeneousSlice hA` proves
  `dotHomogeneousENorm s z = ‖A‖ₑ` for every supplied homogeneous slice datum.
- `criticalNormAt_eq_norm`, `criticalDissipationAt_eq_norm`, and
  `criticalForceAt_eq_norm` identify `y(t)`, `z(t)`, and `b(t)` with the real
  Hilbert norms of supplied order-`1/2`, order-`3/2`, and order-`1/2` data.
- `criticalEnergyPath hcrit t := ‖hcrit.velocityHalf t‖ ^ 2` is the requested
  datum energy path.  `criticalEnergyPath_eq` proves
  `criticalEnergyPath hcrit t = criticalNormAt w.velocity t ^ 2` on `Ico 0 T`.
- `criticalEnergyPath_hasDerivAt` and
  `criticalEnergyDerivative_hasDerivAt` prove, at `t ∈ Ioo 0 T`,
  `HasDerivAt (fun r => y(r)^2) (2 * ⟪hcrit.velocityHalf t,
  deriv hcrit.velocityHalf t⟫) t`.

The three pairing results are:

```lean
critical_laplacian_pairing A Z L hZ hL :
  ⟪L, A⟫ = -‖Z‖ ^ 2

critical_pressure_pairing A P Q hA hP :
  ⟪P, A⟫ = 0

critical_force_pairing A F :
  |⟪F, A⟫| ≤ ‖F‖ * ‖A‖
```

Here `hZ` is the a.e. symbol `Zᵢ(ξ)=|ξ|Aᵢ(ξ)`, `hL` is
`Lᵢ(ξ)=-|ξ|²Aᵢ(ξ)`, `hA` is
`lerayComplement (1/2) A = 0`, and `hP` is
`P = lerayComplement (1/2) Q`.  The pathwise versions are
`criticalLaplacianPairing_path`, `criticalPressurePairing_path`, and
`criticalForcePairing_path`, with conclusions exactly `-z(t)^2`, `0`, and
`|⟪F(t),A(t)⟫| ≤ b(t)y(t)`.

The scalar assembly is:

```lean
theorem rcritical1_of_trilinear
    {w : ClassicalSolutionR ν a f T} (hf : MemForceR f)
    (hcrit : CriticalDatumPath w hf)
    (htri : CriticalTrilinearEstimate (C₀ := C₀) hcrit) :
    (∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt (fun r => criticalNormAt w.velocity r ^ 2)
        (criticalEnergyDerivative hcrit t) t) ∧
      ∀ t ∈ Ioo (0 : ℝ) T,
        criticalEnergyDerivative hcrit t / 2 +
            (ν - C₀ * criticalNormAt w.velocity t) *
              criticalDissipationAt w.velocity t ^ 2
          ≤ criticalForceAt f t * criticalNormAt w.velocity t
```

Its two named unresolved mathematical inputs are exactly:

1. `hcrit : CriticalDatumPath w hf`.  This contains the six homogeneous datum
   paths (`velocityHalf`, `velocityThreeHalf`, `laplacianHalf`,
   `advectionHalf`, `pressureHalf`, `forceHalf`), their slice-datum witnesses,
   `velocityHalf_smooth`, the lifted datum momentum equation
   `deriv velocityHalf = ν • laplacianHalf - advectionHalf - pressureHalf +
   forceHalf`, the order-shift and Laplacian a.e. symbols, and the transverse /
   longitudinal Leray facts.  It contains no pairing equality, trilinear
   estimate, or scalar energy inequality.
2. `htri : CriticalTrilinearEstimate (C₀ := C₀) hcrit`, definitionally

   ```lean
   ∀ t ∈ Ioo (0 : ℝ) T,
     |⟪hcrit.advectionHalf t, hcrit.velocityHalf t⟫| ≤
       C₀ * ‖hcrit.velocityHalf t‖ *
         ‖hcrit.velocityThreeHalf t‖ ^ 2
   ```

`hf` is the ambient force-membership witness, not an additional estimate.

## 2. What is in Lean now

The order-`1/2` force, pressure, advection, Laplacian, and velocity data are
paired entirely on `RealVectorSobolev (1/2)`.  The Laplacian identity is proved
componentwise from the exact homogeneous Fourier symbols using the complex
`L²` integral formula.  Pressure cancellation uses the self-adjoint
Fourier-side Leray complement through
`A04.inner_lerayComplement_eq_zero_of_eq_zero`.  The force estimate is real
Hilbert-space Cauchy--Schwarz.  Homogeneous datum uniqueness connects these
carrier statements to the datum-infimum norms.

The momentum equation is expanded after pairing with the velocity datum;
symmetry of the real inner product, the three identities, `htri`, and scalar
arithmetic yield the literal `henergy` shape consumed by
`R43.criticalNormBound_radius` / `Paper1.critical_norm_bound`.

`research/R43/axioms_s1.lean` audits all 16 theorems.  Every one prints exactly
`[propext, Classical.choice, Quot.sound]`.  Its non-vacuity example constructs
all six zero datum paths for `A04.zeroSol 1 2` using `A04.memForceR_zero`, proves
the zero `htri`, and instantiates both conclusions of
`rcritical1_of_trilinear` at the explicit time `1 ∈ Ioo 0 2`.

## 3. Gaps and exact residuals

S1b remains deliberately open and is exactly the `htri` proposition displayed
above.

The carrier construction remains exactly `hcrit : CriticalDatumPath w hf`.
`D01/HalfOrder.lean` records why it cannot yet be constructed from
`ClassicalSolutionR` and `MemForceR`: integer-order Sobolev data do not yet
produce homogeneous half-order data for a general smooth `H^∞` slice.  The
tree search covered all requested directories.  The nearest Laplacian module,
`D01/LaplacianPairing.lean`, exports directional-derivative skew-adjointness and
explicitly leaves Laplacian datum assembly/order reconciliation open; the C01
momentum theorem is an equality of unweighted carrier-B `toLp` values, not an
order-`1/2` homogeneous datum equality.

There is no residual Lean goal or compiler error in this lane: both gaps are
represented by named inputs.  Failed elaboration attempts, with exact error
text, are preserved in `research/R43/ATTEMPTS_S1.md`.  The diagnostic that fixed
the residual-first pairing orientation was:

```text
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ⟪A, L⟫
in the target expression
  ⟪L, A⟫ = -‖Z‖ ^ 2
```

The initial zero conformance carrier also exposed:

```text
Type mismatch: After simplification, term
  isHomogeneousSliceDatum_zero (1 / 2)
has type
  D01.Homogeneous.IsHomogeneousSliceDatum (1 / 2) 0 0
but is expected to have type
  D01.Homogeneous.IsHomogeneousSliceDatum (1 / 2) (fun x => 0) 0
```

Both elaboration issues are resolved; they are recorded to prevent recurrence,
not listed as mathematical gaps.

## 4. Commands and results

- `. scripts/lean-env.sh; cd verification; LEAN_NUM_THREADS=6 lake build
  NSFormalization.Section4.R43.CriticalPairing` — exit 0.  The target has no
  warnings; Lake replayed pre-existing dependency linter messages.
- `. scripts/lean-env.sh; cd verification; lake env lean
  ../formalization/NSFormalization/Section4/R43/CriticalPairing.lean` — exit 0,
  zero output.
- `. scripts/lean-env.sh; cd verification; lake env lean
  ../research/R43/axioms_s1.lean` — exit 0; all 16 declarations report exactly
  the standard three axioms and the non-vacuity example closes.
- `. scripts/lean-env.sh; make check` — exit 0.
- `. scripts/lean-env.sh; make test` — exit 0.
- `. scripts/lean-env.sh; make test-mutations` — exit 0; all four mutation cases
  behaved as required.
- `git diff --check` — exit 0.
