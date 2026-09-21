# B2 proof attempts and exact residuals

Status after cont_505: **B2 closed conditional only on the three torus norm
bridges**. P6 / L21_H1 remains Partial. Residuals A and B are closed.
No assumed nonlinear estimate or differential inequality is exported as a
classical-solution theorem. The original attempt record below is preserved
as history; the continuation section supersedes its residual status.

## Closed steps

1. `inhomogeneousEnergyIdentityT`: specialize T11's unconditional Fourier
   energy identity to order one. Its left side is the registered H¹ norm,
   with the zero mode retained. The RHS is still Fourier H¹ pairings.
   Initial error: `IsPeriodicDatum 1 ...` did not match
   `IsPeriodicDatum (↑1) ...`. Unfolding the datum predicate for the cast
   and using `convert ... using 1` with `norm_num` resolves the dependent
   phantom-order normalization.
2. `lintegral_convection_holder_632T`: swap the first two factors of T20's
   Haar (3,6,2) Hölder helper; apply the existing pointwise advection bound.
   Unfold both T10.torusLift and Paper1.torusLift when normalizing the chart.
3. `eLpNorm_three_interpolationT`: B1's proof specialized to Haar measure;
   uses the nonnegative-exponent ENNReal identities, including infinite norms.
4. `young_quarticT`, `young_three_quartersT`, `young_two_factorsT`:
   the same domain-independent scalar proofs as B1.
5. `weighted_cubic_assemblyT`: the nonlinear bound uses Y, not G;
   ordinary energy U remains in Y=U+G and in Z≤U+2G+L. Explicit coefficient
   ((2C)^4/(ν/2)^3+(1+ν)), force coefficient (1+2/ν).
   The probe also instantiates G=L=N=Q=0 with arbitrary nonnegative U, so
   the retained ordinary energy is not forced to vanish.
6. `gradient_six_le_laplacian_twoT`: apply T12.gradientLSix to
   `meanZeroPartT z`, then use T20's derivative invariance under constant
   subtraction. No critical-smallness estimate is used.
7. `convection_interpolationT`: combine steps 2, 3, 6. This still contains
   `periodicLpENorm 6 z`; it is deliberately documented as an intermediate
   estimate, not the completed H¹/H² estimate.
8. `velocity_six_le_localized_gradientT`: transfer to the fundamental cube,
   replace z by cutoffMul z there, enlarge to all space, and use the proved
   whole-space velocity Sobolev estimate for the compactly supported field.

Each closed proof step was committed separately (the three Young forms as one
scalar absorption step). The module and every declaration have passing probes
and standard-axiom checks.

## Residual A: inhomogeneous velocity Sobolev embedding

The requested `velocity_six_le_gradient_twoT` is not declared. The direct
T12.gradientLSix route controls a **gradient**, and requires mean subtraction;
it does not supply a bound for velocity with its nonzero constant mode.
The elementary second route, localization, is proved through the whole-space
embedding. It reduces to the following explicit cutoff-product estimate:

```lean
∀ (z : SpatialField), SmoothPeriodicT z →
  eLpNorm (gradientTensor (cutoffMul z)) 2 volume ≤
    343 * (3 * (ENNReal.ofReal cutoffGradBound * periodicLpENorm 2 z +
      periodicLpENorm 2 (gradientTensor z)))
```

The attempted continuation of that proof ends with:

```text
../tmp/b2-velocity-residual.lean:10:53: error: unsolved goals
case h₂
z : SpatialField
hz : SmoothPeriodicT z
⊢ eLpNorm (gradientTensor (cutoffMul z)) 2 volume ≤
    343 * (3 * (ENNReal.ofReal cutoffGradBound * periodicLpENorm 2 z + periodicLpENorm 2 (gradientTensor z)))

```

The attempted proof applies `velocity_six_le_localized_gradientT`, followed by
multiplication monotonicity (`gcongr`). The remaining step is not disproved or
claimed unavailable in Mathlib. T12.dirDeriv_cutoffMul_eq,
norm_dirDeriv_cutoff_le, and the 343-copy lattice-count proof in
GradientLSix.lean:496–556 provide a concrete continuation route. This lane
does not claim that recording that route proves the remaining bound.

A sufficient velocity constant after this bound is
3*343*A05.gradientL6Const*(1+cutoffGradBound), multiplying the sum of the
velocity and gradient L² norms. No claim of optimality is made.

## Residual B: physical RHS of the energy identity

With z(x)=w.velocity(t,x), b(x)=f(t,x), and G,F,N the order-one data,
the remaining identity is

```text
-2ν (gradientSqT z + laplacianSqT z)
 + 2 periodicPairing ((z·∇)z) (laplacian z)
 + 2 periodicPairing z b - 2 periodicPairing b (laplacian z)
=
-2ν (torusGradientNormAt 1 w.velocity t)^2
 + 2 torusRealPairing G F - 2 torusRealPairing G N.
```

Trying `convert inhomogeneousEnergyIdentityT ... using 1` leaves exactly:

```text
../tmp/b2-physical-residual.lean:22:91: error: unsolved goals
ν T : ℝ
a : SpatialField
f : SpaceTimeField
w : ClassicalSolutionT ν a f T
hf : f ∈ forceClassT
t : ℝ
ht : t ∈ Ioo 0 T
G F N : ↥(PeriodicSobolev 1)
hG : IsPeriodicDatum 1 (fun x => w.velocity (t, x)) G
hF : IsPeriodicDatum 1 (fun x => f (t, x)) F
hN : IsPeriodicDatum 1 (fun x => convectionFieldT w.velocity (t, x)) N
⊢ (-2 * ν * ((gradientSqT fun x => w.velocity (t, x)) + laplacianSqT fun x => w.velocity (t, x)) +
          2 *
            periodicPairing (fun x => advection (lift fun y => w.velocity (t, y)) 0 x)
              (laplacian fun x => w.velocity (t, x)) +
        2 * periodicPairing (fun x => w.velocity (t, x)) fun x => f (t, x)) -
      2 * periodicPairing (fun x => f (t, x)) (laplacian fun x => w.velocity (t, x)) =
    -2 * ν * torusGradientNormAt 1 w.velocity t ^ 2 + 2 * torusRealPairing G F - 2 * torusRealPairing G N

```

The Fourier route is T20.hasSum_angularPairing plus order-zero Parseval,
splitting the weight 1+|2πk|², and ordinary convection cancellation.
The elementary alternative is periodic integration by parts directly on the
cube using PeriodicIntegration, then adding ordinary energy. The latter
has not been implemented here; no library impossibility is asserted.
This residual must be discharged analytically, not supplied as a theorem input.
Force Cauchy–Schwarz and conversion from the extended-norm convection
estimate still need assembly after A and B.

## B0 boundary and statement fidelity

The three intended torus norm interfaces are recorded verbatim in P6_SPLIT.md.
T10's weight is 1+|2πk|², so κ=1. No B0 module is restated. The delivered
partial declarations consume no B0 hypotheses; the absent final inequality
is not described as conditional only on B0.

The revised Proposition 2.1 has no displayed H¹-uniform lifespan clause.
This is work toward the separate restart obligation. P6 stays Partial;
there is no contract or article-level closure change.

## Existing-file edits and gates

Authorized existing files: entrypoints.json (module registration),
P6_SPLIT.md (B2 status), AXIOM_AUDIT.json (required refreshed audit),
and DEPENDENCY_GRAPH.md (required regeneration from the inherited graph).
The regenerated graph reflects inherited C35_FULL/G36_FULL closures; this
lane did not edit proof_graph.json or assign those statuses. Generated PDFs
were restored after the successful paper gate because no TeX was changed.
All other delivered sources/reports are new files. The untracked lane brief
is untouched. Gate commands and final results are in REPORT_505.md.

## Intended final constant (not a proved final theorem)

After residual A, one may take Cv=3*343*A05.gradientL6Const*(1+cutoffGradBound).
The interpolation arithmetic then gives C=√2*Cv*√Csix in
|N|≤C Y^(3/4)L^(3/4). The scalar assembly would give c=1 and
Cν=(2C)^4/(ν/2)^3+(1+ν)+(1+2/ν), with force energy lTwoSqT(f(t)).
Neither this physical convection bound nor its classical-solution assembly
is asserted as a proved declaration here.

## cont_505: both residuals closed

### Residual A — CLOSED

`norm_gradient_cutoffMul_leT` proves the pointwise product estimate using
`dirDeriv_cutoffMul_eq`, the three coordinate derivative bounds and the
Frobenius norm formula. `gradientMajorantT` is continuous, periodic and
nonnegative. The localized gradient vanishes off `closedBall 0 3`.
`lintegral_gradient_cutoffMul_leT` adapts T12's lattice tiling proof to this
majorant, using exactly `lattice_count_le = 343`.
`eLpNorm_gradient_cutoffMul_leT` takes the square root (bounding √343 by 343).
`cutoff_gradient_two_leT` closes the previously recorded exact residual by
the L² triangle inequality. `velocity_six_le_gradient_twoT` then gives

```
Cv = velocitySixConstT = 3*343*A05.gradientL6Const*(1+cutoffGradBound)
‖z‖₆ ≤ Cv (‖z‖₂ + ‖∇z‖₂).
```

The alternative mean-split route was inspected but not pursued: the existing
T12 `gradientLSix` controls gradients, not arbitrary mean-zero velocities.
Generalizing a Fourier embedding was unnecessary once the elementary cutoff
route closed. This is not a claim that that alternative cannot be proved.
Actual implementation errors included an unavailable `PiLp.norm_le_of_le`
(replaced by the explicit three-coordinate square estimate), and a
higher-order-unification timeout at `eLpNorm_const_smul_le` (fixed by an
explicit function equality to `3 • ...`, without increasing heartbeats).

### Residual B — CLOSED

`torusRealPairing_one_eqT` combines `hasSum_periodicPairing` and
`hasSum_angularPairing`, and identifies the sum by `hasSum_datum_pair` and
`datum_pair_entry`. Thus the full H¹ pairing is
`periodicPairing z b - periodicPairing (laplacian z) b`.
`periodicPairing_convection_zeroT` transports Haar integration to the cube
and uses `cubeIntegral_transport_energy_zero`. Pressure already cancels in
T11's unconditional Fourier energy identity; no pressure hypothesis is added.
`torusGradientNormAt_one_sqT` splits the Fourier dissipation into gradient
and Laplacian energies, using the existing mean-free Parseval equalities
and derivative invariance under subtraction of constants.
`weightedEnergyIdentityT` closes the physical RHS identity for arbitrary
`a` and `f ∈ forceClassT` (definitionally T10 `MemForceT`).
`abs_pairing_carrier_leT` proves force Cauchy–Schwarz by realizing the fields
in Haar L² and applying the Hilbert-space inner-product bound.

The direct physical integration-by-parts route was used for ordinary
convection cancellation; reconstructing the entire differentiated identity
by physical time differentiation was unnecessary after the Fourier split.
The recorded earlier residual errors remain above as history, not current gaps.

### Assembly and verification

`convection_bound_of_norm_bridgesT` converts the extended-norm interpolation
to real L² upper bounds. `convection_boundT` gives
`|N| ≤ convectionConstT * (lTwoSqT z + gradientSqT z)^(3/4) * laplacianSqT z^(3/4)`
with `convectionConstT = √2 * Cv * √Csix`. Its gradient-norm hypothesis is
exactly the ordinary B0 bridge consumed by the final theorem.
The √2 factor follows from `(√U+√G)² ≤ 2(U+G)`.

`enstrophy_differential_of_norm_bridgesT`, `enstrophy_differentialT` and
`enstrophy_differential_on_IccT` are proved,
with precisely hOne/hTwo/hGradient and the intended Cν, c=κ=1.
The physical identity directly differentiates the registered norm; hOne
is consumed in the energy/nonlinear conversion and retains the requested
all-interior-time interface. No B0 source was imported or restated.

The probe constructs an explicit zero classical solution with horizon 2,
checks the final theorem on the nonempty interval [1/2,1], and discharges
all three bridges. The mutation removes negative Laplacian dissipation
from the scalar energy-balance premise: ν=1, L=Z=3, all other quantities
zero gives the false conclusion 3≤2. The original absorption proof fails
and Lean proves the negation. Removing the positive dissipation term from
the *conclusion* would instead weaken a true theorem, so that cannot be a
semantic negative test.

All exported theorems are included in `axioms_b2.lean` and use exactly
`[propext, Classical.choice, Quot.sound]`. No additional heartbeat limit,
custom axiom, admission, contract, binding, article-coverage change, or B0
import was introduced. Existing-file edits in this continuation are the
B2 module, its probe/axioms/three reports, and the required refreshed
`AXIOM_AUDIT.json`. The untracked lane brief is untouched.
