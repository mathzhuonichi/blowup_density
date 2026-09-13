import NSFormalization.Section4.A01.ConvectionDivergence
import NSFormalization.Section4.A01.ProjectedEquation
import NSFormalization.Section4.A01.RadialPotential
import NSFormalization.Section4.A01.PressureGauge

/-!
# A01 signature checks (lane 113 SIMP/tester) — THIS FILE MUST FAIL

## Signature checks (NOT load-bearing evidence)

Each block below drops one hypothesis (or weakens the conclusion) and tries to
discharge the weakened statement by *applying the original theorem with the
dropped argument omitted*.  Every such application is ill-typed, so **every block
here fails to elaborate** — `lake env lean` on this file exits 1 with one
type-mismatch per block.

**These checks are weak** (`REVIEW_SIMP.md` F4): a missing positional argument
always errors, and the error only witnesses that *the theorem's signature still
has the argument* — it says nothing about whether the weaker statement is
provable by other means.  In fact block N10 below is *wrong*: `hsym` in
`pressure_potential_of_pointwise` is **not** load-bearing (it follows from `hsm`
+ `hdp`), yet N10 "fails" here exactly like the genuinely load-bearing N3/N6.

The real load-bearing evidence lives in the companion file
`research/A01/negative_simp.lean` (must compile SILENTLY): counterexamples that
*refute* the hypothesis-free `hdiv`/`hG` statements, and a *derivation* proving
`hsym` redundant.  Blocks are wrapped in `set_option autoImplicit false in` so a
block that *did* compile would be a real finding (removable hypothesis on a
frozen statement) rather than an `autoImplicit` re-binding (the 077 trap).

Exports with no Prop hypothesis (`convectionDivergence`, `pressureGradient_fderiv_slice`,
`pressureGradient_apply`) are unconditional identities: nothing to drop, no block.

RUN: `lake env lean` this file; expect exit 1, one elaboration error per block.
-/

noncomputable section

/-! ## Section A — ConvectionDivergence + ProjectedEquation -/
namespace NSFormalization.Section4.A01.NegA
open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A01
open NSFormalization.Section4.A02

-- N1: drop `hu` from `convectionDivergence_eq_advection_add_smul_div`
set_option autoImplicit false in
theorem n1 (u : VelocityField) (t : ℝ) (x : Space) :
    convectionDivergence u t x
      = advection u t x + (spatialDivergence u t x) • u (t, x) :=
  convectionDivergence_eq_advection_add_smul_div u t x

-- N2: drop `hdiv` from `convectionDivergence_eq_advection`
set_option autoImplicit false in
theorem n2 (u : VelocityField) (t : ℝ) (x : Space)
    (hu : DifferentiableAt ℝ (fun y : Space => u (t, y)) x) :
    convectionDivergence u t x = advection u t x :=
  convectionDivergence_eq_advection u t x hu

-- N3: drop `hdiv` from `navierStokesResidual_eq_iff_projected`
set_option autoImplicit false in
theorem n3 (ν : ℝ) (u : VelocityField) (p : PressureField) (t : ℝ) (x : Space) (F : Space)
    (hu : DifferentiableAt ℝ (fun y : Space => u (t, y)) x) :
    NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x = F
      ↔ temporalDerivative u t x - ν • spatialLaplacian u t x
          = (F - convectionDivergence u t x) - pressureGradient p t x :=
  navierStokesResidual_eq_iff_projected ν u p t x F hu

-- N4: weaken the conclusion of `projected_of_classicalSolution` from `Ioo 0 T` to `Ico 0 T`
set_option autoImplicit false in
theorem n4 (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
    (u : ClassicalSolutionR ν a f T) :
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
      temporalDerivative u.velocity t x - ν • spatialLaplacian u.velocity t x =
        (f (t, x) - convectionDivergence u.velocity t x)
          - pressureGradient u.pressure t x :=
  projected_of_classicalSolution ν a f T u

end NSFormalization.Section4.A01.NegA

/-! ## Section B — RadialPotential -/
namespace NSFormalization.Section4.A01.NegB
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A01.RadialPotential
open scoped ContDiff RealInnerProductSpace

-- N5: drop `hG` from `inner_fderiv_symm`
set_option autoImplicit false in
theorem n5 {G : SpatialField} (z v w : Space) :
    (inner ℝ (fderiv ℝ G z v) w : ℝ) = inner ℝ (fderiv ℝ G z w) v :=
  inner_fderiv_symm z v w

-- N6: drop `hG` from `hasFDerivAt_radialPotential`
set_option autoImplicit false in
theorem n6 {G : SpatialField} (hsmooth : ContDiff ℝ ∞ G) (x : Space) :
    HasFDerivAt (fun y => ∫ r in (0:ℝ)..1, (inner ℝ (G (r • y)) y : ℝ))
      (innerSL ℝ (G x)) x :=
  hasFDerivAt_radialPotential hsmooth x

-- N7: drop `hslice` from `pressureGradient_pressurePotential`
set_option autoImplicit false in
theorem n7 {G : SpatialField} {G' : SpaceTimeField} {t : ℝ}
    (hG : HasSymmetricJacobian G) (hsmooth : ContDiff ℝ ∞ G) (x : Space) :
    pressureGradient (pressurePotential G') t x = G x :=
  pressureGradient_pressurePotential hG hsmooth x

end NSFormalization.Section4.A01.NegB

/-! ## Section C — PressureGauge -/
namespace NSFormalization.Section4.A01.NegC
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A01.RadialPotential
open NSFormalization.Section4.A01.PressureGauge
open NSFormalization.Section4.A02 (PressureGaugeEquivOn)
open scoped ContDiff RealInnerProductSpace

-- N8: drop `hp` from `hasSymmetricJacobian_pressureGradient`
set_option autoImplicit false in
theorem n8 {T : ℝ} {p : PressureField} {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    HasSymmetricJacobian (fun x : Space => pressureGradient p t x) :=
  hasSymmetricJacobian_pressureGradient ht

-- N9: drop `hp` from `contDiff_gradSlice`
set_option autoImplicit false in
theorem n9 {T : ℝ} {p : PressureField} {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    ContDiff ℝ ∞ (fun y : Space => pressureGradient p t y) :=
  contDiff_gradSlice ht

-- N10: drop `hsym` from `pressure_potential_of_pointwise`
-- NOTE (REVIEW_SIMP.md F1): `hsym` is in fact REDUNDANT (derivable from `hsm` + `hdp`),
-- so this "failure" is spurious as load-bearing evidence — see `negative_simp.lean`
-- `Rev113.Gauge.pressure_potential_of_pointwise_without_hsym`, which proves this very
-- statement.  It fails here only because the signature still lists `hsym`.
set_option autoImplicit false in
theorem n10 {T : ℝ} (p : PressureField)
    (hsm : ∀ t ∈ Ico (0 : ℝ) T, ContDiff ℝ ∞ (fun y : Space => pressureGradient p t y))
    (hdp : ∀ t ∈ Ico (0 : ℝ) T, Differentiable ℝ (fun y : Space => p (t, y))) :
    PressureGaugeEquivOn (Ico (0 : ℝ) T)
      (pressurePotential (fun z : SpaceTime => pressureGradient p z.1 z.2)) p :=
  pressure_potential_of_pointwise p hsm hdp

-- N11: drop `h` from `fderiv_eq_of_pressureGradient_eq`
set_option autoImplicit false in
theorem n11 {p q : PressureField} {t : ℝ} (x : Space) :
    fderiv ℝ (fun y : Space => p (t, y)) x = fderiv ℝ (fun y : Space => q (t, y)) x :=
  fderiv_eq_of_pressureGradient_eq x

end NSFormalization.Section4.A01.NegC

end
