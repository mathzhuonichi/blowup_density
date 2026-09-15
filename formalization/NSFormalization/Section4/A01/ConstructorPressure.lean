import NSFormalization.Section4.A01.ConvectionDivergence
import NSFormalization.Section4.A01.RadialPotential
import NSFormalization.Section4.D01.DatumToJets
import NSFormalization.Section4.D01.LerayLowering
import NSFormalization.Section4.D01.OrderZeroAlgebra

/-!
# A01 constructor pressure (P7c)

This module constructs the scalar pressure attached to a candidate velocity.  The
pointwise vector field to integrate is the gradient forced by the unprojected
momentum equation,

`G = f - (u · ∇)u + νΔu - ∂ₜu`.

The pressure is the radial potential `∫₀¹ G(t,rx) · x dr`, hence is normalized by
`p(t,0) = 0`.  `pressureGradient_pressureOfVelocity` proves pointwise that its
spatial gradient is `G` when a slice is smooth and curl-free.  The datum theorem
`pressureGradient_pressureOfVelocity_lerayComplement` then identifies that
gradient with `D01.Leray.lerayComplement` of the momentum residual, provided the
candidate's projected equation has been transported to the order-zero datum
carrier.

There are two deliberately explicit regularity inputs.

* Slice smoothness and `HasSymmetricJacobian` are the spatial Helmholtz-to-classical
  bridge needed by the radial-potential theorem.
* Joint global smoothness of `pressureGradientOfVelocity` is an additional
  global, endpoint-compatible regularity hypothesis of
  `pressure_smooth_of_velocity_smooth`, not a consequence of c3 plus
  `MemForceR`.  The current tree has only half-open-slab smoothness of the
  candidate velocity; that does not by itself control the upstream two-sided
  `fderiv` used by `temporalDerivative` at `t = 0`.

The existing `D01.isSobolevDatum_pressureGradient_lerayComplement` cannot be used
to define this pressure: its first argument is already a `ClassicalSolutionR`.
The datum calculation below is its constructor-side, non-circular counterpart.
-/

noncomputable section

namespace NSFormalization.Section4.A01

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.D01
open NSFormalization.Paper3 (RealVectorSobolev)
open scoped ContDiff

/-- The smooth momentum-residual slice before removing the solenoidal time
derivative: `f - (u · ∇)u + νΔu`. -/
def momentumResidualOfVelocity (ν : ℝ) (f velocity : VelocityField) : VelocityField :=
  fun z => f z - advection velocity z.1 z.2 + ν • spatialLaplacian velocity z.1 z.2

/-- The candidate pressure gradient determined by the velocity and force:
`f - (u · ∇)u + νΔu - ∂ₜu`.  The projected equation says that this is the
Leray-complement part of `momentumResidualOfVelocity`. -/
def pressureGradientOfVelocity (ν : ℝ) (f velocity : VelocityField) : VelocityField :=
  fun z => momentumResidualOfVelocity ν f velocity z - temporalDerivative velocity z.1 z.2

/-- The pressure of a candidate velocity, in the radial/basepoint gauge. -/
def pressureOfVelocity (ν : ℝ) (f velocity : VelocityField) : PressureField :=
  RadialPotential.pressurePotential (pressureGradientOfVelocity ν f velocity)

/-- The fixed gauge is `p(t,0) = 0`. -/
theorem pressureOfVelocity_basepoint (ν : ℝ) (f velocity : VelocityField) (t : ℝ) :
    pressureOfVelocity ν f velocity (t, 0) = 0 := by
  simp [pressureOfVelocity, RadialPotential.pressurePotential]

/-- The pressure-gradient candidate is square-integrable whenever the momentum
residual and the time-derivative slices are square-integrable. -/
theorem pressureGradientOfVelocity_memLp (ν : ℝ) (f velocity : VelocityField) (t : ℝ)
    (hres : MemLp (fun x : Space => momentumResidualOfVelocity ν f velocity (t, x)) 2 volume)
    (htime : MemLp (fun x : Space => temporalDerivative velocity t x) 2 volume) :
    MemLp (fun x : Space => pressureGradientOfVelocity ν f velocity (t, x)) 2 volume := by
  exact hres.sub htime

/-- The radial potential differentiates back to the constructed gradient,
pointwise on a spatial slice. -/
theorem pressureGradient_pressureOfVelocity (ν : ℝ) (f velocity : VelocityField) (t : ℝ)
    (hsmooth : ContDiff ℝ ∞ (fun x : Space => pressureGradientOfVelocity ν f velocity (t, x)))
    (hsym : RadialPotential.HasSymmetricJacobian
      (fun x : Space => pressureGradientOfVelocity ν f velocity (t, x))) (x : Space) :
    pressureGradient (pressureOfVelocity ν f velocity) t x =
      pressureGradientOfVelocity ν f velocity (t, x) := by
  exact RadialPotential.pressureGradient_pressurePotential hsym hsmooth (fun _ => rfl) x

/-- Constructor-side eq:Rpressure at order zero.  If the projected equation says
that the datum of `∂ₜu` is `A - (I-P)A`, then the datum of the constructed
pressure gradient is `(I-P)A`.  This is the type-correct form of
`∇p = (I-P)(f - (u·∇)u + νΔu)` for the tree's datum-valued Leray operator. -/
theorem pressureGradient_pressureOfVelocity_lerayComplement
    (ν : ℝ) (f velocity : VelocityField) (t : ℝ)
    (hsmooth : ContDiff ℝ ∞ (fun x : Space => pressureGradientOfVelocity ν f velocity (t, x)))
    (hsym : RadialPotential.HasSymmetricJacobian
      (fun x : Space => pressureGradientOfVelocity ν f velocity (t, x)))
    (hres : MemLp (fun x : Space => momentumResidualOfVelocity ν f velocity (t, x)) 2 volume)
    (htime : MemLp (fun x : Space => temporalDerivative velocity t x) 2 volume)
    (hprojected :
      orderZeroDatum htime = orderZeroDatum hres -
        Leray.lerayComplement 0 (orderZeroDatum hres)) :
    IsSobolevDatum 0
      (fun x : Space => pressureGradient (pressureOfVelocity ν f velocity) t x)
      (Leray.lerayComplement 0 (orderZeroDatum hres)) := by
  have hgrad := pressureGradientOfVelocity_memLp ν f velocity t hres htime
  have hdatum : orderZeroDatum hgrad = orderZeroDatum hres - orderZeroDatum htime :=
    orderZeroDatum_sub hres htime
  have hdatum_leray :
      orderZeroDatum hgrad = Leray.lerayComplement 0 (orderZeroDatum hres) := by
    rw [hdatum, hprojected]
    abel
  have hphysical : IsSobolevDatum 0
      (fun x : Space => pressureGradientOfVelocity ν f velocity (t, x))
      (Leray.lerayComplement 0 (orderZeroDatum hres)) := by
    rw [← hdatum_leray]
    exact isSobolevDatum_orderZeroDatum hgrad
  have hfield :
      (fun x : Space => pressureGradient (pressureOfVelocity ν f velocity) t x) =
        fun x : Space => pressureGradientOfVelocity ν f velocity (t, x) := by
    funext x
    exact pressureGradient_pressureOfVelocity ν f velocity t hsmooth hsym x
  rwa [hfield]

/-- All-order constructor-side eq:Rpressure.  Once the order-zero projected
equation has pinned the physical pressure gradient, any order-`m` residual
datum is sent to the order-`m` pressure-gradient datum by the Leray complement.
This is the construction analogue of
`D01.isSobolevDatum_pressureGradient_lerayComplement`. -/
theorem pressureGradient_pressureOfVelocity_lerayComplement_order
    (ν : ℝ) (f velocity : VelocityField) (t : ℝ) (m : ℕ)
    (hsmooth : ContDiff ℝ ∞ (fun x : Space => pressureGradientOfVelocity ν f velocity (t, x)))
    (hsym : RadialPotential.HasSymmetricJacobian
      (fun x : Space => pressureGradientOfVelocity ν f velocity (t, x)))
    (hres : MemLp (fun x : Space => momentumResidualOfVelocity ν f velocity (t, x)) 2 volume)
    (htime : MemLp (fun x : Space => temporalDerivative velocity t x) 2 volume)
    (hprojected :
      orderZeroDatum htime = orderZeroDatum hres -
        Leray.lerayComplement 0 (orderZeroDatum hres))
    {Am : RealVectorSobolev (m : ℝ)}
    (hAm : IsSobolevDatum (m : ℝ)
      (fun x : Space => momentumResidualOfVelocity ν f velocity (t, x)) Am) :
    IsSobolevDatum (m : ℝ)
      (fun x : Space => pressureGradient (pressureOfVelocity ν f velocity) t x)
      (Leray.lerayComplement (m : ℝ) Am) := by
  have h0m : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  refine (Leray.isSobolevDatum_lower_iff h0m).mp ?_
  have hlower : lowerVectorL (m : ℝ) 0 h0m Am = orderZeroDatum hres :=
    isSobolevDatum_unique (Leray.isSobolevDatum_lower h0m hAm)
      (isSobolevDatum_orderZeroDatum hres)
  rw [← Leray.lerayComplement_lowerVectorL, hlower]
  exact pressureGradient_pressureOfVelocity_lerayComplement
    ν f velocity t hsmooth hsym hres htime hprojected

/-- The `ClassicalSolutionR.pressure_gradient` field for the constructed
pressure, on one time slice. -/
theorem pressure_gradient_memLp_slice (ν : ℝ) (f velocity : VelocityField) (t : ℝ)
    (hsmooth : ContDiff ℝ ∞ (fun x : Space => pressureGradientOfVelocity ν f velocity (t, x)))
    (hsym : RadialPotential.HasSymmetricJacobian
      (fun x : Space => pressureGradientOfVelocity ν f velocity (t, x)))
    (hres : MemLp (fun x : Space => momentumResidualOfVelocity ν f velocity (t, x)) 2 volume)
    (htime : MemLp (fun x : Space => temporalDerivative velocity t x) 2 volume) :
    MemLp (fun x : Space => pressureGradient (pressureOfVelocity ν f velocity) t x) 2 volume := by
  have hfield :
      (fun x : Space => pressureGradient (pressureOfVelocity ν f velocity) t x) =
        fun x : Space => pressureGradientOfVelocity ν f velocity (t, x) := by
    funext x
    exact pressureGradient_pressureOfVelocity ν f velocity t hsmooth hsym x
  rw [hfield]
  exact pressureGradientOfVelocity_memLp ν f velocity t hres htime

/-- The full `ClassicalSolutionR.pressure_gradient` row on `[0,T)`. -/
theorem pressure_gradient_memLp {T : ℝ} (ν : ℝ) (f velocity : VelocityField)
    (hsmooth : ∀ t ∈ Ico (0 : ℝ) T,
      ContDiff ℝ ∞ (fun x : Space => pressureGradientOfVelocity ν f velocity (t, x)))
    (hsym : ∀ t ∈ Ico (0 : ℝ) T,
      RadialPotential.HasSymmetricJacobian
        (fun x : Space => pressureGradientOfVelocity ν f velocity (t, x)))
    (hres : ∀ t ∈ Ico (0 : ℝ) T,
      MemLp (fun x : Space => momentumResidualOfVelocity ν f velocity (t, x)) 2 volume)
    (htime : ∀ t ∈ Ico (0 : ℝ) T,
      MemLp (fun x : Space => temporalDerivative velocity t x) 2 volume) :
    ∀ t ∈ Ico (0 : ℝ) T,
      MemLp (fun x : Space => pressureGradient (pressureOfVelocity ν f velocity) t x) 2 volume := by
  intro t ht
  exact pressure_gradient_memLp_slice ν f velocity t
    (hsmooth t ht) (hsym t ht) (hres t ht) (htime t ht)

/-- Spatial smoothness of each pressure slice.  This part needs only spatial
smoothness of the constructed gradient and is independent of joint time
regularity. -/
theorem pressureOfVelocity_slice_smooth (ν : ℝ) (f velocity : VelocityField) (t : ℝ)
    (hsmooth : ContDiff ℝ ∞ (fun x : Space => pressureGradientOfVelocity ν f velocity (t, x))) :
    ContDiff ℝ ∞ (fun x : Space => pressureOfVelocity ν f velocity (t, x)) := by
  have hF : ContDiff ℝ ∞ (fun p : Space × ℝ =>
      (inner ℝ (pressureGradientOfVelocity ν f velocity (t, p.2 • p.1)) p.1 : ℝ)) :=
    (hsmooth.comp (contDiff_snd.smul contDiff_fst)).inner ℝ contDiff_fst
  exact EulerCompactParameterIntegral.integral_contDiff 0 1 (by norm_num) _ hF

/-- Joint pressure smoothness from the additional global, endpoint-compatible
regularity hypothesis that the selected Leray-gradient field is jointly smooth.
This input is not implied by c3 plus `MemForceR`: their half-open-slab
regularity does not control the two-sided `temporalDerivative` at the initial
endpoint. -/
theorem pressure_smooth_of_velocity_smooth {T : ℝ} (ν : ℝ)
    (f velocity : VelocityField)
    (hjoint : ContDiff ℝ ∞ (pressureGradientOfVelocity ν f velocity)) :
    ContDiffOn ℝ ∞ (pressureOfVelocity ν f velocity)
      (Ico (0 : ℝ) T ×ˢ (univ : Set Space)) := by
  let F : SpaceTime × ℝ → ℝ := fun p =>
    inner ℝ (pressureGradientOfVelocity ν f velocity (p.1.1, p.2 • p.1.2)) p.1.2
  have harg : ContDiff ℝ ∞
      (fun p : SpaceTime × ℝ => ((p.1.1, p.2 • p.1.2) : SpaceTime)) := by
    fun_prop
  have hx : ContDiff ℝ ∞ (fun p : SpaceTime × ℝ => p.1.2) := by
    fun_prop
  have hF : ContDiff ℝ ∞ F := (hjoint.comp harg).inner ℝ hx
  exact (EulerCompactParameterIntegral.integral_contDiff 0 1 (by norm_num) F hF).contDiffOn

/-- Momentum follows once the explicitly defined `G = R - ∂ₜu` is smooth and
curl-free.  The genuine mild/Leray projected input is instead the datum equality
used by `pressureGradient_pressureOfVelocity_lerayComplement`; the pointwise
identity needed here follows algebraically from the definitions and
incompressibility. -/
theorem momentum_of_projected {T : ℝ} (ν : ℝ) (f velocity : VelocityField)
    (hvelocity : ContDiffOn ℝ ∞ velocity (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (hdiv : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, spatialDivergence velocity t x = 0)
    (hgradient_smooth : ∀ t ∈ Ioo (0 : ℝ) T,
      ContDiff ℝ ∞ (fun x : Space => pressureGradientOfVelocity ν f velocity (t, x)))
    (hgradient_symm : ∀ t ∈ Ioo (0 : ℝ) T,
      RadialPotential.HasSymmetricJacobian
        (fun x : Space => pressureGradientOfVelocity ν f velocity (t, x))) :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual
        ν velocity (pressureOfVelocity ν f velocity) t x = f (t, x) := by
  intro t ht x
  have htIco : t ∈ Ico (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
  have hu : DifferentiableAt ℝ (fun y : Space => velocity (t, y)) x :=
    ((D01.contDiff_slice hvelocity htIco).differentiable (by simp)) x
  refine (navierStokesResidual_eq_iff_projected ν velocity
    (pressureOfVelocity ν f velocity) t x (f (t, x)) hu (hdiv t htIco x)).2 ?_
  rw [pressureGradient_pressureOfVelocity ν f velocity t
    (hgradient_smooth t ht) (hgradient_symm t ht) x]
  rw [convectionDivergence_eq_advection velocity t x hu (hdiv t htIco x)]
  simp only [pressureGradientOfVelocity, momentumResidualOfVelocity]
  abel

/-- Non-vacuity: zero force and zero velocity produce exactly the zero pressure
in the fixed radial gauge. -/
theorem pressureOfVelocity_zero (ν : ℝ) :
    pressureOfVelocity ν (0 : VelocityField) (0 : VelocityField) = 0 := by
  funext z
  simp [pressureOfVelocity, RadialPotential.pressurePotential,
    pressureGradientOfVelocity, momentumResidualOfVelocity, advection,
    spatialLaplacian, spatialDerivative, temporalDerivative]

end NSFormalization.Section4.A01
