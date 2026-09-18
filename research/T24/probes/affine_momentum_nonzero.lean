import Contracts.V1.Packet
import Bindings.Packet
import NSFormalization.Section3.T24.AffineMomentum
import NavierStokes.SpatialCurl
import NavierStokes.OscillatoryCurl
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Ua3 / Ua7 core — a nonzero admissible perturbation `b`

Run from `verification/` with
`lake env lean ../research/T24/probes/affine_momentum_nonzero.lean`.

The `momentum` field of `AffineVariationAPI` quantifies over the admissible class
`AffineAdmissible c r τ₀ τ₁`; the `b = 0` probe (`affine_momentum_closes.lean`)
shows the class is inhabited but not that it contains a *nonzero* element.  This
file builds one: `b := spatialCurl A` for the smooth compactly supported vector
potential `A(t,x) = θ(t) φ(x) e₁` (`θ`, `φ` `ContDiffBump`s in the time window and
the ball).  Then

* `∇·b = 0` by `NavierStokes.SpatialCurl.spatialDivergence_spatialCurl`
  (curl is solenoidal),
* `b` is smooth (`contDiff_spatialCurl`) and compactly supported inside the
  cylinder (`spatialCurl_tsupport_subset`), so `AffineAdmissible … b` holds, and
* `b ≠ 0`: if `spatialCurl A ≡ 0`, then the `e₂`-component of `curl(φ • e₁)`
  vanishes identically, i.e. `∂₃φ ≡ 0`; but a bump constant along the `e₃`-line
  through the origin would be `1` arbitrarily far out, contradicting compact
  support.

`b` is a concrete nonzero admissible perturbation for the cylinder
`ball 0 1 × (1/4, 3/4)` (`0 < 1`, `0 < 1/4 < 3/4 < 1`), and
`nonzero_admissible_momentum` instantiates the proved `momentum` at it on the
registered packet.  This is exactly the single-bump witness that unit **Ua7**
needs.
-/

noncomputable section

open NavierStokes.ProblemStatement NavierStokes.SpatialCurl Set
open NSFormalization.Section3.T24
open scoped ContDiff

namespace BlowupDensity.T24.NonzeroProbe

/-- Time bump: plateau radius `1/16`, support radius `1/8`, centred at `1/2`. -/
def timeBump : ContDiffBump ((1 : ℝ) / 2) := ⟨1 / 16, 1 / 8, by norm_num, by norm_num⟩

/-- Spatial bump: plateau radius `1/2`, support radius `3/4`, centred at `0`. -/
def spaceBump : ContDiffBump (0 : Space) := ⟨1 / 2, 3 / 4, by norm_num, by norm_num⟩

/-- The smooth compactly supported vector potential `A(t,x) = θ(t) φ(x) e₁`. -/
def potentialA : VelocityField :=
  fun z => (timeBump z.1 * spaceBump z.2) • coordinateVector 0

/-- The perturbation `b := ∇ × A`. -/
def bWitness : VelocityField := spatialCurl potentialA

/-- The `e₂`-component of the curl of `g • e₁` is `∂₃ g` (`fderiv g x e₃`). -/
theorem curl_component_one (g : Space → ℝ) (x : Space)
    (hg : DifferentiableAt ℝ g x) :
    (curl (fun y => g y • coordinateVector 0) x) 1 =
      fderiv ℝ g x (coordinateVector 2) := by
  unfold curl
  rw [fderiv_smul_const hg, curlLinear_apply_one]
  simp [coordinateVector, ContinuousLinearMap.smulRight_apply]

/-- The compact carrier `closedBall(1/2, 1/8) × closedBall(0, 3/4)`. -/
def carrierK : Set SpaceTime :=
  Metric.closedBall ((1 : ℝ) / 2) (1 / 8) ×ˢ Metric.closedBall (0 : Space) (3 / 4)

theorem potentialA_contDiff : ContDiff ℝ ∞ potentialA := by
  have hw : ContDiff ℝ ∞ (fun z : SpaceTime => timeBump z.1 * spaceBump z.2) :=
    (timeBump.contDiff.comp contDiff_fst).mul (spaceBump.contDiff.comp contDiff_snd)
  exact hw.smul contDiff_const

theorem tsupport_potentialA_subset_carrier : tsupport potentialA ⊆ carrierK := by
  apply closure_minimal _ (Metric.isClosed_closedBall.prod Metric.isClosed_closedBall)
  intro z hz
  have hne : timeBump z.1 * spaceBump z.2 ≠ 0 := by
    intro h0
    apply hz
    show (timeBump z.1 * spaceBump z.2) • coordinateVector 0 = 0
    rw [h0, zero_smul]
  have h1 : timeBump z.1 ≠ 0 := fun h => hne (by rw [h, zero_mul])
  have h2 : spaceBump z.2 ≠ 0 := fun h => hne (by rw [h, mul_zero])
  have hz1 : z.1 ∈ tsupport (⇑timeBump) := subset_tsupport _ (Function.mem_support.mpr h1)
  have hz2 : z.2 ∈ tsupport (⇑spaceBump) := subset_tsupport _ (Function.mem_support.mpr h2)
  rw [timeBump.tsupport_eq] at hz1
  rw [spaceBump.tsupport_eq] at hz2
  exact ⟨hz1, hz2⟩

theorem carrierK_subset_cylinder :
    carrierK ⊆ affineCylinder (0 : Space) 1 (1 / 4) (3 / 4) := by
  apply Set.prod_mono
  · rw [Real.closedBall_eq_Icc]
    exact Icc_subset_Ioo (by norm_num) (by norm_num)
  · exact Metric.closedBall_subset_ball (by norm_num)

theorem potentialA_hasCompactSupport : HasCompactSupport potentialA := by
  have hK : IsCompact carrierK :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  apply HasCompactSupport.intro hK
  intro z hz
  by_contra h
  exact hz (tsupport_potentialA_subset_carrier (subset_tsupport potentialA h))

theorem bWitness_contDiff : ContDiff ℝ ∞ bWitness :=
  contDiff_spatialCurl potentialA_contDiff (by simp)

theorem bWitness_hasCompactSupport : HasCompactSupport bWitness :=
  potentialA_hasCompactSupport.of_isClosed_subset (isClosed_tsupport _)
    (NavierStokes.OscillatoryCurl.spatialCurl_tsupport_subset potentialA)

theorem bWitness_tsupport_subset :
    tsupport bWitness ⊆ affineCylinder (0 : Space) 1 (1 / 4) (3 / 4) :=
  (NavierStokes.OscillatoryCurl.spatialCurl_tsupport_subset potentialA).trans
    (tsupport_potentialA_subset_carrier.trans carrierK_subset_cylinder)

theorem bWitness_divergence_free :
    ∀ t : ℝ, ∀ x : Space, spatialDivergence bWitness t x = 0 := by
  intro t x
  have hslice : ContDiffAt ℝ 2 (fun y : Space => potentialA (t, y)) x :=
    ((potentialA_contDiff.comp (contDiff_const.prodMk contDiff_id)).contDiffAt).of_le
      (by norm_num)
  exact spatialDivergence_spatialCurl potentialA t x hslice

/-- The nonzero admissible witness. -/
theorem bWitness_admissible :
    AffineAdmissible (0 : Space) 1 (1 / 4) (3 / 4) bWitness :=
  ⟨bWitness_contDiff, bWitness_hasCompactSupport, bWitness_tsupport_subset,
    bWitness_divergence_free⟩

theorem bWitness_ne_zero : bWitness ≠ 0 := by
  intro hb0
  have hφsmooth : ContDiff ℝ ∞ (⇑spaceBump) := spaceBump.contDiff
  -- On the plateau slice `t = 1/2` the potential is `φ • e₁`, so its curl vanishes.
  have hcurl0 : ∀ x : Space,
      curl (fun y => spaceBump y • coordinateVector 0) x = 0 := by
    intro x
    have hslice : (fun y : Space => potentialA ((1 : ℝ) / 2, y)) =
        (fun y : Space => spaceBump y • coordinateVector 0) := by
      funext y
      have h1 : timeBump ((1 : ℝ) / 2) = 1 :=
        timeBump.one_of_mem_closedBall (Metric.mem_closedBall_self timeBump.rIn_pos.le)
      show (timeBump ((1 : ℝ) / 2) * spaceBump y) • coordinateVector 0 =
        spaceBump y • coordinateVector 0
      rw [h1, one_mul]
    have hz : spatialCurl potentialA ((1 : ℝ) / 2, x) = 0 := by
      have := congrFun hb0 ((1 : ℝ) / 2, x)
      simpa [bWitness] using this
    calc curl (fun y => spaceBump y • coordinateVector 0) x
        = curl (fun y => potentialA ((1 : ℝ) / 2, y)) x := by rw [hslice]
      _ = spatialCurl potentialA ((1 : ℝ) / 2, x) := rfl
      _ = 0 := hz
  -- Hence `∂₃ φ ≡ 0`.
  have hpartial : ∀ x : Space, fderiv ℝ (⇑spaceBump) x (coordinateVector 2) = 0 := by
    intro x
    have hcomp := curl_component_one (⇑spaceBump) x
      (hφsmooth.differentiable (by simp) x)
    have hzero := congrArg (fun v : Space => v 1) (hcurl0 x)
    rw [hcomp] at hzero
    simpa using hzero
  -- `ψ s := φ(s • e₃)` has zero derivative, so it is constant `= φ 0 = 1`.
  have hψ_diff : Differentiable ℝ (fun s : ℝ => spaceBump (s • coordinateVector 2)) :=
    (hφsmooth.differentiable (by simp)).comp (differentiable_id.smul_const _)
  have hψ_deriv : ∀ s : ℝ,
      deriv (fun s : ℝ => spaceBump (s • coordinateVector 2)) s = 0 := by
    intro s
    have hline : HasDerivAt (fun r : ℝ => r • coordinateVector 2)
        (coordinateVector 2) s := by
      simpa using (hasDerivAt_id s).smul_const (coordinateVector 2)
    have hd : DifferentiableAt ℝ (⇑spaceBump) (s • coordinateVector 2) :=
      (hφsmooth.differentiable (by simp)).differentiableAt
    have hcomp := hd.hasFDerivAt.comp_hasDerivAt s hline
    have hderiv := hcomp.deriv
    rw [hpartial (s • coordinateVector 2)] at hderiv
    exact hderiv
  have hconst := is_const_of_deriv_eq_zero hψ_diff hψ_deriv
  have h10 : (fun s : ℝ => spaceBump (s • coordinateVector 2)) 1 =
      (fun s : ℝ => spaceBump (s • coordinateVector 2)) 0 := hconst 1 0
  have hψ0 : (fun s : ℝ => spaceBump (s • coordinateVector 2)) 0 = 1 := by
    show spaceBump ((0 : ℝ) • coordinateVector 2) = 1
    rw [zero_smul]
    exact spaceBump.one_of_mem_closedBall (Metric.mem_closedBall_self spaceBump.rIn_pos.le)
  have hψ1 : (fun s : ℝ => spaceBump (s • coordinateVector 2)) 1 = 0 := by
    show spaceBump ((1 : ℝ) • coordinateVector 2) = 0
    rw [one_smul]
    apply image_eq_zero_of_notMem_tsupport (f := ⇑spaceBump)
    rw [spaceBump.tsupport_eq]
    have hnorm : ‖coordinateVector 2‖ = 1 := by simp [coordinateVector]
    simp only [Metric.mem_closedBall, dist_zero_right, hnorm, not_le]
    show spaceBump.rOut < 1
    norm_num [spaceBump]
  rw [hψ0, hψ1] at h10
  exact absurd h10 (by norm_num)

/-- The proved `momentum` field instantiated at the nonzero admissible witness on
the registered packet `Bindings.packet ν hν`. -/
theorem nonzero_admissible_momentum (ν : ℝ) (hν : 0 < ν) :
    ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν
          (affineVelocity (BlowupDensity.Bindings.packet ν hν).velocity bWitness)
          (affinePressure (BlowupDensity.Bindings.packet ν hν).pressure) t x =
        affineForce ν (BlowupDensity.Bindings.packet ν hν).velocity
          (BlowupDensity.Bindings.packet ν hν).force bWitness (t, x) :=
  momentum (0 : Space) 1 (1 / 4) (3 / 4)
    (BlowupDensity.Bindings.packet ν hν).velocity_smooth
    (BlowupDensity.Bindings.packet ν hν).navier_stokes bWitness bWitness_admissible

#print axioms bWitness_admissible
#print axioms bWitness_ne_zero
#print axioms nonzero_admissible_momentum

end BlowupDensity.T24.NonzeroProbe
