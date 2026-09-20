import NSFormalization.Section3.T17.Correction

/-!
# T17 U4b probe: the canonical periodized force-profile identity

This probe closes `CorrectionAPI.force_profile_identity` at the concrete
`correctionData`.  Its hypotheses are fields already available before
`force_profile_identity` in the canonical record, together with the documented
G1 premise `hv : ContDiff ℝ ∞ v`.
-/

noncomputable section

namespace NSFormalization.Section3.T17

open Set Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 (IsPeriodicOn)
open NSFormalization.Section3.T13 (fundamentalCube two_r_lt_one_of_closure_ball_subset)
open NSFormalization.Section3.T15 (PlacementData)
open NSFormalization.Section3.T16
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Paper1.CorrectionProfile (physicalCorrection)
open NSFormalization.Source.PhysicalRemoval (physical_support)
open scoped ContDiff Topology

/-- The canonical `force_profile_identity` field, literally specialized to
the concrete T17 cutoff/correction data. -/
theorem force_profile_identity_canonical (nu : ℝ)
    {u : VelocityField} {p : PressureField} {f : VelocityField} {K : Set Space}
    (place : PlacementData u p f K) {v : SpaceTimeField} {r delta : ℝ}
    {theta : Space → ℝ} {eta : ℝ → ℝ} {O : Set Space} {thetaR eps0 : ℝ}
    (hv : ContDiff ℝ ∞ v)
    (hpotential : LocalPotentialAPI v u place.Kstar place.x₀ r place.T delta
      (correctionData v place.x₀ place.T theta eta O thetaR eps0))
    (hr : 0 < r)
    (hball : ball place.x₀ r ⊆ ball place.chartCenter place.chartRadius)
    (hvperiodic : IsPeriodicOn univ v) :
    ∀ eps ∈ Ioc (0 : ℝ)
        (correctionData v place.x₀ place.T theta eta O thetaR eps0).ε₀,
      ∀ z ∈ fixedProfileCylinder
          (correctionData v place.x₀ place.T theta eta O thetaR eps0),
        correctionForce nu v
            (correctionData v place.x₀ place.T theta eta O thetaR eps0) eps
            (correctionChartPoint place.x₀ place.T eps z) =
          (eps ^ 2)⁻¹ • rescaledForceProfile nu v place.x₀ place.T eps
            (correctionData v place.x₀ place.T theta eta O thetaR eps0) z := by
  intro eps heps z hz
  let D := correctionData v place.x₀ place.T theta eta O thetaR eps0
  let W := physicalCorrection v place.x₀ place.T theta eta eps
  let G := NSFormalization.Source.correctionForce nu v W
  have hchart : closure (ball place.x₀ r) ⊆ interior fundamentalCube :=
    (closure_mono hball).trans place.chartBall_in_cube
  have htwo : 2 * r < 1 :=
    two_r_lt_one_of_closure_ball_subset hr hchart
  have hrhalf : r < 1 / 2 := by linarith
  have hrr : r + r ≤ 1 := by linarith
  have hforce := force_eq (ν := nu) (v := v) (x₀ := place.x₀)
    (T := place.T) (δ := delta) (r := r) (θ := theta) (η := eta)
    (O := O) (θR := thetaR) (ε₀ := eps0) (ε := eps)
    hvperiodic hv.contDiffOn hpotential.theta_smooth hpotential.eta_smooth
    hpotential.theta_compactSupport hpotential.eta_compactSupport
    hpotential.theta_support hpotential.eta_support hrhalf heps.1
    (hpotential.eps_space eps heps) (hpotential.eps_time eps heps)
  have hWsupport :
      tsupport W ⊆
        Ioo (place.T - 2 * eps ^ 2) (place.T + 2 * eps ^ 2) ×ˢ
          ball place.x₀ (eps * thetaR) := by
    exact physical_support heps.1 v place.x₀ place.T
      hpotential.theta_compactSupport hpotential.eta_compactSupport
      hpotential.theta_support hpotential.eta_support
  have hWslice : ∀ (t : ℝ) (x : Space), W (t, x) ≠ 0 →
      x ∈ ball place.x₀ (eps * thetaR) := by
    intro t x hx
    exact (hWsupport (subset_tsupport W hx)).2
  have hGslice : ∀ (t : ℝ) (x : Space), G (t, x) ≠ 0 →
      x ∈ ball place.x₀ r := by
    intro t x hx
    by_contra hxr
    apply hx
    apply source_correctionForce_support hWslice t x
    intro hxclosed
    exact hxr (closedBall_subset_ball (hpotential.eps_space eps heps) hxclosed)
  obtain ⟨sigma, y⟩ := z
  have hyball : y ∈ closedBall (0 : Space) thetaR := by
    simpa [fixedProfileCylinder, correctionData, localPotentialData] using hz.2
  have hy : ‖y‖ ≤ thetaR := by
    simpa [mem_closedBall, dist_eq_norm] using hyball
  have hxchart : place.x₀ + eps • y ∈ ball place.x₀ r := by
    rw [mem_ball, dist_eq_norm]
    have hnorm : ‖place.x₀ + eps • y - place.x₀‖ = eps * ‖y‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos heps.1]
    rw [hnorm]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hy heps.1.le)
      (hpotential.eps_space eps heps)
  rw [congrFun hforce (correctionChartPoint place.x₀ place.T eps (sigma, y))]
  change latticeLift G (place.T + eps ^ 2 * sigma, place.x₀ + eps • y) = _
  rw [latticeLift_eq_of_ball hGslice hrr hxchart]
  exact physicalForce_eq_rescaledForceProfile nu hv place.x₀ place.T D
    hpotential.theta_smooth hpotential.eta_smooth eps heps (sigma, y) hz

end NSFormalization.Section3.T17

/-! The probe declaration has exactly Lean's three standard axioms. -/

/-- info: 'NSFormalization.Section3.T17.force_profile_identity_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms NSFormalization.Section3.T17.force_profile_identity_canonical
