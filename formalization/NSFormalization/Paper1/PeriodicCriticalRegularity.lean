import NSFormalization.Paper1.PeriodicTestForceNorm
import NSFormalization.Paper1.PeriodicMain
import NSFormalization.Paper1.PeriodicLocalLifespan
import NSFormalization.Paper1.PeriodicInitialData
import NSFormalization.Paper1.ManuscriptTopology

/-!
# Critical regularity and the zero-data regular ball

This file states Proposition `prop:critical` for the actual smooth periodic
force class and the supremum of actual classical flow horizons. The analytic
proof is admitted, as permitted for this formalization stage. Its statement
has no mean-zero-force assumption and its constant precedes the viscosity
and force quantifiers. The proof plan is exactly the manuscript's mean
removal, critical energy bootstrap, H1 energy estimate and squared-H2
continuation argument. Fourier-order monotonicity and the separation of the
singular slice are proved here from existing definitions.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicCriticalRegularity

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Source
open PeriodicForceSpace PeriodicForceConvergence PeriodicDensityFiber
open PeriodicTestForceNorm PeriodicLifespan PeriodicDense PeriodicMain
open PeriodicInitialData PeriodicLocalLifespan PeriodicDensityDichotomy
open ManuscriptTopology
open scoped ContDiff ENNReal

/-- The vector norm inherits the exact Bessel-weight monotonicity at every
real order. Smoothness supplies all coefficient summability obligations. -/
theorem periodicVectorSobolevNorm_mono {F : VelocityField}
    (hF : IsTestForce F) {s r : ℝ} (hsr : s ≤ r) (t : ℝ) :
    periodicVectorSobolevNorm s F t ≤ periodicVectorSobolevNorm r F t := by
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  apply periodicSobolevSq_mono_smooth
    ((coordinateForce_smooth hF.smooth i).comp
      (contDiff_const.prodMk contDiff_id)) _ hsr
  intro x j
  exact congrArg (fun v : Space => (v i : ℂ))
    (hF.periodic t (mem_univ _) x j)

/-- Monotonicity for the actual time L1 distance, including all real orders. -/
theorem forceDistance_order_mono {F G : VelocityField}
    (hF : IsTestForce F) (hG : IsTestForce G) {s r : ℝ} (hsr : s ≤ r) :
    forceDistance s F G ≤ forceDistance r F G := by
  apply eLpNorm_mono_real
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact periodicVectorSobolevNorm_mono (isTestForce_sub hF hG) hsr t
  · exact Real.sqrt_nonneg _

/-- The analytic certificate needed for the critical regularity proposition.

The fields deliberately expose the whole PDE bridge (mean removal, the
critical energy estimate, and continuation) instead of hiding it behind an
axiom.  Constructing this certificate is the remaining analytic task; all
consequences below are elementary and kernel-checkable once it is supplied.
-/
structure CriticalRegularityCertificate where
  radius : ℝ
  radius_pos : 0 < radius
  global_lifespan : ∀ ν : ℝ, 0 < ν → ∀ g : TestForce,
    forceDistance (1 / 2 : ℝ) g.1 0 < ENNReal.ofReal (radius * ν) →
      lifespan ν (fun _ : Space => 0) g.1 = ⊤

/-- Paper 1 `prop:critical`, conditional on its explicit analytic certificate.
The force need not have zero spatial mean. -/
theorem exists_critical_regularity_constant
    (H : CriticalRegularityCertificate) :
    ∃ c : ℝ, 0 < c ∧ ∀ ν : ℝ, 0 < ν → ∀ g : TestForce,
      forceDistance (1 / 2 : ℝ) g.1 0 < ENNReal.ofReal (c * ν) →
        lifespan ν (fun _ : Space => 0) g.1 = ⊤ := by
  exact ⟨H.radius, H.radius_pos, H.global_lifespan⟩

/-- The same positive radius works for every order at or above one half
and every finite positive deadline. -/
theorem critical_regular_ball (H : CriticalRegularityCertificate)
    {ν T s : ℝ} (hν : 0 < ν)
    (hs : (1 : ℝ) / 2 ≤ s) :
    GaugeSeparated ν (fun _ : Space => 0) T s := by
  obtain ⟨c, hc, hglobal⟩ := exists_critical_regularity_constant H
  refine ⟨⟨0, isTestForce_zero⟩, ENNReal.ofReal (c * ν),
    ENNReal.ofReal_pos.mpr (mul_pos hc hν), ?_⟩
  intro G hG hsmall
  have hsmall' : forceDistance (1 / 2 : ℝ) G.1 0 < ENNReal.ofReal (c * ν) :=
    lt_of_le_of_lt (forceDistance_order_mono G.2 isTestForce_zero hs) hsmall
  have htop := hglobal ν hν G hsmall'
  change lifespan ν (fun _ : Space => 0) G.1 ≤ ENNReal.ofReal T at hG
  rw [htop] at hG
  exact ENNReal.ofReal_ne_top (top_le_iff.mp hG)

/-- Main-chain assembly using the local-existence contract and the critical
regularity theorem stated in this file. This is the closest formal analogue
of Paper 1's `thm:main`; only the admitted analytic bridges remain. -/
theorem paper1_main_with_critical_interfaces
    (H : CriticalRegularityCertificate)
    {ν T s : ℝ} (hν : 0 < ν) (hT : 0 < T)
    (hlocal : UnforcedLocalExistence ν) :
    (s < (1 : ℝ) / 2 →
      ∀ a : Space → Space, IsAdmissibleInitialData a →
        GaugeDense ν a T s) ∧
      (GaugeDense ν (fun _ : Space => 0) T s ↔ s < (1 : ℝ) / 2) := by
  apply paper1_main hν hT hlocal
  intro hs
  exact critical_regular_ball H hν hs

/-- Topological form of the same assembly, using the relative
`L¹(0,∞;H^s)` metric on the actual smooth periodic force class. -/
theorem paper1_main_topological
    {ν T s : ℝ} (hν : 0 < ν) (hT : 0 < T)
    (hlocal : UnforcedLocalExistence ν) :
    s < (1 : ℝ) / 2 →
      ∀ a : Space → Space, IsAdmissibleInitialData a →
        DenseAt s (singularSlice ν a T) := by
  intro hs a ha
  exact admissible_slice_dense hν hT hs hlocal ha

end NSFormalization.Paper1.PeriodicCriticalRegularity
