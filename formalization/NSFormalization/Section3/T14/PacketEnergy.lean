import NSFormalization.Source.PacketEnergy
import NavierStokes.R3.ProblemStatement
import NavierStokes.PeriodicUniqueness
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

namespace NSFormalization.Section3.T14

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NavierStokesR3.CompactEnergy
open NavierStokes.PeriodicUniqueness (slab)
open NSFormalization.Source.PacketEnergy
open scoped ContDiff Topology

/-- The accumulated force used in the packet estimate. -/
def accumulatedForce (F : VelocityField) (t : ℝ) : ℝ :=
  ∫ s in Ioo (0 : ℝ) t, Real.sqrt (l2Sq F s)

theorem force_slice_support_subset {f : VelocityField}
    (hf : HasCompactSupport f) (t : ℝ) :
    tsupport (fun x : Space => f (t, x)) ⊆ Prod.snd '' tsupport f := by
  let K : Set Space := Prod.snd '' tsupport f
  have hK : IsCompact K := hf.isCompact.image continuous_snd
  have hzero : ∀ x ∉ K, f (t, x) = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport (f := f)
    intro htx
    exact hx ⟨(t, x), htx, rfl⟩
  apply closure_minimal _ hK.isClosed
  intro x hx
  change f (t, x) ≠ 0 at hx
  by_contra hnot
  exact hx (hzero x hnot)

theorem force_slice_support_subset_all {f : VelocityField}
    (hf : HasCompactSupport f) :
    ∀ t : ℝ, tsupport (fun x : Space => f (t, x)) ⊆ Prod.snd '' tsupport f :=
  fun t => force_slice_support_subset hf t

theorem accumulatedForce_eq_interval {f : VelocityField} {t : ℝ}
    (ht : 0 ≤ t) :
    accumulatedForce f t = ∫ s in (0 : ℝ)..t, Real.sqrt (l2Sq f s) := by
  unfold accumulatedForce
  rw [intervalIntegral.integral_of_le ht, integral_Ioc_eq_integral_Ioo]

theorem work_eq_square_interval {f : VelocityField}
    (hforce_smooth : ContDiff ℝ ∞ f)
    (hforce_support : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    {t : ℝ} (ht : 0 < t) :
    2 * (∫ s in (0 : ℝ)..t,
      Real.sqrt (l2Sq f s) * (∫ r in (0 : ℝ)..s, Real.sqrt (l2Sq f r))) =
      (∫ s in (0 : ℝ)..t, Real.sqrt (l2Sq f s)) ^ 2 := by
  let Kf : Set Space := Prod.snd '' tsupport f
  have hKf : IsCompact Kf := hforce_support.1.isCompact.image continuous_snd
  have hfsupp : ∀ s ∈ Icc (0 : ℝ) t,
      tsupport (fun x : Space => f (s, x)) ⊆ Kf := by
    intro s hs
    exact force_slice_support_subset hforce_support.1 s
  have hfcont : ContinuousOn (fun s : ℝ => Real.sqrt (l2Sq f s)) (Icc 0 t) := by
    exact (l2Sq_continuousOn hKf hforce_smooth.contDiffOn hfsupp).sqrt
  let N : ℝ → ℝ := fun s => ∫ r in (0 : ℝ)..s, Real.sqrt (l2Sq f r)
  obtain ⟨hNcont, hNderiv⟩ := primitive_regular ht.le hfcont
  have hsqcont : ContinuousOn (fun s : ℝ => (N s) ^ 2) (Icc 0 t) :=
    hNcont.pow 2
  have hsqderiv : ∀ s ∈ Ioo (0 : ℝ) t,
      HasDerivAt (fun r : ℝ => (N r) ^ 2)
        ((2 * N s) * Real.sqrt (l2Sq f s)) s := by
    intro s hs
    change HasDerivAt
      ((fun r : ℝ => ∫ q in (0 : ℝ)..r, Real.sqrt (l2Sq f q)) ^ 2)
      ((2 * (∫ q in (0 : ℝ)..s, Real.sqrt (l2Sq f q))) *
        Real.sqrt (l2Sq f s)) s
    simpa using (hNderiv s hs).pow 2
  have hderiv_cont : ContinuousOn
      (fun s : ℝ => (2 * N s) * Real.sqrt (l2Sq f s)) (Icc 0 t) :=
    (continuousOn_const.mul hNcont).mul hfcont
  have hderiv_int : IntervalIntegrable
      (fun s : ℝ => (2 * N s) * Real.sqrt (l2Sq f s)) volume 0 t := by
    apply IntegrableOn.intervalIntegrable
    rw [uIcc_of_le ht.le]
    exact hderiv_cont.integrableOn_compact isCompact_Icc
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    ht.le hsqcont hsqderiv hderiv_int
  have hN0 : N 0 = 0 := by simp [N]
  have hmain :
      (∫ s in (0 : ℝ)..t, (2 * N s) * Real.sqrt (l2Sq f s)) = N t ^ 2 := by
    simpa [hN0] using hFTC
  calc
    2 * (∫ s in (0 : ℝ)..t,
        Real.sqrt (l2Sq f s) * (∫ r in (0 : ℝ)..s, Real.sqrt (l2Sq f r))) =
        ∫ s in (0 : ℝ)..t,
          2 * (Real.sqrt (l2Sq f s) * (∫ r in (0 : ℝ)..s,
            Real.sqrt (l2Sq f r))) := by
              rw [intervalIntegral.integral_const_mul]
    _ = ∫ s in (0 : ℝ)..t,
        (2 * (∫ r in (0 : ℝ)..s, Real.sqrt (l2Sq f r))) *
          Real.sqrt (l2Sq f s) := by
            apply intervalIntegral.integral_congr
            intro s hs
            ring
    _ = N t ^ 2 := hmain

/-- The work term is the square of the accumulated force. -/
theorem work_eq_square_of_packet {f : VelocityField}
    (hforce_smooth : ContDiff ℝ ∞ f)
    (hforce_support : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f) :
    ∀ t ∈ Ico (0 : ℝ) 1,
      2 * (∫ s in Ioo (0 : ℝ) t,
        Real.sqrt (l2Sq f s) * accumulatedForce f s)
      = accumulatedForce f t ^ 2 := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with rfl | ht0
  · simp [accumulatedForce]
  have hinterval := work_eq_square_interval hforce_smooth hforce_support ht0
  have hacc (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) t) :
      accumulatedForce f s = ∫ r in (0 : ℝ)..s, Real.sqrt (l2Sq f r) :=
    accumulatedForce_eq_interval (le_of_lt hs.1)
  have hset :
      (∫ s in Ioo (0 : ℝ) t,
        2 * (Real.sqrt (l2Sq f s) * accumulatedForce f s)) =
      (∫ s in (0 : ℝ)..t,
        2 * (Real.sqrt (l2Sq f s) * (∫ r in (0 : ℝ)..s, Real.sqrt (l2Sq f r))) ) := by
    have hIoc :
        (∫ s in Ioc (0 : ℝ) t,
          2 * (Real.sqrt (l2Sq f s) * accumulatedForce f s)) =
        (∫ s in Ioc (0 : ℝ) t,
          2 * (Real.sqrt (l2Sq f s) *
            (∫ r in (0 : ℝ)..s, Real.sqrt (l2Sq f r)))) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      change 2 * (Real.sqrt (l2Sq f s) * accumulatedForce f s) =
        2 * (Real.sqrt (l2Sq f s) * (∫ r in (0 : ℝ)..s,
          Real.sqrt (l2Sq f r)))
      rw [hacc s hs]
    rw [← integral_Ioc_eq_integral_Ioo, hIoc,
      ← intervalIntegral.integral_of_le ht0.le]
  calc
    2 * (∫ s in Ioo (0 : ℝ) t,
        Real.sqrt (l2Sq f s) * accumulatedForce f s) =
        ∫ s in Ioo (0 : ℝ) t,
          2 * (Real.sqrt (l2Sq f s) * accumulatedForce f s) := by
            rw [integral_const_mul]
    _ = (∫ s in (0 : ℝ)..t,
        2 * (Real.sqrt (l2Sq f s) * (∫ r in (0 : ℝ)..s,
          Real.sqrt (l2Sq f r))) ) := hset
    _ = accumulatedForce f t ^ 2 := by
      have hprim := accumulatedForce_eq_interval (f := f) (le_of_lt ht0)
      calc
        (∫ s in (0 : ℝ)..t,
          2 * (Real.sqrt (l2Sq f s) * (∫ r in (0 : ℝ)..s,
            Real.sqrt (l2Sq f r)))) =
            (∫ s in (0 : ℝ)..t, Real.sqrt (l2Sq f s)) ^ 2 := by
              simpa [mul_assoc] using hinterval
        _ = accumulatedForce f t ^ 2 :=
          congrArg (fun z : ℝ => z ^ 2) hprim.symm

/-- The packet energy inequality in the set-integral form of the specification. -/
theorem energy_le_work_of_packet {ν : ℝ} {u f : VelocityField} {p : PressureField}
    {K : Set Space}
    (hν : 0 < ν)
    (hcarrier_compact : IsCompact K)
    (hvelocity_smooth : ContDiffOn ℝ ∞ u preSingularDomain)
    (hpressure_smooth : ContDiffOn ℝ ∞ p preSingularDomain)
    (hforce_smooth : ContDiff ℝ ∞ f)
    (hforce_support : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (hvelocity_support : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => u (t, x)) ⊆ K)
    (hzero_initial_velocity : ∀ x : Space, u (0, x) = 0)
    (hdivergence_free : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space,
      spatialDivergence u t x = 0)
    (hnavier_stokes : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x = f (t, x)) :
    ∀ t ∈ Ico (0 : ℝ) 1,
      l2Sq u t + 2 * ν * (∫ s in Ioo (0 : ℝ) t, dissipation u s)
        ≤ 2 * (∫ s in Ioo (0 : ℝ) t,
          Real.sqrt (l2Sq f s) * accumulatedForce f s) := by
  let Kf : Set Space := Prod.snd '' tsupport f
  have hKf : IsCompact Kf := hforce_support.1.isCompact.image continuous_snd
  have hfsupp : ∀ s : ℝ, tsupport (fun x : Space => f (s, x)) ⊆ Kf :=
    force_slice_support_subset_all hforce_support.1
  intro t ht
  rcases eq_or_lt_of_le ht.1 with rfl | ht0
  · simp [l2Sq, hzero_initial_velocity, accumulatedForce]
  have hsub : slab 0 t ⊆ preSingularDomain := by
    intro z hz
    exact ⟨⟨hz.1.1, lt_of_le_of_lt hz.1.2 ht.2⟩, hz.2⟩
  have huT := hvelocity_smooth.mono hsub
  have hpT := hpressure_smooth.mono hsub
  have hsupp : ∀ s ∈ Icc (0 : ℝ) t,
      tsupport (fun x : Space => u (s, x)) ⊆ K := by
    intro s hs
    exact hvelocity_support s ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
  have hdivT : ∀ s ∈ Ioo (0 : ℝ) t, ∀ x : Space,
      spatialDivergence u s x = 0 := by
    intro s hs x
    exact hdivergence_free s ⟨le_of_lt hs.1, lt_trans hs.2 ht.2⟩ x
  have hNST : ∀ s ∈ Ioo (0 : ℝ) t, ∀ x : Space,
      NSFormalization.Source.residual ν u p s x = f (s, x) := by
    intro s hs x
    exact hnavier_stokes s ⟨hs.1, lt_trans hs.2 ht.2⟩ x
  have hbound := packet_energy ht0 hν.le hcarrier_compact hKf huT hpT
    hforce_smooth.contDiffOn hsupp
    (fun s hs => hfsupp s) hzero_initial_velocity hdivT hNST t ⟨ht.1, le_rfl⟩
  have hwork := work_eq_square_of_packet hforce_smooth hforce_support t ht
  have hprim := accumulatedForce_eq_interval (f := f) ht.1
  rw [intervalIntegral.integral_of_le ht.1, integral_Ioc_eq_integral_Ioo] at hbound
  have hbound' :
      l2Sq u t + 2 * ν * (∫ s in Ioo (0 : ℝ) t, dissipation u s) ≤
        accumulatedForce f t ^ 2 := by
    rw [hprim]
    exact hbound
  exact hbound'.trans_eq hwork.symm

end NSFormalization.Section3.T14
