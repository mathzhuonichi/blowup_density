import NavierStokes.R3.CompactEnergy
import NSFormalization.Paper1.ScalarEnergy
import NSFormalization.Source.Insertion
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff InnerProductSpace Topology
namespace NSFormalization.Source.PacketEnergy
open NavierStokes.ProblemStatement
open NavierStokes.PeriodicUniqueness (slab spatial_smooth spatialDerivative_eq_within_comp)
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokesR3.CompactEnergy

/-- Cauchy--Schwarz for the actual Lebesgue work integral. -/
theorem work_le {u f : Space → Space} (hu : Continuous u) (hf : Continuous f)
    (hcu : HasCompactSupport u) (hfi : Integrable (fun x => ‖f x‖ ^ 2)) :
    (∫ x, ⟪u x, f x⟫_ℝ) ≤
      Real.sqrt (∫ x, ‖u x‖ ^ 2) * Real.sqrt (∫ x, ‖f x‖ ^ 2) := by
  have hui := integrable_norm_sq hu hcu
  have hup : MemLp u 2 := (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mpr hui
  have hfp : MemLp f 2 := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr hfi
  have hip := integrable_inner_left hu hf hcu
  have hmul : Integrable (fun x => ‖u x‖ * ‖f x‖) :=
    (hu.norm.mul hf.norm).integrable_of_hasCompactSupport hcu.norm.mul_right
  have hcs := integral_mul_norm_le_Lp_mul_Lq (μ := volume)
    (p := 2) (q := 2) Real.HolderConjugate.two_two
    (by simpa using hup) (by simpa using hfp)
  have hb := integral_mono hip hmul (fun x => real_inner_le_norm (u x) (f x))
  apply hb.trans
  simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using hcs

/-- The PDE, support and smoothness yield the sharp scalar energy inequality. -/
theorem pde_energy_inequality {u f : VelocityField} {p : PressureField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x)))
    (hf : Continuous (fun x : Space => f (t, x)))
    (hcu : HasCompactSupport (fun x : Space => u (t, x)))
    (hfi : Integrable (fun x : Space => ‖f (t, x)‖ ^ 2))
    (hdiv : ∀ x, spatialDivergence u t x = 0)
    (hNS : ∀ x, navierStokesResidual u p t x = f (t, x)) :
    energyRate u t + 2 * dissipation u t ≤
      2 * Real.sqrt (l2Sq f t) * Real.sqrt (l2Sq u t) := by
  rw [energy_balance hu hp hf hcu hdiv hNS]
  have h := work_le hu.continuous hf hcu hfi
  change (∫ x, ⟪u (t, x), f (t, x)⟫_ℝ) ≤
    Real.sqrt (l2Sq u t) * Real.sqrt (l2Sq f t) at h
  nlinarith

/-- Arbitrary viscosity follows from the imported unit-viscosity balance by
moving the viscosity correction into the force and integrating its Laplacian. -/
theorem energy_balance_viscosity {ν : ℝ} {u f : VelocityField} {p : PressureField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x)))
    (hf : Continuous (fun x : Space => f (t, x)))
    (hcu : HasCompactSupport (fun x : Space => u (t, x)))
    (hdiv : ∀ x, spatialDivergence u t x = 0)
    (hNS : ∀ x, NSFormalization.Source.residual ν u p t x = f (t, x)) :
    energyRate u t = -2 * ν * dissipation u t +
      2 * ∫ x, ⟪u (t, x), f (t, x)⟫_ℝ := by
  let g : VelocityField := fun z => f z + (ν - 1) • spatialLaplacian u z.1 z.2
  have hL : Continuous (fun x : Space => spatialLaplacian u t x) :=
    (NavierStokes.PeriodicUniqueness.spatialLaplacian_contDiff hu).continuous
  have hg : Continuous (fun x : Space => g (t, x)) :=
    by
      change Continuous (fun x => f (t, x) + (ν - 1) • spatialLaplacian u t x)
      exact hf.add ((continuous_const (y := ν - 1)).smul hL)
  have heq : ∀ x, navierStokesResidual u p t x = g (t, x) := by
    intro x
    dsimp [g]
    rw [← hNS x]
    simp only [NSFormalization.Source.residual, navierStokesResidual, sub_smul, one_smul]
    abel
  have hbalance := energy_balance hu hp hg hcu hdiv heq
  have hiF := integrable_inner_left hu.continuous hf hcu
  have hiL := integrable_inner_left hu.continuous
    (NavierStokes.PeriodicUniqueness.spatialLaplacian_contDiff hu).continuous hcu
  have hwork : (∫ x, ⟪u (t, x), g (t, x)⟫_ℝ) =
      (∫ x, ⟪u (t, x), f (t, x)⟫_ℝ) - (ν - 1) * dissipation u t := by
    simp only [g, inner_add_right, inner_smul_right]
    rw [integral_add hiF (hiL.const_mul _), integral_const_mul,
      integral_laplacian_energy hu hcu]
    unfold dissipation
    ring
  rw [hwork] at hbalance
  nlinarith [hbalance]

/-- Spatial differentiation is jointly continuous up to both slab endpoints. -/
theorem partial_continuousOn {T : ℝ} (hT : 0 < T) {u : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (slab 0 T)) (i : Fin 3) :
    ContinuousOn (fun z : SpaceTime => spatialPartial i (fun y => u (z.1, y)) z.2)
      (slab 0 T) := by
  have hs : UniqueDiffOn ℝ (slab 0 T) :=
    (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ
  have hi : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
    simpa only [ENat.coe_top_add_one] using (le_rfl : (∞ : WithTop ℕ∞) ≤ ∞)
  have hd := ((hu.fderivWithin hs hi).continuousOn).clm_apply
    (continuousOn_const (c := (0, coordinateVector i)))
  apply hd.congr
  intro z hz
  have heq := spatialDerivative_eq_within_comp hu hz.1 z.2
  change spatialDerivative u z.1 z.2 (coordinateVector i) = _
  rw [heq]
  rfl

/-- Fixed compact support permits parameter integration of gradient energy. -/
theorem dissipation_continuousOn {T : ℝ} (hT : 0 < T) {u : VelocityField}
    {K : Set Space} (hK : IsCompact K) (hu : ContDiffOn ℝ ∞ u (slab 0 T))
    (hsupp : ∀ t ∈ Icc 0 T, tsupport (fun x => u (t, x)) ⊆ K) :
    ContinuousOn (dissipation u) (Icc 0 T) := by
  apply continuousOn_finsetSum
  intro i _
  apply NavierStokesR3.CompactTimeIntegral.continuousOn_integral hK
    ((partial_continuousOn hT hu i).norm.pow 2)
  intro t ht x hx
  have hn : x ∉ tsupport (fun y => u (t, y)) := fun h => hx (hsupp t ht h)
  have hd := fderiv_of_notMem_tsupport ℝ hn
  simp [spatialPartial, hd]

/-- Local FTC supplies both regularity conditions for actual time primitives. -/
theorem primitive_regular {T : ℝ} (hT : 0 ≤ T) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 T)) :
    ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, f s) (Icc 0 T) ∧
    ∀ t ∈ Ioo 0 T, HasDerivAt (fun t => ∫ s in (0 : ℝ)..t, f s) (f t) t := by
  have hi : IntegrableOn f (Icc 0 T) := hf.integrableOn_compact isCompact_Icc
  constructor
  · have hi' : IntegrableOn f (uIcc 0 T) := by simpa [uIcc_of_le hT] using hi
    simpa [uIcc_of_le hT] using intervalIntegral.continuousOn_primitive_interval hi'
  · intro t ht
    have hint : IntervalIntegrable f volume 0 t := by
      apply IntegrableOn.intervalIntegrable
      rw [uIcc_of_le ht.1.le]
      exact hi.mono_set (Icc_subset_Icc_right ht.2.le)
    exact intervalIntegral.integral_hasDerivAt_right hint
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
        (hf.mono Ioo_subset_Icc_self) t ht)
      (hf.continuousAt (Icc_mem_nhds ht.1 ht.2))

/-- Sharp packet energy estimate on a compact presingular slab, for every
nonnegative viscosity. Every scalar input is derived from the actual PDE,
joint smoothness, compact spatial support and the zero initial field. -/
theorem packet_energy {T ν : ℝ} (hT : 0 < T) (hν : 0 ≤ ν)
    {u f : VelocityField} {p : PressureField} {K Kf : Set Space}
    (hK : IsCompact K) (hKf : IsCompact Kf)
    (hu : ContDiffOn ℝ ∞ u (slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (slab 0 T))
    (hf : ContDiffOn ℝ ∞ f (slab 0 T))
    (hsupp : ∀ t ∈ Icc 0 T, tsupport (fun x => u (t, x)) ⊆ K)
    (hfsupp : ∀ t ∈ Icc 0 T, tsupport (fun x => f (t, x)) ⊆ Kf)
    (hzero : ∀ x, u (0, x) = 0)
    (hdiv : ∀ t ∈ Ioo 0 T, ∀ x, spatialDivergence u t x = 0)
    (hNS : ∀ t ∈ Ioo 0 T, ∀ x,
      NSFormalization.Source.residual ν u p t x = f (t, x)) :
    ∀ t ∈ Icc 0 T,
      l2Sq u t + 2 * ν * (∫ s in (0 : ℝ)..t, dissipation u s) ≤
        (∫ s in (0 : ℝ)..t, Real.sqrt (l2Sq f s)) ^ 2 := by
  have hcE := l2Sq_continuousOn hK hu hsupp
  have hcb := (l2Sq_continuousOn hKf hf hfsupp).sqrt
  have hcd := dissipation_continuousOn hT hK hu hsupp
  obtain ⟨hcN, hdN⟩ := primitive_regular hT.le hcb
  obtain ⟨hcD, hdD⟩ := primitive_regular hT.le hcd
  apply NSFormalization.Paper1.energy_add_dissipation_le_primitive_sq hT.le hν
    hcE hcD hcN (by simp [l2Sq, hzero]) (by simp) (by simp)
    (fun t _ => integral_nonneg (fun x => sq_nonneg _))
    (fun t _ => dissipation_nonneg u t) (fun t _ => Real.sqrt_nonneg _)
    (fun t ht => energy_hasDerivAt hK hu hsupp ht) hdD hdN
  intro t ht
  have htc : t ∈ Icc 0 T := ⟨ht.1.le, ht.2.le⟩
  have hus := spatial_smooth hu htc
  have hps := spatial_smooth hp htc
  have hfs := spatial_smooth hf htc
  have hcu := slice_compact hK (hsupp t htc)
  have hcf := slice_compact hKf (hfsupp t htc)
  rw [energy_balance_viscosity hus hps hfs.continuous hcu (hdiv t ht) (hNS t ht)]
  have hwork := work_le hus.continuous hfs.continuous hcu
    (integrable_norm_sq hfs.continuous hcf)
  change (∫ x, ⟪u (t, x), f (t, x)⟫_ℝ) ≤
    Real.sqrt (l2Sq u t) * Real.sqrt (l2Sq f t) at hwork
  nlinarith

/-- Zero actual squared L2 energy of a continuous compact field forces
pointwise vanishing, using positivity of Lebesgue measure on open sets. -/
theorem field_eq_zero_of_l2Sq_eq_zero {u : VelocityField} {t : ℝ}
    (hu : Continuous (fun x : Space => u (t, x)))
    (hcu : HasCompactSupport (fun x : Space => u (t, x)))
    (he : l2Sq u t = 0) : ∀ x, u (t, x) = 0 := by
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖u (t, x)‖)
    (integrable_norm_sq hu hcu)).mp he
  have hfun := MeasureTheory.Measure.eq_of_ae_eq hae (hu.norm.pow 2) continuous_const
  intro x
  have hx := congrFun hfun x
  simpa using hx

/-- A packet initially at rest stays identically zero throughout any initial
interval on which its physical forcing vanishes. -/
theorem vanishes_before_forcing {T ν : ℝ} (hT : 0 < T) (hν : 0 ≤ ν)
    {u f : VelocityField} {p : PressureField} {K Kf : Set Space}
    (hK : IsCompact K) (hKf : IsCompact Kf)
    (hu : ContDiffOn ℝ ∞ u (slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (slab 0 T))
    (hf : ContDiffOn ℝ ∞ f (slab 0 T))
    (hsupp : ∀ t ∈ Icc 0 T, tsupport (fun x => u (t, x)) ⊆ K)
    (hfsupp : ∀ t ∈ Icc 0 T, tsupport (fun x => f (t, x)) ⊆ Kf)
    (hzero : ∀ x, u (0, x) = 0)
    (hdiv : ∀ t ∈ Ioo 0 T, ∀ x, spatialDivergence u t x = 0)
    (hNS : ∀ t ∈ Ioo 0 T, ∀ x,
      NSFormalization.Source.residual ν u p t x = f (t, x))
    {τ : ℝ} (hforce : ∀ s ∈ Icc 0 τ, ∀ x, f (s, x) = 0) :
    ∀ t ∈ Icc 0 T, t ≤ τ → ∀ x, u (t, x) = 0 := by
  intro t ht htτ
  have hbound := packet_energy hT hν hK hKf hu hp hf hsupp hfsupp hzero hdiv hNS t ht
  have hF : (∫ s in (0 : ℝ)..t, Real.sqrt (l2Sq f s)) = 0 := by
    calc
      _ = ∫ s in (0 : ℝ)..t, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le ht.1] at hs
        simp [l2Sq, hforce s ⟨hs.1, hs.2.trans htτ⟩]
      _ = 0 := by simp
  have hd : 0 ≤ ∫ s in (0 : ℝ)..t, dissipation u s :=
    intervalIntegral.integral_nonneg_of_forall ht.1 (dissipation_nonneg u)
  have he : l2Sq u t = 0 := by
    rw [hF] at hbound
    have hn : 0 ≤ l2Sq u t := integral_nonneg (fun x => sq_nonneg _)
    have := mul_nonneg hν hd
    nlinarith
  exact field_eq_zero_of_l2Sq_eq_zero (spatial_smooth hu ht).continuous
    (slice_compact hK (hsupp t ht)) he

/-- Dissipation is genuinely time-integrable on each compact presingular slab,
and its time integral satisfies the sharp quantitative bound. -/
theorem packet_dissipation {T ν : ℝ} (hT : 0 < T) (hν : 0 < ν)
    {u f : VelocityField} {p : PressureField} {K Kf : Set Space}
    (hK : IsCompact K) (hKf : IsCompact Kf)
    (hu : ContDiffOn ℝ ∞ u (slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (slab 0 T))
    (hf : ContDiffOn ℝ ∞ f (slab 0 T))
    (hsupp : ∀ t ∈ Icc 0 T, tsupport (fun x => u (t, x)) ⊆ K)
    (hfsupp : ∀ t ∈ Icc 0 T, tsupport (fun x => f (t, x)) ⊆ Kf)
    (hzero : ∀ x, u (0, x) = 0)
    (hdiv : ∀ t ∈ Ioo 0 T, ∀ x, spatialDivergence u t x = 0)
    (hNS : ∀ t ∈ Ioo 0 T, ∀ x,
      NSFormalization.Source.residual ν u p t x = f (t, x)) :
    IntegrableOn (dissipation u) (Icc 0 T) ∧
    ∀ t ∈ Icc 0 T,
      (∫ s in (0 : ℝ)..t, dissipation u s) ≤
        (∫ s in (0 : ℝ)..t, Real.sqrt (l2Sq f s)) ^ 2 / (2 * ν) := by
  refine ⟨(dissipation_continuousOn hT hK hu hsupp).integrableOn_compact isCompact_Icc, ?_⟩
  intro t ht
  have hb := packet_energy hT hν.le hK hKf hu hp hf hsupp hfsupp hzero hdiv hNS t ht
  apply (le_div_iff₀ (by positivity : 0 < 2 * ν)).mpr
  have he : 0 ≤ l2Sq u t := integral_nonneg (fun x => sq_nonneg _)
  nlinarith

end NSFormalization.Source.PacketEnergy
