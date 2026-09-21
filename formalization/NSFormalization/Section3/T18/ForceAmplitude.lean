import NSFormalization.Section3.T18.Assembly
import NSFormalization.Section3.T15.SingleCopy

/-!
# Remark 3.13: force amplitudes

`paper/revised/sections/03-torus.tex:403-410`:
"Since the original force is nonzero,
‖g_ε-g‖_{L∞_{t,x}} ≥ ε⁻³‖F‖∞ - Cε⁻² → ∞."
"The force F is nonzero by (packetenergy), since U blows up."

For extended nonnegative amplitudes divergence means convergence to `𝓝 ⊤`.
-/
noncomputable section
namespace NSFormalization.Section3.T18
open Set MeasureTheory Filter Topology
open NavierStokes.ProblemStatement
open NavierStokesR3.CompactEnergy
open NSFormalization.Source.PacketEnergy
open NSFormalization.Section3.T14 NSFormalization.Section3.T15
open scoped ContDiff ENNReal

/-- Zero forcing gives zero kinetic energy, contradicting the packet blowup. -/
theorem packetForce_ne_zero {ν : ℝ} {u f : VelocityField} {p : PressureField}
    {K : Set Space} (hν : 0 < ν) (hK : IsCompact K)
    (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    (hp : ContDiffOn ℝ ∞ p preSingularDomain)
    (hf : ContDiff ℝ ∞ f)
    (hfc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (hsupp : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => u (t,x)) ⊆ K)
    (hzero : ∀ x : Space, u (0,x) = 0)
    (hdiv : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space, spatialDivergence u t x = 0)
    (hNS : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x = f (t,x))
    (hblow : SpeedUnboundedAtOne u) : f ≠ 0 := by
  intro heq
  obtain ⟨t, x, ht, _, hx⟩ := hblow 1 zero_lt_one 1 zero_lt_one
  have he := energy_le_work_of_packet hν hK hu hp hf hfc hsupp hzero hdiv hNS
    t ⟨ht.1.le, ht.2⟩
  simp [heq, l2Sq, accumulatedForce] at he
  have hd : 0 ≤ ∫ s in Ioo (0 : ℝ) t, dissipation u s :=
    integral_nonneg (fun s => dissipation_nonneg u s)
  have hn : 0 ≤ l2Sq u t := integral_nonneg (fun x => sq_nonneg _)
  have he0 : l2Sq u t = 0 := by
    change l2Sq u t + 2 * ν * (∫ s in Ioo (0 : ℝ) t, dissipation u s) ≤ 0 at he
    nlinarith
  have hc : Continuous (fun x : Space => u (t,x)) :=
    hu.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨⟨ht.1.le, ht.2⟩, mem_univ _⟩)
  have hz := field_eq_zero_of_l2Sq_eq_zero hc (slice_compact hK (hsupp t ⟨ht.1.le, ht.2⟩)) he0 x
  norm_num [hz] at hx

/-- A nonzero force has strictly positive extended supremum norm. -/
theorem packetForce_sup_pos {f : VelocityField} (hf : f ≠ 0) :
    0 < ⨆ z, ‖f z‖ₑ := by
  obtain ⟨z, hz⟩ := Function.ne_iff.mp hf
  exact lt_of_lt_of_le (by simpa using hz) (le_iSup (fun z => ‖f z‖ₑ) z)

/-- Smooth compactly supported forcing has finite amplitude. -/
theorem packetForce_sup_lt_top {f : VelocityField} (hf : Continuous f)
    (hc : HasCompactSupport f) : (⨆ z, ‖f z‖ₑ) < ⊤ := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hf
  apply lt_of_le_of_lt (b := ENNReal.ofReal C) _ ENNReal.ofReal_lt_top
  exact iSup_le (fun z => by simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal (hC z))

/-- Evaluate a nonzero source value in the single supported lattice copy. -/
theorem periodizedScaledForce_at_source {ν M E : ℝ}
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (place : PlacementData u p f K) (S : ScalingAPI (ν := ν) u p f K M E place)
    {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) place.ε₀)
    (z : SpaceTime) (hz : f z ≠ 0) :
    periodizedScaledForce f place.x₀ place.T ε
      (scaledStartTime place.T ε + ε ^ 2 * z.1, place.x₀ + ε • z.2) =
        (ε⁻¹) ^ 3 • f z := by
  have hcube : place.x₀ + ε • z.2 ∈ NSFormalization.Section3.T13.fundamentalCube :=
    interior_subset (place.chartBall_in_cube (subset_closure
      (place.eps_space ε hε z.2 (place.force_projection_subset z.1 z.2
        (subset_tsupport f hz)))))
  rw [S.force_singleCopy ε hε _ _ hcube]
  have hsource : scaledSourcePoint place.x₀ place.T ε
      (scaledStartTime place.T ε + ε ^ 2 * z.1, place.x₀ + ε • z.2) = z := by
    apply Prod.ext
    · simp only [scaledSourcePoint, add_sub_cancel_left]
      field_simp [hε.1.ne']
    · simp [scaledSourcePoint, smul_smul, hε.1.ne']
  simp only [scaledForce, hsource]

/-- The lower scaling inequality suffices for Remark 3.13. -/
theorem periodizedScaledForce_amplitude {ν M E : ℝ}
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (place : PlacementData u p f K) (S : ScalingAPI (ν := ν) u p f K M E place)
    {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) place.ε₀) :
    ENNReal.ofReal ((ε⁻¹) ^ 3) * (⨆ z, ‖f z‖ₑ) ≤
      ⨆ z, ‖periodizedScaledForce f place.x₀ place.T ε z‖ₑ := by
  rw [ENNReal.mul_iSup]
  apply iSup_le
  intro z
  by_cases hz : f z = 0
  · simp [hz]
  have h := le_iSup (fun w => ‖periodizedScaledForce f place.x₀ place.T ε w‖ₑ)
    (scaledStartTime place.T ε + ε ^ 2 * z.1, place.x₀ + ε • z.2)
  rw [periodizedScaledForce_at_source place S hε z hz] at h
  rw [enorm_smul, Real.enorm_eq_ofReal (pow_nonneg (inv_nonneg.mpr hε.1.le) 3)] at h
  exact h

/-- The global order-zero derivative field also directly bounds the amplitude. -/
theorem correctionForce_amplitude_le_deriv (data : InsertionData)
    {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) data.D.ε₀) :
    (⨆ z, ‖NSFormalization.Section3.T17.correctionForce data.ν
      data.reference.velocity data.D ε z‖ₑ) ≤
        ENNReal.ofReal (data.correction.forceDerivConst 0 * (ε⁻¹) ^ 2) := by
  apply iSup_le
  intro z
  have h := data.correction.force_derivative_bound 0 ε hε z
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  simp only [iteratedFDeriv_zero_apply, Nat.add_zero] at h
  simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal h

open NSFormalization.Section3.T17 NSFormalization.Section3.T16

/-- Lift the profile bound through the chart and all periodic copies. -/
theorem correctionForce_norm_le (data : InsertionData)
    {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) data.D.ε₀) (z : SpaceTime) :
    ‖correctionForce data.ν data.reference.velocity data.D ε z‖ ≤
      data.correction.forceProfileConst 0 * (ε⁻¹) ^ 2 := by
  by_cases hz : correctionForce data.ν data.reference.velocity data.D ε z = 0
  · rw [hz, norm_zero]
    exact mul_nonneg (data.correction.forceProfileConst_nonneg 0) (sq_nonneg _)
  have hs := data.correction.force_support ε hε (subset_tsupport _ hz)
  obtain ⟨k, hk⟩ := hs.2
  let y := z.2 - latticeVector k
  let w : SpaceTime := ((z.1 - data.place.T) / ε ^ 2, ε⁻¹ • (y - data.place.x₀))
  have he2 : 0 < ε ^ 2 := sq_pos_of_pos hε.1
  have hw : w ∈ fixedProfileCylinder data.D := by
    constructor
    · constructor
      · apply (le_div_iff₀ he2).mpr
        linarith [hs.1.1]
      · apply (div_le_iff₀ he2).mpr
        linarith [hs.1.2]
    · rw [Metric.mem_closedBall, dist_zero_right]
      change ‖ε⁻¹ • (y - data.place.x₀)‖ ≤ data.D.θRadius
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε.1), inv_mul_eq_div]
      apply (div_le_iff₀ hε.1).mpr
      have hh : ‖y - data.place.x₀‖ < ε * data.D.θRadius := hk
      nlinarith
  have hchart : correctionChartPoint data.place.x₀ data.place.T ε w = (z.1, y) := by
    apply Prod.ext
    · dsimp [correctionChartPoint, w]
      field_simp [hε.1.ne']
      ring
    · simp [correctionChartPoint, w, smul_smul, hε.1.ne']
  have hper : correctionForce data.ν data.reference.velocity data.D ε z =
      correctionForce data.ν data.reference.velocity data.D ε (z.1, y) := by
    have hh := NSFormalization.Section3.T13.periodic_latticeVector
      (g := fun x => correctionForce data.ν data.reference.velocity data.D ε (z.1, x))
      (fun x i => data.correction.force_periodic ε hε z.1 (mem_univ _) x i) y k
    simpa [y, latticeVector, NSFormalization.Section3.T13.latticeVector] using hh
  rw [hper, ← hchart, data.correction.force_profile_identity ε hε w hw, norm_smul]
  have hb := data.correction.force_profile_uniform 0 ε hε w hw
  rw [norm_iteratedFDeriv_zero] at hb
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr he2), inv_pow]
  simpa only [inv_pow] using
    (mul_le_mul_of_nonneg_left hb (sq_nonneg ε⁻¹)).trans_eq (mul_comm _ _)

/-- The correction amplitude is bounded by the record's order-zero profile constant. -/
theorem correctionForce_amplitude_le (data : InsertionData)
    {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) data.D.ε₀) :
    (⨆ z, ‖correctionForce data.ν data.reference.velocity data.D ε z‖ₑ) ≤
      ENNReal.ofReal (data.correction.forceProfileConst 0 * (ε⁻¹) ^ 2) := by
  apply iSup_le
  intro z
  simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal (correctionForce_norm_le data hε z)

/-- Every nonzero packet value gives a reverse-triangle amplitude bound. -/
theorem forceAmplitude_point_lower (data : InsertionData) (A : PeriodicInsertionAPI data)
    {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) A.ε₀) (z : SpaceTime) :
    ENNReal.ofReal ((ε⁻¹) ^ 3 * ‖data.packetForce z‖ -
      data.correction.forceProfileConst 0 * (ε⁻¹) ^ 2) ≤
        ⨆ w, ‖A.force ε w - data.g w‖ₑ := by
  by_cases hz : data.packetForce z = 0
  · simp only [hz, norm_zero, mul_zero, zero_sub]
    rw [ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr
      (mul_nonneg (data.correction.forceProfileConst_nonneg 0) (sq_nonneg _)))]
    exact bot_le
  let w : SpaceTime := (scaledStartTime data.place.T ε + ε ^ 2 * z.1,
    data.place.x₀ + ε • z.2)
  have hs := periodizedScaledForce_at_source data.place data.scaling
    ⟨hε.1, hε.2.trans A.eps_le_scaling⟩ z hz
  have heq : A.force ε w - data.g w =
      correctionForce data.ν data.reference.velocity data.D ε w +
        (ε⁻¹) ^ 3 • data.packetForce z := by
    rw [A.force_formula, hs]
    abel
  have hb := correctionForce_norm_le data ⟨hε.1, hε.2.trans A.eps_le_cutoff⟩ w
  have ht := norm_add_le (A.force ε w - data.g w)
    (-correctionForce data.ν data.reference.velocity data.D ε w)
  have hv : (A.force ε w - data.g w) +
      -correctionForce data.ν data.reference.velocity data.D ε w =
        (ε⁻¹) ^ 3 • data.packetForce z := by rw [heq]; abel
  rw [hv, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hε.1.le) 3)] at ht
  apply le_trans (ENNReal.ofReal_le_ofReal (by linarith :
    (ε⁻¹) ^ 3 * ‖data.packetForce z‖ -
      data.correction.forceProfileConst 0 * (ε⁻¹) ^ 2 ≤ ‖A.force ε w - data.g w‖))
  simpa only [ofReal_norm] using le_iSup (fun w => ‖A.force ε w - data.g w‖ₑ) w

/-- The elementary cubic term dominates the quadratic correction. -/
theorem amplitude_polynomial_tendsto {a : ℝ} (ha : 0 < a) (C : ℝ) :
    Tendsto (fun ε : ℝ => (ε⁻¹) ^ 3 * a - C * (ε⁻¹) ^ 2)
      (𝓝[>] (0 : ℝ)) atTop := by
  have hi : Tendsto (fun ε : ℝ => ε⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_inv_nhdsGT_zero
  have hlin : Tendsto (fun ε : ℝ => a * ε⁻¹ - C) (𝓝[>] (0 : ℝ)) atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [hi.eventually (eventually_ge_atTop ((b + C) / a))] with ε hε
    have := (div_le_iff₀ ha).mp hε
    nlinarith
  convert ((Filter.tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hi).atTop_mul_atTop₀ hlin using 1
  ext ε
  dsimp only [Function.comp_def]
  ring

/-- Amplitudes diverge for every inserted record with nonzero packet force. -/
theorem forceAmplitude_diverges_of_ne_zero (data : InsertionData)
    (A : PeriodicInsertionAPI data) (hf : data.packetForce ≠ 0) :
    Tendsto (fun ε : ℝ => ⨆ z, ‖A.force ε z - data.g z‖ₑ)
      (𝓝[>] (0 : ℝ)) (𝓝 ⊤) := by
  obtain ⟨z, hz⟩ := Function.ne_iff.mp hf
  have ha : 0 < ‖data.packetForce z‖ := norm_pos_iff.mpr hz
  apply tendsto_nhds_top_mono (ENNReal.tendsto_ofReal_atTop.comp
    (amplitude_polynomial_tendsto ha (data.correction.forceProfileConst 0)))
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ≤ A.ε₀ from
      nhdsWithin_le_nhds (eventually_le_nhds A.eps_pos))] with ε hε hε₀
  exact forceAmplitude_point_lower data A ⟨hε, hε₀⟩ z

/-- The displayed lower bound of Remark 3.13, for any insertion record. -/
theorem forceAmplitude_lower (data : InsertionData) (A : PeriodicInsertionAPI data)
    {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) A.ε₀) :
    ENNReal.ofReal ((ε⁻¹) ^ 3 * (⨆ z, ‖data.packetForce z‖ₑ).toReal -
      data.correction.forceProfileConst 0 * (ε⁻¹) ^ 2) ≤
        ⨆ z, ‖A.force ε z - data.g z‖ₑ := by
  have hc : 0 ≤ data.correction.forceProfileConst 0 * (ε⁻¹) ^ 2 :=
    mul_nonneg (data.correction.forceProfileConst_nonneg 0) (sq_nonneg _)
  have he : 0 ≤ (ε⁻¹) ^ 3 := pow_nonneg (inv_nonneg.mpr hε.1.le) 3
  have hb : ENNReal.ofReal ((ε⁻¹) ^ 3) * (⨆ z, ‖data.packetForce z‖ₑ) -
      ENNReal.ofReal (data.correction.forceProfileConst 0 * (ε⁻¹) ^ 2) ≤
        ⨆ z, ‖A.force ε z - data.g z‖ₑ := by
    rw [ENNReal.mul_iSup, ENNReal.iSup_sub]
    apply iSup_le
    intro z
    simpa only [ENNReal.ofReal_sub _ hc, ENNReal.ofReal_mul he, ofReal_norm] using
      forceAmplitude_point_lower data A hε z
  rw [ENNReal.ofReal_sub _ hc, ENNReal.ofReal_mul he]
  exact (tsub_le_tsub_right (mul_le_mul le_rfl ENNReal.ofReal_toReal_le bot_le bot_le) _).trans hb

open NSFormalization.Section3.T10 NSFormalization.Section3.T11

/-- Even the raw insertion bundle forces nonzero packet forcing: otherwise its
scaled solution from rest agrees with the zero solution, contradicting blowup. -/
theorem insertionData_packetForce_ne_zero (data : InsertionData) : data.packetForce ≠ 0 := by
  intro hf
  let ε := data.place.ε₀
  have hε : ε ∈ Ioc (0 : ℝ) data.place.ε₀ := ⟨data.place.eps_pos, le_rfl⟩
  have hF : periodizedScaledForce data.packetForce data.place.x₀ data.place.T ε = 0 := by
    ext z
    simp [periodizedScaledForce, scaledForce, hf, NSFormalization.Section3.T13.periodize]
  have hsol := data.scaling.solution ε hε
  rw [hF] at hsol
  obtain ⟨S, hS, _⟩ := hsol
  let Z : ClassicalSolutionT data.ν 0 0 data.place.T := {
    constantVelocitySolutionT 0 data.place.time_pos with
    momentum := by
      intro t ht x
      simp [constantVelocitySolutionT, NavierStokesR3.ProblemStatement.navierStokesResidual,
        temporalDerivative, advection, spatialDerivative, spatialLaplacian, pressureGradient] }
  obtain ⟨t, x, ht, _, hx⟩ := data.scaling.unboundedSpeed ε hε 1 zero_lt_one 1 zero_lt_one
  have he := NSFormalization.Paper1.PeriodicLocalLifespan.flow_velocity_agree_on_common_interval
    data.correction.viscosity_pos (toFlow S) (toFlow Z) t
    (by simpa using (show t ∈ Ico (0 : ℝ) data.place.T from ⟨ht.1.le, ht.2⟩)) x
  change S.velocity (t,x) = 0 at he
  rw [hS] at he
  norm_num [he] at hx

/-- Divergence for every canonical insertion record, with no extra packet premise. -/
theorem forceAmplitude_diverges (data : InsertionData) (A : PeriodicInsertionAPI data) :
    Tendsto (fun ε : ℝ => ⨆ z, ‖A.force ε z - data.g z‖ₑ)
      (𝓝[>] (0 : ℝ)) (𝓝 ⊤) :=
  forceAmplitude_diverges_of_ne_zero data A (insertionData_packetForce_ne_zero data)

/-- A smooth periodic force with compact time support has finite global amplitude. -/
theorem memForceT_sup_lt_top {f : VelocityField} (hf : MemForceT f) :
    (⨆ z, ‖f z‖ₑ) < ⊤ := by
  obtain ⟨K, hK, _, hsupp⟩ := hf.2.2
  obtain ⟨C, hC⟩ := (hK.prod isCompact_fundamentalCube).exists_bound_of_continuousOn
    hf.1.continuous.continuousOn
  apply lt_of_le_of_lt (b := ENNReal.ofReal (max C 0)) _ ENNReal.ofReal_lt_top
  apply iSup_le
  intro z
  by_cases hz : f z = 0
  · simp [hz]
  have htz : z.1 ∈ K := (hsupp (subset_tsupport f hz)).1
  obtain ⟨n, hn⟩ := exists_sub_latticeVector_mem_fundamentalCube z.2
  have hshift := NSFormalization.Section3.T13.periodic_latticeVector
    (g := fun x => f (z.1,x)) (fun x i => hf.2.1 z.1 (mem_univ _) x i)
    (z.2 - NSFormalization.Section3.T13.latticeVector n) n
  simp only [sub_add_cancel, Prod.mk.eta] at hshift
  have hb : ‖f z‖ ≤ max C 0 := by
    exact (congrArg norm hshift).le.trans
      ((hC (z.1, z.2 - NSFormalization.Section3.T13.latticeVector n) ⟨htz, hn⟩).trans
        (le_max_left _ _))
  simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal hb

/-- Finiteness is recoverable from the scaling record even when the raw compact
support clause has been erased by the insertion bundle. -/
theorem insertionData_packetForce_sup_lt_top (data : InsertionData) :
    (⨆ z, ‖data.packetForce z‖ₑ) < ⊤ := by
  have hε : data.place.ε₀ ∈ Ioc (0 : ℝ) data.place.ε₀ := ⟨data.place.eps_pos, le_rfl⟩
  have hb := memForceT_sup_lt_top (data.scaling.force_mem _ hε)
  have hl := periodizedScaledForce_amplitude data.place data.scaling hε
  by_contra hn
  have he : (⨆ z, ‖data.packetForce z‖ₑ) = ⊤ := not_lt_top_iff.mp hn
  have hc : ENNReal.ofReal ((data.place.ε₀⁻¹) ^ 3) ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos (inv_pos.mpr data.place.eps_pos) 3))
  rw [he, ENNReal.mul_top hc] at hl
  exact (not_le_of_gt hb) hl

/-- The finite real supremum tends to `atTop`; this is the real-valued form of
Remark 3.13's divergence display. -/
theorem forceAmplitude_real_diverges (data : InsertionData) (A : PeriodicInsertionAPI data) :
    Tendsto (fun ε : ℝ => (⨆ z, ‖A.force ε z - data.g z‖ₑ).toReal)
      (𝓝[>] (0 : ℝ)) atTop := by
  obtain ⟨z, hz⟩ := Function.ne_iff.mp (insertionData_packetForce_ne_zero data)
  apply tendsto_atTop_mono' _ _
    (amplitude_polynomial_tendsto (norm_pos_iff.mpr hz) (data.correction.forceProfileConst 0))
  filter_upwards [Ioc_mem_nhdsGT A.eps_pos] with ε hε
  exact (ENNReal.ofReal_le_iff_le_toReal
    (memForceT_sup_lt_top (A.forceDifference_mem ε hε)).ne).mp
      (forceAmplitude_point_lower data A hε z)

end NSFormalization.Section3.T18
