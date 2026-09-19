import NSFormalization.Section3.T24.MultipleAssembled

/-! Regionwise agreement and blow-up for the explicit finite superposition. -/
noncomputable section
namespace NSFormalization.Section3.T24
open Set MeasureTheory
open scoped ENNReal NNReal ContDiff Topology
open NSFormalization.Section4.I02 (spatialGradient)
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T13 NSFormalization.Section3.T15
open NSFormalization.Source.PacketScaling
open NSFormalization.Section4.A02 (SpaceTimeField)

namespace RegionsData
variable {ν : ℝ} {u f : VelocityField} {p : PressureField}
  {K : Set Space} {M E : ℝ} (d : RegionsData ν u p f K M E)

/-- On each prescribed ball all other components vanish. -/
theorem region_agreement : ∀ j, ∀ t ∈ Ico (0 : ℝ) d.T,
    ∀ x ∈ Metric.ball (d.regionCenter j) (d.regionRadius j),
      d.assembledVelocity (t, x) = (d.component j).velocity (t, x) := by
  intro j t ht x hx
  classical
  change (∑ i, (d.component i).velocity (t, x)) = _
  apply Finset.sum_eq_single j
  · intro i _ hij
    apply d.component_support i t ht x
    · exact interior_subset (d.region_interior j (subset_closure hx))
    · intro hi
      exact Set.disjoint_left.mp (d.regions_disjoint hij) hi hx
  · simp

/-- Blow-up witnesses are taken from the Euclidean scaled packet, whose
support lies in the prescribed chart ball, before applying single-copy transfer. -/
theorem region_blowup : ∀ j,
    SpeedUnboundedAtOn d.T (Metric.ball (d.regionCenter j) (d.regionRadius j))
      d.assembledVelocity := by
  intro j A hA δ hδ
  have he := d.eps_admissible j
  have hinv : (((d.ε j)⁻¹ : ℝ) ^ 2)⁻¹ = d.ε j ^ 2 := by
    rw [inv_pow, inv_inv]
  have hb : SpeedUnboundedAt d.T
      (scaledVelocity u (d.placement j).x₀ d.T (d.ε j)) := by
    rw [scaledVelocity_eq_parabolicVelocity, ← hinv]
    exact speed_unbounded_at_target (inv_pos.mpr he.1)
      (by simpa [hinv] using (d.eps_time j).le)
      (d.placement j).x₀ (zeroPastField_speed d.blowup)
  obtain ⟨t, x, ht, hnear, hlarge⟩ := hb A hA δ hδ
  have hne : scaledVelocity u (d.placement j).x₀ d.T (d.ε j) (t, x) ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hlarge
    linarith
  have hx : x ∈ Metric.ball (d.regionCenter j) (d.regionRadius j) :=
    affineImage_subset_ball he (d.placement j).eps_space
      (scaledVelocity_tsupp_subset he.1 d.packet.carrier_compact d.packet.support
        (d.placement j).carrier_subset ht.2 (subset_tsupport _ hne))
  refine ⟨t, x, ht, hnear, hx, ?_⟩
  rw [d.region_agreement j t ⟨ht.1.le, ht.2⟩ x hx, (d.component_pin j).1]
  have hc := (d.scaling j).velocity_singleCopy (d.ε j) he t ht.2 x
    (interior_subset (d.region_interior j (subset_closure hx)))
  rw [d.placement_time j] at hc
  rw [hc]
  exact hlarge

/-- At a point of the cube at most one component is nonzero. -/
theorem enorm_sq_sum (t : ℝ) (ht : t ∈ Ico (0 : ℝ) d.T)
    (x : Space) (hx : x ∈ fundamentalCube) :
    ‖d.assembledVelocity (t, x)‖ₑ ^ (2 : ℕ) =
      ∑ j, ‖(d.component j).velocity (t, x)‖ₑ ^ (2 : ℕ) := by
  classical
  by_cases hb : ∃ j, x ∈ Metric.ball (d.regionCenter j) (d.regionRadius j)
  · obtain ⟨j, hj⟩ := hb
    rw [d.region_agreement j t ht x hj]
    symm
    apply Finset.sum_eq_single j
    · intro i _ hij
      have hz := d.component_support i t ht x hx
        (fun hi => Set.disjoint_left.mp (d.regions_disjoint hij) hi hj)
      simp [hz]
    · simp
  · have hz : ∀ j, (d.component j).velocity (t, x) = 0 :=
      fun j => d.component_support j t ht x hx (fun hj => hb ⟨j, hj⟩)
    simp [assembledVelocity, finiteVelocitySum, hz]

/-- Disjoint-support additivity of the squared Haar slice norm. -/
theorem slice_energy_additive (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) d.T) :
    (eLpNorm (torusLift (fun x => d.assembledVelocity (t, x))) 2
      periodicTorusMeasure) ^ (2 : ℕ) =
    ∑ j, (eLpNorm (torusLift (fun x => (d.component j).velocity (t, x))) 2
      periodicTorusMeasure) ^ (2 : ℕ) := by
  have hsq {g : PeriodicTorus → Space} :
      eLpNorm g 2 periodicTorusMeasure ^ (2 : ℕ) =
        ∫⁻ z, ‖g z‖ₑ ^ (2 : ℕ) ∂periodicTorusMeasure := by
    simpa using (eLpNorm_nnreal_pow_eq_lintegral (f := g)
      (μ := periodicTorusMeasure) (p := (2 : ℝ≥0)) (by norm_num))
  simp_rw [hsq]
  calc
    _ = ∫⁻ z, ∑ j, ‖torusLift (fun x => (d.component j).velocity (t, x)) z‖ₑ ^
        (2 : ℕ) ∂periodicTorusMeasure := by
      apply lintegral_congr
      intro z
      exact d.enorm_sq_sum t ⟨ht.1.le, ht.2⟩ _ (torusChart_mem_fundamentalCube z)
    _ = _ := by
      apply lintegral_finsetSum'
      intro j _
      have hm := ((d.scaling j).energySlices_memLp (d.ε j) (d.eps_admissible j)).1 t ht
      rw [d.placement_time j, ← (d.component_pin j).1] at hm
      exact hm.aestronglyMeasurable.enorm.pow_const 2

/-- The squared component energy constant in the packet normalization. -/
theorem component_energy_sq (j : Fin d.N) :
    energyEssSupT d.T (d.component j).velocity ^ (2 : ℕ) =
      ENNReal.ofReal (M ^ 2 * d.ε j) := by
  rw [(d.component_pin j).1]
  have h := (d.scaling j).packetEnergyIdentity (d.ε j) (d.eps_admissible j)
  rw [d.placement_time j] at h
  rw [h, ← ENNReal.ofReal_pow (mul_nonneg
    (Real.rpow_nonneg (d.eps_admissible j).1.le _)
    (NSFormalization.Section4.I03.energyBound_nonneg d.packet))]
  congr 1
  rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul (d.eps_admissible j).1.le]
  norm_num
  ring

/-- The energy bound for the assembled velocity, with the original packet constant. -/
theorem energy_bound : (energyEssSupT d.T d.assembledVelocity) ^ (2 : ℕ) ≤
    ENNReal.ofReal (M ^ 2 * ∑ j, d.ε j) := by
  have ha : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) d.T)),
      ∀ j, eLpNorm (torusLift (fun x => (d.component j).velocity (t, x))) 2
        periodicTorusMeasure ≤ energyEssSupT d.T (d.component j).velocity := by
    apply (ae_all_iff).mpr
    intro j
    exact ENNReal.ae_le_essSup _
  rw [← ENNReal.rpow_two, ← ENNReal.le_rpow_inv_iff (by norm_num : (0 : ℝ) < 2)]
  refine essSup_le_of_ae_le _ ?_ (by apply Filter.isCobounded_le_of_bot)
  filter_upwards [ha, ae_restrict_mem measurableSet_Ioo] with t h ht
  rw [ENNReal.le_rpow_inv_iff (by norm_num : (0 : ℝ) < 2), ENNReal.rpow_two,
    d.slice_energy_additive t ht]
  calc
    _ ≤ ∑ j, energyEssSupT d.T (d.component j).velocity ^ (2 : ℕ) :=
      Finset.sum_le_sum (fun j _ => ENNReal.pow_le_pow_left (h j))
    _ = ∑ j, ENNReal.ofReal (M ^ 2 * d.ε j) := by
      simp_rw [d.component_energy_sq]
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg
        (fun j _ => mul_nonneg (sq_nonneg M) (d.eps_admissible j).1.le), Finset.mul_sum]

/-- Smoothness of each component's spatial slice. -/
theorem component_slice_contDiff (j : Fin d.N) (t : ℝ) (ht : t < d.T) :
    ContDiff ℝ ∞ (fun x => (d.component j).velocity (t, x)) := by
  rw [(d.component_pin j).1]
  exact contDiff_periodize_of_subset_interior
    (scaledVelocity_slice_contDiff d.packet.extension_smooth (d.eps_admissible j).1 ht)
    (scaledVelocity_slice_subset_cube (d.eps_admissible j) d.packet.carrier_compact
      d.packet.support (d.placement j).carrier_subset (d.placement j).eps_space
      (d.placement j).chartBall_in_cube ht)

/-- On the cube interior, gradients vanish outside the component's ball. -/
theorem component_gradient_support (j : Fin d.N) (t : ℝ) (ht : t < d.T)
    (x : Space) (hx : x ∈ interior fundamentalCube)
    (hout : x ∉ Metric.ball (d.regionCenter j) (d.regionRadius j)) :
    spatialGradient (d.component j).velocity t x = 0 := by
  have heq : (fun y => (d.component j).velocity (t, y)) =ᶠ[nhds x]
      (fun y => scaledVelocity u (d.placement j).x₀ d.T (d.ε j) (t, y)) := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    rw [(d.component_pin j).1]
    exact (d.scaling j).velocity_singleCopy (d.ε j) (d.eps_admissible j) t ht y
      (interior_subset hy)
  have hn : x ∉ tsupport (fun y => scaledVelocity u (d.placement j).x₀ d.T (d.ε j) (t, y)) := by
    intro hs
    exact hout (affineImage_subset_ball (d.eps_admissible j) (d.placement j).eps_space
      (scaledVelocity_tsupp_subset (d.eps_admissible j).1 d.packet.carrier_compact
        d.packet.support (d.placement j).carrier_subset ht hs))
  have hd := heq.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_of_notMem_tsupport ℝ hn] at hd
  simp only [spatialGradient, spatialDerivative, hd]
  rfl

/-- Differentiation commutes with the finite superposition. -/
theorem gradient_sum (t : ℝ) (ht : t < d.T) (x : Space) :
    spatialGradient d.assembledVelocity t x =
      ∑ j, spatialGradient (d.component j).velocity t x := by
  have hd := fderiv_fun_sum (u := Finset.univ)
    (fun j _ => (d.component_slice_contDiff j t ht).differentiable (by simp) x)
  ext i k
  simp only [spatialGradient, spatialDerivative, assembledVelocity, finiteVelocitySum,
    hd, sum_apply, WithLp.ofLp_sum, WithLp.ofLp_toLp, Finset.sum_apply]

/-- Pointwise squared-gradient additivity in the cube interior. -/
theorem gradient_enorm_sq_sum (t : ℝ) (ht : t < d.T)
    (x : Space) (hx : x ∈ interior fundamentalCube) :
    ‖spatialGradient d.assembledVelocity t x‖ₑ ^ (2 : ℕ) =
      ∑ j, ‖spatialGradient (d.component j).velocity t x‖ₑ ^ (2 : ℕ) := by
  classical
  rw [d.gradient_sum t ht x]
  by_cases hb : ∃ j, x ∈ Metric.ball (d.regionCenter j) (d.regionRadius j)
  · obtain ⟨j, hj⟩ := hb
    have hz : ∀ i, i ≠ j → spatialGradient (d.component i).velocity t x = 0 := by
      intro i hij
      exact d.component_gradient_support i t ht x hx
        (fun hi => Set.disjoint_left.mp (d.regions_disjoint hij) hi hj)
    rw [Finset.sum_eq_single j (fun i _ hij => hz i hij) (by simp)]
    symm
    apply Finset.sum_eq_single j
    · intro i _ hij
      simp [hz i hij]
    · simp
  · have hz : ∀ j, spatialGradient (d.component j).velocity t x = 0 :=
      fun j => d.component_gradient_support j t ht x hx (fun hj => hb ⟨j, hj⟩)
    simp [hz]

/-- Squared gradient norms add on each time slice. -/
theorem slice_gradient_additive (t : ℝ) (ht : t < d.T) :
    (eLpNorm (torusLift (fun x => spatialGradient d.assembledVelocity t x)) 2
      periodicTorusMeasure) ^ (2 : ℕ) =
    ∑ j, (eLpNorm (torusLift (fun x => spatialGradient (d.component j).velocity t x)) 2
      periodicTorusMeasure) ^ (2 : ℕ) := by
  have hsq {g : Space → WithLp 2 (Fin 3 → Space)} :
      eLpNorm g 2 (volume.restrict fundamentalCube) ^ (2 : ℕ) =
        ∫⁻ x in fundamentalCube, ‖g x‖ₑ ^ (2 : ℕ) := by
    simpa using (eLpNorm_nnreal_pow_eq_lintegral (f := g)
      (μ := volume.restrict fundamentalCube) (p := (2 : ℝ≥0)) (by norm_num))
  simp_rw [eLpNorm_torusLift_restrict, hsq]
  calc
    _ = ∫⁻ x in fundamentalCube, ∑ j,
        ‖spatialGradient (d.component j).velocity t x‖ₑ ^ (2 : ℕ) := by
      apply lintegral_congr_ae
      apply ae_iff.mpr
      rw [Measure.restrict_apply' measurableSet_fundamentalCube]
      apply measure_mono_null _ volume_frontier_fundamentalCube
      intro x hx
      exact ⟨subset_closure hx.2, fun hi => hx.1 (d.gradient_enorm_sq_sum t ht x hi)⟩
    _ = _ := by
      apply lintegral_finsetSum'
      intro j _
      have hc := NSFormalization.Section4.I02.continuous_spatialGradient
        ((d.component_slice_contDiff j t ht).comp contDiff_snd) t
      exact hc.aestronglyMeasurable.enorm.pow_const 2

/-- A component's squared gradient norm is the Euclidean rescaled dissipation rate. -/
theorem component_gradient_rate (j : Fin d.N) (t : ℝ) (ht : t < d.T) :
    (eLpNorm (torusLift (fun x => spatialGradient (d.component j).velocity t x)) 2
      periodicTorusMeasure) ^ (2 : ℕ) =
      ENNReal.ofReal (NavierStokesR3.CompactEnergy.dissipation
        (NSFormalization.Source.parabolicVelocity (d.ε j)⁻¹ (d.T - d.ε j ^ 2)
          (d.placement j).x₀ (zeroPastField u)) t) := by
  have hs := scaledVelocity_slice_contDiff (x₀ := (d.placement j).x₀) d.packet.extension_smooth (d.eps_admissible j).1 ht
  have hc := scaledVelocity_slice_hasCompactSupport (x₀ := (d.placement j).x₀)
    (d.eps_admissible j).1 d.packet.carrier_compact d.packet.support
    (d.placement j).carrier_subset (d.placement j).Kstar_compact ht
  have hp := scaledVelocity_slice_subset_cube (d.eps_admissible j) d.packet.carrier_compact
    d.packet.support (d.placement j).carrier_subset (d.placement j).eps_space
    (d.placement j).chartBall_in_cube ht
  rw [(d.component_pin j).1]
  rw [show (fun x => spatialGradient (periodizedScaledVelocity u (d.placement j).x₀ d.T (d.ε j)) t x)
      = (fun x => spatialGradient (fun z : SpaceTime => periodize
        (fun y => scaledVelocity u (d.placement j).x₀ d.T (d.ε j) (t, y)) z.2) t x) from rfl]
  rw [eLpNorm_torusLift_spatialGradient_periodize _ hs t hp,
    ← eLpNorm_gradientVector_eq_gradientENorm hs volume]
  have he := NSFormalization.Section4.I03.eLpNorm_spatialGradient_sq_slice hs hc
  rw [scaledVelocity_eq_parabolicVelocity] at he ⊢
  simpa only [ENNReal.rpow_two, spatialGradient, spatialDerivative] using he

/-- The squared component dissipation in the packet normalization. -/
theorem component_dissipation_sq (j : Fin d.N) :
    energyGradientT d.T (d.component j).velocity ^ (2 : ℕ) =
      ENNReal.ofReal (E ^ 2 * d.ε j) := by
  have hE : 0 ≤ E := d.packet.dissipation_eq ▸ Real.sqrt_nonneg _
  rw [(d.component_pin j).1]
  have h := (d.scaling j).packetDissipationIdentity (d.ε j) (d.eps_admissible j)
  rw [d.placement_time j] at h
  rw [h, ← ENNReal.ofReal_pow (mul_nonneg
    (Real.rpow_nonneg (d.eps_admissible j).1.le _) hE)]
  congr 1
  rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul (d.eps_admissible j).1.le]
  norm_num
  ring

/-- Exact dissipation additivity for the finite superposition. -/
theorem dissipation_bound : (energyGradientT d.T d.assembledVelocity) ^ (2 : ℕ) =
    ENNReal.ofReal (E ^ 2 * ∑ j, d.ε j) := by
  have hsq (w : SpaceTimeField) : energyGradientT d.T w ^ (2 : ℕ) =
      ∫⁻ t in Ioo (0 : ℝ) d.T,
        (eLpNorm (torusLift (fun x => spatialGradient w t x)) 2
          periodicTorusMeasure) ^ (2 : ℕ) := by
    unfold energyGradientT
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  rw [hsq]
  calc
    _ = ∫⁻ t in Ioo (0 : ℝ) d.T, ∑ j,
        (eLpNorm (torusLift (fun x => spatialGradient (d.component j).velocity t x)) 2
          periodicTorusMeasure) ^ (2 : ℕ) := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro t ht
      exact d.slice_gradient_additive t ht.2
    _ = ∑ j, ∫⁻ t in Ioo (0 : ℝ) d.T,
        (eLpNorm (torusLift (fun x => spatialGradient (d.component j).velocity t x)) 2
          periodicTorusMeasure) ^ (2 : ℕ) := by
      apply lintegral_finsetSum'
      intro j _
      have hm := (NSFormalization.Section4.I03.scaled_dissipation_integrableOn d.packet
        (d.placement j).x₀ (d.eps_admissible j).1
        ((d.placement j).eps_time (d.ε j) (d.eps_admissible j))).aestronglyMeasurable
      apply hm.aemeasurable.ennreal_ofReal.congr
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact (d.component_gradient_rate j t ht.2).symm
    _ = ∑ j, energyGradientT d.T (d.component j).velocity ^ (2 : ℕ) := by
      simp_rw [hsq]
    _ = ∑ j, ENNReal.ofReal (E ^ 2 * d.ε j) := by
      simp_rw [d.component_dissipation_sq]
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg
        (fun j _ => mul_nonneg (sq_nonneg E) (d.eps_admissible j).1.le), Finset.mul_sum]

end RegionsData
end NSFormalization.Section3.T24
