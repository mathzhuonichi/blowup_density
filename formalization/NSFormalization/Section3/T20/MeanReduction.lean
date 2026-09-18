import NSFormalization.Section3.T20.CriticalRegularity
import NSFormalization.Section3.T12.HaarCube

noncomputable section
namespace NSFormalization.Section3.T20

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar forceTimeMeasure)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open NSFormalization.Section3.T12
open scoped ContDiff ENNReal BigOperators

theorem reductionRegular : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
        ∀ t ∈ Ico (0 : ℝ) T,
          let v := fun x ↦ meanFreeVelocity g w.velocity (t, x)
          let h := fun x ↦ meanFreeForce g (t, x)
          IsMeanZeroT v ∧ SmoothPeriodicT v ∧
            MemPeriodicHomogeneous (1 / 2) v ∧
            MemPeriodicHomogeneous (3 / 2) v ∧
            MemPeriodicHmVector 2 v ∧
            IsMeanZeroT h ∧ SmoothPeriodicT h ∧
            MemPeriodicHomogeneous (1 / 2) h ∧
            periodicLpENorm 2 h ≠ ⊤ ∧
            periodicLpENorm 2 (gradientTensor v) ≠ ⊤ ∧
            periodicLpENorm 2 (laplacian v) ≠ ⊤ := by
  intro ν hν g hg T w t ht
  let a : SpatialField := fun _ ↦ 0
  have ha : a ∈ initialClassT := by
    refine ⟨contDiff_const, ?_, ?_⟩
    · intro x j
      rfl
    · intro x
      simp [spatialDivergence, spatialDerivative, a]
  have hu_smooth : ContDiff ℝ ∞ (fun x ↦ w.velocity (t, x)) :=
    w.velocity_smooth.comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun x ↦ ⟨⟨ht.1, ht.2⟩, mem_univ x⟩)
  have hu_periodic : IsPeriodicSpatial (fun x ↦ w.velocity (t, x)) :=
    w.velocity_periodic t ht
  have hg_smooth : ContDiff ℝ ∞ (fun x ↦ g (t, x)) :=
    hg.1.comp (contDiff_const.prodMk contDiff_id)
  have hg_periodic : IsPeriodicSpatial (fun x ↦ g (t, x)) :=
    hg.2.1 t (mem_univ _)
  have hmean : meanPathT g t = meanT (fun x ↦ w.velocity (t, x)) := by
    have hm := (periodicMeanReductionAPI.mean_formula ν hν a ha g hg T w t ht)
    simpa [meanPathT, velocityMeanT, a, galileanMeanT, meanT_const] using hm.symm
  have htrans_zero :=
    periodicMeanReductionAPI.transformed_mean_zero ν hν a ha g hg T w
  have hv_eq : (fun x ↦ meanFreeVelocity g w.velocity (t, x)) =
      meanZeroPartT (fun x ↦ w.velocity (t, x)) := by
    funext x
    simp [meanFreeVelocity, meanZeroPartT, hmean]
  have hh_eq : (fun x ↦ meanFreeForce g (t, x)) =
      meanZeroPartT (fun x ↦ g (t, x)) := by
    rfl
  have hv_smooth : ContDiff ℝ ∞ (fun x ↦ meanFreeVelocity g w.velocity (t, x)) := by
    rw [hv_eq]
    exact hu_smooth.sub contDiff_const
  have hv_periodic : IsPeriodicSpatial (fun x ↦ meanFreeVelocity g w.velocity (t, x)) := by
    rw [hv_eq]
    intro x j
    simp only [meanZeroPartT]
    change (fun y ↦ w.velocity (t, y)) (x + coordinateVector j) - _ = _
    rw [hu_periodic x j]
  have hh_smooth : ContDiff ℝ ∞ (fun x ↦ meanFreeForce g (t, x)) := by
    rw [hh_eq]
    exact hg_smooth.sub contDiff_const
  have hh_periodic : IsPeriodicSpatial (fun x ↦ meanFreeForce g (t, x)) := by
    rw [hh_eq]
    intro x j
    simp only [meanZeroPartT]
    change (fun y ↦ g (t, y)) (x + coordinateVector j) - _ = _
    rw [hg_periodic x j]
  have hv_zero : IsMeanZeroT (fun x ↦ meanFreeVelocity g w.velocity (t, x)) := by
    unfold IsMeanZeroT
    rw [← MeanIdentity.meanT_translate hv_periodic (galileanShiftT a g t)]
    simpa [galileanVelocityT, meanFreeVelocity, meanPathT, a] using htrans_zero.2.1 t ht
  have hh_zero : IsMeanZeroT (fun x ↦ meanFreeForce g (t, x)) := by
    unfold IsMeanZeroT
    rw [← MeanIdentity.meanT_translate hh_periodic (galileanShiftT a g t)]
    simpa [galileanForceT, meanFreeForce, a] using htrans_zero.2.2 t ht
  have hv_hom (s : ℝ) (hs : 0 < s) :
      MemPeriodicHomogeneous s (fun x ↦ meanFreeVelocity g w.velocity (t, x)) := by
    refine ⟨hv_periodic, memLp_torusLift_vector hv_smooth.continuous 2, hv_zero, ?_⟩
    rw [hv_eq]
    have hlt := NSFormalization.Section3.T13.periodicHomogeneousENorm_lt_top hs
      hu_periodic hu_smooth
    exact ne_of_lt hlt
  have hh_hom : MemPeriodicHomogeneous (1 / 2)
      (fun x ↦ meanFreeForce g (t, x)) := by
    refine ⟨hh_periodic, memLp_torusLift_vector hh_smooth.continuous 2, hh_zero, ?_⟩
    rw [hh_eq]
    have hlt := NSFormalization.Section3.T13.periodicHomogeneousENorm_lt_top
      (by norm_num : (0 : ℝ) < 1 / 2) hg_periodic hg_smooth
    exact ne_of_lt hlt
  have hv_h2 : MemPeriodicHmVector 2
      (fun x ↦ meanFreeVelocity g w.velocity (t, x)) := by
    refine ⟨hv_periodic, memLp_torusLift_vector hv_smooth.continuous 2, ?_⟩
    exact periodicSobolevENorm_ne_top_smooth 2 hv_smooth hv_periodic
  have hh_lp : periodicLpENorm 2 (fun x ↦ meanFreeForce g (t, x)) ≠ ⊤ := by
    exact (memLp_torusLift_vector hh_smooth.continuous 2).eLpNorm_ne_top
  have hv_grad : periodicLpENorm 2 (gradientTensor
      (fun x ↦ meanFreeVelocity g w.velocity (t, x))) ≠ ⊤ := by
    exact (memLp_gradientTensor hv_smooth).eLpNorm_ne_top
  have hv_lap_smooth : ContDiff ℝ ∞ (laplacian
      (fun x ↦ meanFreeVelocity g w.velocity (t, x))) := contDiff_laplacian hv_smooth
  have hv_lap : periodicLpENorm 2 (laplacian
      (fun x ↦ meanFreeVelocity g w.velocity (t, x))) ≠ ⊤ := by
    exact (memLp_torusLift_vector hv_lap_smooth.continuous 2).eLpNorm_ne_top
  exact ⟨hv_zero, ⟨hv_smooth, hv_periodic⟩, hv_hom (1 / 2) (by norm_num),
    hv_hom (3 / 2) (by norm_num), hv_h2, hh_zero, ⟨hh_smooth, hh_periodic⟩,
    hh_hom, hh_lp, hv_grad, hv_lap⟩

theorem meanBound : ∀ (g : SpaceTimeField), g ∈ forceClassT →
    ∀ t : ℝ, 0 ≤ t →
      ENNReal.ofReal ‖meanPathT g t‖ ≤ meanForceIntegralT g t ∧
        meanForceIntegralT g t ≤ criticalRho g := by
  intro g hg t ht
  have hforce_cont : ContDiff ℝ ∞ (forceMeanT g) :=
    MeanIdentity.forceMeanT_contDiff hg.1
  have hzero_mode_le : ∀ (s : ℝ) (z : SpatialField) (A : PeriodicSobolev s),
      IsPeriodicDatum s z A → ‖meanT z‖ ≤ ‖A‖ := by
    intro s z A hA
    have hcoord (i : Fin 3) : ‖A.1 i 0‖ = ‖meanT z i‖ := by
      rw [hA.2.2 i 0, periodicFrequencyWeight]
      simp [periodicFourierCoeff_zero_eq_mean_component hA.2.1 i]
    rw [EuclideanSpace.norm_eq]
    change _ ≤ ‖A.1‖
    rw [PiLp.norm_eq_of_L2 A.1]
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro i _
    rw [← hcoord]
    have hi' := lp.norm_apply_le_norm (show (2 : ENNReal) ≠ 0 by norm_num) (A.1 i) 0
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hi'
  constructor
  · rw [meanForceIntegralT]
    have hnorm : ‖∫ s in (0 : ℝ)..t, forceMeanT g s‖ ≤
        ∫ s in (0 : ℝ)..t, ‖forceMeanT g s‖ :=
      intervalIntegral.norm_integral_le_integral_norm (f := forceMeanT g)
        (μ := volume) ht
    have hfi : IntegrableOn (fun s ↦ ‖forceMeanT g s‖) (Ioc (0 : ℝ) t) volume := by
      exact (hforce_cont.continuous.norm.intervalIntegrable 0 t).1
    have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) t)]
        (fun s ↦ ‖forceMeanT g s‖) := Filter.Eventually.of_forall (fun s ↦ norm_nonneg _)
    have hof := ofReal_integral_eq_lintegral_ofReal hfi hnonneg
    rw [show meanPathT g t = ∫ s in (0 : ℝ)..t, forceMeanT g s by
      simp [meanPathT, galileanMeanT, meanT_const]]
    rw [intervalIntegral.integral_of_le ht]
    have hnorm' : ‖∫ s in Ioc (0 : ℝ) t, forceMeanT g s‖ ≤
        ∫ s in Ioc (0 : ℝ) t, ‖forceMeanT g s‖ := by
      simpa only [intervalIntegral.integral_of_le ht] using hnorm
    exact (ENNReal.ofReal_le_ofReal hnorm').trans_eq hof
  · unfold criticalRho forceSobolevENormT
    apply le_iInf
    rintro ⟨G, hG, hGm⟩
    calc
      meanForceIntegralT g t ≤ ∫⁻ s in Ioi (0 : ℝ),
          ENNReal.ofReal ‖forceMeanT g s‖ := by
            apply lintegral_mono_set
            exact Ioc_subset_Ioi_self
      _ ≤ ∫⁻ s in Ioi (0 : ℝ), ‖G s‖ₑ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        have hpoint := hzero_mode_le (1 / 2) (fun x ↦ g (s, x)) (G s)
          (hG s (le_of_lt hs))
        change ENNReal.ofReal ‖meanT (fun x ↦ g (s, x))‖ ≤ ‖G s‖ₑ
        simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal hpoint
      _ = eLpNorm G 1 forceTimeMeasure := by
        rw [eLpNorm_one_eq_lintegral_enorm]

theorem meanFreeEquation : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
        ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
          temporalDerivative (meanFreeVelocity g w.velocity) t x +
              advection (meanFreeVelocity g w.velocity) t x +
              constantTransportT (meanPathT g)
                (meanFreeVelocity g w.velocity) (t, x) -
              ν • spatialLaplacian (meanFreeVelocity g w.velocity) t x +
              pressureGradient w.pressure t x =
            meanFreeForce g (t, x) := by
  intro ν hν g hg T w t ht x
  let a : SpatialField := fun _ ↦ 0
  have ha : a ∈ initialClassT := by
    refine ⟨contDiff_const, ?_, ?_⟩
    · intro y j
      rfl
    · intro y
      simp [spatialDivergence, spatialDerivative, a]
  have hmean_formula : ∀ r ∈ Ico (0 : ℝ) T,
      velocityMeanT w.velocity r = meanPathT g r := by
    intro r hr
    simpa [meanPathT, a] using
      periodicMeanReductionAPI.mean_formula ν hν a ha g hg T w r hr
  have hm_deriv : HasDerivAt (meanPathT g) (forceMeanT g t) t := by
    have hd := periodicMeanReductionAPI.mean_derivative ν hν a ha g hg T w t ht
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    exact (hmean_formula r ⟨hr.1.le, hr.2⟩).symm
  have hu_full : DifferentiableAt ℝ w.velocity (t, x) :=
    Transport.interior_differentiableAt w.velocity_smooth ht x
  have hu_time : HasDerivAt (fun s : ℝ ↦ w.velocity (s, x))
      (temporalDerivative w.velocity t x) t := by
    have hcomp := hu_full.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
    rw [Transport.temporalDerivative_eq_fderiv hu_full]
    exact hcomp
  have htemporal : temporalDerivative (meanFreeVelocity g w.velocity) t x =
      temporalDerivative w.velocity t x - forceMeanT g t := by
    have hsub := hu_time.sub hm_deriv
    change deriv (fun s : ℝ ↦ w.velocity (s, x) - meanPathT g s) t = _
    exact hsub.deriv
  have hu_slice : ContDiff ℝ 2 (fun y : Space ↦ w.velocity (t, y)) :=
    (Transport.slice_contDiff w.velocity_smooth ⟨ht.1.le, ht.2⟩).of_le (by simp)
  have hu_diff : DifferentiableAt ℝ (fun y : Space ↦ w.velocity (t, y)) x :=
    hu_slice.differentiable (by simp) x
  have hslice : ∀ y : Space,
      meanFreeVelocity g w.velocity (t, y) =
        (1 : ℝ) • w.velocity (t, y + 0) - meanPathT g t := by
    intro y
    simp [meanFreeVelocity]
  have hadv : advection (meanFreeVelocity g w.velocity) t x =
      advection w.velocity t (x + 0) -
        (1 : ℝ) • spatialDerivative w.velocity t (x + 0) (meanPathT g t) := by
    simpa using Transport.advection_slice (x := x) (v := meanFreeVelocity g w.velocity)
      (u := w.velocity) (α := 1) (s := t) (t := t) (Y := 0)
      (c := meanPathT g t) (hslice) (by simpa using hu_diff)
  have hconst : constantTransportT (meanPathT g)
      (meanFreeVelocity g w.velocity) (t, x) =
      spatialDerivative w.velocity t x (meanPathT g t) := by
    unfold constantTransportT
    rw [Transport.spatialDerivative_slice (v := meanFreeVelocity g w.velocity)
      (u := w.velocity) (α := 1) (s := t) (t := t) (Y := 0)
      (c := meanPathT g t) hslice (by simpa using hu_diff)]
    simp
  have hlap : spatialLaplacian (meanFreeVelocity g w.velocity) t x =
      spatialLaplacian w.velocity t (x + 0) := by
    simpa using (Transport.spatialLaplacian_slice (v := meanFreeVelocity g w.velocity)
      (u := w.velocity) (α := 1) (s := t) (t := t) (Y := 0)
      (c := meanPathT g t) x hslice hu_slice)
  have hpg : pressureGradient w.pressure t x =
      pressureGradient w.pressure t (x + 0) := by simp
  have hmom := w.momentum t ht x
  change temporalDerivative w.velocity t x + advection w.velocity t x -
      ν • spatialLaplacian w.velocity t x + pressureGradient w.pressure t x =
      g (t, x) at hmom
  rw [htemporal, hadv, hconst, hlap, hpg]
  simp only [add_zero, one_smul]
  calc
    temporalDerivative w.velocity t x - forceMeanT g t +
          (advection w.velocity t x - spatialDerivative w.velocity t x
            (meanPathT g t)) + spatialDerivative w.velocity t x (meanPathT g t) -
          ν • spatialLaplacian w.velocity t x + pressureGradient w.pressure t x =
        (temporalDerivative w.velocity t x + advection w.velocity t x -
          ν • spatialLaplacian w.velocity t x + pressureGradient w.pressure t x) -
            forceMeanT g t := by module
    _ = g (t, x) - forceMeanT g t := by rw [hmom]
    _ = meanFreeForce g (t, x) := by simp [meanFreeForce, forceMeanT]

end NSFormalization.Section3.T20
