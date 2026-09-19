import NSFormalization.Section3.T23.NoSlipEnergy
import NSFormalization.Section3.T23.DomainTimeIntegral

/-! Difference energy and uniqueness for classical no-slip solutions. -/
noncomputable section
namespace NSFormalization.Section3.T23
open Set MeasureTheory Filter
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open scoped ContDiff InnerProductSpace Topology

/-- Smoothness of the velocity difference on a common subslab. -/
theorem SmoothOnClosedSlab.sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Set ℝ} {Ω : Set Space} {f g : SpaceTime → E}
    (hf : SmoothOnClosedSlab I Ω f) (hg : SmoothOnClosedSlab I Ω g) :
    SmoothOnClosedSlab I Ω (f - g) := by
  obtain ⟨N, hN, hNsub, hf⟩ := hf
  obtain ⟨M, hM, hMsub, hg⟩ := hg
  exact ⟨N ∩ M, hN.inter hM, fun z hz => ⟨hNsub hz, hMsub hz⟩,
    (hf.mono inter_subset_left).sub (hg.mono inter_subset_right)⟩

/-- Restriction to a smaller time set keeps the same neighborhood extension. -/
theorem SmoothOnClosedSlab.mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I J : Set ℝ} {Ω : Set Space} {f : SpaceTime → E}
    (hf : SmoothOnClosedSlab I Ω f) (hJI : J ⊆ I) : SmoothOnClosedSlab J Ω f := by
  obtain ⟨N, hN, hsub, hs⟩ := hf
  exact ⟨N, hN, (Set.prod_mono hJI Subset.rfl).trans hsub, hs⟩

/-- The difference-energy integrand has the same neighborhood smoothness. -/
theorem SmoothOnClosedSlab.norm_sq {I : Set ℝ} {Ω : Set Space} {w : SpaceTimeField}
    (hw : SmoothOnClosedSlab I Ω w) :
    SmoothOnClosedSlab I Ω (fun z => ‖w z‖ ^ 2) := by
  obtain ⟨N, hN, hsub, hs⟩ := hw
  exact ⟨N, hN, hsub, hs.norm_sq ℝ⟩

/-- Actual domain difference energy. -/
def differenceEnergy (Ω : Set Space) (u v : SpaceTimeField) (t : ℝ) : ℝ :=
  ∫ x in Ω, ‖u (t, x) - v (t, x)‖ ^ 2

/-- Continuity of energy up to initial time, from the original solution fields. -/
theorem differenceEnergy_continuousOn {ν T₁ T₂ S : ℝ} {Ω : Set Space}
    {a : SpatialField} {g : SpaceTimeField}
    (hΩ : Bornology.IsBounded Ω) (hm : MeasurableSet Ω)
    (u : ClassicalSolutionOmega ν Ω a g T₁) (v : ClassicalSolutionOmega ν Ω a g T₂)
    (hS : S < min T₁ T₂) :
    ContinuousOn (differenceEnergy Ω u.velocity v.velocity) (Icc 0 S) := by
  have hu := u.velocity_smooth.mono (show Icc 0 S ⊆ Ico 0 T₁ from
    fun _ ht => ⟨ht.1, lt_of_le_of_lt ht.2 (lt_of_lt_of_le hS (min_le_left _ _))⟩)
  have hv := v.velocity_smooth.mono (show Icc 0 S ⊆ Ico 0 T₂ from
    fun _ ht => ⟨ht.1, lt_of_le_of_lt ht.2 (lt_of_lt_of_le hS (min_le_right _ _))⟩)
  exact domainIntegral_continuousOn hΩ hm isCompact_Icc
    (fun z hz => ((hu.sub hv).norm_sq.contDiffAt hz).continuousAt.continuousWithinAt)

/-- Energy differentiation, before using the momentum equations. -/
theorem differenceEnergy_hasDerivAt {ν T₁ T₂ : ℝ} {Ω : Set Space}
    {a : SpatialField} {g : SpaceTimeField}
    (hΩ : Bornology.IsBounded Ω) (hm : MeasurableSet Ω)
    (u : ClassicalSolutionOmega ν Ω a g T₁) (v : ClassicalSolutionOmega ν Ω a g T₂)
    {t : ℝ} (ht : t ∈ Ioo 0 (min T₁ T₂)) :
    HasDerivAt (differenceEnergy Ω u.velocity v.velocity)
      (2 * ∫ x in Ω, ⟪(u.velocity - v.velocity) (t, x),
        temporalDerivative (u.velocity - v.velocity) t x⟫_ℝ) t := by
  have hu := u.velocity_smooth.mono (show Ioo 0 (min T₁ T₂) ⊆ Ico 0 T₁ from
    fun _ hs => ⟨hs.1.le, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩)
  have hv := v.velocity_smooth.mono (show Ioo 0 (min T₁ T₂) ⊆ Ico 0 T₂ from
    fun _ hs => ⟨hs.1.le, lt_of_lt_of_le hs.2 (min_le_right _ _)⟩)
  have h := (hu.sub hv).norm_sq.hasDerivAt_integral hΩ hm isOpen_Ioo ht
  convert h using 1
  · rfl
  · rw [← integral_const_mul]
    apply setIntegral_congr_fun hm
    intro x hx
    have hd : DifferentiableAt ℝ (fun s => (u.velocity - v.velocity) (s, x)) t :=
      (((hu.sub hv).contDiffAt ⟨ht, subset_closure hx⟩).comp t
        (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
    exact (NavierStokes.PeriodicUniqueness.energy_density_derivative hd).deriv.symm

/-- The spatial derivative is linear in the velocity at smooth points. -/
theorem spatialDerivative_sub_at {u v : SpaceTimeField} {t : ℝ} {x : Space}
    (hu : ContDiffAt ℝ ∞ (fun y => u (t, y)) x)
    (hv : ContDiffAt ℝ ∞ (fun y => v (t, y)) x) :
    spatialDerivative (u - v) t x = spatialDerivative u t x - spatialDerivative v t x :=
  fderiv_fun_sub (hu.differentiableAt (by simp)) (hv.differentiableAt (by simp))

/-- Local linearity of the Laplacian; openness supplies a neighborhood for the
first-derivative identity, so no global smoothness premise is needed. -/
theorem spatialLaplacian_sub_on {Ω : Set Space} (hΩ : IsOpen Ω)
    {u v : SpaceTimeField} {t : ℝ}
    (hu : ∀ x ∈ Ω, ContDiffAt ℝ ∞ (fun y => u (t, y)) x)
    (hv : ∀ x ∈ Ω, ContDiffAt ℝ ∞ (fun y => v (t, y)) x)
    {x : Space} (hx : x ∈ Ω) :
    spatialLaplacian (u - v) t x = spatialLaplacian u t x - spatialLaplacian v t x := by
  simp only [spatialLaplacian, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun y => spatialDerivative (u - v) t y (coordinateVector i)) =ᶠ[𝓝 x]
      (fun y => spatialDerivative u t y (coordinateVector i) -
        spatialDerivative v t y (coordinateVector i)) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    rw [spatialDerivative_sub_at (hu y hy) (hv y hy)]
    rfl
  rw [he.fderiv_eq]
  simp only [spatialDerivative]
  rw [fderiv_fun_sub
    ((contDiffAt_partial (hu x hx) i).differentiableAt (by simp))
    ((contDiffAt_partial (hv x hx) i).differentiableAt (by simp))]
  rfl
/-- Subtract the momentum equations locally, retaining the transport by `u`
and the derivative of `v` that is bounded on the compact subslab. -/
theorem difference_momentum {ν T₁ T₂ : ℝ} {Ω : Set Space}
    {a : SpatialField} {g : SpaceTimeField} (hΩ : IsOpen Ω)
    (u : ClassicalSolutionOmega ν Ω a g T₁) (v : ClassicalSolutionOmega ν Ω a g T₂)
    {t : ℝ} (ht : t ∈ Ioo 0 (min T₁ T₂)) {x : Space} (hx : x ∈ Ω) :
    temporalDerivative (u.velocity - v.velocity) t x =
      ν • spatialLaplacian (u.velocity - v.velocity) t x -
      spatialDerivative (u.velocity - v.velocity) t x (u.velocity (t, x)) -
      spatialDerivative v.velocity t x ((u.velocity - v.velocity) (t, x)) -
      pressureGradient (u.pressure - v.pressure) t x := by
  have ht₁ : t ∈ Ico 0 T₁ := ⟨ht.1.le, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
  have ht₂ : t ∈ Ico 0 T₂ := ⟨ht.1.le, lt_of_lt_of_le ht.2 (min_le_right _ _)⟩
  have hu : ∀ y ∈ Ω, ContDiffAt ℝ ∞ (fun z => u.velocity (t, z)) y := fun y hy => u.velocity_smooth.contDiffAt_slice ht₁ (subset_closure hy)
  have hv : ∀ y ∈ Ω, ContDiffAt ℝ ∞ (fun z => v.velocity (t, z)) y := fun y hy => v.velocity_smooth.contDiffAt_slice ht₂ (subset_closure hy)
  have hp := u.pressure_smooth.contDiffAt_slice ht₁ (subset_closure hx)
  have hq := v.pressure_smooth.contDiffAt_slice ht₂ (subset_closure hx)
  have htime (T : ℝ) (z : ClassicalSolutionOmega ν Ω a g T) (htt : t ∈ Ico 0 T) :
      DifferentiableAt ℝ (fun s => z.velocity (s, x)) t :=
    ((z.velocity_smooth.contDiffAt ⟨htt, subset_closure hx⟩).comp t
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hpress : pressureGradient (u.pressure - v.pressure) t x =
      pressureGradient u.pressure t x - pressureGradient v.pressure t x := by
    simp only [pressureGradient, Pi.sub_apply,
      fderiv_fun_sub (hp.differentiableAt (by simp)) (hq.differentiableAt (by simp)),
      _root_.sub_apply, sub_smul, Finset.sum_sub_distrib]
  have ha : advection u.velocity t x - advection v.velocity t x =
      spatialDerivative (u.velocity - v.velocity) t x (u.velocity (t, x)) +
      spatialDerivative v.velocity t x ((u.velocity - v.velocity) (t, x)) := by
    rw [spatialDerivative_sub_at (hu x hx) (hv x hx)]
    simp only [advection, Pi.sub_apply, _root_.sub_apply, map_sub]
    abel
  have hn := (u.momentum t ⟨ht.1, ht₁.2⟩ x hx).trans
    (v.momentum t ⟨ht.1, ht₂.2⟩ x hx).symm
  rw [NavierStokes.PeriodicUniqueness.temporalDerivative_sub (htime T₁ u ht₁) (htime T₂ v ht₂),
    spatialLaplacian_sub_on hΩ hu hv hx, hpress, smul_sub]
  unfold NavierStokesR3.ProblemStatement.navierStokesResidual at hn
  have heq := sub_eq_zero.mpr hn
  have heq' : temporalDerivative u.velocity t x - temporalDerivative v.velocity t x +
      (advection u.velocity t x - advection v.velocity t x) -
      (ν • spatialLaplacian u.velocity t x - ν • spatialLaplacian v.velocity t x) +
      (pressureGradient u.pressure t x - pressureGradient v.pressure t x) = 0 := by
    convert heq using 1
    abel
  rw [ha] at heq'
  apply sub_eq_zero.mp
  convert heq' using 1
  abel

/-- Incompressibility of the difference follows from the raw divergence fields. -/
theorem difference_divergence {ν T₁ T₂ : ℝ} {Ω : Set Space}
    {a : SpatialField} {g : SpaceTimeField}
    (u : ClassicalSolutionOmega ν Ω a g T₁) (v : ClassicalSolutionOmega ν Ω a g T₂)
    {t : ℝ} (ht : t ∈ Ico 0 (min T₁ T₂)) {x : Space} (hx : x ∈ Ω) :
    spatialDivergence (u.velocity - v.velocity) t x = 0 := by
  have ht₁ : t ∈ Ico 0 T₁ := ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
  have ht₂ : t ∈ Ico 0 T₂ := ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_right _ _)⟩
  have hd := spatialDerivative_sub_at
    (u.velocity_smooth.contDiffAt_slice ht₁ (subset_closure hx))
    (v.velocity_smooth.contDiffAt_slice ht₂ (subset_closure hx))
  simp only [spatialDivergence, hd, _root_.sub_apply, PiLp.sub_apply,
    Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr ((u.divergence t ht₁ x hx).trans (v.divergence t ht₂ x hx).symm)

/-- The no-slip fields give the zero boundary values required by IBP. -/
theorem difference_no_slip {ν T₁ T₂ : ℝ} {Ω : Set Space}
    {a : SpatialField} {g : SpaceTimeField}
    (u : ClassicalSolutionOmega ν Ω a g T₁) (v : ClassicalSolutionOmega ν Ω a g T₂)
    {t : ℝ} (ht : t ∈ Ico 0 (min T₁ T₂)) {x : Space} (hx : x ∈ frontier Ω) :
    (u.velocity - v.velocity) (t, x) = 0 := by
  simp only [Pi.sub_apply, u.no_slip t ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩ x hx,
    v.no_slip t ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_right _ _)⟩ x hx, sub_self]

/-- Pointwise smoothness of the spatial Laplacian. -/
theorem contDiffAt_spatialLaplacian {w : SpaceTimeField} {t : ℝ} {x : Space}
    (hw : ContDiffAt ℝ ∞ (fun y => w (t, y)) x) :
    ContDiffAt ℝ ∞ (spatialLaplacian w t) x :=
  ContDiffAt.sum fun i _ => contDiffAt_partial (contDiffAt_partial hw i) i

/-- Pointwise smoothness of the pressure gradient. -/
theorem contDiffAt_pressureGradient {p : SpaceTimeScalar} {t : ℝ} {x : Space}
    (hp : ContDiffAt ℝ ∞ (fun y => p (t, y)) x) :
    ContDiffAt ℝ ∞ (pressureGradient p t) x :=
  ContDiffAt.sum fun i _ => (contDiffAt_partial hp i).smul contDiffAt_const

/-- The difference-energy identity, derived from the momentum equations,
no-slip, incompressibility, and boundary IBP. -/
theorem difference_energy_identity {ν T₁ T₂ : ℝ} {Ω : Set Space}
    {a : SpatialField} {g : SpaceTimeField}
    (hI : IBP Ω) (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (u : ClassicalSolutionOmega ν Ω a g T₁) (v : ClassicalSolutionOmega ν Ω a g T₂)
    {t : ℝ} (ht : t ∈ Ioo 0 (min T₁ T₂)) :
    HasDerivAt (differenceEnergy Ω u.velocity v.velocity)
      (-2 * ν * (∫ x in Ω, ∑ i : Fin 3,
        ‖spatialDerivative (u.velocity - v.velocity) t x (coordinateVector i)‖ ^ 2) -
       2 * (∫ x in Ω, ⟪spatialDerivative v.velocity t x ((u.velocity - v.velocity) (t, x)),
         (u.velocity - v.velocity) (t, x)⟫_ℝ)) t := by
  let w := u.velocity - v.velocity
  let p := u.pressure - v.pressure
  have ht₁ : t ∈ Ico 0 T₁ := ⟨ht.1.le, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
  have ht₂ : t ∈ Ico 0 T₂ := ⟨ht.1.le, lt_of_lt_of_le ht.2 (min_le_right _ _)⟩
  have hu : ∀ x ∈ closure Ω, ContDiffAt ℝ ∞ (fun y => u.velocity (t, y)) x :=
    fun _ hx => u.velocity_smooth.contDiffAt_slice ht₁ hx
  have hv : ∀ x ∈ closure Ω, ContDiffAt ℝ ∞ (fun y => v.velocity (t, y)) x :=
    fun _ hx => v.velocity_smooth.contDiffAt_slice ht₂ hx
  have hw : ∀ x ∈ closure Ω, ContDiffAt ℝ ∞ (fun y => w (t, y)) x :=
    fun x hx => (hu x hx).sub (hv x hx)
  have hp : ∀ x ∈ closure Ω, ContDiffAt ℝ ∞ (fun y => p (t, y)) x := fun x hx =>
    (u.pressure_smooth.contDiffAt_slice ht₁ hx).sub (v.pressure_smooth.contDiffAt_slice ht₂ hx)
  have hwz : ∀ x ∈ frontier Ω, w (t, x) = 0 := fun _ hx =>
    difference_no_slip u v ⟨ht.1.le, ht.2⟩ hx
  have hwd : ∀ x ∈ Ω, spatialDivergence w t x = 0 := fun _ hx =>
    difference_divergence u v ⟨ht.1.le, ht.2⟩ hx
  have hL := hI.integral_laplacian_energy hb ho.measurableSet hw hwz
  have hP := hI.integral_pressure_energy_zero hb ho.measurableSet hw hp hwz hwd
  have hU := hI.integral_transport_energy_zero hb ho.measurableSet hw hu
    (u.no_slip t ht₁) (u.divergence t ht₁)
  change (∫ x in Ω, ⟪w (t, x), spatialDerivative w t x (u.velocity (t, x))⟫_ℝ) = 0 at hU
  have hiL : IntegrableOn (fun x => ⟪w (t, x), spatialLaplacian w t x⟫_ℝ) Ω :=
    integrableOn_of_contDiffAt_closure hb fun x hx =>
      (hw x hx).inner ℝ (contDiffAt_spatialLaplacian (hw x hx))
  have hiP : IntegrableOn (fun x => ⟪w (t, x), pressureGradient p t x⟫_ℝ) Ω :=
    integrableOn_of_contDiffAt_closure hb fun x hx =>
      (hw x hx).inner ℝ (contDiffAt_pressureGradient (hp x hx))
  have hiU : IntegrableOn (fun x => ⟪w (t, x), spatialDerivative w t x (u.velocity (t, x))⟫_ℝ) Ω :=
    integrableOn_of_contDiffAt_closure hb fun x hx =>
      (hw x hx).inner ℝ (((hw x hx).fderiv_right (by simp)).clm_apply (hu x hx))
  have hiV : IntegrableOn (fun x => ⟪w (t, x), spatialDerivative v.velocity t x (w (t, x))⟫_ℝ) Ω :=
    integrableOn_of_contDiffAt_closure hb fun x hx =>
      (hw x hx).inner ℝ (((hv x hx).fderiv_right (by simp)).clm_apply (hw x hx))
  have he : (∫ x in Ω, ⟪w (t, x), temporalDerivative w t x⟫_ℝ) =
      ν * (∫ x in Ω, ⟪w (t, x), spatialLaplacian w t x⟫_ℝ) -
      (∫ x in Ω, ⟪w (t, x), spatialDerivative w t x (u.velocity (t, x))⟫_ℝ) -
      (∫ x in Ω, ⟪w (t, x), spatialDerivative v.velocity t x (w (t, x))⟫_ℝ) -
      (∫ x in Ω, ⟪w (t, x), pressureGradient p t x⟫_ℝ) := by
    calc
      _ = ∫ x in Ω, ν * ⟪w (t, x), spatialLaplacian w t x⟫_ℝ -
          ⟪w (t, x), spatialDerivative w t x (u.velocity (t, x))⟫_ℝ -
          ⟪w (t, x), spatialDerivative v.velocity t x (w (t, x))⟫_ℝ -
          ⟪w (t, x), pressureGradient p t x⟫_ℝ := by
        apply setIntegral_congr_fun ho.measurableSet
        intro x hx
        dsimp
        rw [difference_momentum ho u v ht hx]
        simp only [inner_sub_right, inner_smul_right, w, p]
      _ = _ := by
        have hi₁ : IntegrableOn (fun x => ν * ⟪w (t, x), spatialLaplacian w t x⟫_ℝ -
            ⟪w (t, x), spatialDerivative w t x (u.velocity (t, x))⟫_ℝ) Ω :=
          (hiL.const_mul ν).sub hiU
        have hi₂ : IntegrableOn (fun x => ν * ⟪w (t, x), spatialLaplacian w t x⟫_ℝ -
            ⟪w (t, x), spatialDerivative w t x (u.velocity (t, x))⟫_ℝ -
            ⟪w (t, x), spatialDerivative v.velocity t x (w (t, x))⟫_ℝ) Ω := hi₁.sub hiV
        rw [integral_sub hi₂ hiP, integral_sub hi₁ hiV,
          integral_sub (hiL.const_mul ν) hiU, integral_const_mul]
  rw [hL, hU, hP, sub_zero, sub_zero] at he
  have hd := differenceEnergy_hasDerivAt hb ho.measurableSet u v ht
  change HasDerivAt _ (2 * ∫ x in Ω, ⟪w (t, x), temporalDerivative w t x⟫_ℝ) t at hd
  rw [he] at hd
  convert hd using 1
  simp only [real_inner_comm (spatialDerivative v.velocity t _ _) (w (t, _))]
  dsimp only [w]
  ring

/-- The remaining convection integral is bounded by operator norm times energy. -/
theorem abs_convection_integral_le {Ω : Set Space} (hb : Bornology.IsBounded Ω)
    (hm : MeasurableSet Ω) {v w : Space → Space}
    (hv : ∀ x ∈ closure Ω, ContDiffAt ℝ ∞ v x)
    (hw : ∀ x ∈ closure Ω, ContDiffAt ℝ ∞ w x)
    {C : ℝ} (hC : ∀ x ∈ Ω, ‖fderiv ℝ v x‖ ≤ C) :
    |∫ x in Ω, ⟪fderiv ℝ v x (w x), w x⟫_ℝ| ≤ C * (∫ x in Ω, ‖w x‖ ^ 2) := by
  have hi : IntegrableOn (fun x => ⟪fderiv ℝ v x (w x), w x⟫_ℝ) Ω :=
    integrableOn_of_contDiffAt_closure hb fun x hx =>
      (((hv x hx).fderiv_right (by simp)).clm_apply (hw x hx)).inner ℝ (hw x hx)
  have he : IntegrableOn (fun x => C * ‖w x‖ ^ 2) Ω :=
    (integrableOn_of_contDiffAt_closure hb fun x hx => (hw x hx).norm_sq ℝ).const_mul C
  calc
    |∫ x in Ω, ⟪fderiv ℝ v x (w x), w x⟫_ℝ| ≤
        ∫ x in Ω, |⟪fderiv ℝ v x (w x), w x⟫_ℝ| := abs_integral_le_integral_abs
    _ ≤ ∫ x in Ω, C * ‖w x‖ ^ 2 := by
      apply integral_mono_ae hi.abs he
      filter_upwards [ae_restrict_mem hm] with x hx
      calc
        |⟪fderiv ℝ v x (w x), w x⟫_ℝ| ≤ ‖fderiv ℝ v x (w x)‖ * ‖w x‖ :=
          abs_real_inner_le_norm _ _
        _ ≤ (‖fderiv ℝ v x‖ * ‖w x‖) * ‖w x‖ :=
          mul_le_mul_of_nonneg_right ((fderiv ℝ v x).le_opNorm _) (norm_nonneg _)
        _ ≤ (C * ‖w x‖) * ‖w x‖ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hC x hx) (norm_nonneg _)) (norm_nonneg _)
        _ = C * ‖w x‖ ^ 2 := by ring
    _ = _ := integral_const_mul _ _
/-- Uniqueness on any bounded open domain satisfying the explicit scalar
boundary IBP identity. All energy estimates follow from the solution fields. -/
theorem velocity_eq_of_ibp {ν T₁ T₂ : ℝ} {Ω : Set Space}
    {a : SpatialField} {g : SpaceTimeField} (hν : 0 < ν)
    (hI : IBP Ω) (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (u : ClassicalSolutionOmega ν Ω a g T₁) (v : ClassicalSolutionOmega ν Ω a g T₂)
    {t : ℝ} (ht : t ∈ Ico 0 (min T₁ T₂)) {x : Space} (hx : x ∈ Ω) :
    u.velocity (t, x) = v.velocity (t, x) := by
  obtain ⟨S, htS, hS⟩ := exists_between ht.2
  have hS₀ : 0 ≤ S := ht.1.trans htS.le
  obtain ⟨C, _hC₀, hC⟩ := v.spatialDerivative_bound hb (lt_of_lt_of_le hS (min_le_right _ _))
  let E := differenceEnergy Ω u.velocity v.velocity
  let D : ℝ → ℝ := fun s => ∫ y in Ω, ∑ i : Fin 3,
    ‖spatialDerivative (u.velocity - v.velocity) s y (coordinateVector i)‖ ^ 2
  let B : ℝ → ℝ := fun s => ∫ y in Ω,
    ⟪spatialDerivative v.velocity s y ((u.velocity - v.velocity) (s, y)),
      (u.velocity - v.velocity) (s, y)⟫_ℝ
  let E' : ℝ → ℝ := fun s => -2 * ν * D s - 2 * B s
  have hderiv (s : ℝ) (hs : s ∈ Ioo 0 S) : HasDerivAt E (E' s) s :=
    difference_energy_identity hI ho hb u v ⟨hs.1, hs.2.trans hS⟩
  have hbound (s : ℝ) (hs : s ∈ Ioo 0 S) : E' s ≤ (2 * C) * E s := by
    have hs₁ : s ∈ Ico 0 T₁ := ⟨hs.1.le, lt_of_lt_of_le (hs.2.trans hS) (min_le_left _ _)⟩
    have hs₂ : s ∈ Ico 0 T₂ := ⟨hs.1.le, lt_of_lt_of_le (hs.2.trans hS) (min_le_right _ _)⟩
    have hv : ∀ y ∈ closure Ω, ContDiffAt ℝ ∞ (fun z => v.velocity (s, z)) y :=
      fun _ hy => v.velocity_smooth.contDiffAt_slice hs₂ hy
    have hw : ∀ y ∈ closure Ω, ContDiffAt ℝ ∞ (fun z => (u.velocity - v.velocity) (s, z)) y :=
      fun y hy => (u.velocity_smooth.contDiffAt_slice hs₁ hy).sub (hv y hy)
    have hB : |B s| ≤ C * E s := abs_convection_integral_le hb ho.measurableSet hv hw
      (fun y hy => hC s ⟨hs.1.le, hs.2.le⟩ y (subset_closure hy))
    have hD : 0 ≤ D s := integral_nonneg fun y => Finset.sum_nonneg fun i _ => sq_nonneg _
    have hB' := neg_le_abs (B s)
    dsimp only [E']
    nlinarith [mul_nonneg hν.le hD]
  have hinit : E 0 = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    simp [u.initial y hy, v.initial y hy]
  have hz := NavierStokes.PeriodicUniqueness.gronwall_zero hS₀
    (differenceEnergy_continuousOn hb ho.measurableSet u v hS) hinit
    (fun s _ => integral_nonneg fun y => sq_nonneg _) hderiv hbound t ⟨ht.1, htS.le⟩
  exact eqOn_of_integral_norm_sub_sq_eq_zero ho (by
    intro y hy
    exact (u.velocity_smooth.contDiffAt_slice
      ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩ (subset_closure hy)).continuousAt.continuousWithinAt) (by
    intro y hy
    exact (v.velocity_smooth.contDiffAt_slice
      ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_right _ _)⟩ (subset_closure hy)).continuousAt.continuousWithinAt)
    (difference_energy_integrable hb u v ht) hz hx

/-- The exact U7 conclusion under one explicit boundary integration identity.
For regular-level domains, proving `IBP Ω` is the sole missing analytic input. -/
theorem noSlip_uniqueness_of_ibp : ∀ (ν : ℝ), 0 < ν →
    ∀ (Ω : Set Space), IsBoundedBoxOrSmoothDomain Ω → IBP Ω →
    ∀ (a' : SpatialField), a' ∈ initialClassOmega Ω →
    ∀ (f : SpaceTimeField), f ∈ forceClassOmega Ω →
    ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionOmega ν Ω a' f T₁)
      (u₂ : ClassicalSolutionOmega ν Ω a' f T₂),
    ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x ∈ Ω,
      u₁.velocity (t, x) = u₂.velocity (t, x) := by
  intro ν hν Ω hΩ hI a' _ha f _hf T₁ T₂ u₁ u₂ t ht x hx
  exact velocity_eq_of_ibp hν hI hΩ.1 hΩ.2.1 u₁ u₂ ht hx

/-- The Spec's strictly separated open boxes are open and bounded. -/
theorem IsBoxDomain.open_bounded {Ω : Set Space} (hΩ : IsBoxDomain Ω) :
    IsOpen Ω ∧ Bornology.IsBounded Ω := by
  obtain ⟨a, b, _hab, rfl⟩ := hΩ
  constructor
  · have he : {x : Space | ∀ i, a i < x i ∧ x i < b i} =
        ⋂ i : Fin 3, (fun x : Space => x i) ⁻¹' Ioo (a i) (b i) := by ext x; simp
    rw [he]
    exact isOpen_iInter_of_finite fun i => isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous
  · let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
    apply ((isCompact_Icc : IsCompact (Icc a b)).image e.continuous).isBounded.subset
    intro x hx
    refine ⟨WithLp.ofLp x, ⟨fun i => (hx i).1.le, fun i => (hx i).2.le⟩, ?_⟩
    rfl

/-- U7 on the box branch, with the original solution, initial-data and force
binders and no additional analytic hypotheses. -/
theorem noSlip_uniqueness_box : ∀ (ν : ℝ), 0 < ν →
    ∀ (Ω : Set Space), IsBoxDomain Ω →
    ∀ (a' : SpatialField), a' ∈ initialClassOmega Ω →
    ∀ (f : SpaceTimeField), f ∈ forceClassOmega Ω →
    ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionOmega ν Ω a' f T₁)
      (u₂ : ClassicalSolutionOmega ν Ω a' f T₂),
    ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x ∈ Ω,
      u₁.velocity (t, x) = u₂.velocity (t, x) := by
  intro ν hν Ω hΩ a' _ha f _hf T₁ T₂ u₁ u₂ t ht x hx
  exact velocity_eq_of_ibp hν (ibp_box hΩ) hΩ.open_bounded.1 hΩ.open_bounded.2 u₁ u₂ ht hx

end NSFormalization.Section3.T23



