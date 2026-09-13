import NSFormalization.Paper1.PeriodicInsertion
import NavierStokes.ComparatorBridge

/-!
# Positive-viscosity periodic uniqueness and obstruction to later solutions

The analytic uniqueness theorem is OpenAI's proved viscosity-one periodic
energy theorem. The adapter below only normalizes time and amplitude using
its existing `ComparatorBridge` derivative calculations.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicUniqueness
open NavierStokes NavierStokes.ProblemStatement NavierStokes.ComparatorBridge
open Set Filter MeasureTheory
open scoped ContDiff Topology

/-- Existing derivative formulas give the exact normalization of the physical
residual; the spatial period is unchanged. -/
theorem normalized_residual {ν : ℝ} (hν : 0 < ν) (u : VelocityField) (p : PressureField)
    (t : ℝ) (x : Space)
    (hd : DifferentiableAt ℝ (fun s => u (s,x)) (ν⁻¹*t)) :
    navierStokesResidual (rescale ν⁻¹ ν⁻¹ u) (rescale (ν⁻¹^2) ν⁻¹ p) t x =
      ν⁻¹^2 • Source.residual ν u p (ν⁻¹*t) x := by
  rw [navierStokesResidual,rescale_temporalDerivative _ _ _ _ _ hd,
    rescale_advection,rescale_laplacian,rescale_gradient]
  have hcoef : ν⁻¹^2*ν = ν⁻¹ := by field_simp
  simp only [Source.residual,smul_add,smul_sub,smul_smul]
  rw [hcoef]
  simp only [pow_two]

theorem normalized_time_mem_Icc {ν b t : ℝ} (hν : 0 < ν)
    (ht : t ∈ Icc (0 : ℝ) (ν*b)) : ν⁻¹*t ∈ Icc (0 : ℝ) b := by
  refine ⟨mul_nonneg (inv_nonneg.mpr hν.le) ht.1,?_⟩
  have hh := mul_le_mul_of_nonneg_left ht.2 (inv_nonneg.mpr hν.le)
  simpa only [← mul_assoc,inv_mul_cancel₀ hν.ne',one_mul] using hh

theorem normalized_time_mem_Ioo {ν b t : ℝ} (hν : 0 < ν)
    (ht : t ∈ Ioo (0 : ℝ) (ν*b)) : ν⁻¹*t ∈ Ioo (0 : ℝ) b := by
  refine ⟨mul_pos (inv_pos.mpr hν) ht.1,?_⟩
  have hh := mul_lt_mul_of_pos_left ht.2 (inv_pos.mpr hν)
  simpa only [← mul_assoc,inv_mul_cancel₀ hν.ne',one_mul] using hh

theorem normalized_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ν b : ℝ} (hν : 0 < ν) {f : SpaceTime → E}
    (hf : ContDiffOn ℝ ∞ f (PeriodicUniqueness.slab 0 b)) (a : ℝ) :
    ContDiffOn ℝ ∞ (rescale a ν⁻¹ f) (PeriodicUniqueness.slab 0 (ν*b)) := by
  apply (hf.comp ((contDiff_fst.const_smul ν⁻¹).prodMk contDiff_snd).contDiffOn ?_).const_smul a
  intro z hz
  exact ⟨normalized_time_mem_Icc hν hz.1,mem_univ _⟩

theorem normalized_periodic {E : Type*} [SMul ℝ E] {ν b : ℝ} (hν : 0 < ν)
    {f : SpaceTime → E} (hf : UnitSpatialPeriodsOn (Icc (0 : ℝ) b) f) (a : ℝ) :
    UnitSpatialPeriodsOn (Icc (0 : ℝ) (ν*b)) (rescale a ν⁻¹ f) := by
  intro t ht x i
  exact congrArg (fun v => a • v) (hf _ (normalized_time_mem_Icc hν ht) x i)

/-- Classical periodic uniqueness for every positive viscosity, obtained by
applying the existing viscosity-one theorem to normalized fields. -/
theorem classical_uniqueness_on_Icc {ν b : ℝ} (hν : 0 < ν)
    {u v f : VelocityField} {p q : PressureField}
    (hu : ContDiffOn ℝ ∞ u (PeriodicUniqueness.slab 0 b))
    (hv : ContDiffOn ℝ ∞ v (PeriodicUniqueness.slab 0 b))
    (hp : ContDiffOn ℝ ∞ p (PeriodicUniqueness.slab 0 b))
    (hq : ContDiffOn ℝ ∞ q (PeriodicUniqueness.slab 0 b))
    (hpu : UnitSpatialPeriodsOn (Icc (0 : ℝ) b) u)
    (hpv : UnitSpatialPeriodsOn (Icc (0 : ℝ) b) v)
    (hpp : UnitSpatialPeriodsOn (Icc (0 : ℝ) b) p)
    (hpq : UnitSpatialPeriodsOn (Icc (0 : ℝ) b) q)
    (hdu : ∀ t ∈ Ioo (0 : ℝ) b, ∀ x, spatialDivergence u t x = 0)
    (hdv : ∀ t ∈ Ioo (0 : ℝ) b, ∀ x, spatialDivergence v t x = 0)
    (hNSu : ∀ t ∈ Ioo (0 : ℝ) b, ∀ x, Source.residual ν u p t x = f (t,x))
    (hNSv : ∀ t ∈ Ioo (0 : ℝ) b, ∀ x, Source.residual ν v q t x = f (t,x))
    (hinitial : ∀ x, u (0,x) = v (0,x)) :
    ∀ t ∈ Icc (0 : ℝ) b, ∀ x, u (t,x) = v (t,x) := by
  have hEq := NavierStokes.PeriodicUniqueness.classical_uniqueness_on_Icc
    (normalized_smooth hν hu ν⁻¹) (normalized_smooth hν hv ν⁻¹)
    (normalized_smooth hν hp (ν⁻¹^2)) (normalized_smooth hν hq (ν⁻¹^2))
    (normalized_periodic hν hpu ν⁻¹) (normalized_periodic hν hpv ν⁻¹)
    (normalized_periodic hν hpp (ν⁻¹^2)) (normalized_periodic hν hpq (ν⁻¹^2))
    (f := rescale (ν⁻¹^2) ν⁻¹ f)
    (by
      intro t ht x
      rw [rescale_divergence,hdu _ (normalized_time_mem_Ioo hν ht) x,mul_zero])
    (by
      intro t ht x
      rw [rescale_divergence,hdv _ (normalized_time_mem_Ioo hν ht) x,mul_zero])
    (by
      intro t ht x
      rw [normalized_residual hν u p t x
        (NavierStokes.PeriodicUniqueness.time_differentiable_at_interior hu
          (normalized_time_mem_Ioo hν ht) x),hNSu _ (normalized_time_mem_Ioo hν ht) x]
      rfl)
    (by
      intro t ht x
      rw [normalized_residual hν v q t x
        (NavierStokes.PeriodicUniqueness.time_differentiable_at_interior hv
          (normalized_time_mem_Ioo hν ht) x),hNSv _ (normalized_time_mem_Ioo hν ht) x]
      rfl)
    (by intro x; simp only [rescale,mul_zero,hinitial x])
  intro t ht x
  have ht' : ν*t ∈ Icc (0 : ℝ) (ν*b) :=
    ⟨mul_nonneg hν.le ht.1,mul_le_mul_of_nonneg_left ht.2 hν.le⟩
  have he := congrArg (fun y : Space => ν • y) (hEq (ν*t) ht' x)
  simpa [rescale,smul_smul,← mul_assoc,hν.ne'] using he


/-- Any classical solution with the same force and initial datum agrees with
the inserted periodic trajectory on every time strictly before T. -/
theorem eq_before_terminal {ν r T τ S : ℝ} (hν : 0 < ν) (hτ : 0 ≤ τ) (hTS : T ≤ S)
    {v g U F W : VelocityField} {q P R : PressureField}
    (h : PeriodicInsertion.Properties ν r T τ v q g U F P)
    (hW : ContDiffOn ℝ ∞ W (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    (hR : ContDiffOn ℝ ∞ R (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    (hWper : UnitSpatialPeriodsOn (Ico (0 : ℝ) S) W)
    (hRper : UnitSpatialPeriodsOn (Ico (0 : ℝ) S) R)
    (hWdiv : ∀ t ∈ Ioo (0 : ℝ) S, ∀ x, spatialDivergence W t x = 0)
    (hWNS : ∀ t ∈ Ioo (0 : ℝ) S, ∀ x, Source.residual ν W R t x = g (t,x)+F (t,x))
    (hW0 : ∀ x, W (0,x) = v (0,x)) :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, U (t,x) = W (t,x) := by
  intro t ht x
  have hsubU : NavierStokes.PeriodicUniqueness.slab 0 t ⊆
      Ico (0 : ℝ) T ×ˢ (univ : Set Space) :=
    fun z hz => ⟨⟨hz.1.1,hz.1.2.trans_lt ht.2⟩,hz.2⟩
  have hsubW : NavierStokes.PeriodicUniqueness.slab 0 t ⊆
      Ico (0 : ℝ) S ×ˢ (univ : Set Space) :=
    fun z hz => ⟨⟨hz.1.1,(hz.1.2.trans_lt ht.2).trans_le hTS⟩,hz.2⟩
  have he := classical_uniqueness_on_Icc hν
    (h.velocity_smooth.mono hsubU) (hW.mono hsubW)
    (h.pressure_smooth.mono hsubU) (hR.mono hsubW)
    (fun s hs y i => h.velocity_periodic s ⟨hs.1,hs.2.trans_lt ht.2⟩ y i)
    (fun s hs y i => hWper s ⟨hs.1,(hs.2.trans_lt ht.2).trans_le hTS⟩ y i)
    (fun s hs y i => h.pressure_periodic s ⟨hs.1,hs.2.trans_lt ht.2⟩ y i)
    (fun s hs y i => hRper s ⟨hs.1,(hs.2.trans_lt ht.2).trans_le hTS⟩ y i)
    (fun s hs y => h.divergence_free s ⟨hs.1.le,hs.2.trans ht.2⟩ y)
    (fun s hs y => hWdiv s ⟨hs.1,(hs.2.trans ht.2).trans_le hTS⟩ y)
    (fun s hs y => h.equation s ⟨hs.1,hs.2.trans ht.2⟩ y)
    (fun s hs y => hWNS s ⟨hs.1,(hs.2.trans ht.2).trans_le hTS⟩ y)
    (fun y => ((h.history 0 hτ y).1).trans (hW0 y).symm)
    (f := fun z => g z+F z)
  exact he t ⟨ht.1.le,le_rfl⟩ x

/-- The localized blow-up rules out every later classical periodic solution
with the same initial datum and force. This is an actual nonexistence result;
no unique maximal evolution or local-existence axiom is assumed. -/
theorem no_later_classical_solution {ν r T τ S : ℝ}
    (hν : 0 < ν) (hτ : 0 ≤ τ) (hTS : T < S)
    {v g U F W : VelocityField} {q P R : PressureField}
    (h : PeriodicInsertion.Properties ν r T τ v q g U F P)
    (hW : ContDiffOn ℝ ∞ W (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    (hR : ContDiffOn ℝ ∞ R (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    (hWper : UnitSpatialPeriodsOn (Ico (0 : ℝ) S) W)
    (hRper : UnitSpatialPeriodsOn (Ico (0 : ℝ) S) R)
    (hWdiv : ∀ t ∈ Ioo (0 : ℝ) S, ∀ x, spatialDivergence W t x = 0)
    (hWNS : ∀ t ∈ Ioo (0 : ℝ) S, ∀ x, Source.residual ν W R t x = g (t,x)+F (t,x))
    (hW0 : ∀ x, W (0,x) = v (0,x)) : False := by
  have he := eq_before_terminal hν hτ hTS.le h hW hR hWper hRper hWdiv hWNS hW0
  have hc : ContinuousOn W (Icc (0 : ℝ) T ×ˢ Metric.closedBall (0 : Space) r) :=
    hW.continuousOn.mono (fun z hz => ⟨⟨hz.1.1,hz.1.2.trans_lt hTS⟩,mem_univ _⟩)
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : Space) r)).exists_bound_of_continuousOn hc
  obtain ⟨t,x,ht,hx,_,hbig⟩ := h.local_speed_unbounded (max C 0+1) (by positivity) 1 zero_lt_one
  have hb := hC (t,x) ⟨⟨ht.1.le,ht.2.le⟩,hx⟩
  rw [← he t ht x] at hb
  have hmax := le_max_left C 0
  linarith

end NSFormalization.Paper1.PeriodicUniqueness
