import NSFormalization.Source.RieszHedberg

/-! # Actual unnormalized Riesz potential from L2 to Lp

No normalized Fourier-kernel identity or Sobolev embedding is asserted here.
-/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NSFormalization.RieszPotentialLp
open NSFormalization.RieszPotentialAssembly NSFormalization.RieszHedberg NSFormalization.CenteredMaximal
abbrev Space := NSFormalization.RieszPotentialAssembly.Space

def targetExponent (a : ℝ) : ℝ := 6/(3-2*a)
def potentialConstant (a : ℝ) : ℝ := 4*Real.pi/a + Real.sqrt (4*Real.pi/(3-2*a))

theorem targetExponent_pos {a : ℝ} (ha3 : a < 3/2) : 0 < targetExponent a := by
  unfold targetExponent
  apply div_pos (by norm_num)
  linarith

private theorem constant_algebra {a L : ℝ} (ha : 0 < a) (ha3 : a < 3/2) (hL : 0 ≤ L) :
    (potentialConstant a * L^(2*a/3)) * (Real.sqrt 512 * L)^(1-2*a/3) =
      potentialConstant a * (512:ℝ)^(1/targetExponent a) * L := by
  rw [Real.mul_rpow (Real.sqrt_nonneg _) hL, Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 512)]
  have he : (1/(2:ℝ))*(1-2*a/3) = 1/targetExponent a := by unfold targetExponent; field_simp; ring
  rw [he]
  have hl : L^(2*a/3) * L^(1-2*a/3) = L := by
    rw [← Real.rpow_add_of_nonneg hL (by linarith) (by linarith), show 2*a/3+(1-2*a/3)=1 by ring, Real.rpow_one]
  calc
    _ = potentialConstant a * (512:ℝ)^(1/targetExponent a) * (L^(2*a/3) * L^(1-2*a/3)) := by ring
    _ = _ := by rw [hl]

/-- Quantitative extended norm bound for measurable L2 input. -/
theorem eLpNorm_realPotential_le_measurable {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2)
    {g : Space → ℂ} (hg : Measurable g) (h2 : MemLp g 2 volume) :
    eLpNorm (realPotential a g) (ENNReal.ofReal (targetExponent a)) volume ≤
      ENNReal.ofReal (potentialConstant a * (512:ℝ)^(1/targetExponent a) * (eLpNorm g 2 volume).toReal) := by
  let L := (eLpNorm g 2 volume).toReal
  let F : Space → ℝ := fun x => (centeredMaximal (normDensity g) x).toReal
  have hθ : 0 < 1-2*a/3 := by linarith
  have hβ : 0 < 2*a/3 := by linarith
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  have hA : 0 ≤ potentialConstant a := by unfold potentialConstant; positivity
  have hF2 : MemLp F 2 volume := centeredMaximal_toReal_memLp hg.norm (fun _ => norm_nonneg _) h2.norm
  have hFn : (eLpNorm F 2 volume).toReal ≤ Real.sqrt 512 * L := by
    have hb := centeredMaximal_toLp_norm_le hg.norm (fun _ => norm_nonneg _) h2.norm
    simp only [Lp.norm_toLp, eLpNorm_norm] at hb
    convert hb using 1
    rfl
  have hFn' : eLpNorm F 2 volume ≤ ENNReal.ofReal (Real.sqrt 512 * L) := by
    rw [← ENNReal.ofReal_toReal hF2.2.ne]
    exact ENNReal.ofReal_le_ofReal hFn
  have hp : ENNReal.ofReal (targetExponent a) * ENNReal.ofReal (1-2*a/3) = 2 := by
    rw [← ENNReal.ofReal_mul (targetExponent_pos ha3).le]
    have he : targetExponent a * (1-2*a/3) = 2 := by
      unfold targetExponent
      field_simp [show 3-2*a ≠ 0 by linarith]
      ring
    rw [he]
    norm_num
  have hmajor : ∀ᵐ x : Space ∂volume,
      ‖realPotential a g x‖ ≤ (potentialConstant a * L^(2*a/3)) * ‖F x‖^(1-2*a/3) := by
    filter_upwards [ae_realPotential_hedberg ha ha3 hg h2] with x hx
    simp only [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ realPotential a g x from ENNReal.toReal_nonneg),
      abs_of_nonneg (show 0 ≤ F x from ENNReal.toReal_nonneg)]
    dsimp [potentialConstant, L, F]
    nlinarith [hx]
  calc
    _ ≤ eLpNorm (fun x => (potentialConstant a * L^(2*a/3)) * ‖F x‖^(1-2*a/3))
        (ENNReal.ofReal (targetExponent a)) volume := eLpNorm_mono_ae_real hmajor
    _ = ENNReal.ofReal (potentialConstant a * L^(2*a/3)) *
        eLpNorm F 2 volume ^ (1-2*a/3) := by
      rw [show (fun x => (potentialConstant a * L^(2*a/3)) * ‖F x‖^(1-2*a/3)) =
        (potentialConstant a * L^(2*a/3)) • (fun x => ‖F x‖^(1-2*a/3)) by rfl,
        eLpNorm_const_smul, eLpNorm_norm_rpow F hθ, hp]
      rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hA (Real.rpow_nonneg hL _))]
    _ ≤ ENNReal.ofReal (potentialConstant a * L^(2*a/3)) *
        ENNReal.ofReal (Real.sqrt 512 * L) ^ (1-2*a/3) := by gcongr
    _ = _ := by
      rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (Real.sqrt_nonneg 512) hL) hθ.le,
        ← ENNReal.ofReal_mul (mul_nonneg hA (Real.rpow_nonneg hL _)), constant_algebra ha ha3 hL]

/-- Actual Lp membership follows from the finite quantitative bound. -/
theorem realPotential_memLp_measurable {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2)
    {g : Space → ℂ} (hg : Measurable g) (h2 : MemLp g 2 volume) :
    MemLp (realPotential a g) (ENNReal.ofReal (targetExponent a)) volume :=
  ⟨(measurable_realPotential a hg).aestronglyMeasurable,
    lt_of_le_of_lt (eLpNorm_realPotential_le_measurable ha ha3 hg h2) ENNReal.ofReal_lt_top⟩

/-- Global input AE equality preserves the actual extended potential at every point. -/
theorem potential_congr_ae {g g' : Space → ℂ} (hgg : g =ᵐ[volume] g') (a : ℝ) (x : Space) :
    potential a g x = potential a g' x := by
  unfold potential
  apply lintegral_congr_ae
  filter_upwards [(volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae_eq_comp hgg] with y hy
  change g (x-y) = g' (x-y) at hy
  rw [hy]

theorem realPotential_congr_ae {g g' : Space → ℂ} (hgg : g =ᵐ[volume] g') (a : ℝ) :
    realPotential a g = realPotential a g' := by
  funext x
  exact congrArg ENNReal.toReal (potential_congr_ae hgg a x)

/-- The full quantitative bound requires only actual L2 membership of the input. -/
theorem eLpNorm_realPotential_le {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2)
    {g : Space → ℂ} (h2 : MemLp g 2 volume) :
    eLpNorm (realPotential a g) (ENNReal.ofReal (targetExponent a)) volume ≤
      ENNReal.ofReal (potentialConstant a * (512:ℝ)^(1/targetExponent a) * (eLpNorm g 2 volume).toReal) := by
  let g' := h2.1.mk g
  have he : g =ᵐ[volume] g' := h2.1.ae_eq_mk
  rw [realPotential_congr_ae he a, eLpNorm_congr_ae he]
  exact eLpNorm_realPotential_le_measurable ha ha3 h2.1.measurable_mk (h2.ae_eq he)

/-- Actual Lp membership, with no separate measurability or L1 premise on g. -/
theorem realPotential_memLp {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2)
    {g : Space → ℂ} (h2 : MemLp g 2 volume) :
    MemLp (realPotential a g) (ENNReal.ofReal (targetExponent a)) volume := by
  let g' := h2.1.mk g
  have he : g =ᵐ[volume] g' := h2.1.ae_eq_mk
  rw [realPotential_congr_ae he a]
  exact realPotential_memLp_measurable ha ha3 h2.1.measurable_mk (h2.ae_eq he)

/-- Finite real norm of the actual positive potential with the reviewed constant. -/
theorem realPotential_norm_le {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2)
    {g : Space → ℂ} (h2 : MemLp g 2 volume) :
    (eLpNorm (realPotential a g) (ENNReal.ofReal (targetExponent a)) volume).toReal ≤
      potentialConstant a * (512:ℝ)^(1/targetExponent a) * (eLpNorm g 2 volume).toReal := by
  have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top (eLpNorm_realPotential_le ha ha3 h2)
  rw [ENNReal.toReal_ofReal (by unfold potentialConstant; positivity)] at hb
  exact hb

/-- Measurability of the actual extended potential for any L2 representative. -/
theorem measurable_potential_of_memLp (a : ℝ) {g : Space → ℂ} (h2 : MemLp g 2 volume) :
    Measurable (potential a g) := by
  let g' := h2.1.mk g
  have he : g =ᵐ[volume] g' := h2.1.ae_eq_mk
  have hp : potential a g = potential a g' := funext (potential_congr_ae he a)
  rw [hp]
  exact measurable_potential a h2.1.measurable_mk

/-- The actual extended potential is finite almost everywhere for any L2 representative. -/
theorem ae_potential_lt_top_of_memLp {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2)
    {g : Space → ℂ} (h2 : MemLp g 2 volume) :
    ∀ᵐ x : Space ∂volume, potential a g x < ⊤ := by
  let g' := h2.1.mk g
  have he : g =ᵐ[volume] g' := h2.1.ae_eq_mk
  have hp : potential a g = potential a g' := funext (potential_congr_ae he a)
  rw [hp]
  exact ae_potential_lt_top ha ha3 h2.1.measurable_mk (h2.ae_eq he)

/-- Actual full-kernel integrability holds a.e. for every L2 representative. -/
theorem ae_full_integrable_of_memLp {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2)
    {g : Space → ℂ} (h2 : MemLp g 2 volume) :
    ∀ᵐ x : Space ∂volume, Integrable (fun y => ‖y‖^(a-3) * ‖g (x-y)‖) := by
  let g' := h2.1.mk g
  have he : g =ᵐ[volume] g' := h2.1.ae_eq_mk
  filter_upwards [ae_full_integrable ha ha3 h2.1.measurable_mk (h2.ae_eq he)] with x hx
  apply hx.congr
  filter_upwards [(volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae_eq_comp he] with y hy
  change g (x-y) = g' (x-y) at hy
  rw [hy]

end NSFormalization.RieszPotentialLp
