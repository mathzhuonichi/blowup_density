import NSFormalization.Paper1.PeriodicBridge
import NSFormalization.Paper1.SmoothL6Adapter

/-!
# A proved subcritical periodic bridge for compact packets

For a compact field supported strictly inside one fundamental cube, the
periodic cube `L⁶` norm is exactly its whole-space `L⁶` norm.  Consequently
OpenAI's whole-space homogeneous Sobolev inequality gives a genuine periodic
`H¹ → L⁶` estimate for such compact packets.  This is a subcritical endpoint;
it does not imply the missing uniform `H^(1/2) → L³` estimate for arbitrary
periodic fields.
-/

noncomputable section
namespace NSFormalization.Paper1.PeriodicCompactSobolevL6

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NavierStokes.PeriodicLocalization NavierStokes.PeriodicIntegration
open NSFormalization.Paper1.PeriodicBridge
open NavierStokesR3.Comparison
open scoped ContDiff ENNReal Topology

/-- The cube `Lᵖ` norm used for periodic fields, with the natural real-power
normalization. -/
def periodicLpNorm (p : ℕ) (f : Space → Space) : ℝ :=
  (cubeIntegral (fun x => ‖f x‖ ^ p)) ^ ((p : ℝ)⁻¹)

private theorem wholeLpNorm_eq_integral_six
    {f : Space → Space} (hf : MemLp f 6 (volume : Measure Space)) :
    comparisonLpNorm 6 f =
      (∫ x : Space, ‖f x‖ ^ (6 : ℕ)) ^ ((6 : ℝ)⁻¹) := by
  have heq := MemLp.eLpNorm_eq_integral_rpow_norm
    (p := (6 : ℝ≥0∞)) (by norm_num) (by norm_num) hf
  norm_num only [ENNReal.toReal_ofNat] at heq
  rw [comparisonLpNorm, heq, ENNReal.toReal_ofReal]
  · congr 1 <;> norm_num
  · positivity

private theorem wholeLpNorm_eq_integral_three
    {f : Space → Space} (hf : MemLp f 3 (volume : Measure Space)) :
    comparisonLpNorm 3 f =
      (∫ x : Space, ‖f x‖ ^ (3 : ℕ)) ^ ((3 : ℝ)⁻¹) := by
  have heq := MemLp.eLpNorm_eq_integral_rpow_norm
    (p := (3 : ℝ≥0∞)) (by norm_num) (by norm_num) hf
  norm_num only [ENNReal.toReal_ofNat] at heq
  rw [comparisonLpNorm, heq, ENNReal.toReal_ofReal]
  · congr 1 <;> norm_num
  · positivity

/-- Exact whole-space/cube `L³` identity after periodization. -/
theorem periodicLpNorm_three_periodize_eq
    {r : ℝ} {F : SpaceTime → Space} (hS : SupportedInCube r F)
    (hr : r < 1 / 2) {t : ℝ}
    (h3 : MemLp (fun x : Space => F (t, x)) 3 (volume : Measure Space)) :
    periodicLpNorm 3 (fun x => periodize F (t, x)) =
      comparisonLpNorm 3 (fun x : Space => F (t, x)) := by
  have hcoord : (fun x : Space => ‖periodize F (t, x)‖ ^ (3 : ℕ)) =
      (fun x : Space => periodize (fun z : SpaceTime => ‖F z‖ ^ (3 : ℕ)) (t, x)) := by
    have hp := periodize_comp hS hr (fun v : Space => ‖v‖ ^ (3 : ℕ)) (by simp)
    funext x
    exact congrFun hp (t, x)
  have hi' := h3.integrable_norm_rpow (by norm_num) (by norm_num)
  have hi : Integrable (fun x : Space => ‖F (t, x)‖ ^ (3 : ℕ)) volume := by
    convert hi' using 1
    all_goals norm_num
  rw [periodicLpNorm, hcoord, cubeIntegral_periodize hi]
  exact (wholeLpNorm_eq_integral_three h3).symm

/-- For compact packets, the periodic `L³` norm is controlled by the ordinary
whole-space `L²` and `H¹` endpoints through interpolation and the OpenAI
`H¹ → L⁶` estimate.  This remains a compact-support estimate and is not the
critical periodic `H^(1/2) → L³` theorem. -/
theorem periodicLpNorm_three_periodize_le
    {r : ℝ} {F : SpaceTime → Space} {t : ℝ}
    (hF : ContDiff ℝ 1 (fun x : Space => F (t, x)))
    (hS : SupportedInCube r F) (hr : r < 1 / 2)
    (hc : HasCompactSupport (fun x : Space => F (t, x))) :
    periodicLpNorm 3 (fun x => periodize F (t, x)) ≤
      comparisonLpNorm 2 (fun x : Space => F (t, x)) ^ (1 / 2 : ℝ) *
        ((eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2 : ℝ) *
          comparisonLpNorm 2 (fderiv ℝ (fun x : Space => F (t, x)))) ^ (1 / 2 : ℝ) := by
  let f : Space → Space := fun x => F (t, x)
  have hmem : MemLp f 2 volume := hF.continuous.memLp_of_hasCompactSupport hc
  have hDmem : MemLp (fderiv ℝ f) 2 volume :=
    (hF.continuous_fderiv (by norm_num)).memLp_of_hasCompactSupport (hc.fderiv ℝ)
  have h6 : MemLp f 6 volume :=
    NavierStokesR3.RieszTestOperators.smooth_memLp_six hF hmem hDmem
  have h3data := velocitySlice_memLp_three_interp
    (u := fun z => f z.2) (t := 0) (by simpa using hmem) (by simpa using h6)
  have h3 : MemLp f 3 volume := by simpa using h3data.1
  rw [periodicLpNorm_three_periodize_eq hS hr h3]
  calc
    comparisonLpNorm 3 f ≤ comparisonLpNorm 2 f ^ (1 / 2 : ℝ) *
        comparisonLpNorm 6 f ^ (1 / 2 : ℝ) := by simpa using h3data.2
    _ ≤ comparisonLpNorm 2 f ^ (1 / 2 : ℝ) *
        ((eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2 : ℝ) *
          comparisonLpNorm 2 (fderiv ℝ f)) ^ (1 / 2 : ℝ) := by
      have h6bound := NavierStokesR3.RieszTestOperators.smooth_eLpNorm_six_toReal_le
        hF hmem hDmem
      have h6nonneg : 0 ≤ comparisonLpNorm 6 f := by
        exact ENNReal.toReal_nonneg
      have hbase : comparisonLpNorm 6 f ^ (1 / 2 : ℝ) ≤
          ((eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2 : ℝ) *
            comparisonLpNorm 2 (fderiv ℝ f)) ^ (1 / 2 : ℝ) := by
        apply Real.rpow_le_rpow h6nonneg
        · simpa [comparisonLpNorm] using h6bound
        · norm_num
      have h2nonneg : 0 ≤ comparisonLpNorm 2 f := by
        exact ENNReal.toReal_nonneg
      exact mul_le_mul_of_nonneg_left hbase (Real.rpow_nonneg h2nonneg _)

/-- Exact whole-space/cube `L⁶` identity after periodization. -/
theorem periodicLpNorm_six_periodize_eq
    {r : ℝ} {F : SpaceTime → Space} (hS : SupportedInCube r F)
    (hr : r < 1 / 2) {t : ℝ}
    (h6 : MemLp (fun x : Space => F (t, x)) 6 (volume : Measure Space)) :
    periodicLpNorm 6 (fun x => periodize F (t, x)) =
      comparisonLpNorm 6 (fun x : Space => F (t, x)) := by
  let f : Space → Space := fun x => F (t, x)
  have hcoord : (fun x : Space => ‖periodize F (t, x)‖ ^ (6 : ℕ)) =
      (fun x : Space => periodize (fun z : SpaceTime => ‖F z‖ ^ (6 : ℕ)) (t, x)) := by
    have hp := periodize_comp hS hr (fun v : Space => ‖v‖ ^ (6 : ℕ)) (by simp)
    funext x
    exact congrFun hp (t, x)
  have hi' := h6.integrable_norm_rpow (by norm_num) (by norm_num)
  have hi : Integrable (fun x : Space => ‖F (t, x)‖ ^ (6 : ℕ)) volume := by
    convert hi' using 1
    all_goals norm_num
  rw [periodicLpNorm, hcoord, cubeIntegral_periodize hi]
  exact (wholeLpNorm_eq_integral_six h6).symm

/-- OpenAI's whole-space Sobolev estimate, transported to the periodic cube
for a compactly supported spatial slice. -/
theorem periodicLpNorm_six_periodize_le
    {r : ℝ} {F : SpaceTime → Space} {t : ℝ}
    (hF : ContDiff ℝ 1 (fun x : Space => F (t, x)))
    (hS : SupportedInCube r F) (hr : r < 1 / 2)
    (hc : HasCompactSupport (fun x : Space => F (t, x))) :
    periodicLpNorm 6 (fun x => periodize F (t, x)) ≤
      (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2 : ℝ) *
        comparisonLpNorm 2 (fderiv ℝ (fun x : Space => F (t, x))) := by
  let f : Space → Space := fun x => F (t, x)
  have hmem : MemLp f 2 volume :=
    hF.continuous.memLp_of_hasCompactSupport hc
  have hDmem : MemLp (fderiv ℝ f) 2 volume :=
    (hF.continuous_fderiv (by norm_num)).memLp_of_hasCompactSupport (hc.fderiv ℝ)
  have h6 : MemLp f 6 volume :=
    NavierStokesR3.RieszTestOperators.smooth_memLp_six hF hmem hDmem
  rw [periodicLpNorm_six_periodize_eq hS hr h6]
  exact NavierStokesR3.RieszTestOperators.smooth_eLpNorm_six_toReal_le hF hmem hDmem

end NSFormalization.Paper1.PeriodicCompactSobolevL6
