import NSFormalization.Source.RieszBallMass
import NSFormalization.Source.CenteredMaximalL2

/-! # Actual full unnormalized Riesz potential from near and far estimates -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NSFormalization.RieszPotentialAssembly
abbrev Space := NSFormalization.RieszPotentialTail.Space
open NSFormalization.CenteredMaximal

/-- Reflection followed by translation identifies the actual ball masses. -/
theorem translated_ballMass {H : Space → ℝ≥0∞} (hH : Measurable H) (x : Space) (r : ℝ) :
    (∫⁻ y in Metric.ball (0 : Space) r, H (x-y)) = ∫⁻ z in Metric.ball x r, H z := by
  have hs : (fun y : Space => x-y) ⁻¹' Metric.ball x r = Metric.ball (0 : Space) r := by
    ext y
    simp [Metric.mem_ball, dist_eq_norm]
  rw [← hs]
  exact (volume.measurePreserving_sub_left x).setLIntegral_comp_preimage measurableSet_ball hH

/-- The actual norm density used in the maximal function. -/
def normDensity (g : Space → ℂ) (z : Space) : ℝ≥0∞ := ENNReal.ofReal ‖g z‖

/-- Actual extended nonnegative potential, defined before any real conversion. -/
def potential (a : ℝ) (g : Space → ℂ) (x : Space) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (‖y‖ ^ (a-3) * ‖g (x-y)‖)

theorem translated_ballMass_bound {g : Space → ℂ} (hg : Measurable g) (x : Space)
    (hx : centeredMaximal (normDensity g) x < ⊤) {r : ℝ} (hr : 0 < r) :
    (∫⁻ y in Metric.ball (0 : Space) r, ENNReal.ofReal ‖g (x-y)‖) ≤
      ENNReal.ofReal ((centeredMaximal (normDensity g) x).toReal * (4*Real.pi/3) * r^3) := by
  rw [translated_ballMass hg.norm.ennreal_ofReal]
  have hb := ballMass_le (normDensity g) hr x
  change ballMass (normDensity g) r x ≤ _
  calc
    _ ≤ centeredMaximal (normDensity g) x * ballVolume r := hb
    _ = _ := by
      rw [← ENNReal.ofReal_toReal hx.ne, ballVolume, EuclideanSpace.volume_ball_fin_three,
        ← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_mul (by positivity : 0 ≤ r^3),
        ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
      congr 1
      rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
      ring

/-- Genuine near integrability at finite-maximal points, including zero maximal values. -/
theorem near_integrable {a R : ℝ} (ha : 0 < a) (ha3 : a < 3) (hR : 0 < R)
    {g : Space → ℂ} (hg : Measurable g) (x : Space)
    (hx : centeredMaximal (normDensity g) x < ⊤) :
    IntegrableOn (fun y => ‖y‖ ^ (a-3) * ‖g (x-y)‖) (Metric.ball (0 : Space) R) := by
  apply NSFormalization.RieszBallMass.nearField_integrable ha ha3 hR ENNReal.toReal_nonneg
    (hg.norm.comp (measurable_const.sub measurable_id)) (fun _ => norm_nonneg _)
  intro r hr _
  exact translated_ballMass_bound hg x hx hr

theorem near_integral_bound {a R : ℝ} (ha : 0 < a) (ha3 : a < 3) (hR : 0 < R)
    {g : Space → ℂ} (hg : Measurable g) (x : Space)
    (hx : centeredMaximal (normDensity g) x < ⊤) :
    (∫ y in Metric.ball (0 : Space) R, ‖y‖ ^ (a-3) * ‖g (x-y)‖) ≤
      (4*Real.pi/a) * (centeredMaximal (normDensity g) x).toReal * R^a := by
  apply NSFormalization.RieszBallMass.nearField_integral_bound ha ha3 hR ENNReal.toReal_nonneg
    (hg.norm.comp (measurable_const.sub measurable_id)) (fun _ => norm_nonneg _)
  intro r hr _
  exact translated_ballMass_bound hg x hx hr

private theorem ball_compl (R : ℝ) :
    (Metric.ball (0 : Space) R)ᶜ = {y : Space | R ≤ ‖y‖} := by
  ext y
  simp [Metric.mem_ball, not_lt]

/-- The full kernel product is integrable before its ordinary integral is used. -/
theorem full_integrable {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2)
    {g : Space → ℂ} (hg : Measurable g) (h2 : MemLp g 2 volume) (x : Space)
    (hx : centeredMaximal (normDensity g) x < ⊤) :
    Integrable (fun y => ‖y‖ ^ (a-3) * ‖g (x-y)‖) := by
  have hn := near_integrable ha (by linarith : a < 3) (by norm_num : (0:ℝ)<1) hg x hx
  have ht := NSFormalization.RieszPotentialTail.closedTail_integrable ha3 (by norm_num : (0:ℝ)<1) h2 x
  rw [← ball_compl] at ht
  simpa using hn.union ht

/-- Exact all-radius bound for the same actual full kernel and field. -/
theorem full_integral_bound {a R : ℝ} (ha : 0 < a) (ha3 : a < 3/2) (hR : 0 < R)
    {g : Space → ℂ} (hg : Measurable g) (h2 : MemLp g 2 volume) (x : Space)
    (hx : centeredMaximal (normDensity g) x < ⊤) :
    (∫ y, ‖y‖ ^ (a-3) * ‖g (x-y)‖) ≤
      (4*Real.pi/a) * (centeredMaximal (normDensity g) x).toReal * R^a +
      Real.sqrt (4*Real.pi/(3-2*a)) * (eLpNorm g 2 volume).toReal * R^(a-3/2) := by
  rw [← integral_add_compl measurableSet_ball (full_integrable ha ha3 hg h2 x hx), ball_compl]
  exact add_le_add (near_integral_bound ha (by linarith) hR hg x hx)
    (NSFormalization.RieszPotentialTail.closedTail_bound ha3 hR h2 x)

theorem measurable_potential (a : ℝ) {g : Space → ℂ} (hg : Measurable g) :
    Measurable (potential a g) := by
  apply Measurable.lintegral_prod_right
  change Measurable (fun p : Space × Space => ENNReal.ofReal (‖p.2‖ ^ (a-3) * ‖g (p.1-p.2)‖))
  fun_prop

/-- Full integrability holds almost everywhere for L2 data, with no L1 premise. -/
theorem ae_full_integrable {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2)
    {g : Space → ℂ} (hg : Measurable g) (h2 : MemLp g 2 volume) :
    ∀ᵐ x : Space ∂volume, Integrable (fun y => ‖y‖ ^ (a-3) * ‖g (x-y)‖) := by
  filter_upwards [centeredMaximal_ae_lt_top hg.norm (fun _ => norm_nonneg _) h2.norm] with x hx
  exact full_integrable ha ha3 hg h2 x hx

theorem ae_potential_lt_top {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2)
    {g : Space → ℂ} (hg : Measurable g) (h2 : MemLp g 2 volume) :
    ∀ᵐ x : Space ∂volume, potential a g x < ⊤ := by
  filter_upwards [ae_full_integrable ha ha3 hg h2] with x hx
  exact hx.lintegral_lt_top

/-- The real representative of the actual potential; its a.e. finiteness is proved above. -/
def realPotential (a : ℝ) (g : Space → ℂ) (x : Space) : ℝ := (potential a g x).toReal

theorem measurable_realPotential (a : ℝ) {g : Space → ℂ} (hg : Measurable g) :
    Measurable (realPotential a g) := (measurable_potential a hg).ennreal_toReal

theorem realPotential_eq_integral {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2)
    {g : Space → ℂ} (hg : Measurable g) (h2 : MemLp g 2 volume) (x : Space)
    (hx : centeredMaximal (normDensity g) x < ⊤) :
    realPotential a g x = ∫ y, ‖y‖ ^ (a-3) * ‖g (x-y)‖ := by
  symm
  exact integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun y => mul_nonneg (Real.rpow_nonneg (norm_nonneg y) _) (norm_nonneg _)))
    (full_integrable ha ha3 hg h2 x hx).aestronglyMeasurable

/-- The extended actual potential satisfies the same all-radius estimate. -/
theorem potential_bound {a R : ℝ} (ha : 0 < a) (ha3 : a < 3/2) (hR : 0 < R)
    {g : Space → ℂ} (hg : Measurable g) (h2 : MemLp g 2 volume) (x : Space)
    (hx : centeredMaximal (normDensity g) x < ⊤) :
    potential a g x ≤ ENNReal.ofReal
      ((4*Real.pi/a) * (centeredMaximal (normDensity g) x).toReal * R^a +
        Real.sqrt (4*Real.pi/(3-2*a)) * (eLpNorm g 2 volume).toReal * R^(a-3/2)) := by
  rw [potential, ← ofReal_integral_eq_lintegral_ofReal (full_integrable ha ha3 hg h2 x hx)
    (Filter.Eventually.of_forall (fun y => mul_nonneg (Real.rpow_nonneg (norm_nonneg y) _) (norm_nonneg _)))]
  exact ENNReal.ofReal_le_ofReal (full_integral_bound ha ha3 hR hg h2 x hx)

theorem realPotential_bound {a R : ℝ} (ha : 0 < a) (ha3 : a < 3/2) (hR : 0 < R)
    {g : Space → ℂ} (hg : Measurable g) (h2 : MemLp g 2 volume) (x : Space)
    (hx : centeredMaximal (normDensity g) x < ⊤) :
    realPotential a g x ≤
      (4*Real.pi/a) * (centeredMaximal (normDensity g) x).toReal * R^a +
      Real.sqrt (4*Real.pi/(3-2*a)) * (eLpNorm g 2 volume).toReal * R^(a-3/2) := by
  rw [realPotential_eq_integral ha ha3 hg h2 x hx]
  exact full_integral_bound ha ha3 hR hg h2 x hx

end NSFormalization.RieszPotentialAssembly
