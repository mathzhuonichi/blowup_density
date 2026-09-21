import NSFormalization.Source.RieszFrequencyCutoffs
import NSFormalization.Source.SingularMultiplier

/-! Continuous multiplication by the actual singular symbol |xi|^(-a) from
L2 to tempered distributions, with exact Schwartz pairing. -/
noncomputable section
namespace NSFormalization.RieszSingularMultiplier
open MeasureTheory
open NSFormalization.RieszFrequencyCutoffs NSFormalization.SingularMultiplier
open scoped ENNReal SchwartzMap
abbrev Space := EuclideanSpace ℝ (Fin 3)

def lowDatum (a : ℝ) (ha : a < 3/2) : Data 2 := (low_memLp ha).toLp (low a)
def highDatum (a : ℝ) (ha : 0 ≤ a) : Data ⊤ := (high_memLp ha).toLp (high a)

/-- No smoothness assumption is imposed on the singular symbol at zero. -/
def multiplier (a : ℝ) (ha : 0 ≤ a) (ha3 : a < 3/2) : Data 2 →L[ℂ] 𝓢'(Space, ℂ) :=
  distribution (lowDatum a ha3) (highDatum a ha)

theorem low_pairing_integrable (a : ℝ) (ha3 : a < 3/2) (h : Data 2)
    (φ : 𝓢(Space, ℂ)) : Integrable (fun x => φ x * (low a x * h x)) := by
  have H := memLp_one_iff_integrable.mp
    ((φ.memLp ⊤).mul' (Lp.memLp (lowProduct (lowDatum a ha3) h)))
  apply H.congr
  filter_upwards [lowProduct_ae (lowDatum a ha3) h, (low_memLp ha3).coeFn_toLp] with x hx hl
  change lowProduct (lowDatum a ha3) h x * φ x = _
  rw [mul_comm _ (φ x)]
  rw [hx]
  change φ x * ((low_memLp ha3).toLp (low a) x * h x) = _
  rw [hl]

theorem high_pairing_integrable (a : ℝ) (ha : 0 ≤ a) (h : Data 2)
    (φ : 𝓢(Space, ℂ)) : Integrable (fun x => φ x * (high a x * h x)) := by
  have H := memLp_one_iff_integrable.mp
    ((φ.memLp 2).mul' (Lp.memLp (highProduct (highDatum a ha) h)))
  apply H.congr
  filter_upwards [highProduct_ae (highDatum a ha) h, (high_memLp ha).coeFn_toLp] with x hx hh
  change highProduct (highDatum a ha) h x * φ x = _
  rw [mul_comm _ (φ x)]
  rw [hx]
  change φ x * ((high_memLp ha).toLp (high a) x * h x) = _
  rw [hh]

theorem pairing_integrable (a : ℝ) (ha : 0 ≤ a) (ha3 : a < 3/2) (h : Data 2)
    (φ : 𝓢(Space, ℂ)) : Integrable (fun x => φ x * (symbol a x * h x)) := by
  have H := (low_pairing_integrable a ha3 h φ).add (high_pairing_integrable a ha h φ)
  apply H.congr
  filter_upwards with x
  change φ x * (low a x * h x) + φ x * (high a x * h x) = _
  rw [← mul_add, ← add_mul, low_add_high]

/-- The actual singular-symbol pairing for every complete L2 datum. -/
theorem multiplier_pairing (a : ℝ) (ha : 0 ≤ a) (ha3 : a < 3/2) (h : Data 2)
    (φ : 𝓢(Space, ℂ)) :
    multiplier a ha ha3 h φ = ∫ x : Space, φ x * (symbol a x * h x) := by
  rw [multiplier, distribution_pairing]
  have hl : (∫ x : Space, φ x * (lowDatum a ha3 x * h x)) =
      ∫ x : Space, φ x * (low a x * h x) := by
    apply integral_congr_ae
    filter_upwards [(low_memLp ha3).coeFn_toLp] with x hx
    change φ x * ((low_memLp ha3).toLp (low a) x * h x) = _
    rw [hx]
  have hh : (∫ x : Space, φ x * (highDatum a ha x * h x)) =
      ∫ x : Space, φ x * (high a x * h x) := by
    apply integral_congr_ae
    filter_upwards [(high_memLp ha).coeFn_toLp] with x hx
    change φ x * ((high_memLp ha).toLp (high a) x * h x) = _
    rw [hx]
  rw [hl, hh, ← integral_add (low_pairing_integrable a ha3 h φ) (high_pairing_integrable a ha h φ)]
  apply integral_congr_ae
  filter_upwards with x
  rw [← mul_add, ← add_mul, low_add_high]

/-- The cycles-frequency normalization of the singular symbol. Physical
convolution identification is a separate theorem. -/
def normalizedMultiplier (a : ℝ) (ha : 0 ≤ a) (ha3 : a < 3/2) : Data 2 →L[ℂ] 𝓢'(Space, ℂ) :=
  Complex.ofReal (Real.rpow (2 * Real.pi) (-a)) • multiplier a ha ha3

theorem normalizedMultiplier_apply (a : ℝ) (ha : 0 ≤ a) (ha3 : a < 3/2)
    (h : Data 2) :
    normalizedMultiplier a ha ha3 h =
      Complex.ofReal (Real.rpow (2 * Real.pi) (-a)) • multiplier a ha ha3 h := rfl

/-- Exact normalized Schwartz pairing, without a physical Fourier claim. -/
theorem normalizedMultiplier_pairing (a : ℝ) (ha : 0 ≤ a) (ha3 : a < 3/2)
    (h : Data 2) (φ : 𝓢(Space, ℂ)) :
    normalizedMultiplier a ha ha3 h φ = ∫ x : Space,
      φ x * (Complex.ofReal (Real.rpow (2 * Real.pi) (-a)) * symbol a x * h x) := by
  change Complex.ofReal (Real.rpow (2 * Real.pi) (-a)) * multiplier a ha ha3 h φ = _
  rw [multiplier_pairing, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  ring

end NSFormalization.RieszSingularMultiplier
