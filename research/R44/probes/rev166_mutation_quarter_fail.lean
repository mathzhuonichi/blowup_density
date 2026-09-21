import NSFormalization.Section4.R44.Pieces

open Set intervalIntegral MeasureTheory
open NSFormalization.Section4.R44

/- Expected failure: this substantively strengthens the main scalar theorem's
   conclusion from `Y ≤ theta * nu / 2` to `Y ≤ theta * nu / 4`. -/
example {T nu theta C₂ C₃ R : ℝ} {Y E' Z B : ℝ → ℝ}
    (hT : 0 ≤ T) (hnu : 0 < nu) (htheta : 0 < theta)
    (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hR : 0 ≤ R)
    (hsmall : C₃ * nu⁻¹ * R * Real.exp (C₂ * nu * T) < (theta * nu) ^ 2 / 4)
    (hY : Continuous Y) (hY0 : Y 0 = 0)
    (hYnonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ Y t)
    (hBsq : ContinuousOn (fun t => B t ^ 2) (Icc (0 : ℝ) T))
    (hBbound : ∀ t ∈ Icc (0 : ℝ) T, ∫ s in (0 : ℝ)..t, B s ^ 2 ≤ R)
    (hdE : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt (fun s => Y s ^ 2) (E' t) t)
    (hE'int : IntervalIntegrable E' volume 0 T)
    (henergy : ∀ t ∈ Ioo (0 : ℝ) T, Y t ≤ theta * nu →
      E' t + nu * Z t ^ 2 ≤ C₂ * nu * Y t ^ 2 + C₃ * nu⁻¹ * B t ^ 2) :
    ∀ t ∈ Icc (0 : ℝ) T, Y t ≤ theta * nu / 4 := by
  exact criticalSquaredNormBound_radius hT hnu htheta hC₂ hC₃ hR hsmall
    hY hY0 hYnonneg hBsq hBbound hdE hE'int henergy
