import NSFormalization.Paper1.ScalarEnergyAuxiliary

/-!
# Scalar continuation certificates

Thin wrappers exposing the proved scalar bootstrap and packet inequalities under
names used by the Paper 1 continuation layer.  No PDE or flow objects are
introduced.
-/
namespace NSFormalization.Paper1

/-- A continuous bootstrap estimate closes a subcritical continuation interval. -/
theorem continuation_certificate {T K ρ : ℝ} {y : ℝ → ℝ}
    (hy : Continuous y) (hy0 : y 0 ≤ ρ) (hρ : ρ < K)
    (himprove : ∀ t ∈ Set.Icc 0 T,
      (∀ x ∈ Set.Icc 0 t, y x ≤ K) → y t ≤ ρ) :
    ∀ t ∈ Set.Icc 0 T, y t ≤ ρ := by
  exact continuous_bootstrap hy hy0 hρ himprove

/-- The packet energy estimate in integral form, re-exported for continuation. -/
theorem continuation_packet_bound {T ν : ℝ} {E E' d b : ℝ → ℝ}
    (hT : 0 ≤ T) (hν : 0 ≤ ν) (hE : ContinuousOn E (Set.Icc 0 T))
    (hE0 : E 0 = 0) (hEnonneg : ∀ t ∈ Set.Icc 0 T, 0 ≤ E t)
    (hbcont : Continuous b) (hdcont : Continuous d)
    (hdnonneg : ∀ t ∈ Set.Ioo 0 T, 0 ≤ d t)
    (hbnonneg : ∀ t ∈ Set.Ioo 0 T, 0 ≤ b t)
    (hdE : ∀ t ∈ Set.Ioo 0 T, HasDerivAt E (E' t) t)
    (henergy : ∀ t ∈ Set.Ioo 0 T,
      E' t + 2 * ν * d t ≤ 2 * b t * Real.sqrt (E t)) :
    ∀ t ∈ Set.Icc 0 T,
      E t + 2 * ν * (∫ x in (0 : ℝ)..t, d x) ≤
        (∫ x in (0 : ℝ)..t, b x) ^ 2 := by
  exact packet_energy_integral_bound hT hν hE hE0 hEnonneg hbcont hdcont
    hdnonneg hbnonneg hdE henergy

end NSFormalization.Paper1
