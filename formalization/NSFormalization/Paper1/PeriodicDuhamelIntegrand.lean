import NSFormalization.Paper1.PeriodicForcedDuhamel

noncomputable section

namespace NSFormalization.Paper1.PeriodicForcedDuhamel

open NSFormalization.Paper1.PeriodicHeatMultiplier

/-! Coefficient-level interface for the integrand appearing in `duhamel`.

This deliberately stops before commuting a coordinate evaluation with the
Bochner interval integral.  The latter requires a separate continuous-linear
map API and an explicit integrability transport lemma.
-/

def duhamelIntegrand (ν : ℝ) (hν : 0 ≤ ν) (t τ : ℝ)
    (G : ℝ → FourierHilbert) : FourierHilbert :=
  heat hν (show 0 ≤ max (t - τ) 0 by positivity) (G τ)

theorem duhamelIntegrand_apply {ν : ℝ} (hν : 0 ≤ ν) (t τ : ℝ)
    (G : ℝ → FourierHilbert) (k : PeriodicFrequency) :
    duhamelIntegrand ν hν t τ G k =
      ((heatSymbol ν (max (t - τ) 0) k : ℝ) : ℂ) * G τ k := by
  exact heat_integrand_apply hν (show 0 ≤ max (t - τ) 0 by positivity) (G τ) k

theorem duhamelIntegrand_eq_heat {ν : ℝ} (hν : 0 ≤ ν) (t τ : ℝ)
    (G : ℝ → FourierHilbert) :
    duhamelIntegrand ν hν t τ G =
      heat hν (show 0 ≤ max (t - τ) 0 by positivity) (G τ) := rfl

end NSFormalization.Paper1.PeriodicForcedDuhamel

namespace NSFormalization.Paper1.PeriodicForcedDuhamel

open NSFormalization.Paper1.PeriodicHeatMultiplier

/-- On the forward time region, the globally defined `max` delay is the usual
nonnegative heat delay.  This is the pointwise identity used before any
interval-integral manipulation. -/
theorem duhamelIntegrand_eq_heat_delay {ν : ℝ} (hν : 0 ≤ ν)
    {t τ : ℝ} (hτt : τ ≤ t) (G : ℝ → FourierHilbert) :
    duhamelIntegrand ν hν t τ G = heat hν (sub_nonneg.mpr hτt) (G τ) := by
  simp only [duhamelIntegrand]
  have hmax : max (t - τ) 0 = t - τ := max_eq_left (sub_nonneg.mpr hτt)
  simp only [hmax]

/-- Coefficient form of `duhamelIntegrand_eq_heat_delay`. -/
theorem duhamelIntegrand_apply_of_le {ν : ℝ} (hν : 0 ≤ ν)
    {t τ : ℝ} (hτt : τ ≤ t) (G : ℝ → FourierHilbert)
    (k : PeriodicFrequency) :
    duhamelIntegrand ν hν t τ G k =
      ((heatSymbol ν (t - τ) k : ℝ) : ℂ) * G τ k := by
  rw [duhamelIntegrand_eq_heat_delay hν hτt]
  rfl

end NSFormalization.Paper1.PeriodicForcedDuhamel
