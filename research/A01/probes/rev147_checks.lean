-- Reviewer probe (lane 147, A3-L1·k).  Two checks the review report cites:
--   (1) the `((2:ℕ):ℝ)` vs `(2:ℝ)` numeral identification the module relies on is `rfl`;
--   (2) the order-2 manuscript enorm of `⇑U` is **finite** under exactly the hypotheses of
--       `sobolevENorm_two_toReal_le` — so the recorded `.toReal ≤ 16‖u‖` is not the `⊤ ↦ 0`
--       vacuous statement.  (The bare `.toReal` inequality *would* hold vacuously at `⊤`; see the
--       third example.)  One line from the module's own ingredients: worth exporting.
-- Run: cd verification && lake env lean ../research/A01/probes/rev147_checks.lean
import NSFormalization.Section4.A01.OrderTwoCap

noncomputable section
namespace NSFormalization.Section4.A01
open MeasureTheory
open NSFormalization.Section4.D01
open NSFormalization.Section4.A04 (sobolevENorm_eq)
open NavierStokes.ProblemStatement (Space)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- (1) the numeral identification used by `sobolevNormAt_two_le_of_cylinder`'s `show`/`exact`. -/
example : ((2 : ℕ) : ℝ) = (2 : ℝ) := rfl

/-- (2) finiteness, from exactly `sobolevENorm_two_toReal_le`'s hypotheses. -/
example {q : ℕ} (u : SobolevSpace 1 (q + 1))
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (U : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u) (hq : 4 ≤ q) :
    sobolevENorm ((2 : ℕ) : ℝ) (⇑U) ≠ ⊤ := by
  obtain ⟨A, hA, _⟩ := exists_isSobolevDatum_norm_le 2 (⇑U) (‖u‖ ^ 2)
    (hasWeakDerivsL2Bound_of_cylinder u hu U hU 2 (by omega))
  rw [sobolevENorm_eq hA]
  simp

/-- (3) the `⊤ ↦ 0` caveat: the *bare* `.toReal` inequality is vacuously true at `⊤`. -/
example (z : Space → Space) (c : ℝ) (hc : 0 ≤ c) (h : sobolevENorm ((2 : ℕ) : ℝ) z = ⊤) :
    (sobolevENorm ((2 : ℕ) : ℝ) z).toReal ≤ c := by rw [h]; simpa using hc

/-- (4) the `hslice` hypothesis can be weakened from literal function equality to the a.e.
hand-off that lane 140 documents as B1 (`EulerPairing.exists_isSobolevDatum_m_of_ae`,
`IsSobolevDatum.congr_field`): the same constant survives.  Three extra lines. -/
example {q : ℕ} (u : SobolevSpace 1 (q + 1))
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (U : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u) (hq : 4 ≤ q)
    (z : Space → Space) (hz : z =ᵐ[volume] (⇑U : Space → Space)) :
    (sobolevENorm ((2 : ℕ) : ℝ) z).toReal ≤ 16 * ‖u‖ := by
  have hbound : HasWeakDerivsL2Bound (⇑U) (‖u‖ ^ 2) 2 :=
    hasWeakDerivsL2Bound_of_cylinder u hu U hU 2 (by omega)
  obtain ⟨A, hA, _⟩ := exists_isSobolevDatum_norm_le 2 (⇑U) (‖u‖ ^ 2) hbound
  have hAz : IsSobolevDatum ((2 : ℕ) : ℝ) z A := IsSobolevDatum.congr_field hA hz.symm
  have hA256 : ‖A‖ ^ 2 ≤ 256 * ‖u‖ ^ 2 :=
    norm_isSobolevDatum_le_two (⇑U) (‖u‖ ^ 2) hbound A hA
  have hle : ‖A‖ ≤ 16 * ‖u‖ := by
    nlinarith [hA256, sq_nonneg (‖A‖ - 16 * ‖u‖), norm_nonneg A, norm_nonneg u]
  rw [sobolevENorm_eq hAz]
  simpa [Real.enorm_eq_ofReal (norm_nonneg A), ENNReal.toReal_ofReal (norm_nonneg A)] using hle

end NSFormalization.Section4.A01
