-- REVIEW PROBE (lane 145): what is still missing for A3-L1·k, i.e. the quantitative upgrade of
-- lane 140's `EulerPairing.hasWeakDerivsL2_of_cylinder` to `HasWeakDerivsL2Bound`.
-- The two facts below are the whole analytic content of the missing `M ≤ ‖u‖²` step.
-- Run: cd verification && lake env lean ../research/D01/probes/rev145_a3l1k_glue.lean
import NSFormalization.Source.OrdinaryCylinderDescent
import NSFormalization.Section4.D01.FiniteOrderNorm

open MeasureTheory EulerCylinderSobolevSpace EulerMeanOrdinaryLift EulerLiftedGradientSpace
noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

-- (a) every derivative word of a cylinder Sobolev array is bounded by the array norm
--     (the SobolevSpace norm is the sup norm on the finite word-indexed product).
theorem probe_norm_word_le {q n : ℕ} (u : SobolevSpace 1 q) (hn : n ≤ q) (w : Fin n → Fin 4) :
    ‖word 1 u hn w‖ ≤ ‖u‖ :=
  norm_le_pi_norm (u : SobolevWord q → LiftL2 1) _

-- (b) `ordinaryLift` is a linear isometry, so the descended ordinary L² field has the same norm,
--     and its L² eLpNorm is that norm.
theorem probe_eLpNorm_descend {q n : ℕ} (u : SobolevSpace 1 q) (hn : n ≤ q) (w : Fin n → Fin 4)
    (Zw : EulerMeanSolenoidal.L2) (hZw : ordinaryLift Zw = word 1 u hn w) :
    (eLpNorm (⇑Zw) 2 volume).toReal ^ 2 ≤ ‖u‖ ^ 2 := by
  have h1 : (eLpNorm (⇑Zw) 2 volume).toReal = ‖Zw‖ := (Lp.norm_def Zw).symm
  have h2 : ‖Zw‖ = ‖word 1 u hn w‖ := by rw [← hZw, ordinaryLift.norm_map]
  rw [h1, h2]
  exact pow_le_pow_left₀ (norm_nonneg _) (probe_norm_word_le u hn w) 2
