import NavierStokes.R3EnergyBoundary
import NavierStokes.R3EnergyAbsorption

/-!
# Uniform absorption of diffusion and transport boundary fluxes
-/

noncomputable section
namespace NavierStokes.R3AbsorbedBoundary

open Set Filter MeasureTheory ProblemStatement
open R3CompactEnergy R3CutoffSobolev R3WeightedLp R3EnergyNorms R3EnergyBoundary
open scoped ContDiff ENNReal

theorem exists_boundary_bound {L M U ε : ℝ} (hL : 1 ≤ L) (hM : 0 ≤ M)
    (hU : 0 ≤ U) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (φ : Space → ℝ) (w v : Space → Space),
      1 ≤ R → ContDiff ℝ ∞ φ → HasCompactSupport φ → (∀ x, φ x ∈ Icc (0 : ℝ) 1) →
      (∀ x, ‖fderiv ℝ φ x‖ ≤ L / R) → ContDiff ℝ ∞ w → MemLp w 2 →
      lpNorm w 2 volume ≤ M → (∀ x, ‖v x‖ ≤ ‖w x‖ + U) →
      2 * |diffusionFlux (fun x => φ x ^ 8) w| + |transportFlux (fun x => φ x ^ 8) w v| ≤
        ε * dissipation (fun x => φ x ^ 8) w + C / R := by
  have hL₀ : 0 ≤ L := le_trans zero_le_one hL
  let a := 48 * L * M
  let b := 8 * L * M ^ (3 / 2 : ℝ)
  let d := 8 * L * U * M ^ 2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  obtain ⟨C, hC, hAbs⟩ := R3EnergyAbsorption.absorb_sobolev_errors
    (show 0 ≤ a + b + d by positivity) sobolevConstant_nonneg
    (show 0 ≤ 4 * L * M by positivity) (show 0 < ε / 3 by positivity)
  refine ⟨C, hC, ?_⟩
  intro R φ w v hR hφ hφc hr hφd hw hw₂ bW hv
  have hR' : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let A := lpNorm (weightedDerivativeNorm φ w) 2 volume
  let B := lpNorm (fourthWeight φ (fun x => ‖w x‖)) 6 volume
  have hA : 0 ≤ A := lpNorm_nonneg
  have hB : 0 ≤ B := lpNorm_nonneg
  have hpB : 0 ≤ B ^ (3 / 2 : ℝ) := Real.rpow_nonneg hB _
  have hDiff : |diffusionFlux (fun x => φ x ^ 8) w| ≤ 24 * (L / R) * A * M := by
    apply (diffusionFlux_le hφ hφc hw hr (show 0 ≤ L / R by positivity) hφd hw₂).trans
    exact mul_le_mul_of_nonneg_left bW (by positivity)
  have hTrans : |transportFlux (fun x => φ x ^ 8) w v| ≤
      8 * (L / R) * (B ^ (3 / 2 : ℝ) * M ^ (3 / 2 : ℝ) + U * M ^ 2) := by
    apply (transportFlux_le hφ hφc hw hr (show 0 ≤ L / R by positivity) hU hφd hw₂ hv).trans
    gcongr <;> first | assumption | exact lpNorm_nonneg
  have hpoly : a * A + b * B ^ (3 / 2 : ℝ) + d ≤
      (a + b + d) * (B ^ (3 / 2 : ℝ) + B + A + 1) := by
    nlinarith [mul_nonneg ha hpB, mul_nonneg ha hB, mul_nonneg hb hA, mul_nonneg hb hB,
      mul_nonneg hd hpB, mul_nonneg hd hB, mul_nonneg hd hA]
  have hsmall : 2 * |diffusionFlux (fun x => φ x ^ 8) w| + |transportFlux (fun x => φ x ^ 8) w v| ≤
      (a * A + b * B ^ (3 / 2 : ℝ) + d) / R := by
    have h := add_le_add (mul_le_mul_of_nonneg_left hDiff (by norm_num : (0 : ℝ) ≤ 2)) hTrans
    convert! h using 1
    dsimp [a, b, d]
    ring
  have hsmall' := hsmall.trans (div_le_div_of_nonneg_right hpoly hR'.le)
  have hSob : B ≤ sobolevConstant * (A + (4 * L * M) / R) := by
    have h := weighted_sobolev (hφ.of_le (by simp)) hφc (hw.of_le (by simp)) hr
      (show 0 ≤ L / R by positivity) hφd hw₂
    have hm := mul_le_mul_of_nonneg_left bW (show 0 ≤ 4 * (L / R) by positivity)
    have hh := h.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hm) sobolevConstant_nonneg)
    convert! hh using 1 ; ring
  have hfinal := hAbs R A B hR hA hB hSob
  have hdis := weightedDerivative_sq_le_dissipation hφ hφc hw
  have hdis' := mul_le_mul_of_nonneg_left hdis (show 0 ≤ ε / 3 by positivity)
  have he : (a + b + d) * (B ^ (3 / 2 : ℝ) + B + A + 1) / R =
      (a + b + d) / R * (B ^ (3 / 2 : ℝ) + B + A + 1) := by ring
  rw [he] at hsmall'
  exact hsmall'.trans (hfinal.trans (by dsimp [A] at *; nlinarith only [hdis']))

end NavierStokes.R3AbsorbedBoundary
