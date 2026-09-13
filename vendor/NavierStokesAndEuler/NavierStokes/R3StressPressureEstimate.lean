import NavierStokes.R3EnergyNorms
import NavierStokes.R3EnergyAbsorption

/-!
# Uniform cutoff pressure estimates for a difference stress

The estimates are uniform in the Gaussian regularization parameter and
use only the velocity norms supplied by finite energy and the compact
comparison solution.
-/

noncomputable section
namespace NavierStokes.R3StressPressureEstimate

open Set Filter MeasureTheory ProblemStatement
open R3WeightedLp R3PressureCommutator R3PressureCutoff R3PressureFlux R3RieszApproximation
open R3RieszKernel R3PressureNearKernel R3EnergyNorms R3CutoffSobolev
open scoped ENNReal ContDiff

def nearConstant : ℝ := lpNorm nearBase (6 / 5) volume
def farConstant : ℝ := lpNorm remainderBase 2 volume
def commutatorConstant (L : ℝ) : ℝ := kernelConstant * (96 * L ^ 6)

def rawBound (R L M V B : ℝ) : ℝ :=
  (B ^ (3 / 2 : ℝ) * M ^ (1 / 2 : ℝ) + 2 * (V * M) +
    commutatorConstant L *
      (R ^ (-1 / 2 : ℝ) * nearConstant * (B * M + 2 * (V * M)) +
        R ^ (-3 / 2 : ℝ) * farConstant * (M ^ 2 + 2 * (V * M)))) * (8 * L / R * M)

theorem rawBound_nonneg {R L M V B : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hV : 0 ≤ V) (hB : 0 ≤ B) : 0 ≤ rawBound R L M V B := by
  have hk := kernelConstant_nonneg
  have hn : 0 ≤ nearConstant := lpNorm_nonneg
  have hf : 0 ≤ farConstant := lpNorm_nonneg
  unfold rawBound commutatorConstant
  positivity

theorem regularized_flux_bound {R L : ℝ} {φ U W : Space → ℝ} {g h : Space → ℂ}
    (hφ : Cutoff R L φ) (hφg : φ.HasTemperateGrowth)
    (hWm : Measurable W) (hgm : Measurable g) (hU0 : ∀ x, 0 ≤ U x) (hW0 : ∀ x, 0 ≤ W x)
    (hU₂ : MemLp U 2) (hU₆ : MemLp U 6) (hUi : MemLp U ⊤)
    (hW₂ : MemLp W 2) (hB₆ : MemLp (fourthWeight φ W) 6) (hh : MemLp h 2)
    (hb : ∀ x, ‖g x‖ ≤ W x ^ 2 + 2 * (U x * W x))
    {M V B : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V) (hB : 0 ≤ B)
    (bW : lpNorm W 2 volume ≤ M) (bU₂ : lpNorm U 2 volume ≤ V)
    (bU₆ : lpNorm U 6 volume ≤ V) (bUi : lpNorm U ⊤ volume ≤ V)
    (bB : lpNorm (fourthWeight φ W) 6 volume ≤ B)
    (bh : lpNorm h 2 volume ≤ 8 * L / R * M) (n : ℕ) (i j : Fin 3) :
    ‖∫ x : Space, powerCutoff φ x * regularized n i j g x * h x‖ ≤ rawBound R L M V B := by
  obtain ⟨hg, bg⟩ := stress_L1 hWm hgm hW0 hU₂ hW₂ hb
  obtain ⟨hg5, bg5⟩ := stress_weight_five hφ hWm hgm hU0 hW0 hU₆ hW₂ hB₆ hb
  obtain ⟨hg6, bg6⟩ := stress_weight_six hφ hWm hgm hU0 hW0 hUi hW₂ hB₆ hb
  have hR := hφ.radius_pos
  have hL : 0 ≤ L := le_trans zero_le_one hφ.constant_ge_one
  have hk : 0 ≤ commutatorConstant L := mul_nonneg kernelConstant_nonneg (by positivity)
  have hn : 0 ≤ nearConstant := lpNorm_nonneg
  have hf : 0 ≤ farConstant := lpNorm_nonneg
  have b1 : lpNorm g 1 volume ≤ M ^ 2 + 2 * (V * M) := by
    apply bg.trans
    gcongr <;> first | assumption | exact lpNorm_nonneg
  have b5 : lpNorm (weightedNorm φ g) (3 / 2) volume ≤ B * M + 2 * (V * M) := by
    apply bg5.trans
    gcongr <;> first | assumption | exact lpNorm_nonneg
  have b6 : lpNorm (fun x => powerCutoff φ x * g x) 2 volume ≤
      B ^ (3 / 2 : ℝ) * M ^ (1 / 2 : ℝ) + 2 * (V * M) := by
    apply bg6.trans
    gcongr <;> first | assumption | exact lpNorm_nonneg | exact Real.rpow_nonneg lpNorm_nonneg _
  have berror : errorBound R L φ g ≤ commutatorConstant L *
      (R ^ (-1 / 2 : ℝ) * nearConstant * (B * M + 2 * (V * M)) +
        R ^ (-3 / 2 : ℝ) * farConstant * (M ^ 2 + 2 * (V * M))) := by
    change commutatorConstant L *
      (R ^ (-1 / 2 : ℝ) * nearConstant * lpNorm (weightedNorm φ g) (3 / 2) volume +
        R ^ (-3 / 2 : ℝ) * farConstant * lpNorm g 1 volume) ≤ _
    gcongr
  apply (regularized_flux_le hφ hφg n i j hg hg5 hg6 hh).trans
  unfold rawBound
  exact mul_le_mul (add_le_add b6 berror) bh lpNorm_nonneg (by positivity)

def coefficient (L M V : ℝ) : ℝ :=
  8 * L * M * (M ^ (1 / 2 : ℝ) + commutatorConstant L * nearConstant * M +
    (2 * (V * M) + commutatorConstant L *
      (nearConstant * (2 * (V * M)) + farConstant * (M ^ 2 + 2 * (V * M)))))

theorem coefficient_nonneg {L M V : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (hV : 0 ≤ V) :
    0 ≤ coefficient L M V := by
  have hk : 0 ≤ commutatorConstant L := mul_nonneg kernelConstant_nonneg (by positivity)
  have hn : 0 ≤ nearConstant := lpNorm_nonneg
  have hf : 0 ≤ farConstant := lpNorm_nonneg
  unfold coefficient
  positivity

theorem rawBound_le {R L M V B : ℝ} (hR : 1 ≤ R) (hL : 0 ≤ L)
    (hM : 0 ≤ M) (hV : 0 ≤ V) (hB : 0 ≤ B) :
    rawBound R L M V B ≤ coefficient L M V / R * (B ^ (3 / 2 : ℝ) + B + 1) := by
  have hR' : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hk : 0 ≤ commutatorConstant L := mul_nonneg kernelConstant_nonneg (by positivity)
  have hn : 0 ≤ nearConstant := lpNorm_nonneg
  have hf : 0 ≤ farConstant := lpNorm_nonneg
  have hhalf : R ^ (-1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hR (by norm_num)
  have hthree : R ^ (-3 / 2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hR (by norm_num)
  have hnear := mul_le_mul_of_nonneg_right hhalf
    (by positivity : 0 ≤ nearConstant * (B * M + 2 * (V * M)))
  have hfar := mul_le_mul_of_nonneg_right hthree
    (by positivity : 0 ≤ farConstant * (M ^ 2 + 2 * (V * M)))
  let a := M ^ (1 / 2 : ℝ)
  let b := commutatorConstant L * nearConstant * M
  let c := 2 * (V * M) + commutatorConstant L *
    (nearConstant * (2 * (V * M)) + farConstant * (M ^ 2 + 2 * (V * M)))
  have ha : 0 ≤ a := Real.rpow_nonneg hM _
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hbnd : B ^ (3 / 2 : ℝ) * M ^ (1 / 2 : ℝ) + 2 * (V * M) +
      commutatorConstant L *
        (R ^ (-1 / 2 : ℝ) * nearConstant * (B * M + 2 * (V * M)) +
          R ^ (-3 / 2 : ℝ) * farConstant * (M ^ 2 + 2 * (V * M))) ≤
      a * B ^ (3 / 2 : ℝ) + b * B + c := by
    have hh := mul_le_mul_of_nonneg_left (add_le_add hnear hfar) hk
    dsimp only [a, b, c]
    nlinarith only [hh]
  have hpoly : a * B ^ (3 / 2 : ℝ) + b * B + c ≤ (a + b + c) * (B ^ (3 / 2 : ℝ) + B + 1) := by
    have hp : 0 ≤ B ^ (3 / 2 : ℝ) := Real.rpow_nonneg hB _
    nlinarith [mul_nonneg ha hB, mul_nonneg hb hp, mul_nonneg hc hp, mul_nonneg hc hB]
  have hh := mul_le_mul_of_nonneg_right (hbnd.trans hpoly) (by positivity : 0 ≤ 8 * L / R * M)
  unfold rawBound
  convert! hh using 1
  dsimp only [a, b, c, coefficient]
  ring

/-- A single stress component contributes an arbitrarily small multiple
of the localized dissipation, plus a uniform inverse-radius remainder. -/
theorem exists_regularized_pressure_bound {L M V ε : ℝ}
    (hL : 1 ≤ L) (hM : 0 ≤ M) (hV : 0 ≤ V) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (φ : Space → ℝ) (w : Space → Space)
      (U : Space → ℝ) (g : Space → ℂ), 1 ≤ R → Cutoff R L φ →
      ContDiff ℝ ∞ φ → HasCompactSupport φ → (∀ x, ‖fderiv ℝ φ x‖ ≤ L / R) →
      ContDiff ℝ ∞ w → MemLp w 2 → lpNorm w 2 volume ≤ M →
      (∀ x, 0 ≤ U x) → MemLp U 2 → MemLp U 6 → MemLp U ⊤ →
      lpNorm U 2 volume ≤ V → lpNorm U 6 volume ≤ V → lpNorm U ⊤ volume ≤ V →
      Measurable g → (∀ x, ‖g x‖ ≤ ‖w x‖ ^ 2 + 2 * (U x * ‖w x‖)) →
      ∀ n i j, ‖∫ x : Space,
        (fderiv ℝ (fun y => φ y ^ 8) x (w x) : ℂ) * regularized n i j g x‖ ≤
        ε * R3CompactEnergy.dissipation (fun x => φ x ^ 8) w + C / R := by
  have hL₀ : 0 ≤ L := le_trans zero_le_one hL
  obtain ⟨C, hC, hAbs⟩ := R3EnergyAbsorption.absorb_sobolev_errors
    (coefficient_nonneg hL₀ hM hV) sobolevConstant_nonneg (show 0 ≤ 4 * L * M by positivity)
    (show 0 < ε / 3 by positivity)
  refine ⟨C, hC, ?_⟩
  intro R φ w U g hR hφ hφs hφc hφd hw hw₂ bw hU₀ hU₂ hU₆ hUi bU₂ bU₆ bUi hgm hb n i j
  have hR' : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let A := lpNorm (weightedDerivativeNorm φ w) 2 volume
  let B := lpNorm (fourthWeight φ (fun x => ‖w x‖)) 6 volume
  have hA : 0 ≤ A := lpNorm_nonneg
  have hB : 0 ≤ B := lpNorm_nonneg
  have hB₆ : MemLp (fourthWeight φ (fun x => ‖w x‖)) 6 := by
    have hc : HasCompactSupport (fun x => φ x ^ 4 * ‖w x‖) :=
      (hφc.comp_left (g := fun r : ℝ => r ^ 4) (by norm_num)).mul_right
    exact ((hφs.continuous.pow 4).mul hw.continuous.norm).memLp_of_hasCompactSupport hc
  have hSob : B ≤ sobolevConstant * (A + (4 * L * M) / R) := by
    have h := weighted_sobolev (hφs.of_le (by simp)) hφc (hw.of_le (by simp)) hφ.range
      (show 0 ≤ L / R by positivity) hφd hw₂
    have hm := mul_le_mul_of_nonneg_left bw (show 0 ≤ 4 * (L / R) by positivity)
    have hh := h.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hm) sobolevConstant_nonneg)
    convert! hh using 1
    ring
  obtain ⟨hH, bH⟩ := pressureFluxFactor_memLp hφs hw hφ.range
    (show 0 ≤ L / R by positivity) hφd hw₂
  have bH' : lpNorm (pressureFluxFactor φ w) 2 volume ≤ 8 * L / R * M := by
    have h := bH.trans (mul_le_mul_of_nonneg_left bw (show 0 ≤ 8 * (L / R) by positivity))
    convert! h using 1
    ring
  have bW : lpNorm (fun x => ‖w x‖) 2 volume ≤ M := by rw [lpNorm_norm hw₂.1]; exact bw
  have hreg := regularized_flux_bound hφ
    (hφc.hasTemperateGrowth hφs) hw.continuous.norm.measurable hgm hU₀
    (fun x => norm_nonneg (w x)) hU₂ hU₆ hUi hw₂.norm hB₆ hH hb hM hV hB bW bU₂ bU₆ bUi le_rfl bH' n i j
  have he (x : Space) : powerCutoff φ x * regularized n i j g x * pressureFluxFactor φ w x =
      (fderiv ℝ (fun y => φ y ^ 8) x (w x) : ℂ) * regularized n i j g x := by
    rw [← pressureFluxFactor_identity hφs w x]
    ring
  simp only [he] at hreg
  have hraw := rawBound_le hR hL₀ hM hV hB
  have hpoly : coefficient L M V / R * (B ^ (3 / 2 : ℝ) + B + 1) ≤
      coefficient L M V / R * (B ^ (3 / 2 : ℝ) + B + A + 1) := by
    exact mul_le_mul_of_nonneg_left (by linarith) (div_nonneg (coefficient_nonneg hL₀ hM hV) hR'.le)
  have hfinal := hAbs R A B hR hA hB hSob
  have hdis := weightedDerivative_sq_le_dissipation hφs hφc hw
  have hdis' := mul_le_mul_of_nonneg_left hdis (show 0 ≤ ε / 3 by positivity)
  exact ((hreg.trans hraw).trans hpoly).trans (hfinal.trans (by dsimp [A] at *; nlinarith only [hdis']))

end NavierStokes.R3StressPressureEstimate
