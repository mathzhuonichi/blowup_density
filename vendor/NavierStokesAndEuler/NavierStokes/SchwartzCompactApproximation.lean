import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Compact smooth approximation in Schwartz space

Expanding smooth cutoffs converge in every Schwartz seminorm. Consequently,
two tempered distributions that agree on compact smooth tests are equal.
-/

noncomputable section
namespace NavierStokes.SchwartzCompactApproximation

open Set Filter
open scoped SchwartzMap Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def bump : ContDiffBump (0 : E) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def cutoff (R : ℝ) (x : E) : ℝ := (bump (E := E)) (R⁻¹ • x)

theorem cutoff_contDiff (R : ℝ) : ContDiff ℝ ∞ (cutoff (E := E) R) := by
  apply ((bump (E := E)).contDiff (n := (⊤ : ℕ∞))).comp
  fun_prop

theorem cutoff_compact {R : ℝ} (hR : R ≠ 0) : HasCompactSupport (cutoff (E := E) R) :=
  (bump (E := E)).hasCompactSupport.comp_smul (G₀ := ℝ) (c := R⁻¹) (inv_ne_zero hR)

theorem cutoff_one {R : ℝ} (hR : 0 < R) {x : E} (hx : ‖x‖ ≤ R) : cutoff R x = 1 := by
  apply (bump (E := E)).one_of_mem_closedBall
  simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hR)]
  change R⁻¹ * ‖x‖ ≤ 1
  exact (inv_mul_le_iff₀ hR).mpr (by simpa using hx)

def bumpSchwartz : 𝓢(E, ℝ) := (bump (E := E)).hasCompactSupport.toSchwartzMap ((bump (E := E)).contDiff (n := (⊤ : ℕ∞)))

def derivativeBound (n : ℕ) : ℝ := SchwartzMap.seminorm ℝ 0 n (bumpSchwartz (E := E)) + 1

theorem derivativeBound_nonneg (n : ℕ) : 0 ≤ derivativeBound (E := E) n := by
  unfold derivativeBound
  positivity

theorem cutoff_derivative_bound {R : ℝ} (hR : 1 ≤ R) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (cutoff R) x‖ ≤
      SchwartzMap.seminorm ℝ 0 n (bumpSchwartz (E := E)) := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have he := congrFun (iteratedFDeriv_comp_const_smul (R⁻¹)
    ((bump (E := E)).contDiff (n := (n : ℕ∞)))) x
  change ‖iteratedFDeriv ℝ n (fun z : E => (bump (E := E)) (R⁻¹ • z)) x‖ ≤ _
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hp : R⁻¹ ^ n ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hR)
  exact (mul_le_of_le_one_left (norm_nonneg _) hp).trans
    (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ bumpSchwartz n _)

def approximate (R : ℝ) (f : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x : E => (cutoff R x : ℂ)) f

theorem cutoff_temperate {R : ℝ} (hR : R ≠ 0) :
    (fun x : E => (cutoff R x : ℂ)).HasTemperateGrowth :=
  Complex.ofRealCLM.hasTemperateGrowth.comp
    ((cutoff_compact hR).hasTemperateGrowth (cutoff_contDiff R))

theorem approximate_apply {R : ℝ} (hR : R ≠ 0) (f : 𝓢(E, ℂ)) (x : E) :
    approximate R f x = (cutoff R x : ℂ) * f x := by
  simp [approximate, cutoff_temperate hR, smul_eq_mul]

theorem approximate_compact {R : ℝ} (hR : R ≠ 0) (f : 𝓢(E, ℂ)) :
    HasCompactSupport (approximate R f : E → ℂ) := by
  have hc : HasCompactSupport (fun x : E => (cutoff R x : ℂ) * f x) :=
    ((cutoff_compact (E := E) hR).comp_left (g := Complex.ofReal) (by simp)).mul_right
  convert hc using 1
  funext x
  exact approximate_apply hR f x

theorem cutoff_sub_one_derivative_bound {R : ℝ} (hR : 1 ≤ R) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => cutoff R y - 1) x‖ ≤ derivativeBound (E := E) n := by
  change ‖iteratedFDeriv ℝ n (cutoff R - fun _ : E => (1 : ℝ)) x‖ ≤ _
  rw [iteratedFDeriv_sub_apply ((cutoff_contDiff R).of_le (by simp)).contDiffAt
    contDiffAt_const]
  apply (norm_sub_le _ _).trans
  apply add_le_add (cutoff_derivative_bound hR n x)
  cases n with
  | zero => simp
  | succ n => simp [iteratedFDeriv_succ_const]

theorem approximate_sub_apply {R : ℝ} (hR : R ≠ 0) (f : 𝓢(E, ℂ)) :
    ((approximate R f - f : 𝓢(E, ℂ)) : E → ℂ) = fun x => (cutoff R x - 1) • f x := by
  funext x
  simp [approximate_apply hR, sub_smul, Complex.real_smul]

def approximationBound (k n : ℕ) (f : 𝓢(E, ℂ)) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * derivativeBound (E := E) i *
    SchwartzMap.seminorm ℝ k (n - i) f

theorem approximationBound_nonneg (k n : ℕ) (f : 𝓢(E, ℂ)) :
    0 ≤ approximationBound k n f := by
  unfold approximationBound
  exact Finset.sum_nonneg fun i _ => mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (derivativeBound_nonneg i)) (apply_nonneg _ _)

theorem approximation_derivative_bound {R : ℝ} (hR : 1 ≤ R) (k n : ℕ)
    (f : 𝓢(E, ℂ)) (x : E) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (approximate R f - f : 𝓢(E, ℂ)) x‖ ≤
      approximationBound k n f := by
  rw [approximate_sub_apply (ne_of_gt (lt_of_lt_of_le zero_lt_one hR))]
  have hd := norm_iteratedFDeriv_smul_le ((cutoff_contDiff R).sub (contDiff_const (c := (1 : ℝ))))
    (f.smooth ⊤) x (n := n) (by simp)
  apply (mul_le_mul_of_nonneg_left hd (by positivity)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  calc
    _ = (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y => cutoff R y - 1) x‖ *
      (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖) := by ring
    _ ≤ _ := mul_le_mul
      (mul_le_mul_of_nonneg_left (cutoff_sub_one_derivative_bound hR i x) (by positivity))
      (SchwartzMap.le_seminorm ℝ k (n - i) f x) (by positivity)
      (mul_nonneg (Nat.cast_nonneg _) (derivativeBound_nonneg i))

theorem approximation_derivative_zero {R : ℝ} (hR : 0 < R) (n : ℕ)
    (f : 𝓢(E, ℂ)) {x : E} (hx : ‖x‖ < R) :
    iteratedFDeriv ℝ n (approximate R f - f : 𝓢(E, ℂ)) x = 0 := by
  have he : (approximate R f - f : 𝓢(E, ℂ)) =ᶠ[𝓝 x] (fun _ : E => (0 : ℂ)) := by
    filter_upwards [((continuous_norm : Continuous (fun x : E => ‖x‖)).isOpen_preimage
      (Iio R) isOpen_Iio).mem_nhds hx] with y hy
    change approximate R f y - f y = 0
    rw [approximate_apply (ne_of_gt hR), cutoff_one hR (le_of_lt hy)]
    simp
  have hd := (he.iteratedFDeriv ℝ n).self_of_nhds
  simpa using hd

/-- The cutoff error is at most a fixed Schwartz seminorm bound divided by
its radius. -/
theorem approximation_seminorm_le {R : ℝ} (hR : 1 ≤ R) (k n : ℕ) (f : 𝓢(E, ℂ)) :
    SchwartzMap.seminorm ℝ k n (approximate R f - f) ≤ approximationBound (k + 1) n f / R := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  apply SchwartzMap.seminorm_le_bound ℝ k n _ (div_nonneg (approximationBound_nonneg _ _ _) hRpos.le)
  intro x
  by_cases hx : ‖x‖ < R
  · rw [approximation_derivative_zero hRpos n f hx, norm_zero, mul_zero]
    exact div_nonneg (approximationBound_nonneg _ _ _) hRpos.le
  · have hb := approximation_derivative_bound hR (k + 1) n f x
    rw [le_div_iff₀ hRpos]
    calc
      _ ≤ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (approximate R f - f : 𝓢(E, ℂ)) x‖ * ‖x‖ :=
        mul_le_mul_of_nonneg_left (le_of_not_gt hx) (by positivity)
      _ = ‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ n (approximate R f - f : 𝓢(E, ℂ)) x‖ := by ring
      _ ≤ _ := hb

theorem approximate_tendsto (f : 𝓢(E, ℂ)) :
    Tendsto (fun n : ℕ => approximate ((n : ℝ) + 1) f) atTop (𝓝 f) := by
  apply (schwartz_withSeminorms ℝ E ℂ).tendsto_nhds _ _ |>.mpr
  rintro ⟨k, n⟩ ε hε
  have hr : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).atTop_add
      (tendsto_const_nhds (x := (1 : ℝ)))
  have hb : Tendsto (fun N : ℕ => approximationBound (k + 1) n f / ((N : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Pi.inv_apply] using tendsto_const_nhds.mul hr.inv_tendsto_atTop
  filter_upwards [hb.eventually (gt_mem_nhds hε)] with N hN
  exact (approximation_seminorm_le (R := (N : ℝ) + 1) (by linarith [Nat.cast_nonneg (α := ℝ) N]) k n f).trans_lt hN

/-- Compact smooth tests determine a tempered distribution. -/
theorem tempered_eq_of_compact_tests {S T : 𝓢'(E, ℂ)}
    (h : ∀ f : 𝓢(E, ℂ), HasCompactSupport (f : E → ℂ) → S f = T f) : S = T := by
  ext f
  have hS := S.continuous.continuousAt.tendsto.comp (approximate_tendsto f)
  have hT := T.continuous.continuousAt.tendsto.comp (approximate_tendsto f)
  apply tendsto_nhds_unique hS
  apply hT.congr'
  filter_upwards with n
  exact (h _ (approximate_compact (by positivity) f)).symm

end NavierStokes.SchwartzCompactApproximation
