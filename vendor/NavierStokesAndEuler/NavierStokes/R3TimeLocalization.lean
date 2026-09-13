import NavierStokes.R3SpaceTime
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Compact time localization of finite-energy fields

Multiplying by a compact time cutoff turns uniform spatial `L¹` or `L²`
bounds into the corresponding space-time bounds. Smoothness is only required
on the open time interval containing the cutoff support.
-/

noncomputable section
namespace NavierStokes.R3TimeLocalization

open Set Filter MeasureTheory R3SpaceTime ProblemStatement
open scoped ENNReal Topology ContDiff

def localize (a : ℝ → ℝ) (u : Domain → ℂ) (z : Domain) : ℂ :=
  (a (timeProj z) : ℂ) * u z

theorem localize_contDiff {a : ℝ → ℝ} {u : Domain → ℂ} {s : Set ℝ}
    (ha : ContDiff ℝ ∞ a) (hs : IsOpen s) (has : tsupport a ⊆ s)
    (hu : ContDiffOn ℝ ∞ u (timeProj ⁻¹' s)) : ContDiff ℝ ∞ (localize a u) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : timeProj z ∈ tsupport a
  · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp z (ha.contDiffAt.comp z timeProj.contDiff.contDiffAt)).mul
      ((hu z (has hz)).contDiffAt ((hs.preimage timeProj.continuous).mem_nhds (has hz)))
  · have hzero : a =ᶠ[𝓝 (timeProj z)] (fun _ => (0 : ℝ)) :=
      notMem_tsupport_iff_eventuallyEq.mp hz
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [hzero.comp_tendsto timeProj.continuous.continuousAt] with y hy
    change a (timeProj y) = 0 at hy
    simp [localize, hy]

theorem localize_integrable {a : ℝ → ℝ} {u : Domain → ℂ} {C : ℝ}
    (ha : Integrable a) (hm : AEStronglyMeasurable (localize a u) volume)
    (hu : ∀ t, a t ≠ 0 → Integrable (fun x : Space => u (pack t x)))
    (hb : ∀ t, a t ≠ 0 → (∫ x : Space, ‖u (pack t x)‖) ≤ C) :
    Integrable (localize a u) := by
  rw [integrable_iff_prod]
  have hm' : AEStronglyMeasurable (fun tx : ℝ × Space => localize a u (pack tx.1 tx.2)) volume := by
    exact hm.comp_measurePreserving (WithLp.volume_preserving_toLp ℝ Space)
  apply (integrable_prod_iff hm').mpr
  refine ⟨Eventually.of_forall (fun t => ?_), ?_⟩
  · by_cases ht : a t = 0
    · simp [localize, ht]
    · exact (hu t ht).const_mul (a t : ℂ)
  · have hi := hm'.norm.integral_prod_right'
    apply (ha.norm.mul_const C).mono' hi
    filter_upwards with t
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    by_cases ht : a t = 0
    · simp [localize, ht]
    · simp only [localize, timeProj_pack, norm_mul, Complex.norm_real, integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hb t ht) (norm_nonneg _)

theorem localize_memLp_two {a : ℝ → ℝ} {u : Domain → ℂ} {C : ℝ}
    (ha : MemLp a 2) (hm : AEStronglyMeasurable (localize a u) volume)
    (hu : ∀ t, a t ≠ 0 → MemLp (fun x : Space => u (pack t x)) 2)
    (hb : ∀ t, a t ≠ 0 → (∫ x : Space, ‖u (pack t x)‖ ^ 2) ≤ C) :
    MemLp (localize a u) 2 := by
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  rw [integrable_iff_prod]
  have hm' : AEStronglyMeasurable (fun tx : ℝ × Space => localize a u (pack tx.1 tx.2)) volume :=
    hm.comp_measurePreserving (WithLp.volume_preserving_toLp ℝ Space)
  apply (integrable_prod_iff (hm'.norm.pow 2)).mpr
  refine ⟨Eventually.of_forall (fun t => ?_), ?_⟩
  · by_cases ht : a t = 0
    · simp [localize, ht]
    · have hh := ((memLp_two_iff_integrable_sq_norm (hu t ht).1).mp (hu t ht)).const_mul (‖a t‖ ^ 2)
      simpa only [localize, timeProj_pack, norm_mul, Complex.norm_real, mul_pow, Pi.pow_apply] using hh
  · have hi := (hm'.norm.pow 2).norm.integral_prod_right'
    apply (((memLp_two_iff_integrable_sq_norm ha.1).mp ha).mul_const C).mono' hi
    filter_upwards with t
    change abs (∫ x : Space, abs (‖localize a u (pack t x)‖ ^ 2)) ≤ ‖a t‖ ^ 2 * C
    have haeq (x : Space) : abs (‖localize a u (pack t x)‖ ^ 2) =
        ‖localize a u (pack t x)‖ ^ 2 := abs_of_nonneg (sq_nonneg _)
    simp_rw [haeq]
    rw [abs_of_nonneg (show 0 ≤ ∫ x : Space, ‖localize a u (pack t x)‖ ^ 2 from
      integral_nonneg fun x => sq_nonneg _)]
    by_cases ht : a t = 0
    · simp [localize, ht]
    · simp only [localize, timeProj_pack, norm_mul, Complex.norm_real, mul_pow, integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hb t ht) (sq_nonneg _)

end NavierStokes.R3TimeLocalization
