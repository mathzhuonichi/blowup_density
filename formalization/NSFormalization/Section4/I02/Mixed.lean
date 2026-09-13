import NSFormalization.Section4.I02.Energy
import NSFormalization.Paper1.CorrectionMixedNorms
import NSFormalization.Paper3.PositiveTemporalDensity
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# I02: the mixed Lebesgue bound in the canonical `ENNReal` norm

`CorrectionMixedNorms.mixedNorm p q F` is
`eLpNorm (fun t => (eLpNorm (F t ·) p volume).toReal) q volume`: a time norm of a
*real-valued* function of `t`, over all of `ℝ`.  The registered Section 4 norm
`Contracts.V1.Data.mixedLebesgueENorm q p` is instead an infimum over honest
Bochner paths `ℝ → L^p(R³)` representing the slices of `F`, taken over `(0,∞)`.
The infimum is bounded by any single admissible path, so the transport reduces to
exhibiting one: the path `t ↦ [F(t,·)]`.

Its strong measurability is the only real content, and it comes from continuity:
a continuous compactly supported spacetime field is uniformly continuous
(`HasCompactSupport.uniformContinuous_of_continuous`), all its slices vanish off
one compact spatial set, and `eLpNorm_le_of_ae_bound` over that set turns a
uniform pointwise bound into an `L^p` bound.  Nothing below mentions the
contract; `verification/Bindings/Correction.lean` takes the infimum step.
-/

noncomputable section

namespace NSFormalization.Section4.I02

open NavierStokes NavierStokes.ProblemStatement
open Set MeasureTheory Filter NSFormalization.Paper3
open scoped ContDiff ENNReal Topology

variable {p : ℝ≥0∞}

/-- Every slice of a continuous compactly supported field lies in `L^p`. -/
theorem slice_memLp {H : VelocityField} (hH : Continuous H) (hc : HasCompactSupport H)
    (p : ℝ≥0∞) (t : ℝ) : MemLp (fun x : Space => H (t, x)) p volume :=
  (hH.comp (continuous_const.prodMk continuous_id)).memLp_of_hasCompactSupport
    (slice_hasCompactSupport hc t)

/-- The spatial slices of a compactly supported spacetime field all vanish
outside one compact spatial set. -/
theorem slice_zero_outside {H : VelocityField} (t : ℝ) {x : Space}
    (hx : x ∉ Prod.snd '' tsupport H) : H (t, x) = 0 :=
  image_eq_zero_of_notMem_tsupport (f := H) (fun h => hx ⟨(t, x), h, rfl⟩)

/-- The `L^p`-valued slice path of a continuous compactly supported field is
continuous, hence strongly measurable. -/
theorem continuous_slicePath [Fact (1 ≤ p)] {H : VelocityField}
    (hH : Continuous H) (hc : HasCompactSupport H) :
    Continuous (fun t : ℝ => (slice_memLp hH hc p t).toLp (fun x : Space => H (t, x))) := by
  set B : Set Space := Prod.snd '' tsupport H with hBdef
  have hBc : IsCompact B := hc.isCompact.image continuous_snd
  have hBm : MeasurableSet B := hBc.isClosed.measurableSet
  have hMtop : (volume B) ^ (p.toReal)⁻¹ ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg (by positivity) hBc.measure_lt_top.ne).ne
  set c : ℝ := ((volume B) ^ (p.toReal)⁻¹).toReal with hcdef
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have hden : (0 : ℝ) < c + 1 := by linarith
  rw [Metric.continuous_iff]
  intro b ε hε
  have hε'pos : 0 < ε / (c + 1) := div_pos hε hden
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp
    (hc.uniformContinuous_of_continuous hH) (ε / (c + 1)) hε'pos
  refine ⟨δ, hδ, fun a hab => ?_⟩
  have hpt : ∀ x : Space, ‖H (a, x) - H (b, x)‖ ≤ ε / (c + 1) := by
    intro x
    have hdist : dist ((a, x) : SpaceTime) ((b, x) : SpaceTime) < δ := by
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
      exact hab
    have hlt := hd hdist
    rw [dist_eq_norm] at hlt
    exact hlt.le
  have hind : (fun x : Space => H (a, x) - H (b, x))
      = B.indicator (fun x : Space => H (a, x) - H (b, x)) := by
    funext x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, slice_zero_outside a hx, slice_zero_outside b hx, sub_zero]
  have hbound : eLpNorm (fun x : Space => H (a, x) - H (b, x)) p volume
      ≤ (volume B) ^ (p.toReal)⁻¹ * ENNReal.ofReal (ε / (c + 1)) := by
    nth_rewrite 1 [hind]
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hBm]
    refine (eLpNorm_le_of_ae_bound (Filter.Eventually.of_forall hpt)).trans_eq ?_
    rw [Measure.restrict_apply_univ]
  have hnorm : dist ((slice_memLp hH hc p a).toLp (fun x : Space => H (a, x)))
      ((slice_memLp hH hc p b).toLp (fun x : Space => H (b, x)))
      = (eLpNorm (fun x : Space => H (a, x) - H (b, x)) p volume).toReal := by
    rw [dist_eq_norm, ← MemLp.toLp_sub, Lp.norm_toLp]
    rfl
  rw [hnorm]
  calc (eLpNorm (fun x : Space => H (a, x) - H (b, x)) p volume).toReal
      ≤ ((volume B) ^ (p.toReal)⁻¹ * ENNReal.ofReal (ε / (c + 1))).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hMtop ENNReal.ofReal_ne_top) hbound
    _ = c * (ε / (c + 1)) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hε'pos.le]
    _ < ε := by
        rw [show c * (ε / (c + 1)) = c * ε / (c + 1) by ring, div_lt_iff₀ hden]
        nlinarith

/-- One admissible Bochner path for the mixed Lebesgue norm, with its time norm
bounded by `CorrectionMixedNorms.mixedNorm`.  The infimum defining
`Contracts.V1.Data.mixedLebesgueENorm` is at most this. -/
theorem exists_slicePath [Fact (1 ≤ p)] {H : VelocityField}
    (hH : Continuous H) (hc : HasCompactSupport H) (q : ℝ≥0∞) :
    ∃ G : ℝ → Lp Space p (volume : Measure Space),
      (∀ t : ℝ, (G t : Space → Space) =ᵐ[volume] fun x : Space => H (t, x)) ∧
      AEStronglyMeasurable G positiveTimeMeasure ∧
      eLpNorm G q positiveTimeMeasure ≤ Paper1.CorrectionMixedNorms.mixedNorm p q H := by
  refine ⟨fun t => (slice_memLp hH hc p t).toLp (fun x : Space => H (t, x)),
    fun t => MemLp.coeFn_toLp _, ?_, ?_⟩
  · exact ((continuous_slicePath hH hc).stronglyMeasurable).aestronglyMeasurable
  · refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (le_of_eq ?_)
    refine eLpNorm_congr_enorm_ae (Filter.Eventually.of_forall (fun t => ?_))
    rw [Lp.enorm_toLp, Real.enorm_eq_ofReal ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (slice_memLp hH hc p t).eLpNorm_lt_top.ne]

end NSFormalization.Section4.I02
