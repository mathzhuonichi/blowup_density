import NSFormalization.Section4.I03.HomogeneousScaling
import NSFormalization.Section4.B02.LowHigh
import NSFormalization.Section4.I02.Mixed

/-!
# Measurability of the compact homogeneous path

For `-3/2 < s < 0`, D01's concrete homogeneous datum path of a smooth
compactly supported force is continuous.  The proof uses no negative-order
Bessel-to-homogeneous map.  Instead, uniqueness identifies the difference of
two path values with the homogeneous datum of the corresponding physical slice
difference.  B02's low/high-frequency estimate bounds its squared norm by the
`L¹` and `L²` norms of that difference, and I02 proves that both compact-slice
paths are continuous.

This module stays in `formalization/`: the analytic statement uses only the
local D01 vocabulary.  The downstream named input
`CompactHomogeneousRealization` is discharged in
`verification/Bindings/ScalingHomogeneousClosed.lean`.
-/

noncomputable section

namespace NSFormalization.Section4.I03

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3 NSFormalization.Source
open scoped ContDiff ENNReal

open NSFormalization.Section4.D01.Homogeneous

/-! ## The low/high estimate for a path difference -/

/-- The squared norm of a difference of compact homogeneous data is controlled
by the physical `L¹` and `L²` slice differences.  The low-frequency constant
is finite precisely because `-3/2 < s`; the high-frequency estimate uses
`s ≤ 0`. -/
theorem compactHomogeneousPath_sub_enorm_sq_le {s : ℝ}
    (hs : -3 / 2 < s) (hs0 : s ≤ 0) {F : VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (t u : ℝ) :
    ‖compactHomogeneousPath hs hF hc t - compactHomogeneousPath hs hF hc u‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal ((2 * Real.pi) ^ (-(3 : ℝ)) *
          ∫ ξ in Metric.ball (0 : Space) 1, ‖ξ‖ ^ (2 * s)) *
          eLpNorm (fun x : Space => F (t, x) - F (u, x)) 1 volume ^ (2 : ℝ) +
        eLpNorm (fun x : Space => F (t, x) - F (u, x)) 2 volume ^ (2 : ℝ) := by
  let A := compactHomogeneousPath hs hF hc t - compactHomogeneousPath hs hF hc u
  let z : Space → Space := fun x => F (t, x) - F (u, x)
  let ψ : Fin 3 → SchwartzMap Space ℂ := fun i =>
    compactSchwartzComponents
        (hF.comp (contDiff_const.prodMk contDiff_id)) (compact_spatial_slice' hc t) i -
      compactSchwartzComponents
        (hF.comp (contDiff_const.prodMk contDiff_id)) (compact_spatial_slice' hc u) i
  have hψ : ∀ (i : Fin 3) (x : Space), ψ i x = ((z x i : ℝ) : ℂ) := by
    intro i x
    simp [ψ, z, compactSchwartzComponents_apply]
  have hA : IsHomogeneousSliceDatum s z A := by
    apply isHomogeneousSliceDatum_sub
      (compactHomogeneousPath_slice hs hF hc t)
      (compactHomogeneousPath_slice hs hF hc u)
    · exact integrable_schwartz_mul_component
        (compactSchwartzComponents
          (hF.comp (contDiff_const.prodMk contDiff_id)) (compact_spatial_slice' hc t))
        (fun _ _ => rfl)
    · exact integrable_schwartz_mul_component
        (compactSchwartzComponents
          (hF.comp (contDiff_const.prodMk contDiff_id)) (compact_spatial_slice' hc u))
        (fun _ _ => rfl)
  have he : ‖A‖ₑ = homogeneousFourierENorm s z :=
    enorm_of_isHomogeneousSliceDatum hs z ψ hψ A hA
  rw [he]
  exact NSFormalization.Section4.B02.lowHighSplit s hs hs0 z
    ((I02.slice_memLp hF.continuous hc 1 t).sub (I02.slice_memLp hF.continuous hc 1 u))
    ((I02.slice_memLp hF.continuous hc 2 t).sub (I02.slice_memLp hF.continuous hc 2 u))

/-- Real-norm form of `compactHomogeneousPath_sub_enorm_sq_le`.  Its right-hand
side is the continuous majorant used below. -/
theorem compactHomogeneousPath_sub_norm_sq_le {s : ℝ}
    (hs : -3 / 2 < s) (hs0 : s ≤ 0) {F : VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (t u : ℝ) :
    ‖compactHomogeneousPath hs hF hc t - compactHomogeneousPath hs hF hc u‖ ^ 2 ≤
      ((2 * Real.pi) ^ (-(3 : ℝ)) *
          ∫ ξ in Metric.ball (0 : Space) 1, ‖ξ‖ ^ (2 * s)) *
          dist ((I02.slice_memLp hF.continuous hc 1 t).toLp (fun x => F (t, x)))
            ((I02.slice_memLp hF.continuous hc 1 u).toLp (fun x => F (u, x))) ^ 2 +
        dist ((I02.slice_memLp hF.continuous hc 2 t).toLp (fun x => F (t, x)))
            ((I02.slice_memLp hF.continuous hc 2 u).toLp (fun x => F (u, x))) ^ 2 := by
  have hbound := compactHomogeneousPath_sub_enorm_sq_le hs hs0 hF hc t u
  have h1 := (I02.slice_memLp hF.continuous hc 1 t).sub
    (I02.slice_memLp hF.continuous hc 1 u)
  have h2 := (I02.slice_memLp hF.continuous hc 2 t).sub
    (I02.slice_memLp hF.continuous hc 2 u)
  have h1top : eLpNorm (fun x : Space => F (t, x) - F (u, x)) 1 volume ≠ ⊤ :=
    h1.eLpNorm_lt_top.ne
  have h2top : eLpNorm (fun x : Space => F (t, x) - F (u, x)) 2 volume ≠ ⊤ :=
    h2.eLpNorm_lt_top.ne
  have hC : 0 ≤ (2 * Real.pi) ^ (-(3 : ℝ)) *
      ∫ ξ in Metric.ball (0 : Space) 1, ‖ξ‖ ^ (2 * s) := by
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (setIntegral_nonneg measurableSet_ball (fun ξ _ => Real.rpow_nonneg (norm_nonneg ξ) _))
  have hterm1top : ENNReal.ofReal ((2 * Real.pi) ^ (-(3 : ℝ)) *
          ∫ ξ in Metric.ball (0 : Space) 1, ‖ξ‖ ^ (2 * s)) *
          eLpNorm (fun x : Space => F (t, x) - F (u, x)) 1 volume ^ (2 : ℝ) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) h1top)
  have hterm2top :
      eLpNorm (fun x : Space => F (t, x) - F (u, x)) 2 volume ^ (2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) h2top
  have htop : ENNReal.ofReal ((2 * Real.pi) ^ (-(3 : ℝ)) *
          ∫ ξ in Metric.ball (0 : Space) 1, ‖ξ‖ ^ (2 * s)) *
          eLpNorm (fun x : Space => F (t, x) - F (u, x)) 1 volume ^ (2 : ℝ) +
        eLpNorm (fun x : Space => F (t, x) - F (u, x)) 2 volume ^ (2 : ℝ) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hterm1top, hterm2top⟩
  have hr := ENNReal.toReal_mono htop hbound
  rw [ENNReal.toReal_add hterm1top hterm2top, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hC, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
    ← ENNReal.toReal_rpow, toReal_enorm] at hr
  have he1 : (eLpNorm (fun x : Space => F (t, x) - F (u, x)) 1 volume).toReal =
      dist ((I02.slice_memLp hF.continuous hc 1 t).toLp (fun x => F (t, x)))
        ((I02.slice_memLp hF.continuous hc 1 u).toLp (fun x => F (u, x))) := by
    rw [dist_eq_norm, ← MemLp.toLp_sub, Lp.norm_toLp]
    rfl
  have he2 : (eLpNorm (fun x : Space => F (t, x) - F (u, x)) 2 volume).toReal =
      dist ((I02.slice_memLp hF.continuous hc 2 t).toLp (fun x => F (t, x)))
        ((I02.slice_memLp hF.continuous hc 2 u).toLp (fun x => F (u, x))) := by
    rw [dist_eq_norm, ← MemLp.toLp_sub, Lp.norm_toLp]
    rfl
  simpa only [he1, he2, Real.rpow_two] using hr

/-! ## Continuity and the registered measurability clause -/

/-- D01's concrete compact homogeneous path is continuous at every negative
order in the locally integrable range `-3/2 < s < 0`. -/
theorem compactHomogeneousPath_continuous {s : ℝ}
    (hs : -3 / 2 < s) (hs0 : s < 0) {F : VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    Continuous (compactHomogeneousPath hs hF hc) := by
  let P1 : ℝ → Lp Space 1 (volume : Measure Space) := fun t =>
    (I02.slice_memLp hF.continuous hc 1 t).toLp (fun x => F (t, x))
  let P2 : ℝ → Lp Space 2 (volume : Measure Space) := fun t =>
    (I02.slice_memLp hF.continuous hc 2 t).toLp (fun x => F (t, x))
  have hP1 : Continuous P1 := I02.continuous_slicePath hF.continuous hc
  have hP2 : Continuous P2 := I02.continuous_slicePath hF.continuous hc
  let C : ℝ := (2 * Real.pi) ^ (-(3 : ℝ)) *
    ∫ ξ in Metric.ball (0 : Space) 1, ‖ξ‖ ^ (2 * s)
  have hC : 0 ≤ C := by
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (setIntegral_nonneg measurableSet_ball (fun ξ _ => Real.rpow_nonneg (norm_nonneg ξ) _))
  rw [continuous_iff_continuousAt]
  intro u
  rw [Metric.continuousAt_iff]
  intro ε hε
  let R : ℝ → ℝ := fun t => Real.sqrt
    (C * dist (P1 t) (P1 u) ^ 2 + dist (P2 t) (P2 u) ^ 2)
  have hR : ContinuousAt R u := by
    fun_prop
  obtain ⟨δ, hδ, hδR⟩ := (Metric.continuousAt_iff.mp hR) ε hε
  refine ⟨δ, hδ, fun t htu => ?_⟩
  rw [dist_eq_norm]
  have hsq := compactHomogeneousPath_sub_norm_sq_le hs hs0.le hF hc t u
  change ‖compactHomogeneousPath hs hF hc t - compactHomogeneousPath hs hF hc u‖ ^ 2 ≤
    C * dist (P1 t) (P1 u) ^ 2 + dist (P2 t) (P2 u) ^ 2 at hsq
  have hrad : 0 ≤ C * dist (P1 t) (P1 u) ^ 2 + dist (P2 t) (P2 u) ^ 2 := by
    positivity
  have hle : ‖compactHomogeneousPath hs hF hc t - compactHomogeneousPath hs hF hc u‖ ≤
      R t := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    change ‖compactHomogeneousPath hs hF hc t - compactHomogeneousPath hs hF hc u‖ ^ 2 ≤
      Real.sqrt (C * dist (P1 t) (P1 u) ^ 2 + dist (P2 t) (P2 u) ^ 2) ^ 2
    rw [Real.sq_sqrt hrad]
    exact hsq
  refine hle.trans_lt ?_
  have hRu : R u = 0 := by simp [R]
  have hRt : 0 ≤ R t := Real.sqrt_nonneg _
  have hclose := hδR htu
  rw [hRu, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hRt] at hclose
  exact hclose

/-- The continuity theorem supplies exactly the a.e. strong measurability
clause required by `forceHomogeneousENorm` on positive time. -/
theorem compactHomogeneousPath_aestronglyMeasurable {s : ℝ}
    (hs : -3 / 2 < s) (hs0 : s < 0) {F : VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    AEStronglyMeasurable (compactHomogeneousPath hs hF hc) forceTimeMeasure := by
  have : SecondCountableTopologyEither ℝ (RealVectorSobolev s) :=
    ⟨Or.inl inferInstance⟩
  exact (compactHomogeneousPath_continuous hs hs0 hF hc).aestronglyMeasurable

end NSFormalization.Section4.I03
