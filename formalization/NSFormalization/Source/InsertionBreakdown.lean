import NSFormalization.Source.SmoothLifespan
import NSFormalization.Source.BoundedViscosityUniqueness

/-! Exact insertion rules out every actual continued classical flow. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace NSFormalization.Source.SmoothLifespan
open NavierStokes.ProblemStatement
open NavierStokesR3.ProblemStatement (UniformFiniteEnergy)
open InsertionFamily

/-- Comparison with a hypothetical continued solution turns localized packet
blowup into a statement about all actual solution horizons, not just the
displayed singular trajectory. No local existence theorem is assumed. -/
theorem insertion_has_no_extension {ν r T τ R S : ℝ} {x₀ : Space}
    {a : Space → Space} {g V G : VelocityField} {Q : PressureField}
    (hν : 0 < ν) (hT : 0 < T) (hτ : 0 ≤ τ) (hTR : T < R) (hTS : T < S)
    (U : Flow ν a g R)
    (h : InsertionProperties ν U.velocity U.pressure g x₀ r T τ V Q G) :
    IsEmpty (Flow ν a (g + G) S) := by
  refine ⟨fun W => ?_⟩
  have hvT : ContDiffOn ℝ ∞ U.velocity (Ico (0 : ℝ) T ×ˢ univ) :=
    U.velocity_smooth.mono (fun _ hz => ⟨⟨hz.1.1, hz.1.2.trans hTR⟩, hz.2⟩)
  have henergy : ∀ b ∈ Ioo (0 : ℝ) T, UniformFiniteEnergy (Icc (0 : ℝ) b) V :=
    fun b hb => insertion_energy_on_slab hb.2 hvT
      (U.energy b ⟨hb.1.le, hb.2.trans hTR⟩) h
  obtain ⟨hVs, hQs, _, _, _, _, hdiv, hNS, _, hlocal, hearly⟩ := h
  have heq : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, W.velocity (t, x) = V (t, x) := by
    intro b hb
    have hbS : b < S := hb.2.trans hTS
    have hsub : Icc (0 : ℝ) b ×ˢ (univ : Set Space) ⊆ Ico (0 : ℝ) T ×ˢ univ :=
      fun _ hz => ⟨⟨hz.1.1, hz.1.2.trans_lt hb.2⟩, hz.2⟩
    obtain ⟨B, hB, hBound⟩ := W.velocity_bound b ⟨hb.1.le, hbS⟩
    obtain ⟨D, hD, hDeriv⟩ := W.derivative_bound b ⟨hb.1.le, hbS⟩
    have hc := BoundedViscosityUniqueness.classical_uniqueness_on_Icc hb.1 hν
      (W.velocity_smooth_slab hbS) (hVs.mono hsub)
      (W.pressure_smooth_slab hbS) (hQs.mono hsub)
      (W.energy b ⟨hb.1.le, hbS⟩) (henergy b hb) hB hBound hD hDeriv
      (fun t ht => W.divergence t ⟨ht.1.le, ht.2.trans hbS⟩)
      (fun t ht => hdiv t ⟨ht.1.le, ht.2.trans hb.2⟩)
      (fun t ht x => (W.equation t ⟨ht.1, ht.2.trans hbS⟩ x).trans
        (hNS t ⟨ht.1, ht.2.trans hb.2⟩ x).symm)
      (fun x => (W.initial x).trans
        ((hearly 0 hτ x).1.trans (U.initial x)).symm)
    exact hc b ⟨hb.1.le, le_rfl⟩
  let d := min T (S - T) / 2
  have hd : 0 < d := div_pos (lt_min hT (sub_pos.mpr hTS)) (by norm_num)
  have hdT : d ≤ T / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hdS : d ≤ (S - T) / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  apply LocalizedBlowup.no_continuous_continuation (isCompact_closedBall x₀ r) hlocal
  refine ⟨d, hd, W.velocity, W.velocity_smooth.continuousOn.mono ?_, ?_⟩
  · intro z hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, mem_univ _⟩
  · intro t ht _ x _
    exact heq t ht x

theorem insertion_lifespan_le {ν r T τ R : ℝ} {x₀ : Space}
    {a : Space → Space} {g V G : VelocityField} {Q : PressureField}
    (hν : 0 < ν) (hT : 0 < T) (hτ : 0 ≤ τ) (hTR : T < R)
    (U : Flow ν a g R)
    (h : InsertionProperties ν U.velocity U.pressure g x₀ r T τ V Q G) :
    lifespan ν a (g + G) ≤ ENNReal.ofReal T := by
  rw [lifespan_le_iff_no_extension hT.le]
  exact fun _ hTS => insertion_has_no_extension hν hT hτ hTR hTS U h

/-- The actual inserted flow attains exactly the insertion lifespan. -/
theorem insertion_lifespan_eq {ν r T τ R : ℝ} {x₀ : Space}
    {a : Space → Space} {g V G : VelocityField} {Q : PressureField}
    (hν : 0 < ν) (hT : 0 < T) (hτ : 0 ≤ τ) (hTR : T < R)
    (U : Flow ν a g R)
    (h : InsertionProperties ν U.velocity U.pressure g x₀ r T τ V Q G) :
    lifespan ν a (g + G) = ENNReal.ofReal T :=
  le_antisymm (insertion_lifespan_le hν hT hτ hTR U h)
    (horizon_le_lifespan (insertionFlow hT hτ hTR U h))

end NSFormalization.Source.SmoothLifespan
