import NSFormalization.Paper3.SeparatedBochnerDensity
import NSFormalization.Paper3.CompactSobolevTime

/-!
# Actual physical compact spacetime smooth density

Finite separated-variable sums are realized as original compact smooth physical
functions. Density is inherited from the previous Mathlib-based span adapter.
-/
noncomputable section
namespace NSFormalization.Paper3
open Set MeasureTheory NavierStokes.ProblemStatement
open scoped ContDiff ENNReal

 theorem compactSobolevTimeSlice_add (s : ℝ) {F G : ℝ × Space → ℂ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hFc : HasCompactSupport F) (hGc : HasCompactSupport G) (t : ℝ) :
    compactSobolevTimeSlice s (F + G) (hF.add hG) (hFc.add hGc) t =
      compactSobolevTimeSlice s F hF hFc t + compactSobolevTimeSlice s G hG hGc t := by
  change weightedFourierLp s _ = weightedFourierLp s _ + weightedFourierLp s _
  rw [← map_add]
  congr 1

 theorem compactSobolevTimeSlice_smul (s c : ℝ) {F : ℝ × Space → ℂ}
    (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F) (t : ℝ) :
    compactSobolevTimeSlice s (c • F) (hF.const_smul c) hFc.smul_left t =
      c • compactSobolevTimeSlice s F hF hFc t := by
  change weightedFourierLp s _ = c • weightedFourierLp s _
  rw [← map_smul]
  congr 1

/-- Genuine Bochner vectors admitting an original jointly smooth, physically
compact spacetime representative. -/
def physicalCompactBochner (s : ℝ) (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    Submodule ℝ (Lp (SobolevHilbert s) q (volume : Measure ℝ)) where
  carrier := {v | ∃ (F : ℝ × Space → ℂ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F), v =ᵐ[volume] compactSobolevTimeSlice s F hF hc}
  zero_mem' := by
    refine ⟨0, contDiff_const, HasCompactSupport.zero, ?_⟩
    filter_upwards [Lp.coeFn_zero (E := SobolevHilbert s) (p := q) (μ := (volume : Measure ℝ))] with t ht
    rw [ht]
    change 0 = weightedFourierLp s 0
    rw [map_zero]
  add_mem' := by
    rintro v w ⟨F, hF, hFc, hv⟩ ⟨G, hG, hGc, hw⟩
    refine ⟨F + G, hF.add hG, hFc.add hGc, ?_⟩
    filter_upwards [Lp.coeFn_add v w, hv, hw] with t ht hvt hwt
    rw [ht, Pi.add_apply, hvt, hwt, compactSobolevTimeSlice_add]
  smul_mem' := by
    rintro c v ⟨F, hF, hFc, hv⟩
    refine ⟨c • F, hF.const_smul c, hFc.smul_left, ?_⟩
    filter_upwards [Lp.coeFn_smul c v, hv] with t ht hvt
    rw [ht, Pi.smul_apply, hvt, compactSobolevTimeSlice_smul]

 theorem separated_physical_hasCompactSupport {a : ℝ → ℝ}
    (ha : HasCompactSupport a) {ψ : SchwartzMap Space ℂ}
    (hψ : HasCompactSupport (ψ : Space → ℂ)) :
    HasCompactSupport (fun z : ℝ × Space => a z.1 • ψ z.2) := by
  apply HasCompactSupport.of_support_subset_isCompact (ha.prod hψ)
  intro z hz
  constructor
  · apply subset_tsupport a
    intro hz0
    exact hz (by simp [hz0])
  · apply subset_tsupport (ψ : Space → ℂ)
    intro hz0
    exact hz (by simp [hz0])

 theorem separatedLp_mem_physicalCompactBochner (s : ℝ) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (ψ : SchwartzMap Space ℂ) (hψ : HasCompactSupport (ψ : Space → ℂ))
    (g : Lp ℝ q (volume : Measure ℝ)) (a : ℝ → ℝ)
    (hga : g =ᵐ[volume] a) (hac : HasCompactSupport a) (ha : ContDiff ℝ ∞ a) :
    separatedLp q (weightedFourierLp s ψ) g ∈ physicalCompactBochner s q := by
  let F : ℝ × Space → ℂ := fun z => a z.1 • ψ z.2
  have hF : ContDiff ℝ ∞ F := (ha.comp contDiff_fst).smul ((ψ.smooth ⊤).comp contDiff_snd)
  have hFc : HasCompactSupport F := separated_physical_hasCompactSupport hac hψ
  refine ⟨F, hF, hFc, ?_⟩
  filter_upwards [separatedLp_ae q (weightedFourierLp s ψ) g, hga] with t ht hgat
  rw [ht, hgat]
  change a t • weightedFourierLp s ψ = weightedFourierLp s _
  rw [← map_smul]
  congr 1

/-- For all real s and finite q≥1, actual physical C∞ compact spacetime
functions are dense in the complete Sobolev-valued Bochner Lq space. -/
theorem dense_physicalCompactBochner (s : ℝ) (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq : q ≠ ⊤) :
    Dense (physicalCompactBochner s q : Set (Lp (SobolevHilbert s) q (volume : Measure ℝ))) := by
  apply (dense_span_physical_separated_sobolev s q hq).mono
  apply Submodule.span_le.mpr
  rintro v ⟨h, ⟨ψ, hψ, rfl⟩, g, ⟨a, hga, hac, ha⟩, rfl⟩
  exact separatedLp_mem_physicalCompactBochner s q ψ hψ g a hga hac ha

/-- An explicit original physical compact smooth approximation to any Bochner
Sobolev datum, with error in the genuine completed Bochner norm. -/
theorem exists_physical_compact_smooth_approx (s : ℝ) (q : ℝ≥0∞)
    [Fact (1 ≤ q)] (hq : q ≠ ⊤) (f : Lp (SobolevHilbert s) q (volume : Measure ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (F : ℝ × Space → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F),
      ‖f - (memLp_compactSobolevTimeSlice s hF hc q).toLp
        (compactSobolevTimeSlice s F hF hc)‖ < ε := by
  obtain ⟨v, ⟨F, hF, hc, hv⟩, hdist⟩ :=
    Metric.mem_closure_iff.mp (dense_physicalCompactBochner s q hq f) ε hε
  refine ⟨F, hF, hc, ?_⟩
  have heq : v = (memLp_compactSobolevTimeSlice s hF hc q).toLp
      (compactSobolevTimeSlice s F hF hc) :=
    Lp.ext (hv.trans (memLp_compactSobolevTimeSlice s hF hc q).coeFn_toLp.symm)
  simpa only [dist_eq_norm, heq] using hdist

end NSFormalization.Paper3
