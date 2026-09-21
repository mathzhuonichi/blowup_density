import NSFormalization.Paper1.TimeExtension
import NSFormalization.Paper1.CorrectionProfile
import NSFormalization.Source.Insertion

/-!
# I02, units 1-2: from a slab-regular reference to the global-in-time lemmas

Every correction lemma in `Paper1`/`Source` assumes `ContDiff ℝ ∞ v` on all of
spacetime, while `paper/sections/03-torus.tex:164` only gives the reference on
`[0,T+δ]`.  The bridge is purely slicewise: the radial potential, the localized
correction and the correction force at physical time `t` use the reference only
through its slice `v(t,·)`.  Two congruence lemmas and one local truncation
therefore remove the mismatch, with no re-proof of any estimate.
-/

noncomputable section

namespace NSFormalization.Section4.I02

open NavierStokes NavierStokes.ProblemStatement Set Filter
open NSFormalization.Paper1
open scoped ContDiff Topology

/-- The radial potential at one physical time uses only that time slice. -/
theorem timePotential_congr_slice (v V : VelocityField) (x₀ : Space) (z : SpaceTime)
    (h : ∀ y : Space, v (z.1, y) = V (z.1, y)) :
    RadialPotential.timePotential v x₀ z = RadialPotential.timePotential V x₀ z := by
  have hf : (fun y : Space => v (z.1, y)) = fun y : Space => V (z.1, y) := funext h
  simp only [RadialPotential.timePotential, hf]

/-- The localized correction at one physical time uses only that time slice of
the reference: the curl is spatial and the potential is slicewise. -/
theorem localCorrection_congr_slice (v V : VelocityField) (x₀ : Space)
    (χ : Space → ℝ) (η : ℝ → ℝ) (z : SpaceTime)
    (h : ∀ y : Space, v (z.1, y) = V (z.1, y)) :
    localCorrection v x₀ χ η z = localCorrection V x₀ χ η z := by
  have hf : (fun y : Space => (η z.1 * χ y) • RadialPotential.timePotential v x₀ (z.1, y)) =
      fun y : Space => (η z.1 * χ y) • RadialPotential.timePotential V x₀ (z.1, y) := by
    funext y
    rw [timePotential_congr_slice v V x₀ (z.1, y) h]
  show -SpatialCurl.curl
      (fun y : Space => (η z.1 * χ y) • RadialPotential.timePotential v x₀ (z.1, y)) z.2 = _
  rw [hf]
  rfl

/-- The same statement for the rescaled cutoffs of `eq:cutoff`. -/
theorem physicalCorrection_congr_slice (v V : VelocityField) (x₀ : Space) (T : ℝ)
    (θ : Space → ℝ) (η : ℝ → ℝ) (ε : ℝ) (z : SpaceTime)
    (h : ∀ y : Space, v (z.1, y) = V (z.1, y)) :
    CorrectionProfile.physicalCorrection v x₀ T θ η ε z =
      CorrectionProfile.physicalCorrection V x₀ T θ η ε z :=
  localCorrection_congr_slice v V x₀ _ _ z h

/-- The correction force at one physical time uses the reference only through
that time slice; the two remaining terms differentiate the correction. -/
theorem correctionForce_congr_slice (ν : ℝ) (v V w : VelocityField) (z : SpaceTime)
    (h : ∀ y : Space, v (z.1, y) = V (z.1, y)) :
    Source.correctionForce ν v w z = Source.correctionForce ν V w z := by
  have hf : (fun y : Space => v (z.1, y)) = fun y : Space => V (z.1, y) := funext h
  have hz : v z = V z := by
    have := h z.2
    simpa using this
  simp only [Source.correctionForce, spatialDerivative, hf, hz]

/-- A reference smooth on an open time slab is, near each of its times, the
restriction of a globally smooth field.  This is `timeTruncation` at a bump
centred on the requested time. -/
theorem exists_local_truncation {v : VelocityField} {I : Set ℝ} (hI : IsOpen I)
    (hv : ContDiffOn ℝ ∞ v (I ×ˢ (univ : Set Space))) {t : ℝ} (ht : t ∈ I) :
    ∃ V : VelocityField, ∃ ρ : ℝ, 0 < ρ ∧ ContDiff ℝ ∞ V ∧
      ∀ s ∈ Ioo (t - ρ) (t + ρ), ∀ y : Space, V (s, y) = v (s, y) := by
  obtain ⟨c, hc, hball⟩ := Metric.isOpen_iff.mp hI t ht
  have hsub : Ioo (t - 2 * (c / 2)) (t + 2 * (c / 2)) ⊆ I := by
    have hcc : 2 * (c / 2) = c := by ring
    rw [hcc, ← Real.ball_eq_Ioo]
    exact hball
  obtain ⟨η, hη, _hηc, hηone, hηsupp⟩ := exists_temporal_cutoff t (c / 2) (by linarith)
  refine ⟨timeTruncation v η, c / 2, by linarith,
    timeTruncation_smooth hI hv hη (hηsupp.trans hsub), ?_⟩
  intro s hs y
  exact timeTruncation_eq v η (hηone ⟨hs.1.le, hs.2.le⟩) y

/-- The radial potential inherits the slab regularity of its reference.  This is
the `ContDiffOn` companion of `RadialPotential.timePotential_contDiff`, which
the whole `Paper1` chain lacks. -/
theorem timePotential_contDiffOn {v : VelocityField} {I : Set ℝ} (hI : IsOpen I)
    (hv : ContDiffOn ℝ ∞ v (I ×ˢ (univ : Set Space))) (x₀ : Space) :
    ContDiffOn ℝ ∞ (RadialPotential.timePotential v x₀) (I ×ˢ (univ : Set Space)) := by
  intro z hz
  obtain ⟨V, ρ, hρ, hV, heq⟩ := exists_local_truncation hI hv hz.1
  have hnb : Ioo (z.1 - ρ) (z.1 + ρ) ×ˢ (univ : Set Space) ∈ 𝓝 z :=
    prod_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)) univ_mem
  have hcong : RadialPotential.timePotential v x₀ =ᶠ[𝓝 z]
      RadialPotential.timePotential V x₀ := by
    filter_upwards [hnb] with p hp
    exact timePotential_congr_slice v V x₀ p (fun y => (heq p.1 hp.1 y).symm)
  exact ((RadialPotential.timePotential_contDiff hV x₀).contDiffAt.congr_of_eventuallyEq
    hcong).contDiffWithinAt

/-- The curl identity `eq:potential` needs no extension at all: both hypotheses
of `RadialPotential.curl_centeredPotential` are slicewise. -/
theorem spatialCurl_timePotential_on {v : VelocityField} {I : Set ℝ}
    (hv : ContDiffOn ℝ ∞ v (I ×ˢ (univ : Set Space)))
    (hdiv : ∀ t ∈ I, ∀ x : Space, spatialDivergence v t x = 0) (x₀ : Space)
    {t : ℝ} (ht : t ∈ I) (x : Space) :
    SpatialCurl.curl (fun y : Space => RadialPotential.timePotential v x₀ (t, y)) x =
      v (t, x) := by
  have hs : ContDiff ℝ ∞ (fun y : Space => v (t, y)) :=
    SpatialCurl.contDiff_spatialSlice hv ht
  exact RadialPotential.curl_centeredPotential hs (hdiv t ht) x₀ x

end NSFormalization.Section4.I02
