import NSFormalization.Section3.T22.CutoffDatum

/-!
Probe for T22 U-B3 (`Section3/T22/CutoffDatum.lean`).

1. `exists_cutoff` / `exists_cutoff_isOpen` instantiated on the concrete pair
   `Ω = ball 0 1`, `K = closedBall 0 (1/2)` in ℝ³.
2. The cutoff produced there is fed back into
   `isCutoffDatum_realizes_zeroExtension`, so the two units compose on a concrete
   geometry (the remaining hypotheses are the datum-layer ones U-Z1 supplies).
3. A non-vacuous closed instance of (b): the zero field, whose cutoff datum is the
   zero datum, really is a Sobolev datum of its own zero extension.
-/

noncomputable section

open Set MeasureTheory Filter Metric
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Paper3 (RealVectorSobolev angularRealization)
open NSFormalization.Source.RealSobolev (FourierData)
open NSFormalization.Section4.D01
open NSFormalization.Section4.A02 (SpatialField)
open scoped ContDiff ENNReal SchwartzMap Topology
open NSFormalization.Section3.T22

/-! ## 1. `exists_cutoff` on a concrete compact-in-open pair -/

def probeΩ : Set Space := ball (0 : Space) 1
def probeK : Set Space := closedBall (0 : Space) (1 / 2)

theorem probeΩ_isOpen : IsOpen probeΩ := isOpen_ball
theorem probeK_isCompact : IsCompact probeK := isCompact_closedBall _ _
theorem probeK_subset : probeK ⊆ probeΩ := closedBall_subset_ball (by norm_num)

example : ∃ χ : Space → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ probeΩ ∧
    (∀ᶠ x in 𝓝ˢ probeK, χ x = 1) :=
  exists_cutoff probeΩ_isOpen probeK_isCompact probeK_subset

example : ∃ χ : Space → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ probeΩ ∧
    ∃ V : Set Space, IsOpen V ∧ probeK ⊆ V ∧ ∀ x ∈ V, χ x = 1 :=
  exists_cutoff_isOpen probeΩ_isOpen probeK_isCompact probeK_subset

/-! ## 2. The concrete cutoff feeds `isCutoffDatum_realizes_zeroExtension` -/

theorem probeCutoff : ∃ χ : Space → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
    tsupport χ ⊆ probeΩ ∧ (∀ᶠ x in 𝓝ˢ probeK, χ x = 1) :=
  exists_cutoff probeΩ_isOpen probeK_isCompact probeK_subset

def probeχ : Space → ℝ := probeCutoff.choose

example (s : ℝ) (z : SpatialField) (A B : RealVectorSobolev s)
    (hcut : IsCutoffDatum s probeχ A B)
    (hA : restrictDatum probeΩ s A = restrictField probeΩ z)
    (hsupp : tsupport (zeroExtension probeΩ z) ⊆ probeK) :
    IsSobolevDatum s (zeroExtension probeΩ z) B :=
  isCutoffDatum_realizes_zeroExtension probeCutoff.choose_spec.1 probeCutoff.choose_spec.2.1
    probeCutoff.choose_spec.2.2.1 probeCutoff.choose_spec.2.2.2 hcut hA hsupp

/-! ## 3. A non-vacuous closed instance: the zero field -/

theorem zeroExtension_zero (Ω : Set Space) :
    zeroExtension Ω (fun _ => (0 : Space)) = fun _ => (0 : Space) := by
  funext x
  by_cases hx : x ∈ Ω <;> simp [zeroExtension, hx]

theorem isCutoffDatum_zero (s : ℝ) (χ : Space → ℝ) :
    IsCutoffDatum s χ (0 : RealVectorSobolev s) (0 : RealVectorSobolev s) := by
  intro i ψ
  simp

example (s : ℝ) (χ : Space → ℝ) (hχs : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ probeΩ) (hχ1 : ∀ᶠ x in 𝓝ˢ probeK, χ x = 1) :
    IsSobolevDatum s (zeroExtension probeΩ (fun _ => (0 : Space))) (0 : RealVectorSobolev s) := by
  refine isCutoffDatum_realizes_zeroExtension hχs hχc hχΩ hχ1 (isCutoffDatum_zero s χ) ?_ ?_
  · funext i ψ
    simp [restrictDatum, restrictField]
  · rw [zeroExtension_zero]
    simp [tsupport, Function.support]
