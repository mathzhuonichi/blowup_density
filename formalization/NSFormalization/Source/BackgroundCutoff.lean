import NSFormalization.Source.Insertion

/-!
# Compact divergence-free background removal

This is the cutoff part of `lem:potential` in both manuscripts. The potential
is a concrete smooth vector field whose curl is the reference velocity.
The separate radial homotopy module constructs such a potential.
-/

noncomputable section

namespace NSFormalization.Source

open NavierStokes NavierStokes.ProblemStatement Set Filter
open scoped ContDiff Topology

/-- The negative curl of the cut potential, as in both papers. -/
def cutoffCorrection (χ : Space → ℝ) (A : Space → Space) : Space → Space :=
  fun x => - SpatialCurl.curl (fun y => χ y • A y) x

theorem curl_neg (A : Space → Space) (x : Space) :
    SpatialCurl.curl (fun y => -A y) x = -SpatialCurl.curl A x := by
  simp [SpatialCurl.curl, fderiv_fun_neg]

theorem cutoffCorrection_as_curl (χ : Space → ℝ) (A : Space → Space) :
    cutoffCorrection χ A = SpatialCurl.curl (fun y => -(χ y • A y)) := by
  funext x
  exact (curl_neg _ x).symm

theorem cutoffCorrection_smooth (χ : Space → ℝ) (A : Space → Space)
    (hχ : ContDiff ℝ ∞ χ) (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (cutoffCorrection χ A) := by
  rw [cutoffCorrection_as_curl]
  exact SpatialCurl.contDiff_curl (hχ.smul hA).neg (by simp)

theorem cutoffCorrection_divergence (χ : Space → ℝ) (A : Space → Space)
    (x : Space) (hχ : ContDiffAt ℝ 2 χ x) (hA : ContDiffAt ℝ 2 A x) :
    spatialDivergence (fun z => cutoffCorrection χ A z.2) 0 x = 0 := by
  rw [cutoffCorrection_as_curl]
  exact SpatialCurl.divergence_curl (hχ.smul hA).neg

theorem cutoffCorrection_support (χ : Space → ℝ) (A : Space → Space) :
    tsupport (cutoffCorrection χ A) ⊆ tsupport χ := by
  apply closure_minimal _ (isClosed_tsupport χ)
  intro x hx
  by_contra hnot
  have hc : SpatialCurl.curl (fun y => χ y • A y) x = 0 :=
    SpatialCurl.curl_eq_zero_of_not_mem_tsupport
      (fun h => hnot ((tsupport_smul_subset_left χ A) h))
  exact hx (by simp [cutoffCorrection, hc])

theorem cutoffCorrection_compact (χ : Space → ℝ) (A : Space → Space)
    (hχ : HasCompactSupport χ) : HasCompactSupport (cutoffCorrection χ A) :=
  hχ.of_isClosed_subset (isClosed_tsupport _) (cutoffCorrection_support χ A)

theorem cutoffCorrection_eq_neg (χ : Space → ℝ) (A v : Space → Space)
    (x : Space) (hχ : ∀ᶠ y in 𝓝 x, χ y = 1)
    (hA : SpatialCurl.curl A x = v x) :
    cutoffCorrection χ A x = -v x := by
  rw [cutoffCorrection, SpatialCurl.curl_cutoff_eq hχ, hA]

/-- Equality on an open cutoff plateau gives the full zero germ needed to
cancel both cross-advection terms, rather than just pointwise zero. -/
theorem background_removed_on_open (χ : Space → ℝ) (A v : Space → Space)
    (O : Set Space) (hO : IsOpen O) (hχ : EqOn χ (fun _ => 1) O)
    (hA : EqOn (SpatialCurl.curl A) v O) :
    ∀ x ∈ O, ∀ᶠ y in 𝓝 x, v y + cutoffCorrection χ A y = 0 := by
  intro x hx
  filter_upwards [hO.mem_nhds hx] with y hy
  have hχy : ∀ᶠ z in 𝓝 y, χ z = 1 := by
    filter_upwards [hO.mem_nhds hy] with z hz
    exact hχ hz
  rw [cutoffCorrection_eq_neg χ A v y hχy (hA hy)]
  exact add_neg_cancel _

/-- The cutoff removes an arbitrary smooth background without creating
divergence. This is the spatial operation used before packet insertion. -/
theorem corrected_background_divergence (χ : Space → ℝ) (A v : Space → Space)
    (hχ : ContDiff ℝ ∞ χ) (hA : ContDiff ℝ ∞ A)
    (hv : Differentiable ℝ v)
    (hdiv : ∀ x, spatialDivergence (fun z => v z.2) 0 x = 0) (x : Space) :
    spatialDivergence (fun z => v z.2 + cutoffCorrection χ A z.2) 0 x = 0 := by
  rw [ResidualCalculus.spatialDivergence_add _ _ 0 x (hv x)
    ((cutoffCorrection_smooth χ A hχ hA).differentiable (by simp) x), hdiv x,
    cutoffCorrection_divergence χ A x (hχ.contDiffAt.of_le (by simp))
      (hA.contDiffAt.of_le (by simp)), zero_add]

end NSFormalization.Source
