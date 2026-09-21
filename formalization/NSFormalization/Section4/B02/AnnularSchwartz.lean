import NSFormalization.Section4.B02.Annular
import NSFormalization.Paper3.AngularFourierDilation
import NavierStokes.R3.CompactSchwartz
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# B02 unit 2: the Schwartz realization of a smooth annular datum (`annularSchwartz`)

This module builds the first two sub-lemmas of the spec field `annularSchwartz`
(`research/B02/Spec.lean:362-364`), the single remaining hypothesis of
`Section4/B02/Cutoff.lean`'s `spatialApproxHomogeneous_of`.  The manuscript step is
`paper/sections/04-whole-space.tex:241`:

> "Set `ĥ_n = |ξ| G_n`.  Again `h_n` is Schwartz and `h_n → h` in `Ḣ^{-1}`."

At order `s` the homogeneous weight is `Gᵢ ξ = ((‖ξ‖ ^ (-s) : ℝ) : ℂ) * g i ξ`
(byte-for-byte the weight appearing in `IsHomogeneousDatum`, `Cutoff.lean:246`),
`g i` being the smooth annular representative of the datum `W`.  The realized field
is the inverse angular Fourier transform of `Gᵢ`.  See `research/B02/U2_SPLIT.md` for
the full sub-lemma table; the remaining rows (reality, slice/homogeneous assembly)
are still open.

* **SL1** `contDiff_rpow_mul_of_annulus`: `Gᵢ` is `ContDiff ℝ ∞` with
  `HasCompactSupport`.  Smoothness of `‖·‖ ^ (-s)` away from the origin is why the
  inner radius must be positive; on the ball `‖ξ‖ < δ` the datum `g i` vanishes, so
  the product is smooth (and compactly supported) everywhere.
* **SL2** `exists_schwartz_angularFourier_eq`: a smooth compactly supported function
  is `angularFourier φ` for a (complex) Schwartz `φ`, obtained by inverting the
  Schwartz-level Fourier transform after the normalized angular dilation.
-/

noncomputable section

namespace NSFormalization.Section4.B02

open NSFormalization.Paper3
open NSFormalization.Source (angularFourier)
open NavierStokes.ProblemStatement (Space)
open NavierStokesR3.CompactSchwartz
open scoped ContDiff Topology FourierTransform

/-! ## SL1.  `Gᵢ = ‖ξ‖^(-s)·g` is smooth with compact support -/

/-- `research/B02/U2_SPLIT.md` SL1, `04-whole-space.tex:241`.  For `0 < δ`, if `g` is
smooth and supported in the closed annulus `δ ≤ ‖ξ‖ ≤ R`, then the homogeneous
weight `((‖ξ‖ ^ (-s) : ℝ) : ℂ) * g ξ` is smooth with compact support: `‖·‖ ^ (-s)`
is smooth off the origin, and `g` vanishes near the origin. -/
theorem contDiff_rpow_mul_of_annulus {s δ R : ℝ} (hδ : 0 < δ) {g : Space → ℂ}
    (hg : ContDiff ℝ ∞ g) (hsupp : tsupport g ⊆ closedFrequencyAnnulus δ R) :
    ContDiff ℝ ∞ (fun ξ : Space => ((‖ξ‖ ^ (-s) : ℝ) : ℂ) * g ξ) ∧
      HasCompactSupport (fun ξ : Space => ((‖ξ‖ ^ (-s) : ℝ) : ℂ) * g ξ) := by
  -- `g` has compact support: `tsupport g` is a closed subset of a closed ball.
  have hgcs : HasCompactSupport g := by
    apply IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Space) R)
      (isClosed_tsupport g)
    refine hsupp.trans ?_
    intro ξ hξ
    have hξ' : δ ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ R := hξ
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact hξ'.2
  refine ⟨?_, ?_⟩
  · -- Smoothness, pointwise.
    rw [contDiff_iff_contDiffAt]
    intro ξ₀
    by_cases hξ : ξ₀ = 0
    · -- Near the origin `g = 0`, so the product vanishes on a neighborhood.
      subst hξ
      have h0 : (0 : Space) ∉ tsupport g := by
        intro h
        have hmem : δ ≤ ‖(0 : Space)‖ ∧ ‖(0 : Space)‖ ≤ R := hsupp h
        rw [norm_zero] at hmem
        linarith [hmem.1]
      have hnhd : (tsupport g)ᶜ ∈ 𝓝 (0 : Space) :=
        (isClosed_tsupport g).isOpen_compl.mem_nhds h0
      have hzero : (fun ξ : Space => ((‖ξ‖ ^ (-s) : ℝ) : ℂ) * g ξ) =ᶠ[𝓝 (0 : Space)]
          (fun _ => (0 : ℂ)) := by
        filter_upwards [hnhd] with x hx
        rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
      exact contDiffAt_const.congr_of_eventuallyEq hzero
    · -- Off the origin, `‖·‖ ^ (-s)` is smooth, so the product is.
      have hnorm : ContDiffAt ℝ ∞ (fun ξ : Space => ‖ξ‖) ξ₀ := contDiffAt_norm ℝ hξ
      have hrpow : ContDiffAt ℝ ∞ (fun ξ : Space => (‖ξ‖ ^ (-s) : ℝ)) ξ₀ :=
        hnorm.rpow_const_of_ne (norm_pos_iff.mpr hξ).ne'
      have hrpowC : ContDiffAt ℝ ∞ (fun ξ : Space => ((‖ξ‖ ^ (-s) : ℝ) : ℂ)) ξ₀ := by
        have hcomp : ContDiffAt ℝ ∞
            (fun ξ : Space => Complex.ofRealCLM (‖ξ‖ ^ (-s) : ℝ)) ξ₀ :=
          Complex.ofRealCLM.contDiff.comp_contDiffAt ξ₀ hrpow
        simpa only [Complex.ofRealCLM_apply] using hcomp
      exact hrpowC.mul hg.contDiffAt
  · -- Compact support: the smooth weight times the compactly supported `g`.
    have hrw : (fun ξ : Space => ((‖ξ‖ ^ (-s) : ℝ) : ℂ) * g ξ)
        = (fun ξ : Space => ((‖ξ‖ ^ (-s) : ℝ) : ℂ)) * g := rfl
    rw [hrw]
    exact HasCompactSupport.mul_left hgcs

/-! ## SL2.  Inverting the angular Fourier transform on smooth compact data -/

/-- The normalized angular dilation is a left inverse of its inverse on the Schwartz
space: this is exactly the public `right_inv` field of the (public)
`schwartzAngularDilationEquiv` (`Paper3/AngularFourierDilation.lean:48-64`). -/
theorem schwartzAngularDilation_dilationInv (X : SchwartzMap Space ℂ) :
    schwartzAngularDilation (schwartzAngularDilationInv X) = X :=
  schwartzAngularDilationEquiv.right_inv X

/-- `research/B02/U2_SPLIT.md` SL2, `04-whole-space.tex:241` ("`h_n` is Schwartz").
Every smooth compactly supported `f : Space → ℂ` is the angular Fourier transform
`angularFourier φ` of a Schwartz function `φ`, obtained by inverting the
Schwartz-level Fourier transform `𝓕` after the normalized inverse dilation. -/
theorem exists_schwartz_angularFourier_eq {f : Space → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) :
    ∃ φ : SchwartzMap Space ℂ, ∀ ξ : Space, angularFourier (φ : Space → ℂ) ξ = f ξ := by
  refine ⟨𝓕⁻ (schwartzAngularDilationInv (ofCompactSupport f hf hc)), fun ξ => ?_⟩
  rw [← schwartzAngularDilation_fourier_apply, FourierTransform.fourier_fourierInv_eq,
    schwartzAngularDilation_dilationInv, ofCompactSupport_apply]

end NSFormalization.Section4.B02
