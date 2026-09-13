import NavierStokes.R3ConvolutionYoung

/-!
# Constant-one Young convolution adapters

The analytic estimate and almost-everywhere existence are reused from the
OpenAI source `NavierStokes.R3ConvolutionYoung`. These adapters expose the
`L1 * L2 → L2` order needed by the weighted Fourier tame estimate, for real
or complex measurable representatives. No support restriction is imposed.
-/
noncomputable section
open MeasureTheory Filter NavierStokes.ProblemStatement
open scoped ENNReal
namespace NSFormalization.Source.YoungConvolution
open NavierStokes.R3ConvolutionYoung

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Commutativity of the actual scalar convolution integral. -/
theorem scalarConvolution_comm (f g : Space → 𝕜) :
    scalarConvolution f g = scalarConvolution g f := by
  funext x
  unfold scalarConvolution
  rw [← integral_sub_left_eq_self (fun y : Space => f y * g (x - y)) volume x]
  simp only [sub_sub_cancel, mul_comm]

/-- Extended-norm Young inequality with constant one in `L1 * L2` order. -/
theorem eLpNorm_convolution_one_two {a b : Space → 𝕜}
    (ha : Measurable a) (hb : Measurable b) :
    eLpNorm (scalarConvolution a b) 2 volume ≤
      eLpNorm a 1 volume * eLpNorm b 2 volume := by
  rw [scalarConvolution_comm a b, mul_comm]
  exact eLpNorm_scalarConvolution_two_one hb ha

/-- Both actual convolution existence and L2 membership, with the sharp
constant-one real-valued norm bound. -/
theorem convolution_one_two {a b : Space → 𝕜}
    (ha : Measurable a) (hb : Measurable b)
    (ha₁ : MemLp a 1 volume) (hb₂ : MemLp b 2 volume) :
    (∀ᵐ x ∂volume, Integrable (fun y : Space => a y * b (x - y)) volume) ∧
    MemLp (scalarConvolution a b) 2 volume ∧
    (eLpNorm (scalarConvolution a b) 2 volume).toReal ≤
      (eLpNorm a 1 volume).toReal * (eLpNorm b 2 volume).toReal := by
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [ae_integrable_two_one hb ha hb₂ ha₁] with x hx
    have H := hx.comp_sub_left x
    simpa only [sub_sub_cancel, mul_comm] using H
  · rw [scalarConvolution_comm a b]
    exact scalarConvolution_memLp_two_one hb ha hb₂ ha₁
  · have H := ENNReal.toReal_mono
      (ne_of_lt (ENNReal.mul_lt_top ha₁.2 hb₂.2))
      (eLpNorm_convolution_one_two ha hb)
    simpa only [ENNReal.toReal_mul] using H

/-- Changes of representatives preserve the integrand almost everywhere at
 every output point, by translation invariance. -/
theorem integrand_congr_ae {a a' b b' : Space → 𝕜}
    (ha : a =ᵐ[volume] a') (hb : b =ᵐ[volume] b') (x : Space) :
    (fun y => a y * b (x - y)) =ᵐ[volume] (fun y => a' y * b' (x - y)) := by
  exact ha.mul (hb.comp_tendsto
    (quasiMeasurePreserving_sub_left_of_right_invariant volume x).tendsto_ae)

/-- Young's inequality for arbitrary L1 and L2 representatives. Measurability
 is supplied by `MemLp`; no pointwise measurable representative is assumed. -/
theorem memLp_convolution_one_two {a b : Space → 𝕜}
    (ha₁ : MemLp a 1 volume) (hb₂ : MemLp b 2 volume) :
    (∀ᵐ x ∂volume, Integrable (fun y : Space => a y * b (x - y)) volume) ∧
    MemLp (scalarConvolution a b) 2 volume ∧
    (eLpNorm (scalarConvolution a b) 2 volume).toReal ≤
      (eLpNorm a 1 volume).toReal * (eLpNorm b 2 volume).toReal := by
  let a' := ha₁.1.mk a
  let b' := hb₂.1.mk b
  have ha : a =ᵐ[volume] a' := ha₁.1.ae_eq_mk
  have hb : b =ᵐ[volume] b' := hb₂.1.ae_eq_mk
  have H := convolution_one_two ha₁.1.measurable_mk hb₂.1.measurable_mk
    ((memLp_congr_ae ha).mp ha₁) ((memLp_congr_ae hb).mp hb₂)
  have hc : scalarConvolution a b = scalarConvolution a' b' := by
    funext x
    exact integral_congr_ae (integrand_congr_ae ha hb x)
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [H.1] with x hx
    exact hx.congr (integrand_congr_ae ha hb x).symm
  · rw [hc]
    exact H.2.1
  · rw [hc, eLpNorm_congr_ae ha, eLpNorm_congr_ae hb]
    exact H.2.2

/-- The integral-norm interface used with quantitative Fourier L1 control. -/
theorem integrable_convolution_one_two {a b : Space → 𝕜}
    (ha : Integrable a volume) (hb : MemLp b 2 volume) :
    (∀ᵐ x ∂volume, Integrable (fun y : Space => a y * b (x - y)) volume) ∧
    MemLp (scalarConvolution a b) 2 volume ∧
    (eLpNorm (scalarConvolution a b) 2 volume).toReal ≤
      (∫ y : Space, ‖a y‖) * (eLpNorm b 2 volume).toReal := by
  have H := memLp_convolution_one_two (memLp_one_iff_integrable.mpr ha) hb
  simpa only [eLpNorm_one_eq_lintegral_enorm,
    ← integral_norm_eq_lintegral_enorm ha.aestronglyMeasurable] using H

end NSFormalization.Source.YoungConvolution
