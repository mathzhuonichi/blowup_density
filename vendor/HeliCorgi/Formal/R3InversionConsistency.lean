import Formal.R3DecoderFrequencyBridge

/-!
# Inversion consistency of the physical representative (Clay edge 3b)

Edge 1b produced the explicit pointwise inverse-Fourier *integral* representative
`r3PhysicalRepresentative g = 𝓕⁻ g`, and edge 3a produced the `L²`-level decode
`r3Decoded3PhysicalVelocity f = 𝓕⁻ (r3Decoded3FrequencyL2 f)` together with its
identification with the carrier's tempered-distribution decoder. This file closes the gap
between the two inverse transforms — the `L¹ ∩ L²` inversion-consistency instance needed
here (no general theorem is claimed):

* `r3PhysicalRepresentative_ae_r3Decoded3PhysicalVelocity`:
  `r3PhysicalRepresentative (r3DecodedFrequency 3 f) =ᵐ[volume]
    (r3Decoded3PhysicalVelocity f : R3 → R3C)`.

No general `L¹ ∩ L²` Fourier-inversion library is built. The proof pairs both sides
against smooth compactly supported test functions and concludes by mathlib's
a.e.-uniqueness lemma `ae_eq_of_integral_contDiff_smul_eq`:

* the pointwise side is handled by the `L¹` multiplication formula
  (`VectorFourier.integral_fourierIntegral_smul_eq_flip`, self-adjointness of the
  Fourier integral);
* the `L²` side is handled through tempered distributions
  (`MeasureTheory.Lp.toTemperedDistribution_apply`,
  `MeasureTheory.Lp.fourierInv_toTemperedDistribution_eq`,
  `TemperedDistribution.fourierInv_apply`);
* both land on the same frequency-side integral `∫ ξ, 𝓕⁻ ψ ξ • g ξ`.

Consequently, combined with edge 3a's `r3L2ToTempered_r3Decoded3PhysicalVelocity`, the
`C¹` everywhere classically divergence-free object of the edge-3a capstone is an a.e.
representative of the velocity decoded by the carrier's own Bessel decoder — stated as a
single Lean theorem in `r3DecodedFrequency_incompressible_ae_decoder` (the solenoidal
hypothesis there is the capstone's, not this file's main theorem's). No phantom Sobolev
inclusion is used; no rapid decay is claimed; edges 2 and 4 are untouched.
-/

namespace MNS2

open MeasureTheory FourierTransform
open scoped FourierTransform SchwartzMap ContDiff

noncomputable section

/-- Real scalars act on `R3C` as their complex coercions. -/
theorem r3RealSmul_eq_complexSmul (r : ℝ) (v : R3C) : r • v = ((r : ℝ) : ℂ) • v := by
  ext j
  simp [Complex.real_smul]

/-- The flip of the negated real inner pairing is itself. -/
theorem r3NegInner_flip :
    (-(innerₗ R3)).flip = -(innerₗ R3) := by
  ext x y
  simp [real_inner_comm]

theorem r3ContinuousNegInner :
    Continuous fun p : R3 × R3 => (-(innerₗ R3)) p.1 p.2 := by
  show Continuous fun p : R3 × R3 => -(inner ℝ p.1 p.2 : ℝ)
  exact continuous_inner.neg

/-- The pointwise inverse Fourier integral of an integrable frequency profile is
continuous. -/
theorem continuous_r3PhysicalRepresentative {g : R3 → R3C}
    (hg : Integrable g volume) :
    Continuous (r3PhysicalRepresentative g) := by
  unfold r3PhysicalRepresentative
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    r3ContinuousNegInner hg

/-- **The `L¹` multiplication formula for the inverse transform**: pairing a Schwartz test
function against the pointwise inverse Fourier integral moves the transform to the test
side. -/
theorem integral_smul_r3PhysicalRepresentative {g : R3 → R3C}
    (hg : Integrable g volume) (ψ : 𝓢(R3, ℂ)) :
    ∫ x : R3, ψ x • r3PhysicalRepresentative g x =
      ∫ ξ : R3, 𝓕⁻ (⇑ψ) ξ • g ξ := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (L := -(innerₗ R3)) (μ := (volume : Measure R3))
    (ν := (volume : Measure R3)) (f := ⇑ψ) (g := g)
    Real.continuous_fourierChar r3ContinuousNegInner ψ.integrable hg
  rw [r3NegInner_flip] at h
  exact h.symm

/-- **The tempered pairing of the `L²` decode**: pairing a Schwartz test function against
the `L²` inverse transform gives the same frequency-side integral. -/
theorem integral_smul_r3Decoded3PhysicalVelocity (f : R3L2Velocity) (ψ : 𝓢(R3, ℂ)) :
    ∫ x : R3, ψ x • ((r3Decoded3PhysicalVelocity f : R3L2Velocity) : R3 → R3C) x =
      ∫ ξ : R3, 𝓕⁻ (⇑ψ) ξ • r3DecodedFrequency 3 f ξ := by
  calc ∫ x : R3, ψ x • ((r3Decoded3PhysicalVelocity f : R3L2Velocity) : R3 → R3C) x
      = ((r3Decoded3PhysicalVelocity f : R3L2Velocity) : 𝓢'(R3, R3C)) ψ :=
        (MeasureTheory.Lp.toTemperedDistribution_apply _ ψ).symm
    _ = (𝓕⁻ ((r3Decoded3FrequencyL2 f : R3L2Velocity) : 𝓢'(R3, R3C))) ψ := by
        unfold r3Decoded3PhysicalVelocity
        rw [MeasureTheory.Lp.fourierInv_toTemperedDistribution_eq]
    _ = ((r3Decoded3FrequencyL2 f : R3L2Velocity) : 𝓢'(R3, R3C)) (𝓕⁻ ψ) :=
        TemperedDistribution.fourierInv_apply _ ψ
    _ = ∫ ξ : R3, (𝓕⁻ ψ) ξ • ((r3Decoded3FrequencyL2 f : R3L2Velocity) : R3 → R3C) ξ :=
        MeasureTheory.Lp.toTemperedDistribution_apply _ _
    _ = ∫ ξ : R3, (𝓕⁻ ψ) ξ • r3DecodedFrequency 3 f ξ := by
        refine integral_congr_ae ?_
        unfold r3Decoded3FrequencyL2
        filter_upwards [MemLp.coeFn_toLp (memLp_two_r3DecodedFrequency f)] with ξ hξ
        rw [hξ]
    _ = ∫ ξ : R3, 𝓕⁻ (⇑ψ) ξ • r3DecodedFrequency 3 f ξ := by
        rw [SchwartzMap.fourierInv_coe]

/-- **Clay edge 3b: inversion consistency.** The explicit pointwise inverse-Fourier
integral representative of the decoded frequency data agrees almost everywhere with the
`L²` decode. Combined with edge 3a's tempered identification, the `C¹`, everywhere
classically divergence-free object of the edge-3a capstone is an a.e. representative of
the velocity decoded by the carrier's Bessel decoder. -/
theorem r3PhysicalRepresentative_ae_r3Decoded3PhysicalVelocity (f : R3L2Velocity) :
    r3PhysicalRepresentative (r3DecodedFrequency 3 f) =ᵐ[volume]
      ((r3Decoded3PhysicalVelocity f : R3L2Velocity) : R3 → R3C) := by
  have hh : Integrable (r3DecodedFrequency 3 f) volume := integrable_r3DecodedFrequency f
  have hloc1 : LocallyIntegrable (r3PhysicalRepresentative (r3DecodedFrequency 3 f))
      volume :=
    (continuous_r3PhysicalRepresentative hh).locallyIntegrable
  have hloc2 : LocallyIntegrable
      ((r3Decoded3PhysicalVelocity f : R3L2Velocity) : R3 → R3C) volume :=
    (Lp.memLp (r3Decoded3PhysicalVelocity f)).locallyIntegrable one_le_two
  refine ae_eq_of_integral_contDiff_smul_eq hloc1 hloc2 fun g g_diff g_supp => ?_
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := g_supp.comp_left rfl
  have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  have hψcoe : ⇑(hg₁.toSchwartzMap hg₂) = Complex.ofRealCLM ∘ g := rfl
  have hsmul₁ : ∀ (F : R3 → R3C),
      (∫ x : R3, g x • F x) = ∫ x : R3, (hg₁.toSchwartzMap hg₂) x • F x := by
    intro F
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    rw [hψcoe]
    exact r3RealSmul_eq_complexSmul (g x) (F x)
  rw [hsmul₁, hsmul₁,
    integral_smul_r3PhysicalRepresentative hh (hg₁.toSchwartzMap hg₂),
    integral_smul_r3Decoded3PhysicalVelocity f (hg₁.toSchwartzMap hg₂)]

/-- **Edges 3a + 3b, bundled**: for a solenoidal `L²` Bessel coordinate, the explicit
`C¹`, everywhere classically divergence-free representative is an a.e. representative of
the `L²` decode, whose tempered embedding is exactly the carrier's Bessel decoder. -/
theorem r3DecodedFrequency_incompressible_ae_decoder {f : R3L2Velocity}
    (hf : f ∈ r3L2SolenoidalSubmodule) :
    (ContDiff ℝ 1 (r3PhysicalRepresentative (r3DecodedFrequency 3 f)) ∧
      ∀ x : R3,
        r3ClassicalDivergence
          (r3PhysicalRepresentative (r3DecodedFrequency 3 f)) x = 0) ∧
      r3PhysicalRepresentative (r3DecodedFrequency 3 f) =ᵐ[volume]
        ((r3Decoded3PhysicalVelocity f : R3L2Velocity) : R3 → R3C) ∧
      r3L2ToTemperedCLM (r3Decoded3PhysicalVelocity f) = r3HsToTemperedCLM 3 f :=
  ⟨r3DecodedFrequency_incompressible hf,
    r3PhysicalRepresentative_ae_r3Decoded3PhysicalVelocity f,
    r3L2ToTempered_r3Decoded3PhysicalVelocity f⟩

end

end MNS2
