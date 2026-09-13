import Formal.R3ConjugationReflection
import Mathlib.Analysis.Fourier.LpSpace

/-!
# The Plancherel reality bridge on the `R³` `L²` velocity carrier

This file connects the physical realness predicate `IsR3RealVelocity` with the frequency-side
conjugate-symmetry predicate `IsR3ConjugateSymmetricVelocity` through the Plancherel `L²`
Fourier transform `MeasureTheory.Lp.fourierTransformₗᵢ`.

The chain is:

1. Schwartz-level conjugation and reflection, obtained from the generic
   `SchwartzMap.postcompCLM` (postcomposition with the fiber conjugation `r3CConjCLM`) and
   `SchwartzMap.compCLMOfContinuousLinearEquiv` (precomposition with `x ↦ -x`);
2. the pointwise Fourier–conjugation identity
   `𝓕 (fun x => conj (f x)) ξ = conj (𝓕 f (-ξ))`, proved by moving the real-linear isometry
   `r3CConj` through the Bochner integral and conjugating the character;
3. the exact `L²` intertwining `𝓕 (r3L2Conj g) = r3L2Reflect (r3L2Conj (𝓕 g))`, lifted from
   the Schwartz case by `SchwartzMap.toLp_fourier_eq`, Schwartz density in `L²`, and
   closedness of the agreement set;
4. the predicate equivalence: a coordinate is physically real if and only if its `L²` Fourier
   transform is conjugate-symmetric.

Scope guard: this is an exact statement about the carrier and the Plancherel transform. No
realness-preservation of the concrete Stokes/Leray/convection operators and no realness of
mild solutions is claimed here; those are the next gates.
-/

namespace MNS2

open MeasureTheory SchwartzMap FourierTransform
open scoped FourierTransform RealInnerProductSpace ComplexConjugate ENNReal

noncomputable section

/-! ## Schwartz-level conjugation and reflection -/

/-- Schwartz conjugation: postcomposition with the fiber conjugation. -/
def r3SchwartzConjCLM : 𝓢(R3, R3C) →L[ℝ] 𝓢(R3, R3C) :=
  SchwartzMap.postcompCLM r3CConjCLM

@[simp]
theorem r3SchwartzConjCLM_apply (φ : 𝓢(R3, R3C)) (x : R3) :
    r3SchwartzConjCLM φ x = r3CConj (φ x) :=
  rfl

/-- Schwartz reflection: precomposition with `x ↦ -x`. -/
def r3SchwartzReflectCLM : 𝓢(R3, R3C) →L[ℝ] 𝓢(R3, R3C) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (ContinuousLinearEquiv.neg ℝ)

@[simp]
theorem r3SchwartzReflectCLM_apply (φ : 𝓢(R3, R3C)) (x : R3) :
    r3SchwartzReflectCLM φ x = φ (-x) :=
  rfl

/-! ## The pointwise Fourier–conjugation identity -/

/-- Fiber conjugation is `ℂ`-antilinear. -/
theorem r3CConj_smul (c : ℂ) (v : R3C) : r3CConj (c • v) = conj c • r3CConj v := by
  ext i
  simp [smul_eq_mul, map_mul]

/-- The pointwise Fourier–conjugation identity: the Fourier integral of the conjugate is the
reflected conjugate of the Fourier integral. -/
theorem r3Fourier_conj_eq (f : R3 → R3C) (ξ : R3) :
    𝓕 (fun x => r3CConj (f x)) ξ = r3CConj (𝓕 f (-ξ)) := by
  have key : ∀ v : R3, 𝐞 (-⟪v, ξ⟫) • r3CConj (f v) =
      r3CConj.toLinearIsometry (𝐞 (-⟪v, (-ξ : R3)⟫) • f v) := by
    intro v
    have hchar : conj ((𝐞 (⟪v, ξ⟫) : Circle) : ℂ) = ((𝐞 (-⟪v, ξ⟫) : Circle) : ℂ) := by
      rw [← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv]
    have hinner : -⟪v, (-ξ : R3)⟫ = ⟪v, ξ⟫ := by
      rw [inner_neg_right, neg_neg]
    rw [hinner]
    calc
      𝐞 (-⟪v, ξ⟫) • r3CConj (f v)
          = ((𝐞 (-⟪v, ξ⟫) : Circle) : ℂ) • r3CConj (f v) := Circle.smul_def _ _
      _ = conj ((𝐞 (⟪v, ξ⟫) : Circle) : ℂ) • r3CConj (f v) := by rw [hchar]
      _ = r3CConj (((𝐞 (⟪v, ξ⟫) : Circle) : ℂ) • f v) := (r3CConj_smul _ _).symm
      _ = r3CConj (𝐞 (⟪v, ξ⟫) • f v) := by rw [← Circle.smul_def]
      _ = r3CConj.toLinearIsometry (𝐞 (⟪v, ξ⟫) • f v) := rfl
  calc
    𝓕 (fun x => r3CConj (f x)) ξ
        = ∫ v, 𝐞 (-⟪v, ξ⟫) • r3CConj (f v) := Real.fourier_eq _ _
    _ = ∫ v, r3CConj.toLinearIsometry (𝐞 (-⟪v, (-ξ : R3)⟫) • f v) :=
        integral_congr_ae (Filter.Eventually.of_forall key)
    _ = r3CConj.toLinearIsometry (∫ v, 𝐞 (-⟪v, (-ξ : R3)⟫) • f v) :=
        LinearIsometry.integral_comp_comm _ _
    _ = r3CConj (𝓕 f (-ξ)) := by
        rw [Real.fourier_eq]
        rfl

/-- The Schwartz-level Fourier–conjugation identity. -/
theorem fourier_r3SchwartzConjCLM (φ : 𝓢(R3, R3C)) :
    𝓕 (r3SchwartzConjCLM φ) = r3SchwartzReflectCLM (r3SchwartzConjCLM (𝓕 φ)) :=
  SchwartzMap.ext fun ξ => r3Fourier_conj_eq (⇑φ) ξ

/-! ## `toLp` compatibility of the carrier involutions -/

theorem r3L2Conj_toLp (φ : 𝓢(R3, R3C)) :
    r3L2Conj (φ.toLp 2) = (r3SchwartzConjCLM φ).toLp 2 := by
  refine Lp.ext ?_
  have h1 := coeFn_r3L2Conj (φ.toLp 2)
  have h2 : (fun x => r3CConj ((φ.toLp 2) x)) =ᵐ[volume] fun x => r3CConj (φ x) := by
    filter_upwards [φ.coeFn_toLp 2 volume] with x hx
    rw [hx]
  have h3 : (r3SchwartzConjCLM φ).toLp 2 =ᵐ[volume] fun x => r3CConj (φ x) :=
    (r3SchwartzConjCLM φ).coeFn_toLp 2 volume
  exact h1.trans (h2.trans h3.symm)

theorem r3L2Reflect_toLp (φ : 𝓢(R3, R3C)) :
    r3L2Reflect (φ.toLp 2) = (r3SchwartzReflectCLM φ).toLp 2 := by
  refine Lp.ext ?_
  have h1 := coeFn_r3L2Reflect (φ.toLp 2)
  have h2 : ∀ᵐ x : R3 ∂(volume : Measure R3), (φ.toLp 2 volume) (-x) = φ (-x) :=
    r3MeasurePreserving_neg.quasiMeasurePreserving.ae
      (φ.coeFn_toLp 2 (volume : Measure R3))
  have h3 := (r3SchwartzReflectCLM φ).coeFn_toLp 2 (volume : Measure R3)
  filter_upwards [h1, h2, h3] with x e1 e2 e3
  rw [e1, e2, e3]
  rfl

/-! ## The `L²` bridge -/

/-- The Plancherel `L²` Fourier transform intertwines pointwise conjugation with
reflected conjugation.  This is the exact `L²` form of `𝓕 (conj f) = conj (𝓕 f (-·))`. -/
theorem fourier_r3L2Conj (g : R3L2Velocity) :
    𝓕 (r3L2Conj g) = r3L2Reflect (r3L2Conj (𝓕 g)) := by
  set P := fun g : R3L2Velocity => 𝓕 (r3L2Conj g) = r3L2Reflect (r3L2Conj (𝓕 g)) with hP
  apply DenseRange.induction_on (p := P)
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) g
  · apply isClosed_eq
    · exact continuous_fourier.comp r3L2Conj.continuous
    · exact r3L2Reflect.continuous.comp (r3L2Conj.continuous.comp continuous_fourier)
  · intro φ
    simp only [hP, SchwartzMap.toLpCLM_apply]
    rw [r3L2Conj_toLp, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq,
      r3L2Conj_toLp, r3L2Reflect_toLp, fourier_r3SchwartzConjCLM]

/-- A coordinate is physically real iff its `L²` Fourier transform is conjugate-symmetric. -/
theorem isR3RealVelocity_iff_fourier_conjugateSymmetric (g : R3L2Velocity) :
    IsR3RealVelocity g ↔ IsR3ConjugateSymmetricVelocity (𝓕 g) := by
  constructor
  · intro h
    unfold IsR3ConjugateSymmetricVelocity
    rw [← fourier_r3L2Conj, show r3L2Conj g = g from h]
  · intro h
    have hb : 𝓕 (r3L2Conj g) = 𝓕 g := by
      rw [fourier_r3L2Conj]
      exact h
    exact (Lp.fourierTransformₗᵢ R3 R3C).injective hb

/-- Restatement of the reality bridge with the explicit Plancherel isometry, matching the
operator form used elsewhere in this repository. -/
theorem isR3RealVelocity_iff_fourierTransform_conjugateSymmetric (g : R3L2Velocity) :
    IsR3RealVelocity g ↔
      IsR3ConjugateSymmetricVelocity (Lp.fourierTransformₗᵢ R3 R3C g) :=
  isR3RealVelocity_iff_fourier_conjugateSymmetric g

end

end MNS2
