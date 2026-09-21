import Formal.R3LerayFourierBridge

namespace MNS2

noncomputable section

/-- The real frequency vector, embedded coordinatewise in the complex Fourier velocity fiber. -/
def r3FrequencyVectorComplex (ξ : R3) : R3C :=
  WithLp.toLp 2 (fun i : Fin 3 => ((ξ i : ℝ) : ℂ))

/--
At a fixed real frequency `ξ`, the complex divergence-free Fourier fiber is the complex plane
orthogonal to the embedded frequency vector.
-/
def r3ComplexSolenoidalFiber (ξ : R3) : Submodule ℂ R3C :=
  (ℂ ∙ r3FrequencyVectorComplex ξ)ᗮ

/--
The complex-linear Leray symbol acting on the actual `R3C` fiber used by the repository's
`L²(R³; ℂ³)` Fourier layer.

This closes the scalar-field mismatch between the earlier real fiber symbol and the complex
Plancherel carrier.  It is still a pointwise frequency-fiber operator; the `L²` multiplier
realization is a separate step.
-/
def r3LeraySymbolComplex (ξ : R3) : R3C →L[ℂ] R3C :=
  (r3ComplexSolenoidalFiber ξ).starProjection

@[simp]
theorem mem_r3ComplexSolenoidalFiber_iff_inner
    (ξ : R3) (v : R3C) :
    v ∈ r3ComplexSolenoidalFiber ξ ↔
      inner ℂ (r3FrequencyVectorComplex ξ) v = 0 := by
  simpa [r3ComplexSolenoidalFiber] using
    (Submodule.mem_orthogonal_singleton_iff_inner_right
      (𝕜 := ℂ) (u := r3FrequencyVectorComplex ξ) (v := v))

/-- Every output of the complex Leray symbol is transverse to the real frequency. -/
theorem r3LeraySymbolComplex_mem
    (ξ : R3) (v : R3C) :
    r3LeraySymbolComplex ξ v ∈ r3ComplexSolenoidalFiber ξ := by
  simpa [r3LeraySymbolComplex] using
    (Submodule.starProjection_apply_mem (r3ComplexSolenoidalFiber ξ) v)

/-- Fourier-space transversality of the complex Leray symbol. -/
theorem inner_r3LeraySymbolComplex_eq_zero
    (ξ : R3) (v : R3C) :
    inner ℂ (r3FrequencyVectorComplex ξ) (r3LeraySymbolComplex ξ v) = 0 := by
  exact (mem_r3ComplexSolenoidalFiber_iff_inner ξ (r3LeraySymbolComplex ξ v)).1
    (r3LeraySymbolComplex_mem ξ v)

/-- The complex Leray symbol fixes already-transverse vectors. -/
theorem r3LeraySymbolComplex_fixed_of_mem
    (ξ : R3) (v : R3C) (hv : v ∈ r3ComplexSolenoidalFiber ξ) :
    r3LeraySymbolComplex ξ v = v := by
  simpa [r3LeraySymbolComplex] using
    (Submodule.starProjection_eq_self_iff
      (K := r3ComplexSolenoidalFiber ξ) (v := v)).2 hv

/-- The complex Leray symbol is idempotent at each frequency. -/
theorem r3LeraySymbolComplex_idempotent
    (ξ : R3) (v : R3C) :
    r3LeraySymbolComplex ξ (r3LeraySymbolComplex ξ v) =
      r3LeraySymbolComplex ξ v := by
  exact r3LeraySymbolComplex_fixed_of_mem ξ (r3LeraySymbolComplex ξ v)
    (r3LeraySymbolComplex_mem ξ v)

/-- Orthogonal projection is norm non-increasing on each complex Fourier fiber. -/
theorem norm_r3LeraySymbolComplex_le
    (ξ : R3) (v : R3C) :
    ‖r3LeraySymbolComplex ξ v‖ ≤ ‖v‖ := by
  simpa [r3LeraySymbolComplex] using
    (r3ComplexSolenoidalFiber ξ).norm_starProjection_apply_le v

@[simp]
theorem r3FrequencyVectorComplex_zero :
    r3FrequencyVectorComplex (0 : R3) = 0 := by
  ext i
  simp [r3FrequencyVectorComplex]

/-- At zero frequency the complex Leray symbol is the identity. -/
@[simp]
theorem r3LeraySymbolComplex_zero :
    r3LeraySymbolComplex (0 : R3) = ContinuousLinearMap.id ℂ R3C := by
  simp [r3LeraySymbolComplex, r3ComplexSolenoidalFiber, Submodule.starProjection_top]

/-- The complex symbol annihilates the embedded longitudinal frequency vector. -/
@[simp]
theorem r3LeraySymbolComplex_self
    (ξ : R3) :
    r3LeraySymbolComplex ξ (r3FrequencyVectorComplex ξ) = 0 := by
  have hspan :
      r3FrequencyVectorComplex ξ ∈
        (ℂ ∙ r3FrequencyVectorComplex ξ : Submodule ℂ R3C) :=
    Submodule.mem_span_singleton_self (r3FrequencyVectorComplex ξ)
  have hproj :
      (ℂ ∙ r3FrequencyVectorComplex ξ : Submodule ℂ R3C).starProjection
          (r3FrequencyVectorComplex ξ) = r3FrequencyVectorComplex ξ :=
    (Submodule.starProjection_eq_self_iff
      (K := (ℂ ∙ r3FrequencyVectorComplex ξ : Submodule ℂ R3C))
      (v := r3FrequencyVectorComplex ξ)).2 hspan
  change
    (ℂ ∙ r3FrequencyVectorComplex ξ : Submodule ℂ R3C)ᗮ.starProjection
        (r3FrequencyVectorComplex ξ) = 0
  rw [Submodule.starProjection_orthogonal_val, hproj, sub_self]

/--
Explicit complex Leray formula on the Fourier velocity fiber:
`P(ξ)v = v - (⟪ξ_C,v⟫ / ‖ξ_C‖²) ξ_C`.

Because `ξ_C` has real coordinates, this is the complexification of the usual real matrix
`I - ξ ⊗ ξ / |ξ|²`.
-/
theorem r3LeraySymbolComplex_apply
    (ξ : R3) (v : R3C) :
    r3LeraySymbolComplex ξ v =
      v -
        (inner ℂ (r3FrequencyVectorComplex ξ) v /
          (((‖r3FrequencyVectorComplex ξ‖ ^ 2 : ℝ) : ℂ))) •
          r3FrequencyVectorComplex ξ := by
  have hsingle :
      (ℂ ∙ r3FrequencyVectorComplex ξ : Submodule ℂ R3C).starProjection v =
        (inner ℂ (r3FrequencyVectorComplex ξ) v /
          (((‖r3FrequencyVectorComplex ξ‖ ^ 2 : ℝ) : ℂ))) •
          r3FrequencyVectorComplex ξ := by
    simpa using
      (Submodule.starProjection_singleton
        (𝕜 := ℂ) (v := r3FrequencyVectorComplex ξ) v)
  change
    (ℂ ∙ r3FrequencyVectorComplex ξ : Submodule ℂ R3C)ᗮ.starProjection v =
      v -
        (inner ℂ (r3FrequencyVectorComplex ξ) v /
          (((‖r3FrequencyVectorComplex ξ‖ ^ 2 : ℝ) : ℂ))) •
          r3FrequencyVectorComplex ξ
  rw [Submodule.starProjection_orthogonal_val, hsingle]

end

end MNS2
