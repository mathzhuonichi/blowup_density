import Formal.R3LerayComplexFiberSymbol
import Formal.R3DivergencePointwise

namespace MNS2

noncomputable section

/--
The complex inner product against the embedded real frequency vector is exactly the raw
Fourier-divergence scalar used by the `R³` function-space layer.
-/
theorem inner_r3FrequencyVectorComplex_eq_rawDivergencePointwise
    (ξ : R3) (v : R3C) :
    inner ℂ (r3FrequencyVectorComplex ξ) v =
      r3RawDivergencePointwise ξ v := by
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  simp [r3FrequencyVectorComplex, r3RawDivergencePointwise]
  ring

/--
Membership in the complex transverse fiber is equivalent to vanishing raw Fourier divergence.
-/
theorem mem_r3ComplexSolenoidalFiber_iff_rawDivergencePointwise_eq_zero
    (ξ : R3) (v : R3C) :
    v ∈ r3ComplexSolenoidalFiber ξ ↔
      r3RawDivergencePointwise ξ v = 0 := by
  rw [mem_r3ComplexSolenoidalFiber_iff_inner,
    inner_r3FrequencyVectorComplex_eq_rawDivergencePointwise]

/--
The complex transverse fiber is also exactly the kernel of the normalized divergence used to
construct the closed `L²` solenoidal carrier.
-/
theorem mem_r3ComplexSolenoidalFiber_iff_normalizedDivergencePointwise_eq_zero
    (ξ : R3) (v : R3C) :
    v ∈ r3ComplexSolenoidalFiber ξ ↔
      r3NormalizedDivergencePointwise ξ v = 0 := by
  rw [mem_r3ComplexSolenoidalFiber_iff_rawDivergencePointwise_eq_zero,
    ← r3NormalizedDivergencePointwise_eq_zero_iff]

/-- The explicit complex Leray symbol has zero normalized divergence at every frequency. -/
theorem r3NormalizedDivergencePointwise_r3LeraySymbolComplex
    (ξ : R3) (v : R3C) :
    r3NormalizedDivergencePointwise ξ (r3LeraySymbolComplex ξ v) = 0 := by
  exact
    (mem_r3ComplexSolenoidalFiber_iff_normalizedDivergencePointwise_eq_zero
      ξ (r3LeraySymbolComplex ξ v)).1
      (r3LeraySymbolComplex_mem ξ v)

/--
The complex Leray symbol fixes a vector exactly when that vector satisfies the normalized
Fourier-divergence constraint.
-/
theorem r3LeraySymbolComplex_fixed_iff_normalizedDivergencePointwise_eq_zero
    (ξ : R3) (v : R3C) :
    r3LeraySymbolComplex ξ v = v ↔
      r3NormalizedDivergencePointwise ξ v = 0 := by
  rw [← mem_r3ComplexSolenoidalFiber_iff_normalizedDivergencePointwise_eq_zero]
  exact Submodule.starProjection_eq_self_iff
    (K := r3ComplexSolenoidalFiber ξ) (v := v)

end

end MNS2
