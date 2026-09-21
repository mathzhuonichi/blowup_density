import Mathlib
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

namespace MNS2

open scoped RealInnerProductSpace

noncomputable section

/-- The physical three-dimensional real frequency/vector space. -/
abbrev R3 := EuclideanSpace ℝ (Fin 3)

/--
At a fixed frequency `ξ`, the divergence-free fiber is the plane orthogonal to `ξ`.
This is the pointwise Fourier-space form of the physical three-dimensional
incompressibility condition `ξ · û(ξ) = 0`.
-/
def r3SolenoidalFiber (ξ : R3) : Submodule ℝ R3 :=
  (ℝ ∙ ξ)ᗮ

/--
The real matrix action underlying the Fourier Leray multiplier at frequency `ξ`.
It is the orthogonal projection onto the plane perpendicular to `ξ`.

This is only a frequency-fiber operator.  It is not yet a bounded operator on an
`R^3` function space and does not by itself define the PDE Leray projector.
-/
def r3LeraySymbol (ξ : R3) : R3 →L[ℝ] R3 :=
  (r3SolenoidalFiber ξ).starProjection

@[simp]
theorem mem_r3SolenoidalFiber_iff_inner
    (ξ v : R3) :
    v ∈ r3SolenoidalFiber ξ ↔ inner ℝ ξ v = 0 := by
  simpa [r3SolenoidalFiber] using
    (Submodule.mem_orthogonal_singleton_iff_inner_right
      (𝕜 := ℝ) (u := ξ) (v := v))

/-- Every output of the Leray symbol satisfies the transverse-frequency condition. -/
theorem r3LeraySymbol_mem
    (ξ v : R3) :
    r3LeraySymbol ξ v ∈ r3SolenoidalFiber ξ := by
  simpa [r3LeraySymbol] using
    (Submodule.starProjection_apply_mem (r3SolenoidalFiber ξ) v)

/-- Fourier-space incompressibility of the projected vector. -/
theorem inner_r3LeraySymbol_eq_zero
    (ξ v : R3) :
    inner ℝ ξ (r3LeraySymbol ξ v) = 0 := by
  exact (mem_r3SolenoidalFiber_iff_inner ξ (r3LeraySymbol ξ v)).1
    (r3LeraySymbol_mem ξ v)

/-- The symbol fixes every already-transverse vector. -/
theorem r3LeraySymbol_fixed_of_mem
    (ξ v : R3) (hv : v ∈ r3SolenoidalFiber ξ) :
    r3LeraySymbol ξ v = v := by
  simpa [r3LeraySymbol] using
    (Submodule.starProjection_eq_self_iff
      (K := r3SolenoidalFiber ξ) (v := v)).2 hv

/-- The Leray symbol is idempotent at every frequency. -/
theorem r3LeraySymbol_idempotent
    (ξ v : R3) :
    r3LeraySymbol ξ (r3LeraySymbol ξ v) = r3LeraySymbol ξ v := by
  exact r3LeraySymbol_fixed_of_mem ξ (r3LeraySymbol ξ v)
    (r3LeraySymbol_mem ξ v)

/-- Orthogonal projection is norm non-increasing at each frequency. -/
theorem norm_r3LeraySymbol_le
    (ξ v : R3) :
    ‖r3LeraySymbol ξ v‖ ≤ ‖v‖ := by
  simpa [r3LeraySymbol] using
    (r3SolenoidalFiber ξ).norm_starProjection_apply_le v

/-- At zero frequency there is no longitudinal direction, so the symbol is the identity. -/
@[simp]
theorem r3LeraySymbol_zero :
    r3LeraySymbol (0 : R3) = ContinuousLinearMap.id ℝ R3 := by
  simp [r3LeraySymbol, r3SolenoidalFiber, Submodule.starProjection_top]

/-- The symbol annihilates the longitudinal frequency vector itself. -/
@[simp]
theorem r3LeraySymbol_self
    (ξ : R3) :
    r3LeraySymbol ξ ξ = 0 := by
  have hspan : ξ ∈ (ℝ ∙ ξ : Submodule ℝ R3) :=
    Submodule.mem_span_singleton_self ξ
  have hproj : (ℝ ∙ ξ : Submodule ℝ R3).starProjection ξ = ξ :=
    (Submodule.starProjection_eq_self_iff
      (K := (ℝ ∙ ξ : Submodule ℝ R3)) (v := ξ)).2 hspan
  change (ℝ ∙ ξ : Submodule ℝ R3)ᗮ.starProjection ξ = 0
  rw [Submodule.starProjection_orthogonal_val, hproj, sub_self]

/--
Explicit physical formula for the three-dimensional Leray symbol:
`P(ξ)v = v - ((ξ·v)/|ξ|^2) ξ`.

The zero-frequency case is automatically handled by Lean's field convention and agrees
with `r3LeraySymbol_zero`.
-/
theorem r3LeraySymbol_apply
    (ξ v : R3) :
    r3LeraySymbol ξ v =
      v - (inner ℝ ξ v / ‖ξ‖ ^ 2) • ξ := by
  have hsingle :
      (ℝ ∙ ξ : Submodule ℝ R3).starProjection v =
        (inner ℝ ξ v / ‖ξ‖ ^ 2) • ξ := by
    simpa using
      (Submodule.starProjection_singleton (𝕜 := ℝ) (v := ξ) v)
  change (ℝ ∙ ξ : Submodule ℝ R3)ᗮ.starProjection v =
    v - (inner ℝ ξ v / ‖ξ‖ ^ 2) • ξ
  rw [Submodule.starProjection_orthogonal_val, hsingle]

end

end MNS2
