import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Formal.R3SolenoidalCarrierCompleteness

namespace MNS2

noncomputable section

/-!
`Submodule.starProjection` is available once Lean can synthesize
`CompleteSpace r3L2SolenoidalSubmodule`.  The repository already proves that completeness in
`r3HsSolenoidalVelocity_complete`, but that declaration is a theorem rather than a typeclass
instance.  Install the same fact locally so mathlib can derive
`Submodule.HasOrthogonalProjection` without changing the global instance graph.
-/
local instance r3L2SolenoidalSubmodule_completeSpace :
    CompleteSpace r3L2SolenoidalSubmodule := by
  change CompleteSpace r3NormalizedDivergenceL2OperatorAux.ker
  infer_instance

/--
The physical-space Leray projector on `L²(R³; ℂ³)`, defined as the orthogonal projection onto the
closed solenoidal submodule already constructed from normalized Fourier divergence.

This is the first genuine function-space Leray operator in the repository.  It is independent of
the pointwise real frequency-fiber symbol `r3LeraySymbol`; identifying the two Fourier
realizations is a separate theorem and is intentionally not bundled into this definition.
-/
def r3LerayL2Operator : R3L2Velocity →L[ℂ] R3L2Velocity :=
  r3L2SolenoidalSubmodule.starProjection

/-- Every output of the `L²` Leray projector is divergence-free. -/
theorem r3LerayL2Operator_mem_solenoidal (f : R3L2Velocity) :
    r3LerayL2Operator f ∈ r3L2SolenoidalSubmodule := by
  simpa [r3LerayL2Operator] using
    (Submodule.starProjection_apply_mem r3L2SolenoidalSubmodule f)

/-- The bundled normalized divergence vanishes on every Leray-projected field. -/
theorem r3NormalizedDivergenceL2OperatorAux_r3LerayL2Operator
    (f : R3L2Velocity) :
    r3NormalizedDivergenceL2OperatorAux (r3LerayL2Operator f) = 0 := by
  exact (mem_r3L2SolenoidalSubmodule_iff (r3LerayL2Operator f)).1
    (r3LerayL2Operator_mem_solenoidal f)

/-- The Leray projector fixes every already-solenoidal `L²` field. -/
theorem r3LerayL2Operator_fixed_of_mem
    (f : R3L2Velocity) (hf : f ∈ r3L2SolenoidalSubmodule) :
    r3LerayL2Operator f = f := by
  simpa [r3LerayL2Operator] using
    (Submodule.starProjection_eq_self_iff
      (K := r3L2SolenoidalSubmodule) (v := f)).2 hf

/-- The function-space Leray projector is idempotent. -/
theorem r3LerayL2Operator_idempotent (f : R3L2Velocity) :
    r3LerayL2Operator (r3LerayL2Operator f) = r3LerayL2Operator f := by
  exact r3LerayL2Operator_fixed_of_mem _ (r3LerayL2Operator_mem_solenoidal f)

/-- The range of the function-space Leray projector is exactly the solenoidal submodule. -/
@[simp]
theorem range_r3LerayL2Operator :
    r3LerayL2Operator.range = r3L2SolenoidalSubmodule := by
  simpa [r3LerayL2Operator] using
    (Submodule.range_starProjection r3L2SolenoidalSubmodule)

/-- Orthogonal projection is norm non-increasing on `L²`. -/
theorem norm_r3LerayL2Operator_apply_le (f : R3L2Velocity) :
    ‖r3LerayL2Operator f‖ ≤ ‖f‖ := by
  simpa [r3LerayL2Operator] using
    r3L2SolenoidalSubmodule.norm_starProjection_apply_le f

/-- The `L²` Leray projector has operator norm at most one. -/
theorem norm_r3LerayL2Operator_le_one :
    ‖r3LerayL2Operator‖ ≤ 1 := by
  simpa [r3LerayL2Operator] using
    r3L2SolenoidalSubmodule.starProjection_norm_le

end

end MNS2
