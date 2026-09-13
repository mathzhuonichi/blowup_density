import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
import Formal.R3LerayPointwiseProjectionIdentification
import Formal.LerayProjectedQuadratic

namespace MNS2

open MeasureTheory

noncomputable section

/--
The normalized-divergence operator viewed as a real continuous-linear map.

The concrete Fourier/L² layer is naturally complex-linear, while the existing quadratic mild and
flow-map layers differentiate over `ℝ`.  This definition is only a restriction of scalars; it does
not change the underlying operator or its kernel.
-/
def r3NormalizedDivergenceL2OperatorReal :
    R3L2Velocity →L[ℝ] R3L2ScalarAux :=
  r3NormalizedDivergenceL2OperatorAux.restrictScalars ℝ

/-- The physical `L²` solenoidal class, now bundled as a real submodule for the real Banach calculus. -/
def r3L2SolenoidalRealSubmodule : Submodule ℝ R3L2Velocity :=
  r3NormalizedDivergenceL2OperatorReal.ker

/-- Restricting scalars does not change which `L²` fields are divergence-free. -/
@[simp]
theorem mem_r3L2SolenoidalRealSubmodule_iff (f : R3L2Velocity) :
    f ∈ r3L2SolenoidalRealSubmodule ↔ f ∈ r3L2SolenoidalSubmodule := by
  simp [r3L2SolenoidalRealSubmodule, r3NormalizedDivergenceL2OperatorReal,
    r3L2SolenoidalSubmodule]

/-- The concrete `L²` Leray projector viewed as a real continuous-linear map. -/
def r3LerayL2OperatorReal : R3L2Velocity →L[ℝ] R3L2Velocity :=
  r3LerayL2Operator.restrictScalars ℝ

@[simp]
theorem r3LerayL2OperatorReal_apply (f : R3L2Velocity) :
    r3LerayL2OperatorReal f = r3LerayL2Operator f := by
  rfl

/-- The real-linear view of the Leray projector still lands in the same physical solenoidal class. -/
theorem r3LerayL2OperatorReal_mem_solenoidal (f : R3L2Velocity) :
    r3LerayL2OperatorReal f ∈ r3L2SolenoidalRealSubmodule := by
  rw [mem_r3L2SolenoidalRealSubmodule_iff, r3LerayL2OperatorReal_apply]
  exact r3LerayL2Operator_mem_solenoidal f

/-- The real-linear Leray projector fixes every real-bundled solenoidal field. -/
theorem r3LerayL2OperatorReal_fixed_of_mem
    (f : R3L2Velocity) (hf : f ∈ r3L2SolenoidalRealSubmodule) :
    r3LerayL2OperatorReal f = f := by
  rw [r3LerayL2OperatorReal_apply]
  exact r3LerayL2Operator_fixed_of_mem f
    ((mem_r3L2SolenoidalRealSubmodule_iff f).1 hf)

/-- Idempotence is preserved under restriction from complex to real scalars. -/
theorem r3LerayL2OperatorReal_idempotent (f : R3L2Velocity) :
    r3LerayL2OperatorReal (r3LerayL2OperatorReal f) =
      r3LerayL2OperatorReal f := by
  simp only [r3LerayL2OperatorReal_apply]
  exact r3LerayL2Operator_idempotent f

/-- The pointwise `L²` contraction bound is unchanged in the real-linear view. -/
theorem norm_r3LerayL2OperatorReal_apply_le (f : R3L2Velocity) :
    ‖r3LerayL2OperatorReal f‖ ≤ ‖f‖ := by
  simpa only [r3LerayL2OperatorReal_apply] using
    norm_r3LerayL2Operator_apply_le f

/--
The real-linear view has exactly the same explicit complex Fourier multiplier almost everywhere.
This is the scalar-field bridge needed before the concrete Leray projector can be inserted into the
existing real quadratic mild interfaces.
-/
theorem fourier_r3LerayL2OperatorReal_ae
    (f : R3L2Velocity) :
    ((MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C)
        (r3LerayL2OperatorReal f) : R3 → R3C) =ᵐ[volume]
      fun ξ =>
        r3LeraySymbolComplex ξ
          (((MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C) f) ξ) := by
  simpa only [r3LerayL2OperatorReal_apply] using
    fourier_r3LerayL2Operator_ae f

end

end MNS2
