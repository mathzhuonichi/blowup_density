import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Formal.R3LerayRealLinearBridge

namespace MNS2

noncomputable section

/--
Project the output of any real continuous bilinear map on `L²(R³; ℂ³)` with the concrete physical
Leray projector.

This is deliberately parameterized by `rawConvection`: `L² × L² → L²` is not the physical
Navier--Stokes convection mapping at this regularity, so this definition does not pretend that the
actual term `(u · ∇)v` has already been constructed or bounded on `L²`.
-/
def r3L2ProjectedConvectionOf
    (rawConvection : R3L2Velocity →L[ℝ] R3L2Velocity →L[ℝ] R3L2Velocity) :
    R3L2Velocity →L[ℝ] R3L2Velocity →L[ℝ] R3L2Velocity :=
  (ContinuousLinearMap.postcomp R3L2Velocity r3LerayL2OperatorReal).comp rawConvection

@[simp]
theorem r3L2ProjectedConvectionOf_apply
    (rawConvection : R3L2Velocity →L[ℝ] R3L2Velocity →L[ℝ] R3L2Velocity)
    (u v : R3L2Velocity) :
    r3L2ProjectedConvectionOf rawConvection u v =
      r3LerayL2OperatorReal (rawConvection u v) := by
  rfl

/--
Instantiate the repository's abstract Leray-projected quadratic contract with the genuine physical
`R³` `L²` Leray projector and solenoidal kernel.

Only the raw bilinear map remains a parameter.  Once a physical convection map is constructed on a
carrier where it is actually bounded, the same packaging pattern can be used there without any
further abstract Leray assumptions.
-/
def r3L2LerayProjectedQuadraticContract
    (rawConvection : R3L2Velocity →L[ℝ] R3L2Velocity →L[ℝ] R3L2Velocity) :
    LerayProjectedQuadraticContract R3L2Velocity where
  solenoidal := r3L2SolenoidalRealSubmodule
  leray := r3LerayL2OperatorReal
  rawConvection := rawConvection
  projectedConvection := r3L2ProjectedConvectionOf rawConvection
  projected_apply := by
    intro u v
    rfl
  leray_mem := r3LerayL2OperatorReal_mem_solenoidal
  leray_fixed := by
    intro u hu
    exact r3LerayL2OperatorReal_fixed_of_mem u hu

/-- Every concretely Leray-projected bilinear output is in the physical `R³` solenoidal class. -/
theorem r3L2ProjectedConvectionOf_mem_solenoidal
    (rawConvection : R3L2Velocity →L[ℝ] R3L2Velocity →L[ℝ] R3L2Velocity)
    (u v : R3L2Velocity) :
    r3L2ProjectedConvectionOf rawConvection u v ∈ r3L2SolenoidalRealSubmodule := by
  exact
    (r3L2LerayProjectedQuadraticContract rawConvection).projectedConvection_mem u v

/-- The quadratic diagonal of any such projected bilinear map is physically solenoidal. -/
theorem r3L2ProjectedQuadraticDiagonal_mem_solenoidal
    (rawConvection : R3L2Velocity →L[ℝ] R3L2Velocity →L[ℝ] R3L2Velocity)
    (u : R3L2Velocity) :
    quadraticDiagonal (r3L2ProjectedConvectionOf rawConvection) u ∈
      r3L2SolenoidalRealSubmodule := by
  exact
    (r3L2LerayProjectedQuadraticContract rawConvection).quadraticDiagonal_mem u

/-- The exact real Fréchet derivative of the projected quadratic diagonal is also solenoidal. -/
theorem r3L2ProjectedQuadraticDerivative_mem_solenoidal
    (rawConvection : R3L2Velocity →L[ℝ] R3L2Velocity →L[ℝ] R3L2Velocity)
    (u v : R3L2Velocity) :
    quadraticDerivative (r3L2ProjectedConvectionOf rawConvection) u v ∈
      r3L2SolenoidalRealSubmodule := by
  exact
    (r3L2LerayProjectedQuadraticContract rawConvection).quadraticDerivative_mem u v

end

end MNS2
