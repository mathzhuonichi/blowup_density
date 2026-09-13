import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Normed.Operator.Mul
import Formal.R3CoordinateLinearAux
import Formal.R3LerayL2Operator

namespace MNS2

open scoped SchwartzMap LineDeriv

noncomputable section

/-- Smooth rapidly decaying complexified velocity fields on physical `R³`. -/
abbrev R3SchwartzVelocity := SchwartzMap R3 R3C

/-- Smooth rapidly decaying scalar fields on physical `R³`. -/
abbrev R3SchwartzScalar := SchwartzMap R3 ℂ

/-- The `i`-th physical coordinate direction in `R³`. -/
def r3CoordinateDirection (i : Fin 3) : R3 :=
  WithLp.toLp 2 (fun j : Fin 3 => if j = i then (1 : ℝ) else 0)

/-- Extract the `i`-th velocity component of an `R³` Schwartz field. -/
def r3SchwartzCoordinate (i : Fin 3) :
    R3SchwartzVelocity →L[ℂ] R3SchwartzScalar :=
  SchwartzMap.postcompCLM (r3CoordinateFiberAux i)

@[simp]
theorem r3SchwartzCoordinate_apply
    (i : Fin 3) (u : R3SchwartzVelocity) (x : R3) :
    r3SchwartzCoordinate i u x = u x i := by
  rfl

/-- The physical derivative `∂ᵢ` acting on Schwartz velocity fields. -/
def r3SchwartzCoordinateDerivative (i : Fin 3) :
    R3SchwartzVelocity →L[ℂ] R3SchwartzVelocity :=
  LineDeriv.lineDerivOpCLM ℂ R3SchwartzVelocity (r3CoordinateDirection i)

/-- One coordinate contribution `uᵢ ∂ᵢ v` to the convection term. -/
def r3SchwartzConvectionTerm (i : Fin 3) (u : R3SchwartzVelocity) :
    R3SchwartzVelocity →L[ℂ] R3SchwartzVelocity :=
  (SchwartzMap.pairing
      (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] R3C →L[ℂ] R3C)
      (r3SchwartzCoordinate i u)).comp
    (r3SchwartzCoordinateDerivative i)

/--
The physical complex-bilinear convection operator on the Schwartz core,

`(u · ∇)v = ∑ᵢ uᵢ ∂ᵢ v`.

For each fixed `u` this is bundled as a continuous complex-linear map in `v`.  This is a genuine
physical-space operator on rapidly decaying smooth fields; no Sobolev extension estimate is claimed
here.
-/
def r3SchwartzConvection (u : R3SchwartzVelocity) :
    R3SchwartzVelocity →L[ℂ] R3SchwartzVelocity :=
  ∑ i : Fin 3, r3SchwartzConvectionTerm i u

@[simp]
theorem r3SchwartzConvectionTerm_apply
    (i : Fin 3) (u v : R3SchwartzVelocity) (x : R3) :
    r3SchwartzConvectionTerm i u v x =
      (u x i) • (r3SchwartzCoordinateDerivative i v x) := by
  simp [r3SchwartzConvectionTerm]

/-- Pointwise coordinate formula for the physical Schwartz convection term. -/
theorem r3SchwartzConvection_apply
    (u v : R3SchwartzVelocity) (x : R3) :
    r3SchwartzConvection u v x =
      ∑ i : Fin 3, (u x i) • (r3SchwartzCoordinateDerivative i v x) := by
  simp [r3SchwartzConvection]

@[simp]
theorem r3SchwartzConvection_zero_right (u : R3SchwartzVelocity) :
    r3SchwartzConvection u 0 = 0 := by
  exact (r3SchwartzConvection u).map_zero

/--
The actual Leray-projected Navier--Stokes convection term on Schwartz inputs, valued in the concrete
`L²(R³; ℂ³)` carrier already used by the function-space Leray projector.

This is the first literal `P((u · ∇)v)` object in the concrete `R³` stack.  Its existence on Schwartz
inputs does not yet provide the Sobolev bilinear estimate needed for local well-posedness.
-/
def r3ProjectedSchwartzConvectionL2
    (u v : R3SchwartzVelocity) : R3L2Velocity :=
  r3LerayL2Operator ((r3SchwartzConvection u v).toLp 2)

/-- The projected Schwartz convection term is physically divergence-free in `L²`. -/
theorem r3ProjectedSchwartzConvectionL2_mem_solenoidal
    (u v : R3SchwartzVelocity) :
    r3ProjectedSchwartzConvectionL2 u v ∈ r3L2SolenoidalSubmodule := by
  exact r3LerayL2Operator_mem_solenoidal _

/-- Leray projection does not increase the `L²` norm of the Schwartz convection term. -/
theorem norm_r3ProjectedSchwartzConvectionL2_le
    (u v : R3SchwartzVelocity) :
    ‖r3ProjectedSchwartzConvectionL2 u v‖ ≤ ‖(r3SchwartzConvection u v).toLp 2‖ := by
  exact norm_r3LerayL2Operator_apply_le _

end

end MNS2
