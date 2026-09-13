import Mathlib
import Formal.QuadraticMildNonlinearity

namespace MNS2

noncomputable section

section LerayProjectedQuadratic

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/--
An explicit operator-level contract for a Leray-projected quadratic nonlinearity.

`solenoidal` is the certified divergence-free subspace of the chosen Banach space.
`rawConvection` is the pre-projection bilinear convection operator, `leray` is the
projection, and `projectedConvection` is the bilinear operator used by the mild layer.

The contract deliberately does not identify the ambient Banach space with a concrete
Sobolev/Lp space on `ℝ³`, nor does it construct the physical Leray projector.  A later
`ℝ³` layer must instantiate these fields and prove that `solenoidal` is exactly the
physical three-dimensional divergence-free class.
-/
structure LerayProjectedQuadraticContract (V : Type*)
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] where
  solenoidal : Submodule ℝ V
  leray : V →L[ℝ] V
  rawConvection : V →L[ℝ] V →L[ℝ] V
  projectedConvection : V →L[ℝ] V →L[ℝ] V
  projected_apply : ∀ u v : V,
    projectedConvection u v = leray (rawConvection u v)
  leray_mem : ∀ w : V, leray w ∈ solenoidal
  leray_fixed : ∀ {u : V}, u ∈ solenoidal → leray u = u

/-- The Leray map is idempotent as a consequence of range membership plus fixedness. -/
theorem LerayProjectedQuadraticContract.leray_idempotent_apply
    (C : LerayProjectedQuadraticContract V) (w : V) :
    C.leray (C.leray w) = C.leray w := by
  exact C.leray_fixed (C.leray_mem w)

/-- Every projected bilinear convection output lies in the certified solenoidal subspace. -/
theorem LerayProjectedQuadraticContract.projectedConvection_mem
    (C : LerayProjectedQuadraticContract V) (u v : V) :
    C.projectedConvection u v ∈ C.solenoidal := by
  rw [C.projected_apply]
  exact C.leray_mem (C.rawConvection u v)

/-- The quadratic diagonal used by the mild kernel remains solenoidal. -/
theorem LerayProjectedQuadraticContract.quadraticDiagonal_mem
    (C : LerayProjectedQuadraticContract V) (u : V) :
    quadraticDiagonal C.projectedConvection u ∈ C.solenoidal := by
  exact C.projectedConvection_mem u u

/--
The exact Fréchet derivative of the projected quadratic diagonal also takes values in
the solenoidal subspace.  This is the closure property needed by the linearized mild
semantics: both `P C(u,v)` and `P C(v,u)` are projected before they are added.
-/
theorem LerayProjectedQuadraticContract.quadraticDerivative_mem
    (C : LerayProjectedQuadraticContract V) (u v : V) :
    quadraticDerivative C.projectedConvection u v ∈ C.solenoidal := by
  rw [quadraticDerivative_apply]
  exact C.solenoidal.add_mem
    (C.projectedConvection_mem u v)
    (C.projectedConvection_mem v u)

/-- Package the projected bilinear operator into the existing quadratic mild kernel. -/
def LerayProjectedQuadraticContract.mildKernel
    (C : LerayProjectedQuadraticContract V)
    (H : ℝ → V →L[ℝ] V) : MildEvolutionKernel V :=
  MildEvolutionKernel.ofQuadratic H C.projectedConvection

@[simp]
theorem LerayProjectedQuadraticContract.mildKernel_nonlinearity
    (C : LerayProjectedQuadraticContract V)
    (H : ℝ → V →L[ℝ] V) (u : V) :
    (C.mildKernel H).nonlinearity u = C.projectedConvection u u := by
  rfl

/-- The nonlinear term of the packaged mild kernel is certified solenoidal. -/
theorem LerayProjectedQuadraticContract.mildKernel_nonlinearity_mem
    (C : LerayProjectedQuadraticContract V)
    (H : ℝ → V →L[ℝ] V) (u : V) :
    (C.mildKernel H).nonlinearity u ∈ C.solenoidal := by
  exact C.quadraticDiagonal_mem u

/--
The derivative of the mild nonlinearity is the projected linearized convection and is
again solenoidal.  This theorem exposes the exact bridge from the Leray contract to the
existing quadratic-tangent layer without assuming any PDE existence theorem.
-/
theorem LerayProjectedQuadraticContract.fderiv_mildKernel_nonlinearity_mem
    (C : LerayProjectedQuadraticContract V)
    (H : ℝ → V →L[ℝ] V) (u v : V) :
    (fderiv ℝ (C.mildKernel H).nonlinearity u) v ∈ C.solenoidal := by
  change (fderiv ℝ (quadraticDiagonal C.projectedConvection) u) v ∈ C.solenoidal
  rw [fderiv_quadraticDiagonal]
  exact C.quadraticDerivative_mem u v

end LerayProjectedQuadratic

end

end MNS2
