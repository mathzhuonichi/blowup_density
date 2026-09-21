import NSFormalization.Section4.C01.EnergyDerivative

/-! Reviewer probe for lane 150: the item-6 `rfl` identification, name resolution of
`temporalDerivative`, and the inner-product notation. -/

open Set MeasureTheory Filter Topology
open EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
open NavierStokes.ProblemStatement
open scoped RealInnerProductSpace ContDiff

namespace NSFormalization.Section4.C01

open NSFormalization.Section4.A02 (ClassicalSolutionR MemForceR)

variable {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField} {c S T : ℝ}

set_option pp.fullNames true in
#check @temporalDerivative

set_option pp.fullNames true in
#check fun (X Y : SmoothL2Field Space) => (⟪X.toLp, Y.toLp⟫ : ℝ)

-- (A) item 6: the whole `SmoothL2Field` record, not just its `toLp`, is `rfl`
example (w : ClassicalSolutionR ν a f T) (hc : 0 < c) (hcS : c ≤ S) (hST : S < T)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) (S - c)) :
    velocityField w hST ⟨r + c, ⟨by linarith [hr.1], by linarith [hr.2]⟩⟩
      = velocitySliceField w (Ioo_subset_Ico_self
          (mem_Ioo_of_mem_Icc hc hST (show r + c ∈ Icc c S from
            ⟨by linarith [hr.1], by linarith [hr.2]⟩))) := rfl

-- (B) the `.toLp` form actually used by the assembly
example (w : ClassicalSolutionR ν a f T) (hc : 0 < c) (hcS : c ≤ S) (hST : S < T)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) (S - c)) :
    (velocityField w hST ⟨r + c, ⟨by linarith [hr.1], by linarith [hr.2]⟩⟩).toLp
      = (velocitySliceField w (Ioo_subset_Ico_self
          (mem_Ioo_of_mem_Icc hc hST (show r + c ∈ Icc c S from
            ⟨by linarith [hr.1], by linarith [hr.2]⟩)))).toLp := rfl

-- (C) `axis = coordinateVector` (needed by the V2 `gradientSq` binding)
example (i : Fin 3) : EulerOrdinarySobolev.axis i = coordinateVector i := rfl

-- (D) the function of `energyDerivative_hasDerivAt` really is `ρ ↦ ‖u(ρ+c,·)‖²` at
-- interior `ρ`, i.e. the `projIcc` is the identity there.
example (w : ClassicalSolutionR ν a f T) (hc : 0 < c) (hcS : c ≤ S) (hST : S < T)
    {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) (S - c)) :
    (velocityField w hST
        ⟨(projIcc (0 : ℝ) (S - c) (sub_nonneg.mpr hcS) ρ).1 + c,
          ⟨by have h := (projIcc (0 : ℝ) (S - c) (sub_nonneg.mpr hcS) ρ).2.1; linarith,
           by have h := (projIcc (0 : ℝ) (S - c) (sub_nonneg.mpr hcS) ρ).2.2; linarith⟩⟩).field
      = fun x => w.velocity (ρ + c, x) := by
  funext x
  show w.velocity ((projIcc (0 : ℝ) (S - c) (sub_nonneg.mpr hcS) ρ).1 + c, x)
      = w.velocity (ρ + c, x)
  rw [projIcc_of_mem (sub_nonneg.mpr hcS) (Ioo_subset_Icc_self hρ)]

-- (E) the derivative value really is the PDE's own `∂ₜu` (`temporalDerivative = deriv`)
example (w : ClassicalSolutionR ν a f T) (s : ℝ) (x : Space) :
    temporalDerivative w.velocity s x = deriv (fun ρ : ℝ => w.velocity (ρ, x)) s := rfl

end NSFormalization.Section4.C01
