import NSFormalization.Section4.C01.MomentumCarrierB

/-! Reviewer probe (lane 143): is the explicit `hd` of `energyIdentity_classical` an
escape hatch (a statement-weakening placeholder) or just a spelling?  `hd` is
`d = 2⟪u,∂ₜu⟫`, which is satisfiable by `rfl` for every `w`, so the theorem is
*equivalent* to the hypothesis-free identity below.  If this `example` typechecks,
the theorem carries real content and E4 is genuinely the only missing input. -/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerSmoothLimit
open scoped RealInnerProductSpace ContDiff

namespace NSFormalization.Section4.C01

open NSFormalization.Section4.A02 (ClassicalSolutionR MemForceR)

example {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    2 * ⟪(velocitySliceField w (Ioo_subset_Ico_self ht)).toLp,
          (temporalSliceField w hf ht).toLp⟫
      = -2 * ν * (∫ x, ∑ i : Fin 3,
            ‖fderiv ℝ (velocitySliceField w (Ioo_subset_Ico_self ht)).field x (axis i)‖ ^ 2)
          + 2 * (∫ x, ⟪(velocitySliceField w (Ioo_subset_Ico_self ht)).field x,
                       (forceSliceField hf (le_of_lt ht.1)).field x⟫) :=
  energyIdentity_classical w hf ht rfl

#print axioms energyIdentity_classical

end NSFormalization.Section4.C01
