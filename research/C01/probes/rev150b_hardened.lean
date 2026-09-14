import NSFormalization.Section4.C01.EnergyDerivative

/-! Reviewer HARDENED negative checks for lane 150 (LESSONS 2026-09-14: a mutation must not
be "the lane's script no longer elaborates" alone).  Here the mutated statements are taken as
*hypotheses* and combined with the lane's theorem through `HasDerivAt.unique`; each forces an
identity that a correct energy identity must not force.  Both theorems below COMPILE — that is
the point: they exhibit what the mutation would collapse. -/

noncomputable section

open Set MeasureTheory Filter Topology
open EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
open NavierStokes.ProblemStatement
open scoped RealInnerProductSpace ContDiff

namespace NSFormalization.Section4.C01

open NSFormalization.Section4.A02 (ClassicalSolutionR MemForceR)

variable {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField} {c S T : ℝ}

/-- H1 (factor 2).  If the E4 value were `⟪u,∂ₜu⟫` instead of `2⟪u,∂ₜu⟫`, then
`⟪u(t,·), ∂ₜu(t,·)⟫ = 0` at every interior time of every classical solution. -/
theorem H1_dropTwo_forces_zero
    (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    (hc : 0 < c) (hcS : c ≤ S) (hST : S < T)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) (S - c))
    (hmut : HasDerivAt
      (fun ρ : ℝ =>
        ‖(velocityField w hST
            ⟨(projIcc (0 : ℝ) (S - c) (sub_nonneg.mpr hcS) ρ).1 + c,
              ⟨by have h := (projIcc (0 : ℝ) (S - c) (sub_nonneg.mpr hcS) ρ).2.1; linarith,
               by have h := (projIcc (0 : ℝ) (S - c) (sub_nonneg.mpr hcS) ρ).2.2;
                  linarith⟩⟩).toLp‖ ^ 2)
      (⟪(velocitySliceField w (Ioo_subset_Ico_self
                (mem_Ioo_of_mem_Icc hc hST (show r + c ∈ Icc c S from
                  ⟨by linarith [hr.1], by linarith [hr.2]⟩)))).toLp,
            (temporalSliceField w hf
                (mem_Ioo_of_mem_Icc hc hST (show r + c ∈ Icc c S from
                  ⟨by linarith [hr.1], by linarith [hr.2]⟩))).toLp⟫)
      r) :
    (⟪(velocitySliceField w (Ioo_subset_Ico_self
          (mem_Ioo_of_mem_Icc hc hST (show r + c ∈ Icc c S from
            ⟨by linarith [hr.1], by linarith [hr.2]⟩)))).toLp,
      (temporalSliceField w hf
          (mem_Ioo_of_mem_Icc hc hST (show r + c ∈ Icc c S from
            ⟨by linarith [hr.1], by linarith [hr.2]⟩))).toLp⟫) = 0 := by
  have htrue := energyDerivative_hasDerivAt w hf hc hcS hST hr
  have h := hmut.unique htrue
  linarith [h]

/-- H2 (viscous sign).  If the energy identity carried `+2ν‖∇u‖²` instead of `−2ν‖∇u‖²`,
then `ν · ∫ ∑ᵢ‖∂ᵢu(t,·)‖² = 0` at every interior time of every classical solution — i.e. for
`ν > 0` every classical solution would be spatially constant in the `L²` sense. -/
theorem H2_signFlip_forces_zero_dissipation
    (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    (hmut : HasDerivAt
      (fun s : ℝ =>
        ‖(velocityField w (show (t + T) / 2 < T by linarith [ht.2])
            (projIcc (0 : ℝ) ((t + T) / 2) (by linarith [ht.1, ht.2]) s)).toLp‖ ^ 2)
      (2 * ν * (∫ x, ∑ i : Fin 3,
            ‖fderiv ℝ (velocitySliceField w (Ioo_subset_Ico_self ht)).field x (axis i)‖ ^ 2)
          + 2 * (∫ x, ⟪(velocitySliceField w (Ioo_subset_Ico_self ht)).field x,
                       (forceSliceField hf (le_of_lt ht.1)).field x⟫))
      t) :
    ν * (∫ x, ∑ i : Fin 3,
        ‖fderiv ℝ (velocitySliceField w (Ioo_subset_Ico_self ht)).field x (axis i)‖ ^ 2) = 0 := by
  have htrue := energyIdentity_classical_unconditional w hf ht
  have h := hmut.unique htrue
  linarith [h]

end NSFormalization.Section4.C01
