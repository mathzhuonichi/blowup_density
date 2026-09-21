import NSFormalization.Section4.C01.EnergyDerivative

/-! Reviewer negative check M4 (lane 150): `Ioo` vs `Ico` in row E4's interior guard.
Widening `hr : r ∈ Ioo 0 (S-c)` to `Ico` (so `r = 0`, the left endpoint of the translated
window, is admitted) with the lane's proof script verbatim MUST fail. -/

noncomputable section

open Set MeasureTheory Filter Topology
open EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
open NavierStokes.ProblemStatement
open scoped RealInnerProductSpace ContDiff

namespace NSFormalization.Section4.C01

open NSFormalization.Section4.A02 (ClassicalSolutionR MemForceR)

variable {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField} {c S T : ℝ}

theorem M4_energyDerivative_Ico
    (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    (hc : 0 < c) (hcS : c ≤ S) (hST : S < T)
    {r : ℝ} (hr : r ∈ Ico (0 : ℝ) (S - c)) :
    HasDerivAt
      (fun ρ : ℝ =>
        ‖(velocityField w hST
            ⟨(projIcc (0 : ℝ) (S - c) (sub_nonneg.mpr hcS) ρ).1 + c,
              ⟨by have h := (projIcc (0 : ℝ) (S - c) (sub_nonneg.mpr hcS) ρ).2.1; linarith,
               by have h := (projIcc (0 : ℝ) (S - c) (sub_nonneg.mpr hcS) ρ).2.2;
                  linarith⟩⟩).toLp‖ ^ 2)
      (2 * ⟪(velocitySliceField w (Ioo_subset_Ico_self
                (mem_Ioo_of_mem_Icc hc hST (show r + c ∈ Icc c S from
                  ⟨by linarith [hr.1], by linarith [hr.2]⟩)))).toLp,
            (temporalSliceField w hf
                (mem_Ioo_of_mem_Icc hc hST (show r + c ∈ Icc c S from
                  ⟨by linarith [hr.1], by linarith [hr.2]⟩))).toLp⟫)
      r := by
  have hT' : (0 : ℝ) ≤ S - c := sub_nonneg.mpr hcS
  let ιvel : Icc (0 : ℝ) (S - c) → Icc (0 : ℝ) S := fun ρ =>
    ⟨ρ.1 + c, ⟨by have := ρ.2.1; linarith, by have := ρ.2.2; linarith⟩⟩
  have hιvel : Continuous ιvel :=
    (continuous_subtype_val.add continuous_const).subtype_mk _
  let σ : Icc (0 : ℝ) (S - c) → Icc c S := fun ρ =>
    ⟨ρ.1 + c, ⟨by have := ρ.2.1; linarith, by have := ρ.2.2; linarith⟩⟩
  have hσ : Continuous σ :=
    (continuous_subtype_val.add continuous_const).subtype_mk _
  let A : Icc (0 : ℝ) (S - c) → SmoothL2Field Space := fun ρ => velocityField w hST (ιvel ρ)
  let B : Icc (0 : ℝ) (S - c) → SmoothL2Field Space := fun ρ =>
    temporalSliceField w hf (mem_Ioo_of_mem_Icc hc hST (σ ρ).2)
  have hA : ∀ n, Continuous (fun ρ => (A ρ).jetLp n) :=
    fun n => (velocityField_jetLp_continuous w hST n).comp hιvel
  have hB : ∀ n, Continuous (fun ρ => (B ρ).jetLp n) :=
    fun n => (temporalSlicePath_jetLp_continuous w hf hc hST n).comp hσ
  have hd : ∀ t (ht : t ∈ Ioo 0 (S - c)) x,
      HasDerivAt (fun ρ => (A (projIcc 0 (S - c) hT' ρ)).field x)
        ((B ⟨t, ht.1.le, ht.2.le⟩).field x) t := by
    intro t ht x
    have htc : t + c ∈ Ioo (0 : ℝ) T :=
      ⟨by linarith [ht.1, hc], by linarith [ht.2, hST]⟩
    have hbase := velocity_hasDerivAt_time w htc x
    have hshift : HasDerivAt (fun ρ : ℝ => ρ + c) 1 t := (hasDerivAt_id t).add_const c
    have hcomp := hbase.scomp t hshift
    rw [one_smul] at hcomp
    have h₁ : (fun ρ => w.velocity ((projIcc (0 : ℝ) (S - c) hT' ρ).1 + c, x))
        =ᶠ[𝓝 t] ((fun ρ : ℝ => w.velocity (ρ, x)) ∘ (fun ρ : ℝ => ρ + c)) :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) (fun ρ hρ => by
        show w.velocity ((projIcc (0 : ℝ) (S - c) hT' ρ).1 + c, x) = w.velocity (ρ + c, x)
        rw [projIcc_of_mem hT' (Ioo_subset_Icc_self hρ)])
    exact hcomp.congr_of_eventuallyEq h₁
  have hderiv := wordEnergy_hasDerivWithinAt (S - c) hT' A B hA hB hd 0 ⟨r, hr.1, hr.2.le⟩
  simp only [Nat.zero_add, wordEnergy_zero, wordInner_sum_zero] at hderiv
  exact hderiv.hasDerivAt (Icc_mem_nhds hr.1 hr.2)

end NSFormalization.Section4.C01
