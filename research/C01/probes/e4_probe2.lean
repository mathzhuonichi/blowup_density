import NSFormalization.Section4.C01.PressureJetPath
import Euler.OrdinaryWordTime

open Set MeasureTheory Filter Topology
open EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
open NavierStokes.ProblemStatement
open scoped RealInnerProductSpace ContDiff

namespace NSFormalization.Section4.C01
open NSFormalization.Section4.A02 (ClassicalSolutionR MemForceR)

variable {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField} {c S T : ℝ}

/-- word energy at s=0 collapses to the L² norm squared. -/
theorem wordEnergy_zero (A : SmoothL2Field Space) :
    wordEnergy 0 A = ‖A.toLp‖ ^ 2 := by
  simp [wordEnergy, wordField_zero]

/-- the s=0 pairing sum collapses to a single L² inner product. -/
theorem wordInner_sum_zero (X Y : SmoothL2Field Space) :
    (∑ n ∈ Finset.range 1, ∑ w : Fin n → Fin 3,
      ⟪(wordField X w).toLp, (wordField Y w).toLp⟫) = ⟪X.toLp, Y.toLp⟫ := by
  simp [wordField_zero]

/-- pointwise time derivative of the velocity, re-proved unconditionally from `velocity_smooth`. -/
theorem velocity_hasDerivAt_time (w : ClassicalSolutionR ν a f T)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) T) (x : Space) :
    HasDerivAt (fun ρ => w.velocity (ρ, x)) (temporalDerivative w.velocity s x) s := by
  have hmap : ContDiffOn ℝ ∞ (fun r : ℝ => ((r, x) : ℝ × Space)) (Ico (0 : ℝ) T) :=
    (contDiff_id.prodMk contDiff_const).contDiffOn
  have hsub : (Ico (0 : ℝ) T) ⊆
      (fun r : ℝ => ((r, x) : ℝ × Space)) ⁻¹' (Ico (0 : ℝ) T ×ˢ (univ : Set Space)) :=
    fun r hr => ⟨hr, mem_univ x⟩
  have hcd : ContDiffOn ℝ ∞ (fun r => w.velocity (r, x)) (Ico (0 : ℝ) T) :=
    w.velocity_smooth.comp hmap hsub
  exact ((hcd.differentiableOn (by simp) s (Ioo_subset_Ico_self hs)).differentiableAt
    (Ico_mem_nhds hs.1 hs.2)).hasDerivAt

theorem energyDerivative_hasDerivAt
    (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    (hc : 0 < c) (hcS : c ≤ S) (hST : S < T)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) (S - c)) :
    HasDerivAt
      (fun ρ : ℝ =>
        ‖(velocityField w hST
            ⟨(projIcc (0:ℝ) (S - c) (sub_nonneg.mpr hcS) ρ).1 + c,
              ⟨by have h := (projIcc (0:ℝ) (S-c) (sub_nonneg.mpr hcS) ρ).2.1; linarith,
               by have h := (projIcc (0:ℝ) (S-c) (sub_nonneg.mpr hcS) ρ).2.2; linarith⟩⟩).toLp‖ ^ 2)
      (2 * ⟪(velocitySliceField w (Ioo_subset_Ico_self
                (mem_Ioo_of_mem_Icc hc hST (show r + c ∈ Icc c S from
                  ⟨by linarith [hr.1], by linarith [hr.2]⟩)))).toLp,
            (temporalSliceField w hf
                (mem_Ioo_of_mem_Icc hc hST (show r + c ∈ Icc c S from
                  ⟨by linarith [hr.1], by linarith [hr.2]⟩))).toLp⟫)
      r := by
  have hT' : (0 : ℝ) ≤ S - c := sub_nonneg.mpr hcS
  -- the velocity-index shift Icc 0 (S-c) → Icc 0 S
  let ιvel : Icc (0:ℝ) (S - c) → Icc (0:ℝ) S := fun ρ =>
    ⟨ρ.1 + c, ⟨by have := ρ.2.1; linarith, by have := ρ.2.2; linarith⟩⟩
  have hιvel : Continuous ιvel :=
    (continuous_subtype_val.add continuous_const).subtype_mk _
  -- the derivative-index shift Icc 0 (S-c) → Icc c S
  let σ : Icc (0:ℝ) (S - c) → Icc c S := fun ρ =>
    ⟨ρ.1 + c, ⟨by have := ρ.2.1; linarith, by have := ρ.2.2; linarith⟩⟩
  have hσ : Continuous σ :=
    (continuous_subtype_val.add continuous_const).subtype_mk _
  -- the two SmoothL2Field paths over the shifted window
  let A : Icc (0:ℝ) (S - c) → SmoothL2Field Space := fun ρ => velocityField w hST (ιvel ρ)
  let B : Icc (0:ℝ) (S - c) → SmoothL2Field Space := fun ρ =>
    temporalSliceField w hf (mem_Ioo_of_mem_Icc hc hST (σ ρ).2)
  have hA : ∀ n, Continuous (fun ρ => (A ρ).jetLp n) :=
    fun n => (velocityField_jetLp_continuous w hST n).comp hιvel
  have hB : ∀ n, Continuous (fun ρ => (B ρ).jetLp n) :=
    fun n => (temporalSlicePath_jetLp_continuous w hf hc hST n).comp hσ
  -- the pointwise hd clause
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
    have h₁ : (fun ρ => w.velocity ((projIcc (0:ℝ) (S - c) hT' ρ).1 + c, x))
        =ᶠ[𝓝 t] ((fun ρ : ℝ => w.velocity (ρ, x)) ∘ (fun ρ : ℝ => ρ + c)) :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) (fun ρ hρ => by
        show w.velocity ((projIcc (0:ℝ) (S - c) hT' ρ).1 + c, x) = w.velocity (ρ + c, x)
        rw [projIcc_of_mem hT' (Ioo_subset_Icc_self hρ)])
    exact hcomp.congr_of_eventuallyEq h₁
  -- apply the vendor derivative machinery at s = 0
  have hderiv := wordEnergy_hasDerivWithinAt (S - c) hT' A B hA hB hd 0 ⟨r, hr.1.le, hr.2.le⟩
  simp only [Nat.zero_add, wordEnergy_zero, wordInner_sum_zero] at hderiv
  have hda := hderiv.hasDerivAt (Icc_mem_nhds hr.1 hr.2)
  exact hda

end NSFormalization.Section4.C01
