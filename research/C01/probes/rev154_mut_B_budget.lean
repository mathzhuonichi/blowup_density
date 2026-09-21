import NSFormalization.Section4.C01.EnergyBounds

/-! REVIEW PROBE (lane 154), mutation B: the forcing primitive `∫₀ᵗ‖f(s)‖₂ ds` is dropped
from the budget (`energyBudgetM a f t = l2Norm a`).  Proof of `l2Bound` copied verbatim,
with `energyBudget` replaced by `energyBudgetM` throughout.
Expected: the FTC step `hdN` fails — the budget no longer has derivative `‖f(s)‖₂`. -/

noncomputable section

open Set MeasureTheory Filter Topology
open EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
open NavierStokes.ProblemStatement
open NSFormalization.Paper3
open scoped RealInnerProductSpace ContDiff

namespace NSFormalization.Section4.C01

open NSFormalization.Section4.A02 (ClassicalSolutionR MemForceR)

variable {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField} {T : ℝ}

/-- The mutated budget: `‖a‖₂` alone. -/
def energyBudgetM (a : A02.SpatialField) (_f : A02.SpaceTimeField) (_t : ℝ) : ℝ := l2Norm a

theorem l2Bound_MUT_B (w : ClassicalSolutionR ν a f T) (hf : MemForceR f) (hν : 0 < ν) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) T) :
    l2Norm (slice w.velocity t) ≤ energyBudgetM a f t := by
  have hg_cont : ContinuousOn (fun r => l2Norm (slice f r)) (Ici (0 : ℝ)) :=
    (forceTimeRegularity f hf).2
  have hsub_ico : Icc (0 : ℝ) t ⊆ Ico (0 : ℝ) T :=
    fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
  have hE : ContinuousOn (fun s => l2Sq (slice w.velocity s)) (Icc 0 t) :=
    (velocityL2Sq_continuousOn w).mono hsub_ico
  have huicc : uIcc (0 : ℝ) t = Icc 0 t := uIcc_of_le ht.1
  have hg_int : IntegrableOn (fun r => l2Norm (slice f r)) (uIcc 0 t) volume := by
    rw [huicc]; exact (hg_cont.mono fun r hr => hr.1).integrableOn_Icc
  have hprim_cont : ContinuousOn (fun x => ∫ r in (0 : ℝ)..x, l2Norm (slice f r)) (uIcc 0 t) :=
    intervalIntegral.continuousOn_primitive_interval hg_int
  rw [huicc] at hprim_cont
  have hN : ContinuousOn (energyBudgetM a f) (Icc 0 t) := continuousOn_const
  have hEN0 : Real.sqrt (l2Sq (slice w.velocity 0)) ≤ energyBudgetM a f 0 := by
    have hslice0 : slice w.velocity 0 = a := funext fun x => w.initial x
    rw [hslice0]
    show Real.sqrt (l2Sq a) ≤ l2Norm a
    exact le_of_eq rfl
  have hdN : ∀ s ∈ Ioo (0 : ℝ) t, HasDerivAt (energyBudgetM a f) (l2Norm (slice f s)) s := by
    intro s hs
    have hci : Ici (0 : ℝ) ∈ 𝓝 s := mem_of_superset (Ioi_mem_nhds hs.1) Ioi_subset_Ici_self
    have hcs : ContinuousAt (fun r => l2Norm (slice f r)) s := hg_cont.continuousAt hci
    have hsub_uicc : uIcc (0 : ℝ) s ⊆ Ici (0 : ℝ) := by
      rw [uIcc_of_le hs.1.le]; exact fun r hr => hr.1
    have hii : IntervalIntegrable (fun r => l2Norm (slice f r)) volume 0 s :=
      (hg_cont.mono hsub_uicc).intervalIntegrable
    have hmeas : StronglyMeasurableAtFilter (fun r => l2Norm (slice f r)) (𝓝 s) :=
      ⟨Ioi 0, Ioi_mem_nhds hs.1,
        (hg_cont.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi⟩
    have hprim : HasDerivAt (fun u => ∫ r in (0 : ℝ)..u, l2Norm (slice f r))
        (l2Norm (slice f s)) s :=
      intervalIntegral.integral_hasDerivAt_right hii hmeas hcs
    exact hprim.const_add (l2Norm a)
  have hineq : ∀ s ∈ Ioo (0 : ℝ) t,
      (-2 * ν * gradientSq (slice w.velocity s) + 2 * pairing (slice w.velocity s) (slice f s))
        ≤ 2 * l2Norm (slice f s) * Real.sqrt (l2Sq (slice w.velocity s)) := by
    intro s hs
    have hsT : s ∈ Ioo (0 : ℝ) T := ⟨hs.1, lt_trans hs.2 ht.2⟩
    have hderivE : HasDerivAt (fun σ => l2Sq (slice w.velocity σ))
        (-2 * ν * gradientSq (slice w.velocity s)
          + 2 * pairing (slice w.velocity s) (slice f s)) s :=
      energyIdentity_l2Sq w hf hsT
    have hbound := energyDifferentialBound w hf hsT _ hderivE
    have hdiss : 0 ≤ 2 * ν * gradientSq (slice w.velocity s) :=
      mul_nonneg (mul_nonneg (by norm_num) hν.le) (gradientSq_nonneg _)
    exact le_trans (le_trans (le_add_of_nonneg_right hdiss) hbound) (le_of_eq rfl)
  have key := sqrt_energy_le_primitive' (S := t)
    (E := fun s => l2Sq (slice w.velocity s)) (N := energyBudgetM a f)
    (b := fun s => l2Norm (slice f s))
    (E' := fun s => -2 * ν * gradientSq (slice w.velocity s)
      + 2 * pairing (slice w.velocity s) (slice f s))
    ht.1 hE hN hEN0
    (fun s _ => l2Sq_nonneg _)
    (fun s _ => Real.sqrt_nonneg _)
    (fun s hs => energyIdentity_l2Sq w hf ⟨hs.1, lt_trans hs.2 ht.2⟩)
    hdN hineq
  exact key t ⟨ht.1, le_rfl⟩

end NSFormalization.Section4.C01
