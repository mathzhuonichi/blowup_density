-- Reviewer probe (lane 142 review, REVIEW_A3_M2.md), preserved verbatim; compiles on this branch.
/- Lane 142 review probe 1: signatures, hstep unification, hf1 load-bearing. -/
import NSFormalization.Section4.A01.GronwallInstance

open Set MeasureTheory
open NSFormalization.Section4.A04
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR initialClassR)
open NSFormalization.Section4.D01 (MemForceR)

set_option pp.fullNames true in
#check @NSFormalization.Section4.A01.highOrder_bddAbove_of_kbnd

set_option pp.fullNames true in
#check @NSFormalization.Section4.A01.highOrder_bddAbove_all_orders_of_kbnd

set_option pp.fullNames true in
#check @NSFormalization.Section4.A01.gronwall_bddAbove_Ico

set_option pp.fullNames true in
#check @NSFormalization.Section4.A04.highContinuationIntegral

#print NSFormalization.Section4.A04.Cgron

namespace Rev142

noncomputable section

/-! ### (2b) `hstep` is `highContinuationIntegral` at `t₀ = 0`, verbatim.

The expected type below is `gronwall_bddAbove_Ico`'s `hstep` slot, written out with
`y := ‖u(·)‖_{H^m}`, `k := ‖u(·)‖²_{H²}`, `b := ‖f(·)‖_{H^m}`, `Cgron := NSFormalization.Section4.A04.Cgron m ν`.
It is discharged by a bare `.2` projection — no congr, no `ring_nf`. -/
theorem hstep_is_highContinuationIntegral_verbatim
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f) (hf1 : MemL1Hm f)
    (w : ClassicalSolutionR ν a f T) (hpath : HasSmoothSobolevPath T w.velocity)
    {m : ℕ} (hm : 3 ≤ m) {T₀ : ℝ} (hT₀T : T₀ ≤ T) :
    ∀ t ∈ Ico (0 : ℝ) T₀,
      (fun t => sobolevNormAt (m : ℝ) w.velocity t) t ≤
        (fun t => sobolevNormAt (m : ℝ) w.velocity t) 0 +
          ∫ s in (0 : ℝ)..t,
            (NSFormalization.Section4.A04.Cgron m ν * (fun s => sobolevNormAt 2 w.velocity s ^ 2) s *
                (fun t => sobolevNormAt (m : ℝ) w.velocity t) s
              + (fun s => sobolevNormAt (m : ℝ) f s) s) :=
  fun t ht =>
    (highContinuationIntegral ν a f T hν ha hf hf1 w hpath m hm 0 t le_rfl ht.1
      (lt_of_lt_of_le ht.2 hT₀T)).2

/-! ### (2c) `hf1 : MemL1Hm f` is NOT load-bearing: it is derivable from `hf`.
Restated without the binder and proved by feeding `memL1Hm_of_memForceR hf`. -/
theorem highOrder_bddAbove_of_kbnd_no_hf1
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f)
    (w : ClassicalSolutionR ν a f T) (hpath : HasSmoothSobolevPath T w.velocity)
    {m : ℕ} (hm : 3 ≤ m) {T₀ Kbnd : ℝ} (hT₀ : 0 < T₀) (hT₀T : T₀ ≤ T)
    (hkbnd : ∀ t ∈ Ico (0 : ℝ) T₀,
        (∫ s in (0 : ℝ)..t, sobolevNormAt 2 w.velocity s ^ 2) ≤ Kbnd) :
    ∀ t ∈ Ico (0 : ℝ) T₀,
      sobolevNormAt (m : ℝ) w.velocity t ≤
        (sobolevNormAt (m : ℝ) w.velocity 0 + (forceSobolevENormL1 (m : ℝ) f).toReal)
          * Real.exp (NSFormalization.Section4.A04.Cgron m ν * Kbnd) :=
  NSFormalization.Section4.A01.highOrder_bddAbove_of_kbnd hν ha hf
    (memL1Hm_of_memForceR hf) w hpath hm hT₀ hT₀T hkbnd

end

end Rev142
