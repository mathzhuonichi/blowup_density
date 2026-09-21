import NSFormalization.Section4.A01.AprioriRows

/-!
Conformance for lane 149 (`Section4/A01/AprioriRows.lean`).  Every declaration must have
`#print axioms` = `[propext, Classical.choice, Quot.sound]`, and a cheap non-vacuity witness
must fire the two backbone theorems on a concrete instance (the zero cylinder field / the zero
smooth field), yielding a genuine, non-vacuous conclusion.
-/

noncomputable section
open Set MeasureTheory
open NSFormalization.Section4.D01
open NSFormalization.Section4.A01
open NSFormalization.Paper3 (RealVectorSobolev)
open NavierStokes.ProblemStatement (Space)
open EulerCylinderSobolevSpace
open scoped ENNReal ContDiff

-- (iii) widening
#print axioms kbnd_of_sup_bound_Icc
#print axioms highOrder_bddAbove_of_kbnd_Icc
#print axioms highOrder_bddAbove_all_orders_of_kbnd_Icc

-- (ii) converse
#print axioms sobolevSpace_norm_le_of_forall_word
#print axioms eLpNorm_iteratedFDeriv_le_sobolevENorm_toReal
#print axioms sobolevSpace_norm_le_sobolevENorm
#print axioms sobolevSpace_norm_le_sobolevNormAt

/-! ## Non-vacuity -/

/-- The backbone fires on the zero cylinder field, giving a genuine conclusion `‖(0)‖ ≤ 0`
(so `‖(0 : SobolevSpace 1 q)‖ = 0`). -/
theorem nonvacuous_backbone (q : ℕ) : ‖(0 : SobolevSpace 1 q)‖ ≤ 0 := by
  refine sobolevSpace_norm_le_of_forall_word (0 : SobolevSpace 1 q) le_rfl (fun n hn w => ?_)
  rw [show word 1 (0 : SobolevSpace 1 q) hn w = 0 from rfl, norm_zero]

#print axioms nonvacuous_backbone

/-- The reverse embedding fires on the zero smooth field, giving `0 ≤ jetSobolevConst (q+1) * 0`,
a genuine `0 ≤ 0` inequality (not the vacuous `⊤`-case): the zero field is smooth and `H^{q+1}`. -/
theorem nonvacuous_reverse (q n : ℕ) (hn : n ≤ q + 1) :
    (eLpNorm (iteratedFDeriv ℝ n (fun _ : Space => (0 : Space))) 2 volume).toReal
      ≤ jetSobolevConst (q + 1)
        * (sobolevENorm ((q + 1 : ℕ) : ℝ) (fun _ : Space => (0 : Space))).toReal := by
  have hz : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Space => (0 : Space)) := contDiff_const
  have hL2 : ∀ k : ℕ, MemLp (iteratedFDeriv ℝ k (fun _ : Space => (0 : Space))) 2 volume := by
    intro k
    have : iteratedFDeriv ℝ k (fun _ : Space => (0 : Space)) = 0 := iteratedFDeriv_fun_zero
    rw [this]; exact MemLp.zero
  exact eLpNorm_iteratedFDeriv_le_sobolevENorm_toReal q n hn hz
    (sobolevENorm_ne_top_of_contDiff_memLp hz hL2 _)

#print axioms nonvacuous_reverse

/-! ## Lane-149 review follow-up: new declarations + assembled-theorem non-vacuity (N4) -/

open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Section4.A04 (sobolevNormAt)
open EulerMeanOrdinaryLift

#print axioms kbnd_of_sup_bound_Icc_endpoint
#print axioms sobolevENorm_congr_ae
#print axioms sobolevSpace_norm_le_sobolevENorm_ordinary

/-- Non-vacuity for the assembled single-slice converse (theorem 6): fires on `u = 0`, `z = 0`,
so `hword_jet` is genuinely exercised and the conclusion is a real `0 ≤ jetSobolevConst (q+1) * 0`.
(Reviewer probe §4.) -/
theorem nonvacuous_assembled (q : ℕ) :
    ‖(0 : SobolevSpace 1 (q + 1))‖
      ≤ jetSobolevConst (q + 1)
        * (sobolevENorm ((q + 1 : ℕ) : ℝ) (fun _ : Space => (0 : Space))).toReal := by
  refine sobolevSpace_norm_le_sobolevENorm (0 : SobolevSpace 1 (q + 1)) contDiff_const
    (sobolevENorm_ne_top_of_contDiff_memLp contDiff_const
      (fun k => by rw [show iteratedFDeriv ℝ k (fun _ : Space => (0 : Space)) = 0 from
        iteratedFDeriv_fun_zero]; exact MemLp.zero) _) (fun n hn w => ?_)
  rw [show word 1 (0 : SobolevSpace 1 (q + 1)) hn w = 0 from rfl, norm_zero]
  exact ENNReal.toReal_nonneg

#print axioms nonvacuous_assembled

/-- Non-vacuity for the assembled time-indexed converse (theorem 7): fires on the zero cylinder
path and the zero space-time field. -/
theorem nonvacuous_assembled_time (q : ℕ) (T : ℝ) :
    ∀ t : Icc (0 : ℝ) T,
      ‖(0 : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1))) t‖
        ≤ jetSobolevConst (q + 1) * sobolevNormAt ((q + 1 : ℕ) : ℝ) (0 : SpaceTimeField) ↑t := by
  refine sobolevSpace_norm_le_sobolevNormAt (0 : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)))
    (0 : SpaceTimeField) (fun t => contDiff_const) (fun t => ?_) (fun t n hn w => ?_)
  · -- the slice `fun x => (0 : SpaceTimeField) (↑t, x)` is (literally) the zero field; move the
    -- energy norm onto the clean zero-field form via `sobolevENorm_congr_ae`.
    rw [show sobolevENorm ((q + 1 : ℕ) : ℝ) (fun x : Space => (0 : SpaceTimeField) (↑t, x))
        = sobolevENorm ((q + 1 : ℕ) : ℝ) (fun _ : Space => (0 : Space)) from
      sobolevENorm_congr_ae Filter.EventuallyEq.rfl]
    exact sobolevENorm_ne_top_of_contDiff_memLp contDiff_const
      (fun k => by rw [iteratedFDeriv_fun_zero]; exact MemLp.zero) _
  · rw [show ((0 : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1))) t) = 0 from rfl,
      show word 1 (0 : SobolevSpace 1 (q + 1)) hn w = 0 from rfl, norm_zero]
    exact ENNReal.toReal_nonneg

#print axioms nonvacuous_assembled_time

/-- Non-vacuity for the ordinary-carrier corollary (N5 shape): fires on `u = 0`, `U = 0`, `z = 0`. -/
theorem nonvacuous_assembled_ordinary (q : ℕ) :
    ‖(0 : SobolevSpace 1 (q + 1))‖
      ≤ jetSobolevConst (q + 1)
        * (sobolevENorm ((q + 1 : ℕ) : ℝ) (⇑(0 : EulerMeanSolenoidal.L2))).toReal := by
  have hz0 : (fun _ : Space => (0 : Space)) =ᵐ[volume] ⇑(0 : EulerMeanSolenoidal.L2) :=
    (Lp.coeFn_zero _ _ _).symm
  refine sobolevSpace_norm_le_sobolevENorm_ordinary (0 : SobolevSpace 1 (q + 1))
    (0 : EulerMeanSolenoidal.L2) contDiff_const hz0 ?_ (fun n hn w => ?_)
  · rw [← sobolevENorm_congr_ae hz0]
    exact sobolevENorm_ne_top_of_contDiff_memLp contDiff_const
      (fun k => by rw [show iteratedFDeriv ℝ k (fun _ : Space => (0 : Space)) = 0 from
        iteratedFDeriv_fun_zero]; exact MemLp.zero) _
  · rw [show word 1 (0 : SobolevSpace 1 (q + 1)) hn w = 0 from rfl, norm_zero]
    exact ENNReal.toReal_nonneg

#print axioms nonvacuous_assembled_ordinary
