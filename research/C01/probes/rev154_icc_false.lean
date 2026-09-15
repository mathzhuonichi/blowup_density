import NSFormalization.Section4.C01.EnergyBounds
import NSFormalization.Section4.A04.ZeroSolution
import NSFormalization.Section4.A02.Restrict

/-! REVIEW PROBE (lane 154), hardened negative check: the `Ico → Icc` mutation of `l2Bound`
is not merely unprovable by the lane's route — it is **false**.  `ClassicalSolutionR.congr`
(`A02/Restrict.lean:175`) lets one modify the velocity off the slab `[0,T) × R³`, so the
endpoint value `u(T,·)` is unconstrained. -/

noncomputable section

open Set MeasureTheory Filter Topology
open NavierStokes.ProblemStatement
open scoped RealInnerProductSpace ContDiff

namespace NSFormalization.Section4.C01

open NSFormalization.Section4.A02 (ClassicalSolutionR MemForceR)

/-- The indicator of the unit ball, valued in a unit vector: a field of positive `l2Sq`. -/
def bumpField : A02.SpatialField :=
  Set.indicator (Metric.ball (0 : Space) 1) (fun _ => EuclideanSpace.single (0 : Fin 3) (1 : ℝ))

theorem l2Sq_bumpField_pos : 0 < l2Sq bumpField := by
  have he : ‖EuclideanSpace.single (0 : Fin 3) (1 : ℝ)‖ = 1 := by
    simp
  have hpt : ∀ x : Space,
      ‖bumpField x‖ ^ 2 = (Metric.ball (0 : Space) 1).indicator (fun _ => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ Metric.ball (0 : Space) 1
    · rw [Set.indicator_of_mem hx]
      show ‖Set.indicator (Metric.ball (0 : Space) 1) _ x‖ ^ 2 = 1
      rw [Set.indicator_of_mem hx, he]; norm_num
    · rw [Set.indicator_of_notMem hx]
      show ‖Set.indicator (Metric.ball (0 : Space) 1) _ x‖ ^ 2 = 0
      rw [Set.indicator_of_notMem hx]; simp
  have hval : l2Sq bumpField = (volume (Metric.ball (0 : Space) 1)).toReal := by
    show (∫ x : Space, ‖bumpField x‖ ^ 2) = _
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [integral_indicator_const (1 : ℝ) measurableSet_ball, smul_eq_mul, mul_one]
    rfl
  rw [hval]
  refine ENNReal.toReal_pos (ne_of_gt ?_) (measure_ball_lt_top).ne
  exact Metric.measure_ball_pos volume _ one_pos

/-- **The `Icc` mutation of `l2Bound` is false.** -/
theorem l2Bound_Icc_false :
    ¬ (∀ (ν : ℝ), 0 < ν → ∀ a : A02.SpatialField, ∀ f : A02.SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Icc (0 : ℝ) T,
          l2Norm (slice w.velocity t) ≤ energyBudget a f t) := by
  intro h
  set w0 : ClassicalSolutionR 1 0 0 2 :=
    A04.zeroSol 1 2 (by norm_num) (by norm_num) with hw0
  set u : A02.SpaceTimeField := fun z => if z.1 < 2 then 0 else bumpField z.2 with hu_def
  have hu : ∀ z ∈ Ico (0 : ℝ) 2 ×ˢ (univ : Set Space), u z = w0.velocity z := by
    rintro ⟨s, x⟩ ⟨hs, -⟩
    show (if s < 2 then 0 else bumpField x) = (0 : A02.SpaceTimeField) (s, x)
    rw [if_pos hs.2]
    rfl
  have hp : ∀ z ∈ Ico (0 : ℝ) 2 ×ˢ (univ : Set Space), w0.pressure z = w0.pressure z :=
    fun _ _ => rfl
  have key := h 1 (by norm_num) 0 0 A04.memForceR_zero 2 (w0.congr hu hp) 2
    ⟨by norm_num, le_rfl⟩
  have hslice : slice (w0.congr hu hp).velocity 2 = bumpField := by
    funext x
    show (if (2 : ℝ) < 2 then 0 else bumpField x) = bumpField x
    rw [if_neg (lt_irrefl (2 : ℝ))]
  have hbudget : energyBudget (0 : A02.SpatialField) (0 : A02.SpaceTimeField) 2 = 0 := by
    have hzero : l2Norm (0 : A02.SpatialField) = 0 := by
      show Real.sqrt (∫ x : Space, ‖(0 : A02.SpatialField) x‖ ^ 2) = 0
      simp
    have hprim : forcePrimitive (0 : A02.SpaceTimeField) 2 = 0 := by
      show (∫ s in (0 : ℝ)..(2 : ℝ), l2Norm (slice (0 : A02.SpaceTimeField) s)) = 0
      have : ∀ s : ℝ, l2Norm (slice (0 : A02.SpaceTimeField) s) = 0 := by
        intro s
        show Real.sqrt (∫ x : Space, ‖(0 : A02.SpaceTimeField) (s, x)‖ ^ 2) = 0
        simp
      simp [this]
    show l2Norm (0 : A02.SpatialField) + forcePrimitive (0 : A02.SpaceTimeField) 2 = 0
    rw [hzero, hprim]; norm_num
  rw [hslice, hbudget] at key
  have hpos : 0 < l2Norm bumpField := Real.sqrt_pos.mpr l2Sq_bumpField_pos
  linarith

end NSFormalization.Section4.C01
