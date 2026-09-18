import NSFormalization.Section3.T22.OrderZero

/-!
# Non-vacuity probe for `orderZero` (T22 · U-A5)

(a) `orderZero` inhabits the `BoundedDomainNormAPI.orderZero` field type verbatim.
(b) A concrete nonzero `ContDiffBump` field `z : Space → Space` on `Ω = ball 0 1`:
    the identity holds with both sides finite (`< ⊤`) and nonzero, so it is not the
    trivial `⊤ = ⊤` or `0 = 0`.
-/

noncomputable section
namespace T22ProbeA5
open MeasureTheory NavierStokes.ProblemStatement Metric
open NSFormalization.Section3.T22
open NSFormalization.Section4.D01
open NSFormalization.Section4.A02 (SpatialField)
open scoped ContDiff ENNReal

-- (a) `orderZero` has exactly the type of the `BoundedDomainNormAPI.orderZero` field.
example : BoundedDomainNormAPI →
    (∀ (Ω : Set Space), IsOpen Ω → ∀ z : SpatialField, ContDiffOn ℝ ∞ z Ω →
      domainSobolevENorm Ω 0 (restrictField Ω z) = eLpNorm z 2 (volume.restrict Ω)) :=
  BoundedDomainNormAPI.orderZero

example : ∀ (Ω : Set Space), IsOpen Ω → ∀ z : SpatialField, ContDiffOn ℝ ∞ z Ω →
    domainSobolevENorm Ω 0 (restrictField Ω z) = eLpNorm z 2 (volume.restrict Ω) :=
  orderZero

-- (b) concrete nonzero bump field on `ball 0 1`.
def bump : ContDiffBump (0 : Space) := ⟨1, 2, one_pos, one_lt_two⟩
def zField : Space → Space := fun x => bump x • coordinateVector 0

theorem zField_contDiff : ContDiff ℝ ∞ zField := bump.contDiff.smul contDiff_const

theorem zField_hasCompactSupport : HasCompactSupport zField := by
  show HasCompactSupport ((fun r : ℝ => r • coordinateVector 0) ∘ (bump : Space → ℝ))
  exact bump.hasCompactSupport.comp_left (by simp)

theorem zField_memLp : MemLp zField 2 volume :=
  zField_contDiff.continuous.memLp_of_hasCompactSupport zField_hasCompactSupport

/-- On `ball 0 1` the bump is `1`, so the field is the constant `coordinateVector 0`. -/
theorem zField_eq_on_ball : ∀ x ∈ ball (0 : Space) 1, zField x = coordinateVector 0 := by
  intro x hx
  have hb : bump x = 1 :=
    bump.one_of_mem_closedBall (ball_subset_closedBall hx)
  simp only [zField, hb, one_smul]

theorem zField_ne_zero : zField 0 ≠ 0 := by
  have hz : zField 0 = coordinateVector 0 :=
    zField_eq_on_ball 0 (mem_ball_self one_pos)
  rw [hz, coordinateVector]; simp

/-- The `orderZero` identity for this concrete field, with both sides finite for a nonzero field. -/
theorem probe_closes :
    domainSobolevENorm (ball 0 1) 0 (restrictField (ball 0 1) zField)
        = eLpNorm zField 2 (volume.restrict (ball 0 1))
      ∧ eLpNorm zField 2 (volume.restrict (ball 0 1)) < ⊤
      ∧ zField 0 ≠ 0 := by
  have heq := orderZero (ball 0 1) isOpen_ball zField zField_contDiff.contDiffOn
  refine ⟨heq, ?_, zField_ne_zero⟩
  calc eLpNorm zField 2 (volume.restrict (ball 0 1))
      ≤ eLpNorm zField 2 volume := eLpNorm_mono_measure _ Measure.restrict_le_self
    _ < ⊤ := zField_memLp.2

end T22ProbeA5

#print axioms T22ProbeA5.probe_closes
