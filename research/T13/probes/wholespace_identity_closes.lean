import NSFormalization.Section3.T13.WholeSpaceIdentity
import Contracts.V1.Data
import Contracts.V1.HomogeneousNorm
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Lane 348 closure probe

`research/` is not a Lean module root, so this probe closes the exact
`wholeSpace_identity` field of `research/T13/probes/api_on_canonical.lean`
(the whole-space Gagliardo/Fourier identity, `03-torus.tex:40-51`) with the
shipped `NSFormalization.Section3.T13.wholeSpace_identity`, and instantiates it
on an explicit smooth, nonzero, compactly supported witness field.
-/

noncomputable section

namespace NSFormalization.Section3.T13

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section4.D01 (dotHomogeneousENorm)
open scoped ContDiff ENNReal BigOperators Topology

/-! The registered whole-space field and norm vocabulary is reused definitionally. -/

example :
    NSFormalization.Section4.A02.SpatialField =
      BlowupDensity.Contracts.V1.Data.SpatialField := rfl

example (s : ℝ) (f : SpatialField) :
    dotHomogeneousENorm s f =
      BlowupDensity.Contracts.V1.HomogeneousNorm.dotHomogeneousENorm s f := rfl

/-! ## The `wholeSpace_identity` field, closed verbatim -/

example :
    ∀ (s : ℝ), 0 < s → s < 1 → ∀ f : SpatialField,
      ContDiff ℝ ∞ f → HasCompactSupport f →
        IReal s f < ⊤ ∧
          IReal s f = cFrac s * dotHomogeneousENorm s f ^ (2 : ℕ) :=
  wholeSpace_identity

/-! ## Non-vacuity: an explicit smooth nonzero compactly supported field -/

/-- Centre of the fundamental cube. -/
def probeCenter : Space := (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun _ => (1/2 : ℝ))

/-- A genuine smooth bump supported in `closedBall probeCenter (1/4)`. -/
def probeBump : ContDiffBump probeCenter := ⟨1/8, 1/4, by norm_num, by norm_num⟩

/-- A nonzero smooth vector field supported in `ball probeCenter (3/8)`. -/
def probeField : SpatialField := fun x => (probeBump x) • coordinateVector 0

theorem probeField_contDiff : ContDiff ℝ ∞ probeField :=
  probeBump.contDiff.smul contDiff_const

theorem probeField_hasCompactSupport : HasCompactSupport probeField :=
  probeBump.hasCompactSupport.smul_right

theorem probeField_ne_zero : probeField probeCenter ≠ 0 := by
  have h1 : probeBump probeCenter = 1 :=
    probeBump.one_of_mem_closedBall (Metric.mem_closedBall_self probeBump.rIn_pos.le)
  have h2 : probeField probeCenter = coordinateVector 0 := by simp [probeField, h1]
  rw [h2]
  intro hcon
  have hz : (coordinateVector (0 : Fin 3)) 0 = 0 := by rw [hcon]; rfl
  rw [coordinateVector] at hz
  simp at hz

/-- The identity, instantiated on the explicit nonzero witness at `s = 1/2`:
`IReal` is finite and equals `c_s` times the squared homogeneous norm. -/
example :
    IReal (1/2 : ℝ) probeField < ⊤ ∧
      IReal (1/2 : ℝ) probeField
        = cFrac (1/2) * dotHomogeneousENorm (1/2) probeField ^ (2 : ℕ) :=
  wholeSpace_identity (1/2) (by norm_num) (by norm_num) probeField
    probeField_contDiff probeField_hasCompactSupport

end NSFormalization.Section3.T13
