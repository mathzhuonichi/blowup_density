/-
  Lane 144 reviewer — dedup probe: are the new lemmas already `simp` one-liners
  from the tree?  Every block below is EXPECTED TO FAIL (i.e. the module earns
  its place).  Run from verification/.
-/
import NSFormalization.Section4.A04.DerivNorm
import NSFormalization.Section4.A04.LaplacianDatum
import NSFormalization.Section4.A04.PressureDrop
import NSFormalization.Section4.D01.DatumToJets

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.D01 (MemForceR SmoothSquareIntegrableJets)
open NSFormalization.Section4.A02 (initialClassR SpatialField SpaceTimeField)

noncomputable section
namespace Rev144Dedup
set_option autoImplicit false

example : MemForceR (0 : SpaceTimeField) := by simp
example : (0 : SpatialField) ∈ initialClassR := by simp
example (s t : ℝ) : NSFormalization.Section4.A04.sobolevNormAt s (0 : SpaceTimeField) t = 0 := by simp
example (s t : ℝ) :
    NSFormalization.Section4.A04.gradientSobolevNormAt s (0 : SpaceTimeField) t = 0 := by simp
example (T : ℝ) : NSFormalization.Section4.A04.HasSmoothSobolevPath T (0 : SpaceTimeField) := by simp
example : SmoothSquareIntegrableJets (fun _ : Space => (0 : Space)) := by simp

end Rev144Dedup
end
