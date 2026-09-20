import NSFormalization.Section3.T12.Cutoff
import NSFormalization.Section3.T12.TameProduct

/-!
# U2 closure probe

This uses the same finitely supported two-mode coefficient pattern (the
`probeFreq`/`probeCoeff` definitions) as `tame_product_closes.lean`, turns its
real scalar Fourier series into a genuine three-vector field, and checks
directly that cutoff localization is unchanged on the fundamental cube.  The
research probes are compiled as standalone source files, so the two tiny
coefficient definitions are repeated here rather than imported.
-/

noncomputable section

namespace NSFormalization.Section3.T12

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open NSFormalization.Section4.A02 (SpatialField)
open scoped ENNReal BigOperators

def probeFreq : PeriodicFrequency := fun i ↦ if i = 0 then 1 else 0

def probeCoeff (k : PeriodicFrequency) : ℂ :=
  if k = probeFreq then 1 else if k = -probeFreq then 1 else 0

/-- The two-mode real scalar from the TameProduct probe. -/
def probeScalar : Space → ℝ := scalarOfCoeff probeCoeff

/-- Put that scalar in every one of the three vector components. -/
def probeVector : SpatialField := fun x ↦
  WithLp.toLp 2 (fun _ : Fin 3 ↦ probeScalar x)

example : ∀ x ∈ fundamentalCube,
    cutoffMul probeVector x = probeVector x := by
  intro x hx
  simp [cutoffMul, probeVector, cutoff_eq_one x hx]

example : EqOn (cutoffMul probeVector) probeVector fundamentalCube :=
  cutoffMul_eq_on_cube probeVector

end NSFormalization.Section3.T12
