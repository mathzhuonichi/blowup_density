/-
  Lane 144 reviewer — positive probes: the two load-bearing facts behind
  `const_not_jets`, and the A02/D01 `MemForceR` defeq claimed in the docstring.
  Run:  cd verification && lake env lean ../research/MAINT/probes/rev144_positive.lean
-/
import NSFormalization.Section4.A04.ZeroSolution

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.A04

noncomputable section
namespace Rev144Pos

set_option autoImplicit false

-- P1: `const_not_jets` really rests on R³ having infinite volume.
example : (volume (univ : Set Space)) = ⊤ := by simp

-- P2: the docstring's defeq claim: D01.MemForceR = A02.MemForceR.
example : @NSFormalization.Section4.D01.MemForceR = @NSFormalization.Section4.A02.MemForceR := rfl

-- P3: the D01 witness is accepted where an A02.MemForceR is demanded.
example : NSFormalization.Section4.A02.MemForceR 0 := memForceR_zero

-- P4: `zeroSol` really inhabits the A02 restatement that Bindings bridge.
example (ν T : ℝ) (hν : 0 < ν) (hT : 0 < T) :
    NSFormalization.Section4.A02.ClassicalSolutionR ν 0 0 T := zeroSol ν T hν hT

-- P5: the momentum field is the genuine eq:NS residual clause, at interior times.
example (ν T : ℝ) (hν : 0 < ν) (hT : 0 < T) :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν (zeroSol ν T hν hT).velocity
        (zeroSol ν T hν hT).pressure t x = (0 : SpaceTime → Space) (t, x) :=
  (zeroSol ν T hν hT).momentum

-- P6: the `sobolev` field's datum path is continuous on the whole horizon.
example (ν T : ℝ) (hν : 0 < ν) (hT : 0 < T) (m : ℕ) :
    ∃ G : ℝ → NSFormalization.Paper3.RealVectorSobolev (m : ℝ),
      ContinuousOn G (Ico (0 : ℝ) T) ∧
        ∀ t ∈ Ico (0 : ℝ) T,
          NSFormalization.Section4.D01.IsSobolevDatum (m : ℝ)
            (fun x => (zeroSol ν T hν hT).velocity (t, x)) (G t) :=
  (zeroSol ν T hν hT).sobolev m

end Rev144Pos
end
