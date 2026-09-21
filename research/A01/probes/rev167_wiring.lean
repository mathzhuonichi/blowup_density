import NSFormalization.Section4.A01.ForceBridge
import NSFormalization.Section4.A01.Horizon
import NSFormalization.Section4.A04.ZeroSolution

/-! Reviewer-only positive probes for lane 167's two consumer handoffs. -/

open Set MeasureTheory NavierStokes.ProblemStatement
open EulerLpTranslation EulerLpTranslation.SmoothL2Field
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerCylinderSobolev EulerPressureSpatialRegularity

noncomputable section
set_option autoImplicit false

namespace NSFormalization.Section4.A01

/-! The force package can be unpacked directly into the two facts used downstream. -/
example {S : ℝ} {f : A02.SpaceTimeField} (hf : D01.MemForceR f) :
    (∀ n, Continuous fun t : Icc (0 : ℝ) S => (C01.forcePath hf t).jetLp n) ∧
      A04.MemL1Hm f := by
  rcases forcePath_of_memForceR (S := S) hf with ⟨F, rfl, hF, hL1⟩
  exact ⟨hF, hL1⟩

/-! Required zero-force instantiation on an inhabited prescribed horizon. -/
example :
    ∃ F : Icc (0 : ℝ) 1 → SmoothL2Field Space,
      F = C01.forcePath A04.memForceR_zero ∧
      (∀ n, Continuous fun t => (F t).jetLp n) ∧
      A04.MemL1Hm (0 : A02.SpaceTimeField) :=
  forcePath_of_memForceR A04.memForceR_zero

/-! These are exactly the relevant `t = 0` clauses in
`localTheory_on_prescribed_horizon`; `SmoothL2Field.toLp_ae` supplies the last premise. -/
example {q : ℕ} {S : ℝ} (hS : 0 < S)
    (a : SmoothL2Field Space)
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hU0 : U ⟨0, le_rfl, hS.le⟩ = a.toLp)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (hdiv : ∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0)
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t,
      sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) :
    a.field ∈ A02.initialClassR := by
  let t0 : Icc (0 : ℝ) S := ⟨0, le_rfl, hS.le⟩
  apply initialClassR_of_smoothL2 (u := u t0) (U := U t0)
  · exact fun θ => hu θ t0
  · exact hU t0
  · exact hdiv t0
  · rw [show U t0 = a.toLp from hU0]
    exact a.toLp_ae.symm

end NSFormalization.Section4.A01
