import NSFormalization.Section4.A01.Continuation
import Euler.OrdinaryCauchyInterpolation
import Euler.OrdinaryH3Norms
import Euler.SmoothL2Series
import Euler.LpSmoothFieldAlgebra

/-! Transitive-axiom audit for lane 126-A01 (unit A2b / A3 row A2b-a′).
Every declaration of `NSFormalization.Section4.A01.Continuation` must depend on exactly
`[propext, Classical.choice, Quot.sound]`. -/

open NSFormalization.Section4.A01

#print axioms forced_global_mild_of_bound
#print axioms forced_mild_divergenceFree
#print axioms forced_ordinary_descent
#print axioms forced_global_of_bound
#print axioms forced_global_of_bound'
#print axioms forced_uniform_restart_time

/-! Non-vacuity (reviewer F5): `ha` and `hu₀` are jointly satisfiable on concrete data
(`zeroField`), rather than re-applying the theorem under its own hypotheses (the
`logs/LESSONS.md` anti-pattern). -/
open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanSmoothRepresentative
open EulerOrdinarySobolev EulerSmoothL2Series EulerCylinderSobolevSpace

noncomputable section
set_option autoImplicit false

-- (c1) zero data is divergence-free: `ha` is satisfiable.
example : ∀ x, EulerSmoothLimit.divergence (SmoothL2Field.zeroField : SmoothL2Field Space).field x = 0 := by
  intro x
  simp [EulerSmoothLimit.divergence, SmoothL2Field.zeroField]

-- (c2) zero data satisfies `hu₀` for every `R ≥ 0`.
example {q : ℕ} {R : ℝ} (hR : 0 ≤ R) :
    ‖ordinarySobolev (q + 1) (SmoothL2Field.zeroField : SmoothL2Field Space).toLp
      (SmoothL2Field.zeroField : SmoothL2Field Space).translation_contDiff‖ ≤ R := by
  refine (ordinarySobolev_norm_le_tensor SmoothL2Field.zeroField (q + 1)).trans ?_
  have h : tensorNorm (q + 1) (SmoothL2Field.zeroField : SmoothL2Field Space) = 0 := by
    simp [tensorNorm, zeroField_jet]
  rw [h]; exact hR
