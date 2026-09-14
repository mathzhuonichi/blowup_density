import NSFormalization.Section4.A01.Horizon
import Euler.OrdinaryCauchyInterpolation
import Euler.OrdinaryH3Norms
import Euler.SmoothL2Series
import Euler.LpSmoothFieldAlgebra

/-! Transitive-constant audit for lane 139-A01 (unit A3 row A3-L2, module
`NSFormalization.Section4.A01.Horizon`).  Every new declaration must depend on exactly
`[propext, Classical.choice, Quot.sound]`. -/

open NSFormalization.Section4.A01

#print axioms HasAprioriBound
#print axioms horizonOf
#print axioms horizonOf_eq
#print axioms localTheory_on_prescribed_horizon
#print axioms exists_local_shape_of_aprioriBound

/-! Non-vacuity (mirroring `research/A01/axioms_a2b_inv.lean`): the shared hypotheses `ha` and
`hu₀` of `localTheory_on_prescribed_horizon` / `exists_local_shape_of_aprioriBound` are jointly
satisfiable on concrete data (`zeroField`) — a genuine instantiation, not a re-application of
the theorem under its own hypotheses.

The remaining hypothesis `HasAprioriBound` is **deliberately not** instantiated here: it is
nobody's theorem yet, even for zero data — producing it needs the uniform bound over all mild
solutions that A3-M2 (Grönwall) + A3-L1·k (order-2 cap) will supply, and lane 134's reviewer
finding F5 records that even the zero-data instance would itself need the global uniqueness the
continuation stack deliberately avoids.  So, exactly like its parent
`forced_global_of_bound_unconditional`, the full A3-L2 theorem has no concrete instantiation
until A3 supplies `HasAprioriBound`; this file audits axioms and the two shared premises only. -/

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
