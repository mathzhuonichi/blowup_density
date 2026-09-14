/-
  Lane 144 reviewer — negative (mutation) probes for `A04.ZeroSolution`.
  Each block replays the module's own proof with `0` replaced by a NONZERO
  constant field `c`.  Every block is expected to FAIL to elaborate.
  Run:  cd verification && lake env lean ../research/MAINT/probes/rev144_mutation.lean
-/
import NSFormalization.Section4.A04.ZeroSolution

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.D01 (IsSobolevDatum MemForceR SmoothSquareIntegrableJets sobolevENorm)
open NSFormalization.Section4.A02 (initialClassR MemHInfty IsSolenoidal SpatialField SpaceTimeField)
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Section4.A04 (isSobolevDatum_zero)
open scoped ContDiff

noncomputable section
namespace Rev144

set_option autoImplicit false

/-! ### M1. `jets_zero` at a nonzero constant: same proof, must break. -/
theorem M1_jets_const {c : Space} (hc : c ≠ 0) :
    SmoothSquareIntegrableJets (fun _ : Space => c) := by
  refine ⟨contDiff_const, fun n => ?_⟩
  have : iteratedFDeriv ℝ n (fun _ : Space => c) = 0 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · ext x m; simp
    · exact iteratedFDeriv_const_of_ne (by omega) _
  rw [this]; exact MemLp.zero

/-! ### M2. `zero_mem_initialClassR` at a nonzero constant: same proof, must break. -/
theorem M2_initialClass_const {c : Space} (hc : c ≠ 0) :
    (fun _ : Space => c) ∈ initialClassR := by
  refine ⟨⟨contDiff_const, fun m => ⟨0, isSobolevDatum_zero (m : ℝ)⟩⟩, ?_⟩
  intro x
  simp [spatialDivergence, spatialDerivative]

/-! ### M3. `sobolevNormAt_zero` at a nonzero constant: same proof, must break. -/
theorem M3_sobolevNormAt_const {c : Space} (hc : c ≠ 0) (s t : ℝ) :
    NSFormalization.Section4.A04.sobolevNormAt s (fun _ : SpaceTime => c) t = 0 := by
  have hd : IsSobolevDatum s (fun _ : Space => c) 0 := isSobolevDatum_zero s
  show (sobolevENorm s (fun _ : Space => c)).toReal = 0
  rw [NSFormalization.Section4.A04.sobolevENorm_eq hd]; simp

end Rev144
end
