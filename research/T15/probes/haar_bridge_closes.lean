import NSFormalization.Section3.T15.HaarBridge
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# T15 U-TB1 non-vacuity probe

The three shipped U-TB1 identities are instantiated at an explicit smooth
*nonzero* field supported strictly inside the fundamental cube — the same
`ContDiffBump` witness used by `research/T13/probes/constant_endpoints_closes.lean`.
This shows the hypotheses of `eLpNorm_torusLift_periodize`,
`eLpNorm_torusLift_spatialGradient_periodize` and
`eLpNorm_torusLift_periodize_slice` are jointly satisfiable at a genuine packet,
so the equalities are not vacuous.

`research/` is not a Lean root, so the witness is restated here verbatim.
Run: `cd verification && lake env lean ../research/T15/probes/haar_bridge_closes.lean`.
-/

noncomputable section

namespace NSFormalization.Section3.T15

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section4.I02 (spatialGradient)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open scoped ContDiff ENNReal BigOperators Topology

/-! ## The explicit witness (restated from the lane-344 probe). -/

/-- Centre of the fundamental cube. -/
def probeCenter : Space := (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun _ => (1/2 : ℝ))

/-- A genuine smooth bump supported in `closedBall probeCenter (1/4)`. -/
def probeBump : ContDiffBump probeCenter := ⟨1/8, 1/4, by norm_num, by norm_num⟩

/-- A nonzero smooth vector field supported in `ball probeCenter (3/8)`. -/
def probeField : SpatialField := fun x => (probeBump x) • coordinateVector 0

theorem probe_ball_admissible :
    closure (Metric.ball probeCenter (3/8 : ℝ)) ⊆ interior fundamentalCube := by
  refine (Metric.closure_ball_subset_closedBall).trans ?_
  rw [interior_fundamentalCube]
  intro x hx i
  have hd : ‖x - probeCenter‖ ≤ 3/8 := by
    rw [← dist_eq_norm]; exact hx
  have h1 : |x i - probeCenter i| ≤ 3/8 := by
    have h := abs_spaceCoord_le_norm (x - probeCenter) i
    have h2 : (x - probeCenter) i = x i - probeCenter i := rfl
    rw [h2] at h
    linarith
  have hc : probeCenter i = 1/2 := rfl
  rw [hc, abs_le] at h1
  exact ⟨by linarith [h1.1], by linarith [h1.2]⟩

theorem probeField_contDiff : ContDiff ℝ ∞ probeField :=
  probeBump.contDiff.smul contDiff_const

theorem probeField_supported : SupportedInBall probeCenter (3/8 : ℝ) probeField := by
  have hsub : Function.support probeField ⊆ Function.support (⇑probeBump) := by
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro hg
    exact hx (by simp [probeField, hg])
  have h1 : tsupport probeField ⊆ tsupport (⇑probeBump) := closure_mono hsub
  rw [probeBump.tsupport_eq] at h1
  refine h1.trans ?_
  intro y hy
  rw [Metric.mem_closedBall] at hy
  rw [Metric.mem_ball]
  have hr : probeBump.rOut = (1/4 : ℝ) := rfl
  rw [hr] at hy
  linarith

/-- The interior support hypothesis consumed by every U-TB1 identity. -/
theorem probeField_tsupport_interior :
    tsupport probeField ⊆ interior fundamentalCube :=
  probeField_supported.trans (subset_closure.trans probe_ball_admissible)

/-! ## Non-vacuity of the three shipped identities. -/

/-- Goal 1 holds at the concrete nonzero packet. -/
example :
    eLpNorm (torusLift (periodize probeField)) 2 periodicTorusMeasure
      = eLpNorm probeField 2 volume :=
  eLpNorm_torusLift_periodize probeField probeField_contDiff probeField_tsupport_interior

/-- Goal 2 (gradient companion) holds at the concrete packet, at any time. -/
example (t : ℝ) :
    eLpNorm (torusLift
        (fun x => spatialGradient (fun p : SpaceTime => periodize probeField p.2) t x)) 2
        periodicTorusMeasure = gradientENorm probeField volume :=
  eLpNorm_torusLift_spatialGradient_periodize probeField probeField_contDiff t
    probeField_tsupport_interior

/-- Goal 3 (time-slice form) holds for the constant-in-time extension. -/
example (t : ℝ) :
    eLpNorm (torusLift (periodize
        (fun x => (fun p : SpaceTime => probeField p.2) (t, x)))) 2 periodicTorusMeasure
      = eLpNorm (fun x => (fun p : SpaceTime => probeField p.2) (t, x)) 2 volume :=
  eLpNorm_torusLift_periodize_slice (fun p : SpaceTime => probeField p.2) t
    probeField_contDiff probeField_tsupport_interior

end NSFormalization.Section3.T15
