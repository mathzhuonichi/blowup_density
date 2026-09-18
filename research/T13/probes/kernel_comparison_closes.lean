import NSFormalization.Section3.T13.KernelComparison
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Lane 354 closure probe

`research/` is not a Lean module root, so this probe re-derives the concrete
witnesses (an admissible ball and a genuine smooth bump field supported in it)
and then

* instantiates the four shipped items of lane 354 on them (non-vacuity):
  `exists_separation`, `tailGeomConst_lt_top`, `latticeTail_le_tailGeomConst`,
  `iTorus_singular_le`, `iTorus_periodize_le`;
* records, in one `example`, how lane 359 will feed `iTorus_periodize_le`
  (this lane's §2 estimate) into the homogeneous term of `localization`,
  together with `torus_identity` (lane 345) and a `wholeSpace_identity`-shaped
  fact (lanes 345/348) — supplied as hypotheses of the `example` only.

The bump witness is identical to lane 344's `constant_endpoints_closes.lean`.
-/

noncomputable section

namespace NSFormalization.Section3.T13

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section4.D01 (dotHomogeneousENorm)
open NSFormalization.Section3.T10
open scoped ContDiff ENNReal BigOperators Topology

/-! ## The admissible ball and a genuine smooth compactly supported witness. -/

/-- Centre of the fundamental cube. -/
def probeCenter : Space := (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun _ => (1 / 2 : ℝ))

/-- A genuine smooth bump supported in `closedBall probeCenter (1/4)`. -/
def probeBump : ContDiffBump probeCenter := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- A nonzero smooth vector field supported in `ball probeCenter (3/8)`. -/
def probeField : SpatialField := fun x => (probeBump x) • coordinateVector 0

theorem probe_ball_admissible :
    closure (Metric.ball probeCenter (3 / 8 : ℝ)) ⊆ interior fundamentalCube := by
  refine (Metric.closure_ball_subset_closedBall).trans ?_
  rw [interior_fundamentalCube]
  intro x hx i
  have hd : ‖x - probeCenter‖ ≤ 3 / 8 := by
    rw [← dist_eq_norm]; exact hx
  have h1 : |x i - probeCenter i| ≤ 3 / 8 := by
    have h := abs_spaceCoord_le_norm (x - probeCenter) i
    have h2 : (x - probeCenter) i = x i - probeCenter i := rfl
    rw [h2] at h
    linarith
  have hc : probeCenter i = 1 / 2 := rfl
  rw [hc, abs_le] at h1
  exact ⟨by linarith [h1.1], by linarith [h1.2]⟩

theorem probeField_contDiff : ContDiff ℝ ∞ probeField :=
  probeBump.contDiff.smul contDiff_const

theorem probeField_supported : SupportedInBall probeCenter (3 / 8 : ℝ) probeField := by
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
  have hr : probeBump.rOut = 1 / 4 := rfl
  rw [hr] at hy
  linarith

theorem probeCenter_mem_cube : probeCenter ∈ fundamentalCube := by
  intro i
  have hc : probeCenter i = 1 / 2 := rfl
  rw [hc]; exact ⟨by norm_num, by norm_num⟩

theorem probeCenter_mem_closure_ball :
    probeCenter ∈ closure (Metric.ball probeCenter (3 / 8 : ℝ)) :=
  subset_closure (Metric.mem_ball_self (by norm_num))

/-! ## Item 1 (separation), non-vacuous. -/

example : ∃ δ : ℝ, 0 < δ ∧
    closure (Metric.ball probeCenter (3 / 8 : ℝ)) ⊆
      {x : Space | ∀ i, δ ≤ x i ∧ x i ≤ 1 - δ} :=
  exists_separation (by norm_num) probe_ball_admissible

/-! ## Item 2 (the geometric constant), non-vacuous. -/

example : tailGeomConst (1 / 2 : ℝ) probeCenter (3 / 8 : ℝ) < ⊤ :=
  tailGeomConst_lt_top (by norm_num) (by norm_num) probe_ball_admissible

example : latticeTail (1 / 2 : ℝ) (probeCenter - probeCenter)
    ≤ tailGeomConst (1 / 2 : ℝ) probeCenter (3 / 8 : ℝ) :=
  latticeTail_le_tailGeomConst (by norm_num) (by norm_num) probe_ball_admissible
    probeCenter probeCenter_mem_closure_ball probeCenter probeCenter_mem_cube

/-! ## Item 3 (singular part), non-vacuous. -/

example :
    (∫⁻ x in fundamentalCube, ∫⁻ y in fundamentalCube,
        ENNReal.ofReal (‖probeField x - probeField y‖ ^ 2)
          * fractionalRadialKernel (1 / 2 : ℝ) (x - y))
      ≤ IReal (1 / 2 : ℝ) probeField :=
  iTorus_singular_le probeField_contDiff.continuous

/-! ## Item 4 (the assembled kernel comparison), non-vacuous. -/

example :
    ITorus (1 / 2 : ℝ) (periodize probeField)
      ≤ IReal (1 / 2 : ℝ) probeField
        + 4 * tailGeomConst (1 / 2 : ℝ) probeCenter (3 / 8 : ℝ)
          * (eLpNorm probeField 2 volume) ^ 2 :=
  iTorus_periodize_le (by norm_num) (by norm_num) (by norm_num) probe_ball_admissible
    probeField_contDiff probeField_supported

/-! ## Consumer sketch: how lane 359 feeds the homogeneous term of `localization`.

`iTorus_periodize_le` (this lane) bounds the torus difference integral; combined
with `torus_identity` (lane 345, `hTorusId`) and `wholeSpace_identity`
(lanes 345/348, `hWhole`) — both hypotheses of the example only — it bounds the
`cFrac`-weighted square of the torus homogeneous norm by the corresponding
whole-space square plus `4·tailGeomConst·‖f‖₂²`.  Lane 359 then divides by
`cFrac s > 0` (`constant_pos_finite`, lane 344) and takes square roots, and
combines the result with the `L²` term through
`periodicSobolevENorm_le_l2_add_homogeneous` (lane 353). -/
example {s : ℝ} {c : Space} {r : ℝ} {f : SpatialField}
    (hs : 0 < s) (hs1 : s < 1) (hr : 0 < r)
    (hball : closure (Metric.ball c r) ⊆ interior fundamentalCube)
    (hf : ContDiff ℝ ∞ f) (hsupp : SupportedInBall c r f)
    (hTorusId : ITorus s (periodize f)
        = cFrac s * periodicHomogeneousENorm s (meanZeroPartT (periodize f)) ^ 2)
    (hWhole : IReal s f = cFrac s * dotHomogeneousENorm s f ^ 2) :
    cFrac s * periodicHomogeneousENorm s (meanZeroPartT (periodize f)) ^ 2
      ≤ cFrac s * dotHomogeneousENorm s f ^ 2
        + 4 * tailGeomConst s c r * (eLpNorm f 2 volume) ^ 2 := by
  rw [← hTorusId, ← hWhole]
  exact iTorus_periodize_le hs hs1 hr hball hf hsupp

end NSFormalization.Section3.T13
