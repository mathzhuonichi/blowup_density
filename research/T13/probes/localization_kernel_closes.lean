import NSFormalization.Section3.T13.LocalizationKernel
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Lane 353 closure probe

`research/` is not a Lean module root, so this probe re-derives the concrete
witnesses and instantiates the three shipped estimates of lane 353 on them
(non-vacuity):

* The primary witness is the lane-344 `ContDiffBump` field `probeField`
  (`research/T13/probes/constant_endpoints_closes.lean:200-262`), supported in
  the admissible ball `ball probeCenter (3/8)`.  On it:
  `two_r_lt_one_of_closure_ball_subset` gives `2 * (3/8) < 1`, and the §1 tail
  bound `latticeTail_le_tailConst` applies at the support-difference radius
  `2 * (3/8)` to every difference `x - y` of two points of the support ball.
* `tailSum_lt_top` / `tailConst_lt_top` / `summable_latticeVector_rpow` witness
  finiteness of the §1 constant.
* §3 (`periodicSobolevENorm_le_l2_add_homogeneous`) needs a smooth *periodic*
  field, which the compactly supported bump is not, so it is instantiated on
  the nonconstant smooth periodic mode `cos(2π x₀) e₀` as an additional
  instance.
* One `example` records lane 354's assembly step: §3 followed by
  `add_le_add hL2 hHom`, with the two bounds it supplies as hypotheses only.

The §2 kernel comparison `iTorus_periodize_le` is lane 354's (with the
clearance constant `C_{s,d}` identified in
`research/T13/ATTEMPTS_LOCALIZATION_KERNEL.md`); the coefficient-vs-physical
`L²` bridge is lane 359's.  Neither is attempted here.
-/

noncomputable section

namespace NSFormalization.Section3.T13

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section3.T10
open scoped ContDiff ENNReal BigOperators Topology

/-! ## §1 finiteness of the auxiliary lattice constant -/

example : Summable (fun n : PeriodicFrequency => ‖latticeVector n‖ ^ (-(4 : ℝ))) :=
  summable_latticeVector_rpow (by norm_num)

example : tailSum (1 / 2 : ℝ) < ⊤ := tailSum_lt_top (by norm_num)

example : tailConst (1 / 2 : ℝ) (3 / 4 : ℝ) < ⊤ := tailConst_lt_top (by norm_num) (by norm_num)

/-! ## The lane-344 `ContDiffBump` witness (copied verbatim) -/

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

/-- The witness field is genuinely nonzero. -/
theorem probeField_ne_zero : probeField probeCenter ≠ 0 := by
  have h1 : probeBump probeCenter = 1 :=
    probeBump.one_of_mem_closedBall (Metric.mem_closedBall_self probeBump.rIn_pos.le)
  have h2 : probeField probeCenter = coordinateVector 0 := by simp [probeField, h1]
  rw [h2]
  intro hcon
  have hz : (coordinateVector (0 : Fin 3)) 0 = 0 := by rw [hcon]; rfl
  rw [coordinateVector] at hz
  simp at hz

/-! ## The shipped estimates on the bump witness -/

/-- `two_r_lt_one` on the bump's admissible ball: the support-difference radius
`2 * (3/8) = 3/4` is genuinely below `1`. -/
example : 2 * (3 / 8 : ℝ) < 1 :=
  two_r_lt_one_of_closure_ball_subset (by norm_num) probe_ball_admissible

/-- The §1 tail bound on the bump support: for any two points of
`ball probeCenter (3/8)` the lattice tail at their difference is controlled by
`tailConst s (2 * (3/8))`.  This is exactly the region of lane 354's tail
estimate in which both points lie in the support ball. -/
example {s : ℝ} (hs : 0 ≤ s) {x y : Space}
    (hx : x ∈ Metric.ball probeCenter (3 / 8 : ℝ))
    (hy : y ∈ Metric.ball probeCenter (3 / 8 : ℝ)) :
    latticeTail s (x - y) ≤ tailConst s (2 * (3 / 8 : ℝ)) := by
  rw [Metric.mem_ball, dist_eq_norm] at hx hy
  refine latticeTail_le_tailConst hs (by norm_num) (by norm_num) ?_
  have hxy : x - y = (x - probeCenter) - (y - probeCenter) := by abel
  rw [hxy]
  calc ‖(x - probeCenter) - (y - probeCenter)‖
        ≤ ‖x - probeCenter‖ + ‖y - probeCenter‖ := norm_sub_le _ _
    _ ≤ 2 * (3 / 8) := by linarith

/-- The bump field really is admissible smooth-supported input, so the above
instances are not vacuous. -/
example : ContDiff ℝ ∞ probeField ∧ SupportedInBall probeCenter (3 / 8 : ℝ) probeField ∧
    probeField probeCenter ≠ 0 :=
  ⟨probeField_contDiff, probeField_supported, probeField_ne_zero⟩

/-! ## §3 non-vacuity: a genuine smooth periodic single mode

`§3` needs a smooth *periodic* field, which the compactly supported bump is
not; the nonconstant mode `cos(2π x₀) e₀` supplies one. -/

/-- The single mode `x ↦ cos(2π x₁) e₁`. -/
def probeMode : SpatialField :=
  fun x ↦ Real.cos (2 * Real.pi * x 0) • coordinateVector 0

theorem probeMode_contDiff : ContDiff ℝ ∞ probeMode := by
  have h1 : ContDiff ℝ ∞ (fun x : Space ↦ Real.cos (2 * Real.pi * x 0)) :=
    Real.contDiff_cos.comp
      (contDiff_const.mul ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).contDiff))
  exact h1.smul (contDiff_const : ContDiff ℝ ∞ fun _ : Space ↦ coordinateVector (0 : Fin 3))

theorem probeMode_periodic : IsPeriodicSpatial probeMode := by
  intro x j
  show Real.cos (2 * Real.pi * (x + coordinateVector j) 0) • coordinateVector 0
    = Real.cos (2 * Real.pi * x 0) • coordinateVector 0
  by_cases hj : j = 0
  · subst hj
    have hcoord : (x + coordinateVector 0) 0 = x 0 + 1 := by
      show x 0 + (coordinateVector 0 : Space) 0 = x 0 + 1
      rw [coordinateVector]; simp
    rw [hcoord, show 2 * Real.pi * (x 0 + 1) = 2 * Real.pi * x 0 + 2 * Real.pi by ring,
      Real.cos_add_two_pi]
  · have hcoord : (x + coordinateVector j) 0 = x 0 := by
      show x 0 + (coordinateVector j : Space) 0 = x 0
      rw [coordinateVector]; simp [Ne.symm hj]
    rw [hcoord]

/-- §3 instantiated on the nonconstant smooth periodic mode. -/
example :
    periodicSobolevENorm (1 / 2 : ℝ) probeMode ≤
      periodicSobolevENorm 0 probeMode +
        periodicHomogeneousENorm (1 / 2 : ℝ) (meanZeroPartT probeMode) :=
  periodicSobolevENorm_le_l2_add_homogeneous (by norm_num) (by norm_num)
    probeMode_contDiff probeMode_periodic

/-! ## Consumer sketch: how lane 354 assembles the localization bound

`hL2` is what the `endpoint_zero`/Parseval bridge (lane 359) supplies for the
coefficient `L²` term; `hHom` is what `torus_identity` combined with the §2
estimate `iTorus_periodize_le` (lane 354), `wholeSpace_identity` and
`constant_pos_finite` supply for the homogeneous term.  §3
(`periodicSobolevENorm_le_l2_add_homogeneous`) is the reduction that turns those
two bounds into the inhomogeneous bound.  Both hypotheses are probe-only. -/
example {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {g : SpatialField}
    (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicSpatial g) {L2 hom : ℝ≥0∞}
    (hL2 : periodicSobolevENorm 0 g ≤ L2)
    (hHom : periodicHomogeneousENorm s (meanZeroPartT g) ≤ hom) :
    periodicSobolevENorm s g ≤ L2 + hom :=
  (periodicSobolevENorm_le_l2_add_homogeneous hs hs1 hg hgp).trans (add_le_add hL2 hHom)

end NSFormalization.Section3.T13
