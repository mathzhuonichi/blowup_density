import NSFormalization.Section3.T13.LocalizationKernel
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Lane 353 closure probe

`research/` is not a Lean module root, so this probe re-derives the concrete
witnesses (an admissible ball and a smooth periodic single mode) and then

* instantiates the three shipped estimates of lane 353 on them (non-vacuity):
  `latticeTail_le_tailConst` / `tailConst_lt_top` (§1), the geometric
  `two_r_lt_one_of_closure_ball_subset`, and
  `periodicSobolevENorm_le_l2_add_homogeneous` (§3);
* records, in one `example`, how lane 354 will assemble the localization
  bound from §3 together with a `torus_identity`-shaped, an
  `iTorus_periodize_le`-shaped (the still-open §2 estimate), a
  `wholeSpace_identity`-shaped and an `endpoint_zero`-shaped fact — all as
  hypotheses of the `example` only.

The §2 kernel comparison `iTorus_periodize_le` is **not** shipped by lane 353
(see `research/T13/REPORT_353.md`); the consumer example therefore carries the
two bounds it would supply (`hL2`, `hHom`) as hypotheses, so the reduction step
that §3 provides is type-checked against the real target shape.
-/

noncomputable section

namespace NSFormalization.Section3.T13

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section3.T10
open scoped ContDiff ENNReal BigOperators Topology

/-! ## §1 non-vacuity: the lattice tail bound and its finite constant -/

example : Summable (fun n : PeriodicFrequency => ‖latticeVector n‖ ^ (-(4 : ℝ))) :=
  summable_latticeVector_rpow (by norm_num)

example : tailSum (1 / 2 : ℝ) < ⊤ := tailSum_lt_top (by norm_num)

example : tailConst (1 / 2 : ℝ) (3 / 4 : ℝ) < ⊤ := tailConst_lt_top (by norm_num) (by norm_num)

/-- The tail at the cube's zero difference is bounded by the uniform constant. -/
example : latticeTail (1 / 2 : ℝ) (0 : Space) ≤ tailConst (1 / 2 : ℝ) (3 / 4 : ℝ) :=
  latticeTail_le_tailConst (by norm_num) (by norm_num) (by norm_num)
    (by rw [norm_zero]; norm_num)

/-! ## An explicit admissible ball and the `2r < 1` consequence -/

/-- Centre of the fundamental cube. -/
def probeCenter : Space := (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun _ => (1 / 2 : ℝ))

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

/-- The support-difference radius `2r = 3/4` is genuinely below `1`. -/
example : 2 * (3 / 8 : ℝ) < 1 :=
  two_r_lt_one_of_closure_ball_subset (by norm_num) probe_ball_admissible

/-! ## §3 non-vacuity: a genuine smooth periodic single mode -/

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

`hL2` is what the `endpoint_zero`/Parseval bridge supplies for the coefficient
`L²` term; `hHom` is what `torus_identity` combined with the open §2 estimate
`iTorus_periodize_le`, `wholeSpace_identity` and `constant_pos_finite` supply
for the homogeneous term.  §3 (`periodicSobolevENorm_le_l2_add_homogeneous`) is
the reduction that turns those two bounds into the inhomogeneous bound. -/
example {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {g : SpatialField}
    (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicSpatial g) {L2 hom : ℝ≥0∞}
    (hL2 : periodicSobolevENorm 0 g ≤ L2)
    (hHom : periodicHomogeneousENorm s (meanZeroPartT g) ≤ hom) :
    periodicSobolevENorm s g ≤ L2 + hom :=
  (periodicSobolevENorm_le_l2_add_homogeneous hs hs1 hg hgp).trans (add_le_add hL2 hHom)

end NSFormalization.Section3.T13
