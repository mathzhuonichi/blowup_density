import NSFormalization.Section3.T17.ForceSupport
import NSFormalization.Section3.T17.Correction
import NSFormalization.Section3.T15.HaarBridge
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! # T17 (`lem:correction`), unit U8: torus support volume and duration of the
periodized correction force

The two canonical `CorrectionAPI` fields `force_spatial_volume` /
`force_time_length` (`research/T17/Spec.lean:861,866`,
`Section3/T17/Correction.lean:182,188`), together with the real constant
`spatialVolumeConst` and its nonnegativity, are proved here at the concrete
`correctionData` of unit U2, i.e. for the periodized correction
`latticeLift (physicalCorrection v x₀ T θ η ε)`.

## Route

Lane 425's `force_support` puts the whole space-time support of the periodized
force inside `Ioo (T - 2ε²) (T + 2ε²) ×ˢ periodicSet (ball x₀ (ε·θRadius))`.
The measured object, however, is the support of the **torus lift**
`torusSpaceTimeLift`, which reads the field at the canonical `(0,1]³`
representative `torusRepr z` of a torus point.  Two steps close the gap.

* **Support transfer** (§2).  `torusSpaceTimeLift f z = f (z.1, torusRepr z.2)`
  holds definitionally, so a point of `Function.support (torusSpaceTimeLift f)`
  has `torusRepr z.2 ∈ periodicSet (ball x₀ ρ)`, i.e.
  `torusRepr z.2 - latticeVector k ∈ ball x₀ ρ` for some lattice frequency `k`.
  Since `torusPoint` kills lattice vectors and inverts `torusRepr`, this gives
  `z.2 ∈ torusPoint '' ball x₀ ρ`.  Enlarging the open ball to the closed one
  makes the right-hand side compact, hence closed, so the inclusion survives the
  closure defining `tsupport`.  Note `torusRepr` is *not* continuous, so the
  closed enlargement is what makes the step work.
* **Haar/Lebesgue set bridge** (§1).  `measure_torusPoint_image_le`: for a
  compact `A ⊆ R³`, `periodicTorusMeasure (torusPoint '' A) ≤ volume A`.  Its
  proof is the measure-free change of variables `T15.lintegral_enorm_torusLift`
  applied to the indicator of `periodicSet A`, which is unit-periodic, so
  `T13.torusLift_torusPoint` evaluates its lift to `1` on all of
  `torusPoint '' A`; the resulting cube integral is dominated by the lattice-sum
  unfolding `T13.lintegral_eq_tsum_halfOpenCube` of `volume A`, term `-k` of the
  sum absorbing the frequency `k` witnessing membership in `periodicSet A`.

Then the spatial bound is Mathlib's `EuclideanSpace.volume_closedBall_fin_three`
on `closedBall x₀ (ε·θRadius)` and the temporal bound is `Real.volume_Icc` on
`Icc (T - 2ε²) (T + 2ε²)`, whose length is exactly `4ε²`.  Both constants are
the manuscript's: `(4/3)π·θRadius³` and `4`.

## The `hv` premise

`hv : ContDiff ℝ ∞ v` is inherited **only** through lane 425's `force_support`
(where it enters `Transport.force_eq`'s local smoothness premise); nothing in
this module uses the regularity of the reference again.  This is the open G1
issue of `research/T17/SPEC_ISSUES.md`.  The extra `0 ≤ θR` premise of the
spatial bound is the `theta_radius_pos` field of `T16.LocalPotentialAPI`, i.e.
data already fixed by the cutoff record, not a new hypothesis about the PDE.
-/

noncomputable section

namespace NSFormalization.Section3.T17

open Set MeasureTheory Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 (PeriodicTorus periodicTorusMeasure torusLift IsPeriodicSpatial
  IsPeriodicOn PeriodicFrequency)
open NSFormalization.Section3.T13 (fundamentalCube halfOpenCube torusPoint torusPoint_torusRepr
  torusLift_torusPoint fundamentalCube_ae_eq_halfOpenCube lintegral_eq_tsum_halfOpenCube
  measurableSet_halfOpenCube)
open NSFormalization.Section3.T16 (periodicSet latticeVector)
open NSFormalization.Section4.A02 (SpaceTimeField)
open scoped ContDiff ENNReal Topology BigOperators

/-! ## 0. Lattice vectors, the quotient map, and periodic indicators -/

/-- The T16 and T13 spellings of the Euclidean lattice vector agree. -/
theorem latticeVector_eq (k : PeriodicFrequency) :
    latticeVector k = NSFormalization.Section3.T13.latticeVector k := rfl

/-- Coordinates of a lattice vector. -/
theorem latticeVector_coord (k : PeriodicFrequency) (i : Fin 3) :
    latticeVector k i = (k i : ℝ) := rfl

/-- Coordinates of a unit coordinate vector. -/
theorem coordinateVector_coord (i j : Fin 3) :
    coordinateVector i j = if j = i then (1 : ℝ) else 0 := by
  simp [coordinateVector, eq_comm]

theorem latticeVector_neg (k : PeriodicFrequency) : latticeVector (-k) = -latticeVector k := by
  refine PiLp.ext fun i => ?_
  show ((((-k) i : ℤ)) : ℝ) = -((k i : ℤ) : ℝ)
  rw [Pi.neg_apply]
  push_cast
  ring

theorem latticeVector_add_single (k : PeriodicFrequency) (i : Fin 3) :
    latticeVector (k + fun j => if j = i then 1 else 0)
      = latticeVector k + coordinateVector i := by
  refine PiLp.ext fun j => ?_
  show ((k j + (if j = i then (1 : ℤ) else 0) : ℤ) : ℝ) = (k j : ℝ) + coordinateVector i j
  rw [coordinateVector_coord]
  by_cases hj : j = i <;> simp [hj]

theorem latticeVector_sub_single (k : PeriodicFrequency) (i : Fin 3) :
    latticeVector (k - fun j => if j = i then 1 else 0)
      = latticeVector k - coordinateVector i := by
  refine PiLp.ext fun j => ?_
  show ((k j - (if j = i then (1 : ℤ) else 0) : ℤ) : ℝ) = (k j : ℝ) - coordinateVector i j
  rw [coordinateVector_coord]
  by_cases hj : j = i <;> simp [hj]

/-- An integer is zero in the unit circle. -/
theorem intCast_unitAddCircle_eq_zero (k : ℤ) : ((k : ℝ) : UnitAddCircle) = 0 := by
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨k, by simp⟩

/-- The quotient projection `R³ → T³` is continuous. -/
theorem continuous_torusPoint : Continuous (torusPoint : Space → PeriodicTorus) := by
  refine continuous_pi fun i => ?_
  exact (AddCircle.continuous_mk' (1 : ℝ)).comp (by fun_prop : Continuous fun x : Space => x i)

/-- The quotient projection kills lattice translations. -/
theorem torusPoint_sub_latticeVector (x : Space) (k : PeriodicFrequency) :
    torusPoint (x - latticeVector k) = torusPoint x := by
  funext i
  show (((x - latticeVector k) i : ℝ) : UnitAddCircle) = ((x i : ℝ) : UnitAddCircle)
  have hc : (x - latticeVector k) i = x i - (k i : ℝ) := by
    simp [latticeVector_coord]
  rw [hc, show ((x i - (k i : ℝ) : ℝ) : UnitAddCircle)
      = ((x i : ℝ) : UnitAddCircle) - (((k i : ℤ) : ℝ) : UnitAddCircle) from rfl,
    intCast_unitAddCircle_eq_zero, sub_zero]

theorem mem_periodicSet_self {A : Set Space} {a : Space} (ha : a ∈ A) : a ∈ periodicSet A := by
  refine ⟨0, ?_⟩
  have h0 : latticeVector (0 : PeriodicFrequency) = 0 := by
    refine PiLp.ext fun j => ?_
    show (((0 : PeriodicFrequency) j : ℤ) : ℝ) = (0 : Space) j
    simp
  rw [h0, sub_zero]
  exact ha

/-- The periodic lift of a set is invariant under unit coordinate shifts. -/
theorem mem_periodicSet_add_coordinateVector {A : Set Space} (x : Space) (i : Fin 3) :
    (x + coordinateVector i ∈ periodicSet A) ↔ (x ∈ periodicSet A) := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k - fun j => if j = i then 1 else 0, ?_⟩
    rw [latticeVector_sub_single,
      show x - (latticeVector k - coordinateVector i)
        = x + coordinateVector i - latticeVector k from by abel]
    exact hk
  · rintro ⟨k, hk⟩
    refine ⟨k + fun j => if j = i then 1 else 0, ?_⟩
    rw [latticeVector_add_single,
      show x + coordinateVector i - (latticeVector k + coordinateVector i)
        = x - latticeVector k from by abel]
    exact hk

/-- The indicator of a periodic lift is a unit-periodic scalar field. -/
theorem indicator_periodicSet_isPeriodicSpatial (A : Set Space) :
    IsPeriodicSpatial ((periodicSet A).indicator (fun _ => (1 : ℝ))) := by
  intro x i
  by_cases hx : x ∈ periodicSet A
  · rw [Set.indicator_of_mem ((mem_periodicSet_add_coordinateVector x i).2 hx),
      Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem (fun h => hx ((mem_periodicSet_add_coordinateVector x i).1 h)),
      Set.indicator_of_notMem hx]

/-! ## 1. The single-copy Haar/Lebesgue set bridge -/

/-- **The new torus bridge of U8.**  The Haar measure of the torus image of a
compact Euclidean set is at most the Lebesgue measure of that set.  No
injectivity of `torusPoint` on `A` is needed: the fundamental-cube unfolding
`T13.lintegral_eq_tsum_halfOpenCube` already sums the whole lattice orbit. -/
theorem measure_torusPoint_image_le {A : Set Space} (hA : IsCompact A) :
    periodicTorusMeasure (torusPoint '' A) ≤ volume A := by
  classical
  set g : Space → ℝ := (periodicSet A).indicator (fun _ => (1 : ℝ)) with hgdef
  have hgper : IsPeriodicSpatial g := indicator_periodicSet_isPeriodicSpatial A
  have hE : MeasurableSet (torusPoint '' A) :=
    (hA.image continuous_torusPoint).measurableSet
  have hAm : MeasurableSet A := hA.measurableSet
  have hgval : ∀ x : Space, ‖g x‖ₑ ^ (1 : ℝ)
      = (periodicSet A).indicator (fun _ => (1 : ℝ≥0∞)) x := by
    intro x
    rw [ENNReal.rpow_one]
    by_cases hx : x ∈ periodicSet A
    · rw [hgdef, Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      simp
    · rw [hgdef, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      simp
  have hone : ∀ z ∈ torusPoint '' A, (1 : ℝ≥0∞) ≤ ‖torusLift g z‖ₑ ^ (1 : ℝ) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [torusLift_torusPoint hgper a, hgval a,
      Set.indicator_of_mem (mem_periodicSet_self ha)]
  have hmaj : ∀ x : Space, (periodicSet A).indicator (fun _ => (1 : ℝ≥0∞)) x
      ≤ ∑' n : PeriodicFrequency,
          A.indicator (fun _ => (1 : ℝ≥0∞))
            (x + NSFormalization.Section3.T13.latticeVector n) := by
    intro x
    by_cases hx : x ∈ periodicSet A
    · rw [Set.indicator_of_mem hx]
      obtain ⟨k, hk⟩ := hx
      refine le_trans (le_of_eq ?_) (ENNReal.le_tsum (-k))
      rw [← latticeVector_eq, latticeVector_neg,
        show x + -latticeVector k = x - latticeVector k from by abel,
        Set.indicator_of_mem hk]
    · rw [Set.indicator_of_notMem hx]
      simp
  have hmeasA : Measurable (A.indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hAm
  calc periodicTorusMeasure (torusPoint '' A)
      = ∫⁻ _ in torusPoint '' A, (1 : ℝ≥0∞) ∂periodicTorusMeasure := (setLIntegral_one _).symm
    _ ≤ ∫⁻ z in torusPoint '' A, ‖torusLift g z‖ₑ ^ (1 : ℝ) ∂periodicTorusMeasure := by
        refine lintegral_mono_ae ?_
        exact (ae_restrict_iff' hE).2 (Filter.Eventually.of_forall hone)
    _ ≤ ∫⁻ z, ‖torusLift g z‖ₑ ^ (1 : ℝ) ∂periodicTorusMeasure :=
        setLIntegral_le_lintegral _ _
    _ = ∫⁻ x in fundamentalCube, ‖g x‖ₑ ^ (1 : ℝ) ∂(volume : Measure Space) :=
        NSFormalization.Section3.T15.lintegral_enorm_torusLift g 1
    _ = ∫⁻ x in halfOpenCube, ‖g x‖ₑ ^ (1 : ℝ) ∂(volume : Measure Space) :=
        setLIntegral_congr fundamentalCube_ae_eq_halfOpenCube
    _ ≤ ∫⁻ x in halfOpenCube, ∑' n : PeriodicFrequency,
          A.indicator (fun _ => (1 : ℝ≥0∞))
            (x + NSFormalization.Section3.T13.latticeVector n) ∂(volume : Measure Space) := by
        refine lintegral_mono fun x => ?_
        rw [hgval x]
        exact hmaj x
    _ = ∑' n : PeriodicFrequency, ∫⁻ x in halfOpenCube,
          A.indicator (fun _ => (1 : ℝ≥0∞))
            (x + NSFormalization.Section3.T13.latticeVector n) ∂(volume : Measure Space) := by
        refine lintegral_tsum fun n => ?_
        exact (hmeasA.comp (measurable_id.add_const _)).aemeasurable
    _ = ∫⁻ x : Space, A.indicator (fun _ => (1 : ℝ≥0∞)) x ∂(volume : Measure Space) :=
        (lintegral_eq_tsum_halfOpenCube hmeasA).symm
    _ = volume A := lintegral_indicator_one hAm

/-! ## 2. Support of the torus lift of a field with cylinder support -/

/-- The canonical `(0,1]³` representative of a torus point, i.e. the point at
which `torusLift` reads its argument. -/
def torusRepr (z : PeriodicTorus) : Space := torusLift (id : Space → Space) z

theorem torusPoint_torusRepr_self (z : PeriodicTorus) : torusPoint (torusRepr z) = z :=
  torusPoint_torusRepr z

theorem torusSpaceTimeLift_apply (f : SpaceTimeField) (z : ℝ × PeriodicTorus) :
    torusSpaceTimeLift f z = f (z.1, torusRepr z.2) := rfl

/-- The space-time support of the torus lift sits in the closed time window
times the torus image of the **closed** ball.  The closed enlargement of the
manuscript's open ball is what makes the target closed, hence stable under the
closure defining `tsupport`; `torusRepr` itself is discontinuous. -/
theorem tsupport_torusSpaceTimeLift_subset {f : SpaceTimeField} {a b ρ : ℝ} {x₀ : Space}
    (hf : tsupport f ⊆ Ioo a b ×ˢ periodicSet (ball x₀ ρ)) :
    tsupport (torusSpaceTimeLift f) ⊆ Icc a b ×ˢ (torusPoint '' closedBall x₀ ρ) := by
  refine closure_minimal ?_
    (isClosed_Icc.prod ((isCompact_closedBall x₀ ρ).image continuous_torusPoint).isClosed)
  intro z hz
  have hne : f (z.1, torusRepr z.2) ≠ 0 := hz
  have h := hf (subset_tsupport _ hne)
  refine ⟨Ioo_subset_Icc_self h.1, ?_⟩
  obtain ⟨k, hk⟩ := h.2
  exact ⟨torusRepr z.2 - latticeVector k, ball_subset_closedBall hk,
    by rw [torusPoint_sub_latticeVector, torusPoint_torusRepr_self]⟩

theorem torusTemporalSupport_subset_Icc {f : SpaceTimeField} {a b ρ : ℝ} {x₀ : Space}
    (hf : tsupport f ⊆ Ioo a b ×ˢ periodicSet (ball x₀ ρ)) :
    torusTemporalSupport f ⊆ Icc a b := by
  rintro _ ⟨z, hz, rfl⟩
  exact (tsupport_torusSpaceTimeLift_subset hf hz).1

theorem torusSpatialSupport_subset_image {f : SpaceTimeField} {a b ρ : ℝ} {x₀ : Space}
    (hf : tsupport f ⊆ Ioo a b ×ˢ periodicSet (ball x₀ ρ)) :
    torusSpatialSupport f ⊆ torusPoint '' closedBall x₀ ρ := by
  rintro _ ⟨z, hz, rfl⟩
  exact (tsupport_torusSpaceTimeLift_subset hf hz).2

/-! ## 3. The constant and the two measure bounds -/

/-- `03-torus.tex:225`: the spatial-volume constant of `eq:bgzero`'s force, the
Euclidean volume `(4/3)π θRadius³` of the unit-scale support ball. -/
def spatialVolumeConst (θR : ℝ) : ℝ := Real.pi * 4 / 3 * θR ^ 3

/-- `03-torus.tex:225`: the spatial-volume constant is nonnegative.  `0 ≤ θR` is
the `theta_radius_pos` datum of `T16.LocalPotentialAPI`. -/
theorem spatialVolumeConst_nonneg {θR : ℝ} (hθR : 0 ≤ θR) : 0 ≤ spatialVolumeConst θR := by
  unfold spatialVolumeConst
  positivity

/-- `03-torus.tex:225`: any field whose space-time support lies in a time window
times the periodic lift of `ball x₀ (ε θR)` has torus spatial support of Haar
measure at most `(4/3)π θR³ ε³`. -/
theorem measure_torusSpatialSupport_le {f : SpaceTimeField} {a b θR ε : ℝ} {x₀ : Space}
    (hf : tsupport f ⊆ Ioo a b ×ˢ periodicSet (ball x₀ (ε * θR)))
    (hε : 0 < ε) (hθR : 0 ≤ θR) :
    periodicTorusMeasure (torusSpatialSupport f)
      ≤ ENNReal.ofReal (spatialVolumeConst θR * ε ^ 3) := by
  have hρ : 0 ≤ ε * θR := mul_nonneg hε.le hθR
  refine le_trans (measure_mono (torusSpatialSupport_subset_image hf)) ?_
  refine le_trans (measure_torusPoint_image_le (isCompact_closedBall x₀ (ε * θR))) ?_
  rw [EuclideanSpace.volume_closedBall_fin_three, ← ENNReal.ofReal_pow hρ,
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  unfold spatialVolumeConst
  ring

/-- `03-torus.tex:225`: the same support hypothesis bounds the length of the
torus temporal support by the length of the time window.  The temporal
coordinate is not periodized, so no torus bridge is involved. -/
theorem measure_torusTemporalSupport_le {f : SpaceTimeField} {a b ρ : ℝ} {x₀ : Space}
    (hf : tsupport f ⊆ Ioo a b ×ˢ periodicSet (ball x₀ ρ)) :
    volume (torusTemporalSupport f) ≤ ENNReal.ofReal (b - a) := by
  refine le_trans (measure_mono (torusTemporalSupport_subset_Icc hf)) ?_
  rw [Real.volume_Icc]

/-! ## 4. The two canonical fields at the concrete `correctionData` -/

/-- **U8 (a)** — `03-torus.tex:225`, `CorrectionAPI.force_spatial_volume`: the
torus spatial support of the periodized correction force has Haar measure at
most `spatialVolumeConst θRadius * ε³`.  `hv` enters only through lane 425's
`force_support`. -/
theorem force_spatial_volume (ν : ℝ) {v : SpaceTimeField}
    (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T δ r : ℝ)
    (hvper : IsPeriodicOn univ v)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (O : Set Space) (θR ε₀ : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR)
    (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hr2 : r < 1 / 2) (hθR : 0 ≤ θR)
    (hεtime : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min T δ)
    (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r) :
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
      periodicTorusMeasure (torusSpatialSupport
          (correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε)) ≤
        ENNReal.ofReal (spatialVolumeConst θR * ε ^ 3) := by
  intro ε hε
  exact measure_torusSpatialSupport_le
    (force_support ν hv x₀ T δ r hvper O θR ε₀ hθ hη hθc hηc hθsupp hηsupp hr2
      hεtime hεspace ε hε) hε.1 hθR

/-- **U8 (b)** — `03-torus.tex:225`, `CorrectionAPI.force_time_length`: the
torus temporal support of the periodized correction force has Lebesgue measure
at most `4ε²`.  `hv` enters only through lane 425's `force_support`. -/
theorem force_time_length (ν : ℝ) {v : SpaceTimeField}
    (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T δ r : ℝ)
    (hvper : IsPeriodicOn univ v)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (O : Set Space) (θR ε₀ : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR)
    (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hr2 : r < 1 / 2)
    (hεtime : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min T δ)
    (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r) :
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
      volume (torusTemporalSupport
          (correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε)) ≤
        ENNReal.ofReal (4 * ε ^ 2) := by
  intro ε hε
  refine (measure_torusTemporalSupport_le
    (force_support ν hv x₀ T δ r hvper O θR ε₀ hθ hη hθc hηc hθsupp hηsupp hr2
      hεtime hεspace ε hε)).trans (le_of_eq ?_)
  congr 1
  ring

end NSFormalization.Section3.T17
