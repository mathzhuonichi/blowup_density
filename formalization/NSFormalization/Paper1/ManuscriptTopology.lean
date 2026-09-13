import NSFormalization.Paper1.PeriodicDense
import NSFormalization.Paper1.PeriodicTestForceFiniteness
import NSFormalization.Paper1.PeriodicFourierInjectivity
import Mathlib.Topology.MetricSpace.Basic

/-!
# Paper 1 relative force-norm topology

For each real order `s`, the actual smooth periodic test-force space carries
the metric given by its `L¹_t H^s_x` distance. The norm uses the unit-period
angular weight `1 + |2πk|²` and the Euclidean sum of squared component norms.
Compact positive-time support identifies the full-line time gauge with the
manuscript norm on `(0, infinity)`.

Only separation of the Fourier norm is admitted below. Finiteness, symmetry,
the triangle inequality, the positive-time identification, and the passage
from the existing insertion approximations to density are proved. The
admission is stated for the actual smooth periodic fields at every real
order; it does not assume the desired density conclusion.
-/
noncomputable section
namespace NSFormalization.Paper1.ManuscriptTopology

open Set Filter MeasureTheory
open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration
open NSFormalization.Source
open NSFormalization.Paper1.PeriodicForceSpace
open NSFormalization.Paper1.PeriodicForceConvergence
open NSFormalization.Paper1.PeriodicForceTopology
open NSFormalization.Paper1.PeriodicTestForceNorm
open NSFormalization.Paper1.PeriodicTestForceFiniteness
open NSFormalization.Paper1.PeriodicDensityFiber
open NSFormalization.Paper1.PeriodicDensityDichotomy
open NSFormalization.Paper1.PeriodicDense
open NSFormalization.Paper1.PeriodicInitialData
open scoped ENNReal ContDiff

/-- Fourier uniqueness and continuity upgrade a zero `L¹_t H^s_x` distance
between actual smooth periodic fields to pointwise equality. This holds at
negative orders too, because every Bessel weight is strictly positive.
Remaining proof: zero weighted coefficient energy almost everywhere in time,
Fourier uniqueness for each spatial slice, then continuity in spacetime. -/
theorem eq_of_forceDistance_eq_zero (s : ℝ) {F G : VelocityField}
    (hF : IsTestForce F) (hG : IsTestForce G)
    (hzero : forceDistance s F G = 0) : F = G := by
  have hmeas : AEStronglyMeasurable (forceProfile s F G) volume :=
    (stronglyMeasurable_forceProfile_of_testForces hF hG s).aestronglyMeasurable
  have hprof : forceProfile s F G =ᵐ[volume] 0 := by
    rw [forceDistance_eq_profile] at hzero
    exact (eLpNorm_eq_zero_iff hmeas (by norm_num : (1 : ℝ≥0∞) ≠ 0)).1 hzero
  have hslice : ∀ᵐ t : ℝ ∂volume,
      (fun x : Space => F (t, x)) = (fun x : Space => G (t, x)) := by
    filter_upwards [hprof] with t ht
    have hsum : ∑ i : Fin 3,
        periodicSobolevSq s (fun x => coordinateForce (F - G) i (t, x)) = 0 := by
      have hsqrt : Real.sqrt (∑ i : Fin 3,
          periodicSobolevSq s (fun x => coordinateForce (F - G) i (t, x))) = 0 := by
        simpa [forceProfile, periodicVectorSobolevNorm] using ht
      have hnonneg : 0 ≤ ∑ i : Fin 3,
          periodicSobolevSq s (fun x => coordinateForce (F - G) i (t, x)) := by
        apply Finset.sum_nonneg
        intro i hi
        exact tsum_nonneg (fun k => mul_nonneg
          (Real.rpow_nonneg ((one_le_periodicFrequencyWeight k).trans' zero_le_one) s)
          (sq_nonneg _))
      nlinarith [Real.sq_sqrt hnonneg]
    funext x
    ext i
    have hterm : periodicSobolevSq s
        (fun y => coordinateForce (F - G) i (t, y)) = 0 := by
      have hi := Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin 3)))
        (f := fun j => periodicSobolevSq s
          (fun y => coordinateForce (F - G) j (t, y)))
        (fun j hj => tsum_nonneg (fun k => mul_nonneg
          (Real.rpow_nonneg ((one_le_periodicFrequencyWeight k).trans' zero_le_one) s)
          (sq_nonneg _))) (Finset.mem_univ i)
      have hnonneg_i : 0 ≤ periodicSobolevSq s
          (fun y => coordinateForce (F - G) i (t, y)) := by
        exact tsum_nonneg (fun k => mul_nonneg
          (Real.rpow_nonneg ((one_le_periodicFrequencyWeight k).trans' zero_le_one) s)
          (sq_nonneg _))
      nlinarith
    have hf : ContDiff ℝ ∞
        (fun y : Space => coordinateForce (F - G) i (t, y)) :=
      (coordinateForce_smooth (hF.smooth.sub hG.smooth) i).comp
        (contDiff_const.prodMk contDiff_id)
    have hp : UnitPeriods
        (fun y : Space => coordinateForce (F - G) i (t, y)) := by
      intro y j
      dsimp [coordinateForce]
      have hFp := hF.periodic t (Set.mem_univ _) y j
      have hGp := hG.periodic t (Set.mem_univ _) y j
      simpa [Complex.ofReal_sub] using
        congrArg₂ (fun a b : Space => ((a i : ℝ) : ℂ) - ((b i : ℝ) : ℂ)) hFp hGp
    have hz := periodic_eq_zero_of_periodicSobolevSq_zero hf hp hterm
    apply sub_eq_zero.mp
    have hc : (((((F (t, x)).ofLp i - (G (t, x)).ofLp i : ℝ) : ℂ))) = 0 := by
      simpa [coordinateForce] using congrFun hz x
    exact Complex.ofReal_injective hc
  have hpoint : ∀ z : SpaceTime, F z = G z := by
    intro z
    rcases z with ⟨t, x⟩
    have htx : (fun r : ℝ => F (r, x)) =ᵐ[volume]
        (fun r : ℝ => G (r, x)) := by
      filter_upwards [hslice] with r hr
      exact congrFun hr x
    have hFc : Continuous (fun r : ℝ => F (r, x)) :=
      hF.smooth.continuous.comp (continuous_id.prodMk continuous_const)
    have hGc : Continuous (fun r : ℝ => G (r, x)) :=
      hG.smooth.continuous.comp (continuous_id.prodMk continuous_const)
    exact congrFun (Measure.eq_of_ae_eq htx hFc hGc) t
  exact funext hpoint

/-- The full-line force gauge is exactly the positive-time norm in Paper 1,
not merely a comparable norm. -/
theorem forceDistance_eq_positiveTime (s : ℝ) {F G : VelocityField}
    (hF : IsTestForce F) (hG : IsTestForce G) :
    forceDistance s F G =
      eLpNorm (forceProfile s F G) 1 (volume.restrict (Ioi (0 : ℝ))) := by
  symm
  apply eLpNorm_restrict_eq_of_support_subset
  intro t ht
  by_contra hnot
  have hnonpos : t ≤ 0 := le_of_not_gt hnot
  have hzero (f : VelocityField) (hf : IsTestForce f) (x : Space) : f (t, x) = 0 := by
    obtain ⟨K, _, hKpos, hKf⟩ := hf.time_support
    apply image_eq_zero_of_notMem_tsupport
    intro hz
    exact (not_lt_of_ge hnonpos) (hKpos (hKf hz).1)
  apply ht
  simp [forceProfile, periodicVectorSobolevNorm, periodicSobolevSq,
    coordinateForce, hzero F hF, hzero G hG,
    periodicFourierCoeff_eq_cube, NavierStokes.PeriodicIntegration.cubeIntegral]

/-- The genuine extended metric of the actual Fourier gauge. All values are
finite by `forceDistance_lt_top_of_testForces_all_s`. -/
def forceEMetric (s : ℝ) : EMetricSpace TestForce where
  edist F G := forceDistance s F.1 G.1
  edist_self F := PeriodicForceTopology.forceDistance_self s F.1
  edist_comm F G := forceDistance_comm s F.1 G.1
  edist_triangle F G H := forceDistance_triangle_of_testForces F.2 G.2 H.2 s
  eq_of_edist_eq_zero {F G} h :=
    Subtype.ext (eq_of_forceDistance_eq_zero s F.2 G.2 h)

/-- The finite metric whose real distance is the exact periodic force norm.
It is parameterized by the Sobolev order instead of installing conflicting
global instances on the same test-force subtype. -/
def forceMetric (s : ℝ) : MetricSpace TestForce :=
  letI := forceEMetric s
  EMetricSpace.toMetricSpace (fun F G =>
    (forceDistance_lt_top_of_testForces_all_s F.2 G.2 s).ne)

/-- The relative `L¹(0,infinity;H^s)` topology on the smooth force class. -/
def relativeTopology (s : ℝ) : TopologicalSpace TestForce :=
  (forceMetric s).toUniformSpace.toTopologicalSpace

/-- Density in the manuscript's relative norm topology, on the original
smooth test-force subtype. -/
def DenseAt (s : ℝ) (S : Set TestForce) : Prop :=
  @Dense TestForce (relativeTopology s) S

/-- Local use of `forceMetric s` retains the exact extended distance. -/
theorem edist_eq_forceDistance (s : ℝ) (F G : TestForce) :
    @edist TestForce (forceMetric s).toEDist F G =
      forceDistance s F.1 G.1 := rfl

/-- The ordinary real metric is the finite norm value of the same gauge. -/
theorem dist_eq_forceDistance_toReal (s : ℝ) (F G : TestForce) :
    @dist TestForce (forceMetric s).toDist F G =
      (forceDistance s F.1 G.1).toReal := rfl

/-- The metric closure criterion exactly matches the already constructed
periodic gauge approximations, including every positive extended radius. -/
theorem denseAt_iff_approximation (s : ℝ) (S : Set TestForce) :
    DenseAt s S ↔ ∀ g : TestForce, ∀ ρ : ℝ≥0∞, 0 < ρ →
      ∃ G ∈ S, forceDistance s G.1 g.1 < ρ := by
  letI : MetricSpace TestForce := forceMetric s
  change @Dense TestForce (forceMetric s).toUniformSpace.toTopologicalSpace S ↔ _
  constructor
  · intro hd g ρ hρ
    obtain ⟨G, hG, hdist⟩ := EMetric.mem_closure_iff.mp (hd g) ρ hρ
    exact ⟨G, hG, by simpa only [edist_eq_forceDistance, forceDistance_comm] using hdist⟩
  · intro ha g
    apply EMetric.mem_closure_iff.mpr
    intro ρ hρ
    obtain ⟨G, hG, hdist⟩ := ha g ρ hρ
    exact ⟨G, hG, by simpa only [edist_eq_forceDistance, forceDistance_comm] using hdist⟩

/-- The older gauge-density interface is now exactly topological density in
Paper 1's force topology. -/
theorem denseAt_singularSlice_iff_GaugeDense (ν T s : ℝ) (a : Space → Space) :
    DenseAt s (singularSlice ν a T) ↔ GaugeDense ν a T s :=
  denseAt_iff_approximation s (singularSlice ν a T)

/-- A regular metric ball is disjoint from the singular slice, hence the
singular forces are not dense. This is the exact topological obstruction used
by the critical regularity argument; its premise is an analytic statement about
the concrete force norm. -/
theorem not_denseAt_of_regular_ball
    (ν T s : ℝ) (a : Space → Space) (g : TestForce) (ρ : ℝ)
    (hρ : 0 < ρ)
    (hreg : ∀ G : TestForce,
      @dist TestForce (forceMetric s).toDist g G < ρ →
      G ∉ singularSlice ν a T) :
    ¬ DenseAt s (singularSlice ν a T) := by
  letI : MetricSpace TestForce := forceMetric s
  intro hd
  change @Dense TestForce (forceMetric s).toUniformSpace.toTopologicalSpace
    (singularSlice ν a T) at hd
  obtain ⟨G, hG, hdist⟩ := Metric.mem_closure_iff.mp (hd g) ρ hρ
  exact hreg G hdist hG

/-- Critical non-density in the zero slice follows directly from a regular
ball for the actual relative force topology. -/
theorem zero_slice_nondense_of_regular_ball
    {ν T s : ℝ}
    (g : TestForce) (ρ : ℝ) (hρ : 0 < ρ)
    (hreg : ∀ G : TestForce,
      @dist TestForce (forceMetric s).toDist g G < ρ →
      G ∉ singularSlice ν (fun _ : Space => 0) T) :
    ¬ DenseAt s (singularSlice ν (fun _ : Space => 0) T) :=
  not_denseAt_of_regular_ball ν T s (fun _ : Space => 0) g ρ hρ hreg

/-- Actual topological subcritical density at rest, using the existing
unconditional insertion/dichotomy theorem. -/
theorem zero_slice_dense {ν T s : ℝ}
    (hν : 0 < ν) (hT : 0 < T) (hs : s < 1 / 2) :
    DenseAt s (singularSlice ν (fun _ : Space => 0) T) :=
  (denseAt_singularSlice_iff_GaugeDense ν T s _).2 (zero_slice_GaugeDense hν hT hs)

/-- The fixed-data density proposition uses precisely the remaining unforced
periodic local-existence input; no approximation or topology premise remains. -/
theorem admissible_slice_dense {ν T s : ℝ}
    (hν : 0 < ν) (hT : 0 < T) (hs : s < 1 / 2)
    (hlocal : UnforcedLocalExistence ν) {a : Space → Space}
    (ha : IsAdmissibleInitialData a) :
    DenseAt s (singularSlice ν a T) :=
  (denseAt_singularSlice_iff_GaugeDense ν T s a).2
    (admissible_slice_GaugeDense hν hT hs hlocal ha)

end NSFormalization.Paper1.ManuscriptTopology
