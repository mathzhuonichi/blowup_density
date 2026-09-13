import NSFormalization.Source.LocalReferenceHelpers
import NavierStokes.PeriodicLocalization
import NavierStokes.PeriodicIntegration
import NavierStokes.PeriodicResidualLimits
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Compact fields as genuine periodic fields

The periodization itself and all local-finiteness/smoothness proofs are reused
from OpenAI's `PeriodicLocalization`. The mean identity adapts the existing
`TorusAverages.integral_periodize` proof from two coordinates to three using
Mathlib's fundamental-domain integration theorem.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicBridge
open NavierStokes NavierStokes.ProblemStatement
open NavierStokes.PeriodicLocalization NavierStokes.PeriodicIntegration
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal

/-- Spatial Frechet derivatives agree with the original compact field on its
injective chart. No derivative of an unproved formal sum is used. -/
theorem spatialDerivative_periodize_local {r : ℝ} {u : VelocityField}
    (hu : SupportedInCube r u) {z : SpaceTime} (hz : z.2 ∈ innerCube r) :
    spatialDerivative (periodize u) z.1 z.2 = spatialDerivative u z.1 z.2 :=
  ResidualRegularity.spatialDerivative_congr (periodize_eventuallyEq hu hz)

theorem temporalDerivative_periodize_local {r : ℝ} {u : VelocityField}
    (hu : SupportedInCube r u) {z : SpaceTime} (hz : z.2 ∈ innerCube r) :
    temporalDerivative (periodize u) z.1 z.2 = temporalDerivative u z.1 z.2 :=
  ResidualRegularity.temporalDerivative_congr (periodize_eventuallyEq hu hz)

theorem spatialLaplacian_periodize_local {r : ℝ} {u : VelocityField}
    (hu : SupportedInCube r u) {z : SpaceTime} (hz : z.2 ∈ innerCube r) :
    spatialLaplacian (periodize u) z.1 z.2 = spatialLaplacian u z.1 z.2 :=
  ResidualRegularity.spatialLaplacian_congr (periodize_eventuallyEq hu hz)

/-- The actual arbitrary-viscosity nonlinear residual is unchanged locally. -/
theorem residual_periodize_local (ν : ℝ) {r : ℝ} {u : VelocityField} {p : PressureField}
    (hu : SupportedInCube r u) (hp : SupportedInCube r p)
    {z : SpaceTime} (hz : z.2 ∈ innerCube r) :
    Source.residual ν (periodize u) (periodize p) z.1 z.2 = Source.residual ν u p z.1 z.2 :=
  Source.LocalReferenceHelpers.residual_congr ν (periodize_eventuallyEq hu hz)
    (periodize_eventuallyEq hp hz)

/-- All the identities apply on the entire centered closed fundamental cube
when the original support lies strictly inside it. -/
theorem innerCube_of_unitCube {r : ℝ} (hr : r < 1/2) {x : Space}
    (hx : ∀ i : Fin 3, |x i| ≤ 1/2) : x ∈ innerCube r := by
  intro i
  have hi := hx i
  linarith

/-- The genuine three-coordinate lattice translation action. -/
local instance coordinateLatticeAction : AddAction Lattice Coords where
  vadd n x := fun i => (n i : ℝ) + x i
  zero_vadd x := by
    change (fun i => ((0 : Lattice) i : ℝ) + x i) = x
    funext i
    simp
  add_vadd n m x := by
    change (fun i => ((n + m) i : ℝ) + x i) =
      (fun i => (n i : ℝ) + ((m i : ℝ) + x i))
    funext i
    simp [add_assoc]

local instance : MeasurableVAdd Lattice Coords where
  measurable_const_vadd _ := measurable_const.add measurable_id
  measurable_vadd_const _ := measurable_of_countable _

local instance : VAddInvariantMeasure Lattice Coords (volume : Measure Coords) where
  measure_preimage_vadd n s _ :=
    measure_preimage_add (volume : Measure Coords) (fun i => (n i : ℝ)) s

def fundamentalCoordinates : Set Coords := univ.pi fun _ : Fin 3 => Ico (0 : ℝ) 1

/-- The same floor construction as OpenAI's two-dimensional fundamental square,
with its dimension replaced by `Fin 3`. -/
theorem fundamentalCoordinates_isAddFundamentalDomain :
    IsAddFundamentalDomain Lattice fundamentalCoordinates (volume : Measure Coords) := by
  apply IsAddFundamentalDomain.mk'
    ((MeasurableSet.univ_pi (fun _ => measurableSet_Ico)).nullMeasurableSet)
  intro x
  refine ⟨(fun i => -⌊x i⌋), ?_, ?_⟩
  · intro i _
    change ((-⌊x i⌋ : ℤ) : ℝ) + x i ∈ Ico (0 : ℝ) 1
    simpa only [Int.cast_neg, Int.fract, sub_eq_add_neg, add_comm] using
      (show Int.fract (x i) ∈ Ico (0 : ℝ) 1 from ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩)
  · intro n hn
    funext i
    have hi : ⌊(n i : ℝ) + x i⌋ = 0 := Int.floor_eq_zero_iff.mpr (hn i (mem_univ _))
    rw [Int.floor_intCast_add] at hi
    omega

/-- Coordinate and Euclidean Lebesgue measures agree via the existing
Mathlib measure-preserving Euclidean equivalence. -/
theorem toSpace_measurePreserving : MeasurePreserving toSpace :=
  PiLp.volume_preserving_toLp (Fin 3)

theorem coordinate_periodize {E : Type*} [NormedAddCommGroup E]
    (f : SpaceTime → E) (t : ℝ) (y : Coords) :
    periodize f (t, toSpace y) = ∑' n : Lattice, f (t, toSpace (n +ᵥ y)) := by
  unfold periodize translate
  rw [← (Equiv.neg Lattice).tsum_eq]
  apply tsum_congr
  intro n
  congr 2
  ext i
  change y i - ((-n) i : ℝ) = (n i : ℝ) + y i
  simp [add_comm]

/-- Every integrable spatial slice has the same integral as its actual
periodization over a fundamental cube. -/
theorem cubeIntegral_periodize {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : SpaceTime → E} {t : ℝ} (hf : Integrable (fun x => f (t,x))) :
    cubeIntegral (fun x => periodize f (t,x)) = ∫ x : Space, f (t,x) := by
  let g : Coords → E := fun y => f (t,toSpace y)
  have hg : Integrable g :=
    (toSpace_measurePreserving.integrable_comp_emb toSpace.toHomeomorph.measurableEmbedding).mpr hf
  have hm (n : Lattice) : AEStronglyMeasurable (fun y => g (n +ᵥ y))
      (volume.restrict fundamentalCoordinates) :=
    (hg.aestronglyMeasurable.comp_measurePreserving
      (measurePreserving_add_left (volume : Measure Coords) (fun i => (n i : ℝ)))).restrict
  have hn : (∑' n : Lattice, ∫⁻ y in fundamentalCoordinates, ‖g (n +ᵥ y)‖ₑ) ≠ ⊤ := by
    rw [← fundamentalCoordinates_isAddFundamentalDomain.lintegral_eq_tsum'' (fun y => ‖g y‖ₑ)]
    exact hg.hasFiniteIntegral.ne
  have hi : (∫ y in fundamentalCoordinates, ∑' n : Lattice, g (n +ᵥ y)) = ∫ y, g y := by
    rw [integral_tsum hm hn]
    exact (fundamentalCoordinates_isAddFundamentalDomain.integral_eq_tsum'' g hg).symm
  have hdomain : (volume : Measure Coords).restrict fundamentalCoordinates =
      volume.restrict cube :=
    Measure.restrict_congr_set Measure.univ_pi_Ico_ae_eq_Icc
  change (∫ y in cube, periodize f (t,toSpace y)) = _
  rw [← hdomain]
  simp_rw [coordinate_periodize]
  exact hi.trans (toSpace_measurePreserving.integral_comp
    toSpace.toHomeomorph.measurableEmbedding (fun x => f (t,x)))

/-- In particular, a zero mean compact field stays mean zero after periodizing. -/
theorem cubeIntegral_periodize_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : SpaceTime → E} {t : ℝ} (hf : Integrable (fun x => f (t,x)))
    (hzero : (∫ x : Space, f (t,x)) = 0) :
    cubeIntegral (fun x => periodize f (t,x)) = 0 :=
  (cubeIntegral_periodize hf).trans hzero


/-- Existing nearest-lattice representatives lie in the closed centered cube.
Their discontinuity is never used as a smooth change of coordinates. -/
theorem representative_unitCube (x : Space) :
    ∀ i : Fin 3, |PeriodicResidualLimits.representative x i| ≤ 1/2 := by
  intro i
  simpa only [PeriodicResidualLimits.representative, PiLp.sub_apply,
    CompactForceDecay.integerShift_apply, PeriodicResidualLimits.nearestIndex] using abs_sub_round (x i)

/-- Equality of two actual periodic fields can be checked on one closed cube. -/
theorem periodic_eq_of_unitCube {E : Type*} {f g : SpaceTime → E}
    (hf : UnitSpatialPeriodsOn univ f) (hg : UnitSpatialPeriodsOn univ g)
    (heq : ∀ t x, (∀ i : Fin 3, |x i| ≤ 1/2) → f (t,x) = g (t,x)) : f = g := by
  funext z
  have hleft := (CompactForceDecay.periodic_integerShift hf z.1
    (PeriodicResidualLimits.nearestIndex z.2)).sub_eq z.2
  have hright := (CompactForceDecay.periodic_integerShift hg z.1
    (PeriodicResidualLimits.nearestIndex z.2)).sub_eq z.2
  exact hleft.symm.trans ((heq z.1 (PeriodicResidualLimits.representative z.2)
    (representative_unitCube z.2)).trans hright)

/-- Outside the closed support cube, the original field is identically zero
on an actual spacetime neighborhood. -/
theorem zero_germ_outside_cube {E : Type*} [NormedAddCommGroup E]
    {r : ℝ} {f : SpaceTime → E} (hf : SupportedInCube r f)
    {z : SpaceTime} {i : Fin 3} (hi : r < |z.2 i|) :
    f =ᶠ[𝓝 z] (fun _ => 0) := by
  have hopen : IsOpen {w : SpaceTime | r < |w.2 i|} :=
    isOpen_lt continuous_const (continuous_abs.comp ((EuclideanSpace.proj i).continuous.comp continuous_snd))
  filter_upwards [hopen.mem_nhds hi] with w hw
  by_contra hne
  exact (not_le_of_gt hw) (hf w hne i)

/-- Composing a field with a zero-preserving map preserves its support bound. -/
theorem supported_comp {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {r : ℝ} {f : SpaceTime → E} (hf : SupportedInCube r f)
    (φ : E → F) (hφ : φ 0 = 0) : SupportedInCube r (fun z => φ (f z)) := by
  intro z hz
  apply hf z
  intro hzero
  exact hz ((congrArg φ hzero).trans hφ)

/-- No cross-copy terms appear in any zero-preserving nonlinear expression. -/
theorem periodize_comp {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {r : ℝ} {f : SpaceTime → E} (hf : SupportedInCube r f) (hr : r < 1/2)
    (φ : E → F) (hφ : φ 0 = 0) :
    (fun z => φ (periodize f z)) = periodize (fun z => φ (f z)) := by
  apply periodic_eq_of_unitCube
  · intro t _ x i
    exact congrArg φ (unitSpatialPeriodsOn_periodize f univ t (mem_univ _) x i)
  · exact unitSpatialPeriodsOn_periodize _ univ
  · intro t x hx
    rw [periodize_eq_on_unitCube hf hr hx,
      periodize_eq_on_unitCube (supported_comp hf φ hφ) hr hx]

/-- In particular, the actual periodic spatial L² energy equals the original
whole-space L² energy, with no overlap factor. -/
theorem cubeIntegral_periodize_norm_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ} {u : SpaceTime → E} (hu : SupportedInCube r u) (hr : r < 1/2) {t : ℝ}
    (hi : Integrable (fun x => ‖u (t,x)‖^2)) :
    cubeIntegral (fun x => ‖periodize u (t,x)‖^2) = ∫ x : Space, ‖u (t,x)‖^2 := by
  have he := periodize_comp hu hr (fun v : E => ‖v‖^2) (by simp)
  have he' : (fun x => ‖periodize u (t,x)‖^2) =
      (fun x => periodize (fun z => ‖u z‖^2) (t,x)) := by
    funext x
    exact congrFun he (t,x)
  rw [he']
  exact cubeIntegral_periodize hi

theorem supported_spatialDerivative {r : ℝ} {u : VelocityField}
    (hu : SupportedInCube r u) :
    SupportedInCube r (fun z => spatialDerivative u z.1 z.2) := by
  intro z hz i
  by_contra hnot
  have he := ResidualRegularity.spatialDerivative_congr
    (zero_germ_outside_cube hu (i := i) (lt_of_not_ge hnot))
  apply hz
  simpa [spatialDerivative] using he

/-- Periodization commutes with the actual spatial derivative on all of R³. -/
theorem spatialDerivative_periodize {r : ℝ} {u : VelocityField}
    (hu : SupportedInCube r u) (hr : r < 1/2) :
    (fun z => spatialDerivative (periodize u) z.1 z.2) =
      periodize (fun z => spatialDerivative u z.1 z.2) := by
  apply periodic_eq_of_unitCube
    (ResidualRegularity.spatialDerivative_periods (unitSpatialPeriodsOn_periodize u univ))
    (unitSpatialPeriodsOn_periodize _ univ)
  intro t x hx
  rw [spatialDerivative_periodize_local hu (innerCube_of_unitCube hr hx),
    periodize_eq_on_unitCube (supported_spatialDerivative hu) hr hx]

/-- The compact support bound is inherited by the actual arbitrary-viscosity residual. -/
theorem supported_residual (ν : ℝ) {r : ℝ} {u : VelocityField} {p : PressureField}
    (hu : SupportedInCube r u) (hp : SupportedInCube r p) :
    SupportedInCube r (fun z => Source.residual ν u p z.1 z.2) := by
  intro z hz i
  by_contra hnot
  have hgt : r < |z.2 i| := lt_of_not_ge hnot
  have he := Source.LocalReferenceHelpers.residual_congr ν
    (zero_germ_outside_cube hu hgt) (zero_germ_outside_cube hp hgt)
  apply hz
  simpa [Source.residual, temporalDerivative, advection, spatialDerivative,
    spatialLaplacian, pressureGradient] using he

/-- The arbitrary-viscosity residual inherits the exact periods of its fields. -/
theorem residual_unitPeriods (ν : ℝ) {u : VelocityField} {p : PressureField}
    (hu : UnitSpatialPeriodsOn univ u) (hp : UnitSpatialPeriodsOn univ p) :
    UnitSpatialPeriodsOn univ (fun z => Source.residual ν u p z.1 z.2) := by
  intro t ht x i
  simp only [Source.residual,
    ResidualRegularity.temporalDerivative_periods isOpen_univ hu t ht x i,
    ResidualRegularity.advection_periods hu t ht x i,
    ResidualRegularity.spatialLaplacian_periods hu t ht x i,
    ResidualRegularity.pressureGradient_periods hp t ht x i]

/-- With disjoint spatial copies, periodization commutes with the complete
nonlinear Navier--Stokes residual for every viscosity. -/
theorem residual_periodize (ν : ℝ) {r : ℝ} {u : VelocityField} {p : PressureField}
    (hu : SupportedInCube r u) (hp : SupportedInCube r p) (hr : r < 1/2) :
    (fun z => Source.residual ν (periodize u) (periodize p) z.1 z.2) =
      periodize (fun z => Source.residual ν u p z.1 z.2) := by
  apply periodic_eq_of_unitCube
    (residual_unitPeriods ν (unitSpatialPeriodsOn_periodize u univ)
      (unitSpatialPeriodsOn_periodize p univ)) (unitSpatialPeriodsOn_periodize _ univ)
  intro t x hx
  rw [residual_periodize_local ν hu hp (innerCube_of_unitCube hr hx),
    periodize_eq_on_unitCube (supported_residual ν hu hp) hr hx]


/-- Every uniformly cube-supported slice is genuinely compactly supported. -/
theorem slice_compact_of_supported {E : Type*} [NormedAddCommGroup E]
    {r : ℝ} {f : SpaceTime → E} (hf : SupportedInCube r f) (t : ℝ) :
    HasCompactSupport (fun x => f (t,x)) := by
  apply HasCompactSupport.intro
    (isCompact_Icc.image toSpace.continuous : IsCompact
      (toSpace '' Icc (fun _ : Fin 3 => -r) (fun _ => r)))
  intro x hx
  by_contra hn
  apply hx
  refine ⟨(fun i => x i), ?_, rfl⟩
  exact ⟨fun i => (abs_le.mp (hf (t,x) hn i)).1,
    fun i => (abs_le.mp (hf (t,x) hn i)).2⟩

/-- The individual ordinary coordinate gradients commute with periodization. -/
theorem spatialPartial_periodize {r : ℝ} {u : VelocityField}
    (hu : SupportedInCube r u) (hr : r < 1/2) (i : Fin 3) :
    (fun z => spatialPartial i (fun y => periodize u (z.1,y)) z.2) =
      periodize (fun z => spatialPartial i (fun y => u (z.1,y)) z.2) := by
  have he := congrArg (fun F : SpaceTime → Space →L[ℝ] Space =>
    fun z => F z (coordinateVector i)) (spatialDerivative_periodize hu hr)
  exact he.trans (periodize_comp (supported_spatialDerivative hu) hr
    (fun A : Space →L[ℝ] Space => A (coordinateVector i)) (by simp))

/-- Full actual periodic dissipation equals the compact whole-space dissipation. -/
theorem dissipation_periodize {r : ℝ} {u : VelocityField}
    (hu : SupportedInCube r u) (hr : r < 1/2) {t : ℝ}
    (hs : ContDiff ℝ ∞ (fun x => u (t,x))) :
    PeriodicUniqueness.dissipation (periodize u) t = NavierStokesR3.CompactEnergy.dissipation u t := by
  unfold PeriodicUniqueness.dissipation NavierStokesR3.CompactEnergy.dissipation
  apply Finset.sum_congr rfl
  intro i _
  have hc := slice_compact_of_supported hu t
  have hi := NavierStokesR3.CompactEnergy.integrable_dissipation_terms hs hc i
  have hdSupport := supported_comp (supported_spatialDerivative hu)
    (fun A : Space →L[ℝ] Space => A (coordinateVector i)) (by simp)
  have he (x : Space) := congrFun (spatialPartial_periodize hu hr i) (t,x)
  simp_rw [he]
  exact cubeIntegral_periodize_norm_sq hdSupport hr hi

/-- Exact divergence commutation, derived from the actual gradient identity. -/
theorem spatialDivergence_periodize {r : ℝ} {u : VelocityField}
    (hu : SupportedInCube r u) (hr : r < 1/2) :
    (fun z => spatialDivergence (periodize u) z.1 z.2) =
      periodize (fun z => spatialDivergence u z.1 z.2) := by
  have he := congrArg (fun F : SpaceTime → Space →L[ℝ] Space =>
    fun z => ∑ i : Fin 3, F z (coordinateVector i) i) (spatialDerivative_periodize hu hr)
  exact he.trans (periodize_comp (supported_spatialDerivative hu) hr
    (fun A : Space →L[ℝ] Space => ∑ i : Fin 3, A (coordinateVector i) i) (by simp))

/-- Incompressibility is preserved globally, not only inside the local chart. -/
theorem periodize_divergence_free {r : ℝ} {u : VelocityField}
    (hu : SupportedInCube r u) (hr : r < 1/2) {t : ℝ}
    (hdiv : ∀ x, spatialDivergence u t x = 0) (x : Space) :
    spatialDivergence (periodize u) t x = 0 := by
  have he := congrFun (spatialDivergence_periodize hu hr) (t,x)
  exact he.trans (periodize_eq_zero_of_timeSlice hdiv x)

/-- A whole-space PDE on a fixed time slice transports to the actual periodic
PDE with the periodized force. -/
theorem periodize_pde (ν : ℝ) {r : ℝ} {u f : VelocityField} {p : PressureField}
    (hu : SupportedInCube r u) (hp : SupportedInCube r p) (hr : r < 1/2) {t : ℝ}
    (hNS : ∀ x, Source.residual ν u p t x = f (t,x)) (x : Space) :
    Source.residual ν (periodize u) (periodize p) t x = periodize f (t,x) := by
  have he := congrFun (residual_periodize ν hu hp hr) (t,x)
  apply he.trans
  apply tsum_congr
  intro n
  exact hNS (x - lattice n)


/-- The nonlinear residual increment of a compact perturbation vanishes
outside the same support cube, even when the reference itself is not compact. -/
theorem supported_residual_increment (ν : ℝ) {r : ℝ}
    (v : VelocityField) (q : PressureField) {w : VelocityField} {p : PressureField}
    (hw : SupportedInCube r w) (hp : SupportedInCube r p) :
    SupportedInCube r (fun z => Source.residual ν (v+w) (q+p) z.1 z.2 -
      Source.residual ν v q z.1 z.2) := by
  intro z hz i
  by_contra hnot
  have hgt : r < |z.2 i| := lt_of_not_ge hnot
  have hw0 := zero_germ_outside_cube hw hgt
  have hp0 := zero_germ_outside_cube hp hgt
  have hvEq : v+w =ᶠ[𝓝 z] v := by
    filter_upwards [hw0] with y hy
    simp only [Pi.add_apply,hy,add_zero]
  have hqEq : q+p =ᶠ[𝓝 z] q := by
    filter_upwards [hp0] with y hy
    simp only [Pi.add_apply,hy,add_zero]
  exact hz (sub_eq_zero.mpr (Source.LocalReferenceHelpers.residual_congr ν hvEq hqEq))

/-- Actual residual increments periodize around an existing periodic
reference. This is the bridge used by localized perturbative insertion. -/
theorem residual_increment_periodize (ν : ℝ) {r : ℝ}
    {v w : VelocityField} {q p : PressureField}
    (hv : UnitSpatialPeriodsOn univ v) (hq : UnitSpatialPeriodsOn univ q)
    (hw : SupportedInCube r w) (hp : SupportedInCube r p) (hr : r < 1/2) :
    (fun z => Source.residual ν (v + periodize w) (q + periodize p) z.1 z.2 -
      Source.residual ν v q z.1 z.2) =
      periodize (fun z => Source.residual ν (v+w) (q+p) z.1 z.2 -
        Source.residual ν v q z.1 z.2) := by
  have hV : UnitSpatialPeriodsOn univ (v+periodize w) := by
    intro t ht x i
    exact congrArg₂ (· + ·) (hv t ht x i)
      (unitSpatialPeriodsOn_periodize w univ t ht x i)
  have hQ : UnitSpatialPeriodsOn univ (q+periodize p) := by
    intro t ht x i
    exact congrArg₂ (· + ·) (hq t ht x i)
      (unitSpatialPeriodsOn_periodize p univ t ht x i)
  apply periodic_eq_of_unitCube
  · intro t ht x i
    exact congrArg₂ (· - ·) (residual_unitPeriods ν hV hQ t ht x i)
      (residual_unitPeriods ν hv hq t ht x i)
  · exact unitSpatialPeriodsOn_periodize _ univ
  · intro t x hx
    have hz := innerCube_of_unitCube hr hx
    have hwe := (Filter.EventuallyEq.rfl (f := v)).add (periodize_eventuallyEq hw (z := (t,x)) hz)
    have hpe := (Filter.EventuallyEq.rfl (f := q)).add (periodize_eventuallyEq hp (z := (t,x)) hz)
    have he := Source.LocalReferenceHelpers.residual_congr ν hwe hpe
    change Source.residual ν (v+periodize w) (q+periodize p) t x - Source.residual ν v q t x = _
    rw [he,periodize_eq_on_unitCube (supported_residual_increment ν v q hw hp) hr hx]

/-- The physical PDE residual after periodic insertion has exactly the
periodized perturbation force. -/
theorem periodic_reference_pde (ν : ℝ) {r : ℝ}
    {v w f g : VelocityField} {q p : PressureField}
    (hv : UnitSpatialPeriodsOn univ v) (hq : UnitSpatialPeriodsOn univ q)
    (hw : SupportedInCube r w) (hp : SupportedInCube r p) (hr : r < 1/2) {t : ℝ}
    (href : ∀ x, Source.residual ν v q t x = g (t,x))
    (hNS : ∀ x, Source.residual ν (v+w) (q+p) t x = g (t,x)+f (t,x)) (x : Space) :
    Source.residual ν (v+periodize w) (q+periodize p) t x = g (t,x)+periodize f (t,x) := by
  have he := congrFun (residual_increment_periodize ν hv hq hw hp hr) (t,x)
  have hforce : periodize (fun z => Source.residual ν (v+w) (q+p) z.1 z.2 -
      Source.residual ν v q z.1 z.2) (t,x) = periodize f (t,x) := by
    apply tsum_congr
    intro n
    change Source.residual ν (v+w) (q+p) t (x-lattice n) -
      Source.residual ν v q t (x-lattice n) = f (t,x-lattice n)
    rw [hNS,href,add_sub_cancel_left]
  change Source.residual ν (v+periodize w) (q+periodize p) t x - Source.residual ν v q t x = _ at he
  rw [href,hforce] at he
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)


/-- Checking one cube also works on an arbitrary prescribed set of times. -/
theorem periodic_eqOn_of_unitCube {E : Type*} {I : Set ℝ} {f g : SpaceTime → E}
    (hf : UnitSpatialPeriodsOn I f) (hg : UnitSpatialPeriodsOn I g)
    (heq : ∀ t ∈ I, ∀ x, (∀ i : Fin 3, |x i| ≤ 1/2) → f (t,x) = g (t,x)) :
    EqOn f g (I ×ˢ (univ : Set Space)) := by
  intro z hz
  have hf0 : UnitSpatialPeriodsOn univ (fun y : SpaceTime => f (z.1,y.2)) :=
    fun _ _ x i => hf z.1 hz.1 x i
  have hg0 : UnitSpatialPeriodsOn univ (fun y : SpaceTime => g (z.1,y.2)) :=
    fun _ _ x i => hg z.1 hz.1 x i
  have he := periodic_eq_of_unitCube hf0 hg0 (fun _ x hx => heq z.1 hz.1 x hx)
  exact congrFun he z

/-- Local-in-time version of the already proved periodic residual calculus. -/
theorem residual_periods_on (ν : ℝ) {I : Set ℝ} (hI : IsOpen I)
    {u : VelocityField} {p : PressureField}
    (hu : UnitSpatialPeriodsOn I u) (hp : UnitSpatialPeriodsOn I p) :
    UnitSpatialPeriodsOn I (fun z => Source.residual ν u p z.1 z.2) := by
  intro t ht x i
  simp only [Source.residual,
    ResidualRegularity.temporalDerivative_periods hI hu t ht x i,
    ResidualRegularity.advection_periods hu t ht x i,
    ResidualRegularity.spatialLaplacian_periods hu t ht x i,
    ResidualRegularity.pressureGradient_periods hp t ht x i]

/-- Reference periodicity is needed only on the open physical time interval
where the equation is asserted. -/
theorem residual_increment_periodize_on (ν : ℝ) {I : Set ℝ} (hI : IsOpen I) {r : ℝ}
    {v w : VelocityField} {q p : PressureField}
    (hv : UnitSpatialPeriodsOn I v) (hq : UnitSpatialPeriodsOn I q)
    (hw : SupportedInCube r w) (hp : SupportedInCube r p) (hr : r < 1/2) :
    EqOn (fun z => Source.residual ν (v + periodize w) (q + periodize p) z.1 z.2 -
      Source.residual ν v q z.1 z.2)
      (periodize (fun z => Source.residual ν (v+w) (q+p) z.1 z.2 -
        Source.residual ν v q z.1 z.2)) (I ×ˢ (univ : Set Space)) := by
  have hV : UnitSpatialPeriodsOn I (v+periodize w) := by
    intro t ht x i
    exact congrArg₂ (· + ·) (hv t ht x i) (unitSpatialPeriodsOn_periodize w I t ht x i)
  have hQ : UnitSpatialPeriodsOn I (q+periodize p) := by
    intro t ht x i
    exact congrArg₂ (· + ·) (hq t ht x i) (unitSpatialPeriodsOn_periodize p I t ht x i)
  apply periodic_eqOn_of_unitCube
  · intro t ht x i
    exact congrArg₂ (· - ·) (residual_periods_on ν hI hV hQ t ht x i)
      (residual_periods_on ν hI hv hq t ht x i)
  · exact unitSpatialPeriodsOn_periodize _ I
  · intro t _ x hx
    have hz := innerCube_of_unitCube hr hx
    have hwe := (Filter.EventuallyEq.rfl (f := v)).add (periodize_eventuallyEq hw (z := (t,x)) hz)
    have hpe := (Filter.EventuallyEq.rfl (f := q)).add (periodize_eventuallyEq hp (z := (t,x)) hz)
    have he := Source.LocalReferenceHelpers.residual_congr ν hwe hpe
    change Source.residual ν (v+periodize w) (q+periodize p) t x - Source.residual ν v q t x = _
    rw [he,periodize_eq_on_unitCube (supported_residual_increment ν v q hw hp) hr hx]

theorem periodic_reference_pde_on (ν : ℝ) {I : Set ℝ} (hI : IsOpen I) {r : ℝ}
    {v w f g : VelocityField} {q p : PressureField}
    (hv : UnitSpatialPeriodsOn I v) (hq : UnitSpatialPeriodsOn I q)
    (hw : SupportedInCube r w) (hp : SupportedInCube r p) (hr : r < 1/2) {t : ℝ} (ht : t ∈ I)
    (href : ∀ x, Source.residual ν v q t x = g (t,x))
    (hNS : ∀ x, Source.residual ν (v+w) (q+p) t x = g (t,x)+f (t,x)) (x : Space) :
    Source.residual ν (v+periodize w) (q+periodize p) t x = g (t,x)+periodize f (t,x) := by
  have he := residual_increment_periodize_on ν hI hv hq hw hp hr (x := (t,x)) ⟨ht,mem_univ _⟩
  have hforce : periodize (fun z => Source.residual ν (v+w) (q+p) z.1 z.2 -
      Source.residual ν v q z.1 z.2) (t,x) = periodize f (t,x) := by
    apply tsum_congr
    intro n
    change Source.residual ν (v+w) (q+p) t (x-lattice n) -
      Source.residual ν v q t (x-lattice n) = f (t,x-lattice n)
    rw [hNS,href,add_sub_cancel_left]
  change Source.residual ν (v+periodize w) (q+periodize p) t x - Source.residual ν v q t x = _ at he
  rw [href,hforce] at he
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)


/-- Compact spacetime support gives a closed time-support projection, and
periodization introduces no new time into it. -/
theorem time_support_periodize {E : Type*} [NormedAddCommGroup E]
    {f : SpaceTime → E} (hf : HasCompactSupport f) :
    tsupport (periodize f) ⊆ Prod.fst ⁻¹' (Prod.fst '' tsupport f) := by
  apply closure_minimal _ ((hf.image continuous_fst).isClosed.preimage continuous_fst)
  intro z hz
  by_contra hn
  apply hz
  apply periodize_eq_zero_of_timeSlice
  intro x
  apply image_eq_zero_of_notMem_tsupport
  intro hx
  exact hn ⟨(z.1,x),hx,rfl⟩

end NSFormalization.Paper1.PeriodicBridge
