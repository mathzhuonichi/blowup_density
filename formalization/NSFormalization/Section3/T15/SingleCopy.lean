import NSFormalization.Section3.T15.Placement
import NSFormalization.Section3.T15.Scaling
import NavierStokes.PeriodicLocalization

/-!
# T15 U3 — lattice summability and the single supported copy

For every admissible scale, `Placement` puts each rescaled spatial slice
strictly inside the fundamental cube.  Such a slice is bounded in the vendor
periodizer's sense, so its lattice translates have finite support at every
point and are summable.  On the closed fundamental cube, every nonzero lattice
translate misses the strict interior support; hence the periodization is its
zero-lattice copy.

The six final theorems have literally the types of the corresponding fields of
the canonical `ScalingAPI`.  Their extra arguments are precisely the raw packet
support clauses used by `Placement`.
-/

noncomputable section

namespace NSFormalization.Section3.T15

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open scoped BigOperators Topology

/-! ## Value-generic lattice facts -/

/-- Strict support in the fundamental cube gives a coordinate bound suitable
for the vendor's locally finite periodization theorem. -/
theorem supportedInCube_of_tsupport_subset_interior
    {V : Type*} [NormedAddCommGroup V] {g : Space → V}
    (hsupp : tsupport g ⊆ interior fundamentalCube) :
    NavierStokes.PeriodicLocalization.SupportedInCube 1
      (fun z : SpaceTime => g z.2) := by
  intro z hz i
  have hi := interior_subset_fundamentalCubeInterior
    (hsupp (subset_tsupport g hz)) i
  rw [abs_of_nonneg hi.1.le]
  exact hi.2.le

/-- At every spatial point, only finitely many lattice translates of a field
strictly supported in the fundamental cube can be nonzero. -/
theorem summable_lattice_of_tsupport_subset_interior
    {V : Type*} [NormedAddCommGroup V] {g : Space → V}
    (hsupp : tsupport g ⊆ interior fundamentalCube) (x : Space) :
    Summable (fun n : PeriodicFrequency => g (x - latticeVector n)) := by
  have h := NavierStokes.PeriodicLocalization.summable_translate
    (supportedInCube_of_tsupport_subset_interior hsupp) ((0 : ℝ), x)
  exact h

/-- On the closed cube a nonzero lattice translate cannot meet support lying
strictly in the cube interior.  This is the value-generic form of
`T13.eq_zero_of_mem_cube`, needed also for scalar pressure. -/
theorem lattice_term_eq_zero_of_mem_cube
    {V : Type*} [Zero V] {g : Space → V}
    (hsupp : tsupport g ⊆ interior fundamentalCube)
    {x : Space} (hx : x ∈ fundamentalCube)
    {n : PeriodicFrequency} (hn : n ≠ 0) :
    g (x - latticeVector n) = 0 := by
  by_contra hne
  have hmem : x - latticeVector n ∈ interior fundamentalCube :=
    hsupp (subset_tsupport g hne)
  have hI := interior_subset_fundamentalCubeInterior hmem
  obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := Function.ne_iff.mp hn
  have hxi := hx i
  have hIi := hI i
  have hcoord : (x - latticeVector n) i = x i - (n i : ℝ) := rfl
  rw [hcoord] at hIi
  rcases lt_or_gt_of_ne hi with hneg | hpos
  · have hz : (1 : ℤ) ≤ -n i := by omega
    have hz' : (1 : ℝ) ≤ -(n i : ℝ) := by exact_mod_cast hz
    linarith [hxi.2, hIi.2]
  · have hz : (1 : ℤ) ≤ n i := by omega
    have hz' : (1 : ℝ) ≤ (n i : ℝ) := by exact_mod_cast hz
    linarith [hxi.1, hIi.1]

/-- The lattice sum of a field strictly supported in the cube is its single
zero-lattice copy throughout the closed fundamental cube. -/
theorem tsum_eq_single_copy_of_mem_cube
    {V : Type*} [NormedAddCommGroup V] {g : Space → V}
    (hsupp : tsupport g ⊆ interior fundamentalCube)
    {x : Space} (hx : x ∈ fundamentalCube) :
    (∑' n : PeriodicFrequency, g (x - latticeVector n)) = g x := by
  have h := tsum_eq_single (L := SummationFilter.unconditional PeriodicFrequency)
    (0 : PeriodicFrequency)
    (fun n hn => lattice_term_eq_zero_of_mem_cube hsupp hx hn)
  simpa only [latticeVector_zero, sub_zero] using h

/-! ## The six canonical `ScalingAPI` fields -/

/-- The velocity lattice family is summable at every admissible scale,
presingular time, and spatial point. -/
theorem velocity_summable
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hcarrier_compact : IsCompact K)
    (hvelocity_support : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => u (t, x)) ⊆ K)
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      ∀ t : ℝ, t < place.T → ∀ x : Space,
        Summable (fun n : PeriodicFrequency ↦
          scaledVelocity u place.x₀ place.T ε (t, x - latticeVector n)) := by
  intro ε hε t ht x
  exact summable_lattice_of_tsupport_subset_interior
    (scaledVelocity_slice_subset_cube hε hcarrier_compact hvelocity_support
      place.carrier_subset place.eps_space place.chartBall_in_cube ht) x

/-- The raw pressure lattice family is summable at every admissible scale,
presingular time, and spatial point. -/
theorem pressure_summable
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hcarrier_compact : IsCompact K)
    (hpressure_support : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => p (t, x)) ⊆ K)
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      ∀ t : ℝ, t < place.T → ∀ x : Space,
        Summable (fun n : PeriodicFrequency ↦
          scaledPressure p place.x₀ place.T ε (t, x - latticeVector n)) := by
  intro ε hε t ht x
  exact summable_lattice_of_tsupport_subset_interior
    (scaledPressure_slice_subset_cube hε hcarrier_compact hpressure_support
      place.carrier_subset place.eps_space place.chartBall_in_cube ht) x

/-- The force lattice family is summable at every admissible scale and every
spacetime point. -/
theorem force_summable
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hforce_support : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      ∀ t : ℝ, ∀ x : Space,
        Summable (fun n : PeriodicFrequency ↦
          scaledForce f place.x₀ place.T ε (t, x - latticeVector n)) := by
  intro ε hε t x
  exact summable_lattice_of_tsupport_subset_interior
    (scaledForce_slice_subset_cube hε place.Kstar_compact hforce_support
      place.force_projection_subset place.eps_space place.chartBall_in_cube t) x

/-- On the fundamental cube the periodized velocity is its single zero-lattice
copy. -/
theorem velocity_singleCopy
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hcarrier_compact : IsCompact K)
    (hvelocity_support : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => u (t, x)) ⊆ K)
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      ∀ t : ℝ, t < place.T → ∀ x ∈ fundamentalCube,
        periodizedScaledVelocity u place.x₀ place.T ε (t, x) =
          scaledVelocity u place.x₀ place.T ε (t, x) := by
  intro ε hε t ht x hx
  exact tsum_eq_single_copy_of_mem_cube
    (scaledVelocity_slice_subset_cube hε hcarrier_compact hvelocity_support
      place.carrier_subset place.eps_space place.chartBall_in_cube ht) hx

/-- On the fundamental cube the raw periodized pressure is its single
zero-lattice copy. -/
theorem pressure_singleCopy
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hcarrier_compact : IsCompact K)
    (hpressure_support : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => p (t, x)) ⊆ K)
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      ∀ t : ℝ, t < place.T → ∀ x ∈ fundamentalCube,
        periodizedScaledPressure p place.x₀ place.T ε (t, x) =
          scaledPressure p place.x₀ place.T ε (t, x) := by
  intro ε hε t ht x hx
  exact tsum_eq_single_copy_of_mem_cube
    (scaledPressure_slice_subset_cube hε hcarrier_compact hpressure_support
      place.carrier_subset place.eps_space place.chartBall_in_cube ht) hx

/-- On the fundamental cube the periodized force is its single zero-lattice
copy at every real time. -/
theorem force_singleCopy
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hforce_support : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      ∀ t : ℝ, ∀ x ∈ fundamentalCube,
        periodizedScaledForce f place.x₀ place.T ε (t, x) =
          scaledForce f place.x₀ place.T ε (t, x) := by
  intro ε hε t x hx
  exact tsum_eq_single_copy_of_mem_cube
    (scaledForce_slice_subset_cube hε place.Kstar_compact hforce_support
      place.force_projection_subset place.eps_space place.chartBall_in_cube t) hx

end NSFormalization.Section3.T15
