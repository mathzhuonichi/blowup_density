import NSFormalization.Section3.T15.SingleCopy
import NSFormalization.Paper1.PeriodicBridge

/-!
# T15 U7 — the periodized scaled force belongs to the torus force class

The parabolically scaled Euclidean force remains globally smooth and has
compact support strictly in positive physical time.  Placement puts every
spatial slice strictly inside the fundamental cube, so the vendor's locally
finite periodizer preserves smoothness.  Reindexing the lattice sum gives unit
spatial periodicity, while periodization introduces no new time into support.
-/

noncomputable section

namespace NSFormalization.Section3.T15

open Set Filter Topology
open NavierStokes.ProblemStatement
open NavierStokes.PeriodicLocalization
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open NSFormalization.Source.PacketScaling
open scoped ContDiff Topology

/-- The scaled force has the uniform coordinate bound required by the vendor
periodizer.  It follows slice-by-slice from the strict placement support. -/
theorem scaledForce_supportedInCube
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hforce_support : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u p f K) {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) place.ε₀) :
    SupportedInCube 1 (scaledForce f place.x₀ place.T ε) := by
  intro z hz i
  have hslice : z.2 ∈ tsupport (fun x : Space =>
      scaledForce f place.x₀ place.T ε (z.1, x)) := subset_tsupport _ hz
  have hi := interior_subset_fundamentalCubeInterior
    (scaledForce_slice_subset_cube hε place.Kstar_compact hforce_support
      place.force_projection_subset place.eps_space place.chartBall_in_cube z.1 hslice) i
  rw [abs_of_nonneg hi.1.le]
  exact hi.2.le

/-- `03-torus.tex:108-123`: every admissible periodized scaled force is
globally smooth, unit-periodic in space, and compactly supported at positive
times.  These are exactly the three clauses of the canonical `MemForceT`. -/
theorem force_mem
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hforce_smooth : ContDiff ℝ ∞ f)
    (hforce_support : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      MemForceT (periodizedScaledForce f place.x₀ place.T ε) := by
  intro ε hε
  have ht₀ : 0 ≤ place.T - ε ^ 2 := by
    have hsquare : 0 ≤ ε ^ 2 := sq_nonneg ε
    linarith [place.eps_time ε hε]
  have hscaledSupport :
      NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport
        (scaledForce f place.x₀ place.T ε) := by
    rw [scaledForce_eq_parabolicForce]
    exact parabolicForce_positive_support hforce_support (inv_pos.mpr hε.1) ht₀ place.x₀
  have hscaledSmooth : ContDiff ℝ ∞ (scaledForce f place.x₀ place.T ε) := by
    rw [scaledForce_eq_parabolicForce]
    exact parabolicForce_smooth hforce_smooth ε⁻¹ (place.T - ε ^ 2) place.x₀
  refine ⟨?_, ?_, ?_⟩
  · change ContDiff ℝ ∞
      (NavierStokes.PeriodicLocalization.periodize
        (scaledForce f place.x₀ place.T ε))
    exact contDiff_periodize (scaledForce_supportedInCube hforce_support place hε)
      hscaledSmooth
  · change IsPeriodicOn univ
      (NavierStokes.PeriodicLocalization.periodize
        (scaledForce f place.x₀ place.T ε))
    exact unitSpatialPeriodsOn_periodize (scaledForce f place.x₀ place.T ε) univ
  · let Ktime : Set ℝ := Prod.fst '' tsupport (scaledForce f place.x₀ place.T ε)
    refine ⟨Ktime, hscaledSupport.1.isCompact.image continuous_fst, ?_, ?_⟩
    · rintro t ⟨z, hz, rfl⟩
      exact (hscaledSupport.2 hz).1
    · have htime := NSFormalization.Paper1.PeriodicBridge.time_support_periodize
        hscaledSupport.1
      change tsupport
        (NavierStokes.PeriodicLocalization.periodize
          (scaledForce f place.x₀ place.T ε)) ⊆ Ktime ×ˢ univ
      intro z hz
      exact ⟨htime hz, mem_univ _⟩

end NSFormalization.Section3.T15
