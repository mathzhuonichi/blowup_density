import NSFormalization.Section3.T15.Equation
import NSFormalization.Section3.T15.SobolevPath
import NSFormalization.Section3.T15.Pressure
import NSFormalization.Paper1.PeriodicPressureNormalization

/-!
# T15 U11: assembly of the explicit periodized classical solution

The raw velocity and pressure periodizations are jointly smooth before the
target time and have the unit lattice periods.  Haar pressure normalization
agrees with cube-mean normalization, so the existing smooth-normalization
theorem applies on the full half-open slab, including time zero.
-/

noncomputable section

namespace NSFormalization.Section3.T15

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T13
open NSFormalization.Source NSFormalization.Source.PacketScaling
open NSFormalization.Section4.A02 (SpatialField SpaceTimeScalar)
open scoped ContDiff Topology

/-! ## Smoothness and periodicity of the two explicit fields -/

/-- Haar normalization is the same operation as the existing cube-mean
normalization, by the canonical Haar-to-cube integration theorem. -/
theorem normalizePressureT_eq_normalizedPressure (q : SpaceTimeScalar) :
    normalizePressureT q =
      NSFormalization.Paper1.PeriodicPressureNormalization.normalizedPressure q := by
  funext z
  unfold normalizePressureT pressureMeanT
  unfold NSFormalization.Paper1.PeriodicPressureNormalization.normalizedPressure
    NSFormalization.Paper1.PeriodicPressureNormalization.pressureMean
  rw [NSFormalization.Paper1.integral_torusLift]

/-- The raw periodized pressure is jointly smooth on the physical solution slab. -/
theorem periodizedPressure_contDiffOn
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hext : ContDiffOn ℝ ∞ (zeroPastField p)
      (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
    (hK : IsCompact K)
    (hp : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => p (t, x)) ⊆ K)
    (place : PlacementData u p f K) {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) place.ε₀) :
    ContDiffOn ℝ ∞ (periodizedScaledPressure p place.x₀ place.T ε)
      (Ico (0 : ℝ) place.T ×ˢ (univ : Set Space)) := by
  have hscaled := dilate_smoothOn (f := zeroPastField p) (ε⁻¹ ^ 2)
    (inv_pos.2 hε.1) (place.T - ε ^ 2) place.x₀ hext
  rw [NSFormalization.Section4.I03.parabolic_window ε place.T] at hscaled
  exact (contDiffOn_periodize_of_slice_support hscaled (fun t ht =>
    scaledPressure_slice_subset_cube hε hK hp place.carrier_subset place.eps_space
      place.chartBall_in_cube ht)).mono
        (prod_mono (Ico_subset_Iio_self) (subset_refl _))

/-- Subtracting the time-dependent Haar mean preserves joint slab smoothness. -/
theorem normalizedScaledPressure_contDiffOn
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hext : ContDiffOn ℝ ∞ (zeroPastField p)
      (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
    (hK : IsCompact K)
    (hp : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => p (t, x)) ⊆ K)
    (place : PlacementData u p f K) {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) place.ε₀) :
    ContDiffOn ℝ ∞ (normalizedScaledPressure p place.x₀ place.T ε)
      (Ico (0 : ℝ) place.T ×ˢ (univ : Set Space)) := by
  rw [normalizedScaledPressure, normalizePressureT_eq_normalizedPressure]
  exact NSFormalization.Paper1.PeriodicPressureNormalization.normalizedPressure_contDiffOn
    (periodizedPressure_contDiffOn hext hK hp place hε)

/-- Spatially constant pressure normalization preserves every unit period. -/
theorem isPeriodicOn_normalizePressureT {q : SpaceTimeScalar} {I : Set ℝ}
    (hq : IsPeriodicOn I q) : IsPeriodicOn I (normalizePressureT q) := by
  intro t ht x i
  show q (t, x + coordinateVector i) - pressureMeanT q t =
    q (t, x) - pressureMeanT q t
  rw [hq t ht x i]

/-- The explicit periodized velocity has the required unit spatial periods. -/
theorem periodizedVelocity_periodic
    (u : VelocityField) (x₀ : Space) (T ε : ℝ) :
    IsPeriodicOn (Ico (0 : ℝ) T) (periodizedScaledVelocity u x₀ T ε) := by
  change IsPeriodicOn (Ico (0 : ℝ) T)
    (NavierStokes.PeriodicLocalization.periodize (scaledVelocity u x₀ T ε))
  exact NavierStokes.PeriodicLocalization.unitSpatialPeriodsOn_periodize
    (scaledVelocity u x₀ T ε) (Ico 0 T)

/-- The normalized explicit pressure has the required unit spatial periods. -/
theorem normalizedScaledPressure_periodic
    (p : PressureField) (x₀ : Space) (T ε : ℝ) :
    IsPeriodicOn (Ico (0 : ℝ) T) (normalizedScaledPressure p x₀ T ε) := by
  apply isPeriodicOn_normalizePressureT
  change IsPeriodicOn (Ico (0 : ℝ) T)
    (NavierStokes.PeriodicLocalization.periodize (scaledPressure p x₀ T ε))
  exact NavierStokes.PeriodicLocalization.unitSpatialPeriodsOn_periodize
    (scaledPressure p x₀ T ε) (Ico 0 T)

/-! ## The classical solution and the literal `ScalingAPI.solution` field -/

/-- The explicit periodized velocity and normalized pressure, assembled with
all thirteen fields of `ClassicalSolutionT`. -/
def periodizedSolution
    {ν : ℝ} {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hcarrier_compact : IsCompact K)
    (hvelocity_support : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => u (t, x)) ⊆ K)
    (hpressure_support : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => p (t, x)) ⊆ K)
    (hforce_support : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (hforce_zero : ∀ t : ℝ, t ≤ 0 → ∀ x : Space, f (t, x) = 0)
    (hvelocity_extension_smooth : ContDiffOn ℝ ∞ (zeroPastField u)
      (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
    (hpressure_extension_smooth : ContDiffOn ℝ ∞ (zeroPastField p)
      (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
    (hequation : ∀ t : ℝ, t < 1 → ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν
        (zeroPastField u) (zeroPastField p) t x = zeroPastField f (t, x))
    (hdivergence : ∀ t : ℝ, t < 1 → ∀ x : Space,
      spatialDivergence (zeroPastField u) t x = 0)
    (place : PlacementData u p f K) {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) place.ε₀) :
    ClassicalSolutionT ν (0 : SpatialField)
      (periodizedScaledForce f place.x₀ place.T ε) place.T where
  velocity := periodizedScaledVelocity u place.x₀ place.T ε
  pressure := normalizedScaledPressure p place.x₀ place.T ε
  horizon_pos := by
    have hmargin := place.eps_time place.ε₀ ⟨place.eps_pos, le_rfl⟩
    nlinarith [sq_nonneg place.ε₀]
  velocity_smooth := (periodizedVelocity_contDiffOn hvelocity_extension_smooth
    hcarrier_compact hvelocity_support place hε).mono
      (prod_mono Ico_subset_Iio_self (subset_refl _))
  pressure_smooth := normalizedScaledPressure_contDiffOn hpressure_extension_smooth
    hcarrier_compact hpressure_support place hε
  initial := by
    intro x
    simpa using periodized_initial place ε hε x
  divergence := periodized_divergence hcarrier_compact hvelocity_support hdivergence
    place ε hε
  momentum := periodized_momentum hcarrier_compact hvelocity_support hpressure_support
    hforce_support hforce_zero hequation place ε hε
  sobolev := periodized_sobolev hvelocity_extension_smooth hcarrier_compact
    hvelocity_support place ε hε
  pressure_gradient := periodized_pressure_gradient hpressure_extension_smooth
    hcarrier_compact hpressure_support place ε hε
  velocity_periodic := periodizedVelocity_periodic u place.x₀ place.T ε
  pressure_periodic := normalizedScaledPressure_periodic p place.x₀ place.T ε
  pressure_gauge := pressure_gauge hcarrier_compact hpressure_support
    hpressure_extension_smooth place ε hε

/-- The `ScalingAPI.solution` field under exactly the raw packet clauses used
by its thirteen constituent solution fields. -/
theorem solution
    {ν : ℝ} {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hcarrier_compact : IsCompact K)
    (hvelocity_support : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => u (t, x)) ⊆ K)
    (hpressure_support : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => p (t, x)) ⊆ K)
    (hforce_support : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (hforce_zero : ∀ t : ℝ, t ≤ 0 → ∀ x : Space, f (t, x) = 0)
    (hvelocity_extension_smooth : ContDiffOn ℝ ∞ (zeroPastField u)
      (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
    (hpressure_extension_smooth : ContDiffOn ℝ ∞ (zeroPastField p)
      (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
    (hequation : ∀ t : ℝ, t < 1 → ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν
        (zeroPastField u) (zeroPastField p) t x = zeroPastField f (t, x))
    (hdivergence : ∀ t : ℝ, t < 1 → ∀ x : Space,
      spatialDivergence (zeroPastField u) t x = 0)
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      ∃ S : ClassicalSolutionT ν (0 : SpatialField)
          (periodizedScaledForce f place.x₀ place.T ε) place.T,
        S.velocity = periodizedScaledVelocity u place.x₀ place.T ε ∧
          S.pressure = normalizedScaledPressure p place.x₀ place.T ε := by
  intro ε hε
  exact ⟨periodizedSolution hcarrier_compact hvelocity_support hpressure_support
    hforce_support hforce_zero hvelocity_extension_smooth hpressure_extension_smooth
    hequation hdivergence place hε, rfl, rfl⟩

end NSFormalization.Section3.T15
