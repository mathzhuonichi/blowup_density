import NSFormalization.Section3.T24.Multiple
import NSFormalization.Section3.T23.Boundary
import NSFormalization.Section3.T22.Domain

/-!
Proposition 3.16, `paper/revised/sections/03-torus.tex:511-535`:
"Fix finitely many disjoint interior balls ... in a bounded three-dimensional domain."
"In a bounded domain its boundary condition is homogeneous no-slip."
"Apply ... to each building block with start time T − ε_j²."
Specification only: no inhabitant or existence theorem is supplied.
TORUS→Ω: the domain and its class are parameters; the torus-only ScalingAPI
field is dropped and explicit no_slip added (30 fields in total).
The raw scaledVelocity/scaledPressure/scaledForce names are T15.Bridges wrappers
for Source.PacketScaling, used by Section4/I03/Energy.lean:
scaled_smoothOn, eLpNorm_scaled_slice, energyEssSup_scaled_le,
scaled_total_dissipation, energyGradient_scaled_eq. No lattice sum or background.
Pressure alone is adjusted by its Ω-average, as required by the owner's gauge.
-/
noncomputable section
namespace NSFormalization.Section3.T24
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NavierStokesR3.CompactEnergy (l2Sq dissipation)
open NSFormalization.Section3.T10 NSFormalization.Section3.T13 NSFormalization.Section3.T15
open NSFormalization.Section3.T23
open NSFormalization.Section3.T14 (accumulatedForce)
open NSFormalization.Source.PacketScaling (zeroPastField)
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open scoped ContDiff ENNReal BigOperators Topology

/-- `03-torus.tex:530` (revised): restricted physical L² energy.
TORUS→Ω: eLpNorm with volume.restrict Ω is exactly the right side of the
registered T04.bounded_domain_norm / T22.BoundedDomainNormAPI.orderZero:
domainSobolevENorm Ω 0 (restrictField Ω z). We use the physical L² spelling. -/
def energyEssSupOmega (Ω : Set Space) (T : ℝ) (z : SpaceTimeField) : ℝ≥0∞ :=
  essSup (fun t ↦ eLpNorm (fun x ↦ z (t, x)) 2 (volume.restrict Ω))
    (volume.restrict (Ioo (0 : ℝ) T))

/-- `03-torus.tex:531` (revised): restricted full-gradient L² dissipation.
TORUS→Ω: the registered I02 spatialGradient (Euclidean full matrix norm),
not the operator norm of spatialDerivative; physical restricted L² as in I03. -/
def energyGradientOmega (Ω : Set Space) (T : ℝ) (z : SpaceTimeField) : ℝ≥0∞ :=
  (∫⁻ t in Ioo (0 : ℝ) T,
    (eLpNorm (fun x ↦ NSFormalization.Section4.I02.spatialGradient z t x)
      2 (volume.restrict Ω)) ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹)

/-- `03-torus.tex:511-535` (revised): bounded-domain twin, raw packet fields. -/
structure MultipleRegionsOmegaAPI {ν : ℝ} (u : VelocityField) (p : PressureField) (f : VelocityField)
    (K : Set Space) (M D : ℝ) (T : ℝ) (Ω : Set Space) (_hΩ : IsOpen Ω ∧ Bornology.IsBounded Ω ∧ Ω.Nonempty)
    {N : ℕ} (regionCenter : Fin N → Space) (regionRadius : Fin N → ℝ) : Type where
  /-- `paper/revised/sections/03-torus.tex:512`: Positive prescribed terminal time. -/
  T_pos : 0 < T
  /-- `paper/revised/sections/03-torus.tex:512,515`: Nonempty finite family of regions. -/
  N_pos : 0 < N
  /-- `paper/revised/sections/03-torus.tex:512`: Each prescribed ball has positive radius. -/
  regionRadius_pos : ∀ j : Fin N, 0 < regionRadius j
  /-- `paper/revised/sections/03-torus.tex:512,520`: Closure of each prescribed ball lies inside Ω. -/
  -- TORUS→Ω: see COMPARISON_OMEGA.md for this domain field.
  region_interior : ∀ j : Fin N,
    closure (Metric.ball (regionCenter j) (regionRadius j)) ⊆ Ω
  /-- `paper/revised/sections/03-torus.tex:512,525`: The prescribed open balls are pairwise disjoint. -/
  regions_disjoint : Pairwise (fun i j : Fin N ↦
    Disjoint (Metric.ball (regionCenter i) (regionRadius i))
      (Metric.ball (regionCenter j) (regionRadius j)))
  /-- `paper/revised/sections/03-torus.tex:520`: One cube-free placement of the shared packet in each prescribed ball. -/
  -- TORUS→Ω: see COMPARISON_OMEGA.md for this domain field.
  placement : Fin N → DomainPlacementData u p f K
  /-- `paper/revised/sections/03-torus.tex:520,535`: Each placement has the common terminal time T. -/
  placement_time : ∀ j : Fin N, (placement j).T = T
  /-- `paper/revised/sections/03-torus.tex:520`: The placement chart is exactly the prescribed ball, not a freely chosen region. -/
  placement_chart : ∀ j : Fin N,
    (placement j).chartCenter = regionCenter j ∧
      (placement j).chartRadius = regionRadius j
  /-- `paper/revised/sections/03-torus.tex:520`: The selected positive length scale for each component. -/
  ε : Fin N → ℝ
  /-- `paper/revised/sections/03-torus.tex:520`: Each chosen scale lies in its placement threshold interval. -/
  eps_admissible : ∀ j : Fin N, ε j ∈ Ioc (0 : ℝ) (placement j).ε₀
  /-- `paper/revised/sections/03-torus.tex:520`: The start time T − ε_j² is strictly positive. -/
  eps_time : ∀ j : Fin N, ε j ^ 2 < T
  /-- `paper/revised/sections/03-torus.tex:512,517,520,526`: Actual classical no-slip component from rest with the raw scaled force. -/
  -- TORUS→Ω: see COMPARISON_OMEGA.md for this domain field.
  component : ∀ j : Fin N,
    ClassicalSolutionOmega ν Ω (0 : SpatialField)
      (scaledForce f (placement j).x₀ T (ε j)) T
  /-- `paper/revised/sections/03-torus.tex:520,523`: Velocity is the raw scaled packet; pressure is its Ω-mean-normalized scaled pressure (gauge convention at revised line 458). -/
  -- TORUS→Ω: see COMPARISON_OMEGA.md for this domain field.
  component_pin : ∀ j : Fin N,
    (component j).velocity = scaledVelocity u (placement j).x₀ T (ε j) ∧
      (component j).pressure = domainNormalizePressure Ω (scaledPressure p (placement j).x₀ T (ε j))
  /-- `paper/revised/sections/03-torus.tex:520,525`: Each velocity vanishes globally outside its ball before T. -/
  -- TORUS→Ω: see COMPARISON_OMEGA.md for this domain field.
  component_support : ∀ j : Fin N, ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
    x ∉ Metric.ball (regionCenter j) (regionRadius j) →
      (component j).velocity (t, x) = 0
  /-- `paper/revised/sections/03-torus.tex:520,526`: Each raw scaled force vanishes globally outside its ball at every time. -/
  -- TORUS→Ω: see COMPARISON_OMEGA.md for this domain field.
  component_force_support : ∀ j : Fin N, ∀ t : ℝ, ∀ x : Space,
    x ∉ Metric.ball (regionCenter j) (regionRadius j) →
      scaledForce f (placement j).x₀ T (ε j) (t, x) = 0
  /-- `paper/revised/sections/03-torus.tex:523`: The velocity of the finite superposition. -/
  assembled_velocity : SpaceTimeField
  /-- `paper/revised/sections/03-torus.tex:523`: The assembled velocity equals the explicit finite sum of component velocities. -/
  assembled_velocity_formula :
    assembled_velocity = finiteVelocitySum (fun j ↦ (component j).velocity)
  /-- `paper/revised/sections/03-torus.tex:523`: The pressure of the finite superposition. -/
  assembled_pressure : SpaceTimeScalar
  /-- `paper/revised/sections/03-torus.tex:523`: The pressure equals the finite sum of the gauged component pressures. -/
  assembled_pressure_formula :
    assembled_pressure = finitePressureSum (fun j ↦ (component j).pressure)
  /-- `paper/revised/sections/03-torus.tex:523`: The force of the finite superposition. -/
  assembled_force : SpaceTimeField
  /-- `paper/revised/sections/03-torus.tex:523`: The force equals the finite sum of un-periodised scaled forces. -/
  -- TORUS→Ω: see COMPARISON_OMEGA.md for this domain field.
  assembled_force_formula :
    assembled_force =
      finiteForceSum (fun j ↦ scaledForce f (placement j).x₀ T (ε j))
  /-- `paper/revised/sections/03-torus.tex:512,517,526`: The sum is a classical solution on Ω from zero initial velocity. -/
  -- TORUS→Ω: see COMPARISON_OMEGA.md for this domain field.
  solution : ClassicalSolutionOmega ν Ω (0 : SpatialField) assembled_force T
  /-- `paper/revised/sections/03-torus.tex:523,526`: The solution fields equal the prescribed sums. -/
  solution_pin :
    solution.velocity = assembled_velocity ∧ solution.pressure = assembled_pressure
  /-- `paper/revised/sections/03-torus.tex:526`: The summed force is smooth on finite closed slabs with compact positive temporal support. -/
  -- TORUS→Ω: see COMPARISON_OMEGA.md for this domain field.
  force_mem : assembled_force ∈ forceClassOmega Ω
  /-- `paper/revised/sections/03-torus.tex:526`: Initial vanishing of the explicit sum on all of space. -/
  rest : ∀ x : Space, assembled_velocity (0, x) = 0
  /-- `paper/revised/sections/03-torus.tex:528`: Inside each ball the sum equals its own component. -/
  region_agreement : ∀ j : Fin N, ∀ t ∈ Ico (0 : ℝ) T,
    ∀ x ∈ Metric.ball (regionCenter j) (regionRadius j),
      assembled_velocity (t, x) = (component j).velocity (t, x)
  /-- `paper/revised/sections/03-torus.tex:514-515,528,535`: Separate pointwise limsup blow-up witnesses in each prescribed ball. -/
  region_blowup : ∀ j : Fin N,
    SpeedUnboundedAtOn T (Metric.ball (regionCenter j) (regionRadius j))
      assembled_velocity
  /-- `paper/revised/sections/03-torus.tex:530`: Squared restricted essential-supremum L² energy is at most M² Σ ε_j. -/
  -- TORUS→Ω: see COMPARISON_OMEGA.md for this domain field.
  energy_bound : (energyEssSupOmega Ω T assembled_velocity) ^ (2 : ℕ) ≤
    ENNReal.ofReal (M ^ 2 * ∑ j : Fin N, ε j)
  /-- `paper/revised/sections/03-torus.tex:531`: Squared restricted gradient L² norm equals D² Σ ε_j; this is an equality. -/
  -- TORUS→Ω: see COMPARISON_OMEGA.md for this domain field.
  dissipation_bound : (energyGradientOmega Ω T assembled_velocity) ^ (2 : ℕ) =
    ENNReal.ofReal (D ^ 2 * ∑ j : Fin N, ε j)

  /-- `paper/revised/sections/03-torus.tex:517,533`: The assembled velocity vanishes on the frontier of Ω throughout [0,T). -/
  -- TORUS→Ω: see COMPARISON_OMEGA.md for this domain field.
  no_slip : ∀ t ∈ Ico (0 : ℝ) T, ∀ x ∈ frontier Ω, assembled_velocity (t, x) = 0

/-- `03-torus.tex:511-535 (revised)`: existence with all raw packet clauses. -/
def multipleRegionsOmegaStatement : Prop :=
  ∀ (ν : ℝ) (hν : 0 < ν),
    ∀ (u : VelocityField) (p : PressureField) (f : VelocityField)
      (K : Set Space) (M D τ : ℝ),
    ContDiffOn ℝ ∞ u preSingularDomain →
    ContDiffOn ℝ ∞ p preSingularDomain →
    ContDiff ℝ ∞ f →
    NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f →
    IsCompact K →
    (∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space ↦ u (t, x)) ⊆ K) →
    (∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space ↦ p (t, x)) ⊆ K) →
    (∀ x : Space, u (0, x) = 0) →
    (∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space, spatialDivergence u t x = 0) →
    (∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x = f (t, x)) →
    NavierStokes.ProblemStatement.SpeedUnboundedAtOne u →
    (∀ t ∈ Ico (0 : ℝ) 1,
      NavierStokesR3.ProblemStatement.SquareIntegrableAtTime u t) →
    IsLUB ((fun t : ℝ ↦ Real.sqrt (l2Sq u t)) '' Ico (0 : ℝ) 1) M →
    IntegrableOn (dissipation u) (Ioo (0 : ℝ) 1) →
    D = Real.sqrt (∫ t in Ioo (0 : ℝ) 1, dissipation u t) →
    0 < τ → τ < 1 →
    (∀ t ∈ Icc (0 : ℝ) τ, ∀ x : Space, f (t, x) = 0) →
    (∀ t ∈ Icc (0 : ℝ) τ, ∀ x : Space, u (t, x) = 0) →
    (∀ t ∈ Icc (0 : ℝ) τ, ∀ x : Space, p (t, x) = 0) →
    (∀ t : ℝ, t ≤ 0 → ∀ x : Space, f (t, x) = 0) →
    ContDiffOn ℝ ∞ (zeroPastField u) (Iio (1 : ℝ) ×ˢ (univ : Set Space)) →
    ContDiffOn ℝ ∞ (zeroPastField p) (Iio (1 : ℝ) ×ˢ (univ : Set Space)) →
    (∀ t : ℝ, t < 1 → ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν
        (zeroPastField u) (zeroPastField p) t x = zeroPastField f (t, x)) →
    (∀ t : ℝ, t < 1 → ∀ x : Space,
      spatialDivergence (zeroPastField u) t x = 0) →
    (∀ t ∈ Ico (0 : ℝ) 1,
      l2Sq u t + 2 * ν * (∫ s in Ioo (0 : ℝ) t, dissipation u s)
        ≤ 2 * (∫ s in Ioo (0 : ℝ) t,
          Real.sqrt (l2Sq f s) * accumulatedForce f s)) →
    (∀ t ∈ Ico (0 : ℝ) 1,
      2 * (∫ s in Ioo (0 : ℝ) t,
        Real.sqrt (l2Sq f s) * accumulatedForce f s)
        = accumulatedForce f t ^ 2) →
    -- TORUS→Ω: prescribe the bounded domain before the regions.
    ∀ (Ω : Set Space) (hΩ : IsOpen Ω ∧ Bornology.IsBounded Ω ∧ Ω.Nonempty),
    ∀ (T : ℝ), 0 < T → ∀ (N : ℕ), 0 < N →
      ∀ (regionCenter : Fin N → Space) (regionRadius : Fin N → ℝ),
        (∀ j : Fin N, 0 < regionRadius j) →
        (∀ j : Fin N, closure (Metric.ball (regionCenter j) (regionRadius j)) ⊆
          Ω) →
        Pairwise (fun i j : Fin N ↦
          Disjoint (Metric.ball (regionCenter i) (regionRadius i))
            (Metric.ball (regionCenter j) (regionRadius j))) →
        Nonempty (MultipleRegionsOmegaAPI (ν := ν) u p f K M D T Ω hΩ regionCenter regionRadius)

end NSFormalization.Section3.T24
