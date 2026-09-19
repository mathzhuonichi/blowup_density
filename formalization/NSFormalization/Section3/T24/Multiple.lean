import NSFormalization.Section3.T15.Assembly

/-! Canonical raw-field interface for `03-torus.tex:668-740`, specifically
`prop:multiple` at lines 697-722. Only the packet-indexed spelling is changed.
The 30 fields are synchronized with research/T24/Spec.lean. -/
noncomputable section
namespace NSFormalization.Section3.T24
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NavierStokesR3.CompactEnergy (l2Sq dissipation)
open NSFormalization.Section3.T10 NSFormalization.Section3.T13 NSFormalization.Section3.T15
open NSFormalization.Section3.T14 (accumulatedForce)
open NSFormalization.Source.PacketScaling (zeroPastField)
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open scoped ContDiff ENNReal BigOperators Topology

/-- `03-torus.tex:710`: the finite superposition `u = ∑_j U_j`. -/
def finiteVelocitySum {N : ℕ} (U : Fin N → SpaceTimeField) : SpaceTimeField :=
  fun z ↦ ∑ j : Fin N, U j z

/-- `03-torus.tex:710`: the finite superposition `p = ∑_j P_j`. -/
def finitePressureSum {N : ℕ} (P : Fin N → SpaceTimeScalar) : SpaceTimeScalar :=
  fun z ↦ ∑ j : Fin N, P j z

/-- `03-torus.tex:710`: the finite superposition `f = ∑_j F_j`. -/
def finiteForceSum {N : ℕ} (F : Fin N → SpaceTimeField) : SpaceTimeField :=
  fun z ↦ ∑ j : Fin N, F j z

/-- `03-torus.tex:713-717`: unbounded speed in a fixed spatial ball `B` in every
left neighbourhood of the terminal time `T`, i.e. the pointwise reading of
`limsup_{t↑T} ‖u(t)‖_{L∞(B)} = ∞`. -/
def SpeedUnboundedAtOn (T : ℝ) (B : Set Space) (u : SpaceTimeField) : Prop :=
  ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
    ∃ t : ℝ, ∃ x : Space,
      t ∈ Ioo (0 : ℝ) T ∧ T - δ < t ∧ x ∈ B ∧ M < ‖u (t, x)‖

/-- Proposition `prop:multiple` (`paper/sections/03-torus.tex:697-722`) on the
torus: at fixed `ν>0`, `T>0`, and `N` prescribed disjoint interior balls, a
forced solution from rest whose velocity blows up separately in each ball, with
finite energy and dissipation.

`Type`-valued: the record carries the per-region T15 placement/scaling data and
the selected component solutions.  No new constant is introduced: `M, D` are the
imported packet's `energyBound`/`dissipationBound`.

The paper's bounded-domain / homogeneous-no-slip branch (`03-torus.tex:698,706,720`)
is deliberately omitted: the existing bounded-domain vocabulary (T22,
`Section3/T22/Domain.lean`, contract `T04.bounded_domain_norm`) and no-slip
material are not yet threaded into the reconciled T24b torus API, so an honest
omission is recorded here rather than a placeholder field — out of V1 scope. -/
structure MultipleRegionsAPI {ν : ℝ} (u : VelocityField) (p : PressureField) (f : VelocityField)
    (K : Set Space) (M D : ℝ) (T : ℝ)
    {N : ℕ} (regionCenter : Fin N → Space) (regionRadius : Fin N → ℝ) : Type where
  /-- `03-torus.tex:698`: `T>0`.  Non-vacuity: makes `(0,T)` a genuine
  evolution interval. -/
  T_pos : 0 < T
  /-- `03-torus.tex:697-700`: at least one region.  Non-vacuity: rules out the
  empty family, for which every clause below is vacuous. -/
  N_pos : 0 < N
  /-- `03-torus.tex:697-700`: each prescribed ball `B_j` has positive radius.
  Exact quantifier order: `∀ j`.  Non-vacuity: excludes empty balls. -/
  regionRadius_pos : ∀ j : Fin N, 0 < regionRadius j
  /-- `03-torus.tex:697-699`: each `B_j` is an interior ball,
  `closure B_j ⊆ interior Q` for the fundamental cube `Q`.
  Exact quantifier order: `∀ j`.  Non-vacuity: this concrete containment is the
  separation from other lattice translates used by the single-copy transfer. -/
  region_interior : ∀ j : Fin N,
    closure (Metric.ball (regionCenter j) (regionRadius j)) ⊆ interior fundamentalCube
  /-- `03-torus.tex:698-699`: the prescribed balls are pairwise disjoint.
  Non-vacuity: pairwise `Disjoint` of the explicit balls, the premise that kills
  every cross transport `(U_i·∇)U_j`. -/
  regions_disjoint : Pairwise (fun i j : Fin N ↦
    Disjoint (Metric.ball (regionCenter i) (regionRadius i))
      (Metric.ball (regionCenter j) (regionRadius j)))
  /-- `03-torus.tex:701-706`: one T15 placement record per region, over the one
  shared imported packet.
  Exact quantifier order: a function of `j`.  Non-vacuity: `PlacementData`
  concretely carries `x₀, B, K_*, ε₀` and every smallness condition. -/
  placement : Fin N → PlacementData u p f K
  /-- `03-torus.tex:721`: all placements share the common terminal time `T`.
  Exact quantifier order: `∀ j`.  Non-vacuity: equates each `(placement j).T`
  with the fixed `T`. -/
  placement_time : ∀ j : Fin N, (placement j).T = T
  /-- `03-torus.tex:701-705`: the T15 chart ball of region `j` is exactly the
  prescribed ball `B_j`.  This is the link without which none of T15's
  chart-ball conclusions attach to `B_j`.
  Exact quantifier order: `∀ j`.  Non-vacuity: pins both chart centre and
  radius to `regionCenter j` / `regionRadius j`. -/
  placement_chart : ∀ j : Fin N,
    (placement j).chartCenter = regionCenter j ∧
      (placement j).chartRadius = regionRadius j
  /-- `03-torus.tex:701-706`: one T15 scaling API per region, over the shared
  packet and that region's placement.
  Exact quantifier order: `∀ j`.  Non-vacuity: `ScalingAPI` concretely carries
  every rescaled-field identity for region `j`. -/
  scaling : ∀ j : Fin N, ScalingAPI (ν := ν) u p f K M D (placement j)
  /-- `03-torus.tex:701-704`: the chosen scale of region `j`. -/
  ε : Fin N → ℝ
  /-- `03-torus.tex:703-704`: each scale is admissible, `ε_j ∈ (0,ε₀]`.
  Exact quantifier order: `∀ j`.  Non-vacuity: membership in the concrete
  admissible interval (in particular `0 < ε_j`). -/
  eps_admissible : ∀ j : Fin N, ε j ∈ Ioc (0 : ℝ) (placement j).ε₀
  /-- `03-torus.tex:702`: `ε_j² < T`, the paper's displayed smallness clause.
  Exact quantifier order: `∀ j`.  Non-vacuity: a concrete inequality on each
  chosen scale. -/
  eps_time : ∀ j : Fin N, ε j ^ 2 < T
  /-- `03-torus.tex:706-712`: the selected component solution of region `j`,
  from rest, with the explicit periodized rescaled force of that region.
  Exact quantifier order: a function of `j`.  Non-vacuity: an actual
  `ClassicalSolutionT` witness, with all its regularity/PDE/gauge fields. -/
  component : ∀ j : Fin N,
    ClassicalSolutionT ν (0 : SpatialField)
      (periodizedScaledForce f (placement j).x₀ T (ε j)) T
  /-- `03-torus.tex:706-712`: each component is pinned to T15's explicit
  periodized velocity and mean-normalized pressure, not an arbitrary solution.
  Exact quantifier order: `∀ j`, then both field equations.
  Non-vacuity: two equalities of explicit fields, forbidding substitution. -/
  component_pin : ∀ j : Fin N,
    (component j).velocity = periodizedScaledVelocity u (placement j).x₀ T (ε j) ∧
      (component j).pressure = normalizedScaledPressure p (placement j).x₀ T (ε j)
  /-- `03-torus.tex:701-712`: on the fundamental cube the component velocity
  vanishes outside its region `B_j` (the single-copy support, measured on the
  cube because the periodized field is spatially periodic and its `ℝ³`-support
  meets every lattice translate).
  Exact quantifier order: `∀ j`, `∀ t ∈ Ico 0 T`, `∀ x ∈ fundamentalCube`,
  `x ∉ B_j`.  Non-vacuity: pins the velocity to `0` on `Q ∖ B_j`; delivered by
  T15's `velocity_singleCopy` and `eps_space`. -/
  component_support : ∀ j : Fin N, ∀ t ∈ Ico (0 : ℝ) T, ∀ x ∈ fundamentalCube,
    x ∉ Metric.ball (regionCenter j) (regionRadius j) →
      (component j).velocity (t, x) = 0
  /-- `03-torus.tex:701-712`: on the fundamental cube the region-`j` force
  vanishes outside `B_j`, at every real time.
  Exact quantifier order: `∀ j`, `∀ t`, `∀ x ∈ fundamentalCube`, `x ∉ B_j`.
  Non-vacuity: pins the periodized force to `0` on `Q ∖ B_j`; delivered by
  T15's `force_singleCopy` and `eps_space`. -/
  component_force_support : ∀ j : Fin N, ∀ t : ℝ, ∀ x ∈ fundamentalCube,
    x ∉ Metric.ball (regionCenter j) (regionRadius j) →
      periodizedScaledForce f (placement j).x₀ T (ε j) (t, x) = 0
  /-- `03-torus.tex:710`: the assembled velocity `u`. -/
  assembled_velocity : SpaceTimeField
  /-- `03-torus.tex:710`: `u = ∑_j U_j`.
  Non-vacuity: equates `assembled_velocity` with the explicit finite sum of the
  component velocities. -/
  assembled_velocity_formula :
    assembled_velocity = finiteVelocitySum (fun j ↦ (component j).velocity)
  /-- `03-torus.tex:710`: the assembled pressure `p`. -/
  assembled_pressure : SpaceTimeScalar
  /-- `03-torus.tex:710`: `p = ∑_j P_j`.
  Non-vacuity: equates `assembled_pressure` with the explicit finite sum. -/
  assembled_pressure_formula :
    assembled_pressure = finitePressureSum (fun j ↦ (component j).pressure)
  /-- `03-torus.tex:710`: the assembled force `f`. -/
  assembled_force : SpaceTimeField
  /-- `03-torus.tex:710`: `f = ∑_j F_j`.
  Non-vacuity: equates `assembled_force` with the explicit finite sum of the
  periodized rescaled forces. -/
  assembled_force_formula :
    assembled_force =
      finiteForceSum (fun j ↦ periodizedScaledForce f (placement j).x₀ T (ε j))
  /-- `03-torus.tex:711-716`: the assembled triple is itself a classical
  periodic solution from rest at the same `ν` and terminal time `T`.
  Non-vacuity: an actual `ClassicalSolutionT` witness for the summed force. -/
  solution : ClassicalSolutionT ν (0 : SpatialField) assembled_force T
  /-- `03-torus.tex:711-716`: the assembled solution's fields are the assembled
  velocity and pressure.
  Non-vacuity: two equalities pinning the solution to the explicit sums. -/
  solution_pin :
    solution.velocity = assembled_velocity ∧ solution.pressure = assembled_pressure
  /-- `03-torus.tex:711-716`: the assembled force is an admissible torus force.
  Non-vacuity: membership of the explicit sum in the concrete `forceClassT`. -/
  force_mem : assembled_force ∈ forceClassT
  /-- `03-torus.tex:711`: rest, `u(0,·) = 0`.
  Exact quantifier order: `∀ x`.  Non-vacuity: pins the assembled velocity at
  `t=0` to `0`. -/
  rest : ∀ x : Space, assembled_velocity (0, x) = 0
  /-- `03-torus.tex:712-717`: on each region `B_j` the sum agrees with its own
  component, so `B_j` inherits that component's singularity.
  Exact quantifier order: `∀ j`, `∀ t ∈ Ico 0 T`, `∀ x ∈ B_j`.
  Non-vacuity: equates the assembled velocity with `(component j).velocity` on
  `B_j`; follows from the disjoint single-copy supports. -/
  region_agreement : ∀ j : Fin N, ∀ t ∈ Ico (0 : ℝ) T,
    ∀ x ∈ Metric.ball (regionCenter j) (regionRadius j),
      assembled_velocity (t, x) = (component j).velocity (t, x)
  /-- `03-torus.tex:713-717,722`: the separate blow-up in each region,
  `limsup_{t↑T} ‖u(t)‖_{L∞(B_j)} = ∞`.
  Exact quantifier order: `∀ j`, then `SpeedUnboundedAtOn`'s `M,δ` and witnesses.
  Non-vacuity: the assembled velocity attains arbitrarily large values near `T`
  inside each `B_j`. -/
  region_blowup : ∀ j : Fin N,
    SpeedUnboundedAtOn T (Metric.ball (regionCenter j) (regionRadius j))
      assembled_velocity
  /-- `03-torus.tex:718`: the energy bound `sup_{t<T} ‖u(t)‖₂² ≤ M² Σ_j ε_j`,
  in the registered torus `E_T` spelling `(energyEssSupT T u)² ≤ …`, with
  `M = M`.
  Non-vacuity: an `ℝ≥0∞` inequality on the explicit essential-supremum energy,
  inherited from T15's `packetEnergyIdentity` by disjointness. -/
  energy_bound : (energyEssSupT T assembled_velocity) ^ (2 : ℕ) ≤
    ENNReal.ofReal (M ^ 2 * ∑ j : Fin N, ε j)
  /-- `03-torus.tex:719`: the dissipation identity
  `∫₀^T ‖∇u(t)‖₂² dt = D² Σ_j ε_j`, an equality (`=`, not `≤`), in the spelling
  `(energyGradientT T u)² = …` with `D = D`.
  Non-vacuity: an `ℝ≥0∞` equality on the explicit gradient energy, inherited
  from T15's `packetDissipationIdentity` by disjointness. -/
  dissipation_bound : (energyGradientT T assembled_velocity) ^ (2 : ℕ) =
    ENNReal.ofReal (D ^ 2 * ∑ j : Fin N, ε j)

/-- `03-torus.tex:697-722`: existence with all raw packet clauses. -/
def multipleRegionsStatement : Prop :=
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
    ∀ (T : ℝ), 0 < T → ∀ (N : ℕ), 0 < N →
      ∀ (regionCenter : Fin N → Space) (regionRadius : Fin N → ℝ),
        (∀ j : Fin N, 0 < regionRadius j) →
        (∀ j : Fin N, closure (Metric.ball (regionCenter j) (regionRadius j)) ⊆
          interior fundamentalCube) →
        Pairwise (fun i j : Fin N ↦
          Disjoint (Metric.ball (regionCenter i) (regionRadius i))
            (Metric.ball (regionCenter j) (regionRadius j))) →
        Nonempty (MultipleRegionsAPI (ν := ν) u p f K M D T regionCenter regionRadius)

end NSFormalization.Section3.T24
