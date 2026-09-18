import Contracts.V1.Packet
import Contracts.V1.PacketImport
import Contracts.V1.TorusData
import NSFormalization.Section3.T15.Scaling

/-!
# T15 canonical scaling structure-conformance probe

The two structures below are copied from `research/T15/Spec.lean:560-916`
with only the namespace changed.  The surrounding definitions use the same
formulas and resolve to the registered/canonical T10 and T13 vocabulary.

The fieldwise maps exercise the repository's structure exception in both
directions.  The only explicit `rfl` bridges needed inside the maps are the
four rescaling families (velocity, pressure, force, and normalized pressure);
their definitions accept a `PacketImportAPI` in the Spec spelling and a raw
field in the canonical spelling.
-/

noncomputable section

namespace BlowupDensity.T15.ScalingCanonicalProbe.Spec

open Set MeasureTheory Filter Topology
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
  (SpatialField SpaceTimeField SpaceTimeScalar forceTimeMeasure
    IsLebesgueSlicePath mixedLebesgueENorm criticalOrder)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open NSFormalization.Section3.T14
open NSFormalization.Section4.I02 (spatialGradient)
open NSFormalization.Source.PacketScaling (SpeedUnboundedAt)
open scoped ContDiff ENNReal BigOperators Topology

def scaledStartTime (T ε : ℝ) : ℝ := T - ε ^ 2

def scaledSourcePoint (x₀ : Space) (T ε : ℝ) (z : SpaceTime) : SpaceTime :=
  ((ε⁻¹) ^ 2 * (z.1 - scaledStartTime T ε), ε⁻¹ • (z.2 - x₀))

def scaledVelocity {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space) (T ε : ℝ) :
    SpaceTimeField :=
  fun z ↦ ε⁻¹ • zeroPastField P.velocity (scaledSourcePoint x₀ T ε z)

def scaledPressure {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space) (T ε : ℝ) :
    SpaceTimeScalar :=
  fun z ↦ (ε⁻¹) ^ 2 *
    zeroPastField P.pressure (scaledSourcePoint x₀ T ε z)

def scaledForce {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space) (T ε : ℝ) :
    SpaceTimeField :=
  fun z ↦ (ε⁻¹) ^ 3 • P.force (scaledSourcePoint x₀ T ε z)

def periodizedScaledVelocity {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space)
    (T ε : ℝ) : SpaceTimeField :=
  fun z ↦ periodize (fun x ↦ scaledVelocity P x₀ T ε (z.1, x)) z.2

def periodizedScaledPressure {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space)
    (T ε : ℝ) : SpaceTimeScalar :=
  fun z ↦ ∑' n : PeriodicFrequency,
    scaledPressure P x₀ T ε (z.1, z.2 - latticeVector n)

def periodizedScaledForce {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space)
    (T ε : ℝ) : SpaceTimeField :=
  fun z ↦ periodize (fun x ↦ scaledForce P x₀ T ε (z.1, x)) z.2

def normalizedScaledPressure {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space)
    (T ε : ℝ) : SpaceTimeScalar :=
  normalizePressureT (periodizedScaledPressure P x₀ T ε)

def IsPeriodicLebesgueSlicePath (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) (G : ℝ → Lp Space p periodicTorusMeasure) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    (G t : PeriodicTorus → Space) =ᵐ[periodicTorusMeasure]
      torusLift (fun x ↦ f (t, x))

def mixedLebesgueENormT (q p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) : ℝ≥0∞ :=
  ⨅ G : {G : ℝ → Lp Space p periodicTorusMeasure //
      IsPeriodicLebesgueSlicePath p f G ∧
        AEStronglyMeasurable G forceTimeMeasure},
    eLpNorm G.1 q forceTimeMeasure

def MemMixedLebesgueR (q p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) : Prop :=
  ∃ G : ℝ → Lp Space p (volume : Measure Space),
    IsLebesgueSlicePath p f G ∧ MemLp G q forceTimeMeasure

def MemMixedLebesgueT (q p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) : Prop :=
  ∃ G : ℝ → Lp Space p periodicTorusMeasure,
    IsPeriodicLebesgueSlicePath p f G ∧ MemLp G q forceTimeMeasure

def MemForceSobolevT (q : ℝ≥0∞) (s : ℝ) (f : SpaceTimeField) : Prop :=
  ∃ G : ℝ → PeriodicSobolev s,
    IsPeriodicSobolevPath s f G ∧ MemLp G q forceTimeMeasure

def EnergySlicesMemLpT (T : ℝ) (u : SpaceTimeField) : Prop :=
  (∀ t ∈ Ioo (0 : ℝ) T,
      MemLp (torusLift (fun x ↦ u (t, x))) 2 periodicTorusMeasure) ∧
    ∀ t ∈ Ioo (0 : ℝ) T,
      MemLp (torusLift (fun x ↦ spatialGradient u t x)) 2 periodicTorusMeasure

def alphaT (p q : ℝ≥0∞) : ℝ := -3 + 3 / p.toReal + 2 / q.toReal

structure PlacementData {ν : ℝ} (P : PacketAPI ν) where
  /-- `03-torus.tex:103-106`: the target singular time `T`.

  Non-vacuity: positivity makes `(0,T)` a genuine evolution interval. -/
  T : ℝ
  /-- `03-torus.tex:103-106`: `0<T`.

  Non-vacuity: this rules out the empty or reversed time interval. -/
  time_pos : 0 < T
  /-- `03-torus.tex:102-105`: center of the fixed localization ball `B`.

  Non-vacuity: it is used in the concrete ball containment below. -/
  chartCenter : Space
  /-- `03-torus.tex:102-105`: radius of the fixed localization ball `B`.

  Non-vacuity: the next field requires this radius to be positive. -/
  chartRadius : ℝ
  /-- `03-torus.tex:22-23,102`: `B` has positive radius.

  Non-vacuity: this excludes an empty metric ball. -/
  chartRadius_pos : 0 < chartRadius
  /-- `03-torus.tex:22-23,102-105`: the closure of `B` is contained in the
  coordinate chart, here the interior of the fixed fundamental cube.

  Non-vacuity: this is the separation from other lattice translates used by
  the single-copy clauses. -/
  chartBall_in_cube :
    closure (Metric.ball chartCenter chartRadius) ⊆ interior fundamentalCube
  /-- `03-torus.tex:102,105`: the placement center `x₀∈B`.

  Non-vacuity: the point is tied to the same concrete chart ball. -/
  x₀ : Space
  /-- `03-torus.tex:102`: `x₀∈B`.

  Non-vacuity: this is membership in the explicit ball above. -/
  x₀_mem : x₀ ∈ Metric.ball chartCenter chartRadius
  /-- `03-torus.tex:101-102`: the compact spatial set `K_*` enlarged to cover
  both the velocity/pressure carrier and the spatial projection of `supp F`.

  Non-vacuity: the following three fields constrain this actual set. -/
  Kstar : Set Space
  /-- `03-torus.tex:101`: `K_*` is compact.

  Non-vacuity: this is an assertion about the carried set, not an existential
  choice made separately for each scale. -/
  Kstar_compact : IsCompact Kstar
  /-- `03-torus.tex:101`: `K⊆K_*`, where `K` is T14's packet carrier.

  Exact quantifier order: every point of `P.carrier` lies in the fixed
  `Kstar`.  Non-vacuity: this links placement to the selected packet. -/
  carrier_subset : P.carrier ⊆ Kstar
  /-- `03-torus.tex:101-102`: the spatial projection of `supp F` is in `K_*`.

  Exact quantifier order: for every spacetime support point `(t,x)`, its
  spatial coordinate lies in `Kstar`.  Non-vacuity: this rules out choosing a
  set that only covers the velocity carrier. -/
  force_projection_subset : ∀ t : ℝ, ∀ x : Space,
    (t, x) ∈ tsupport P.force → x ∈ Kstar
  /-- `03-torus.tex:103`: one positive threshold for all sufficiently small
  scales.

  Non-vacuity: every conclusion below uses the same interval `(0,ε₀]`. -/
  ε₀ : ℝ
  /-- `03-torus.tex:103`: `ε₀>0`.

  Non-vacuity: `(0,ε₀]` contains admissible scales. -/
  eps_pos : 0 < ε₀
  /-- `03-torus.tex:103`, harmless normalization after shrinking: `ε₀≤1`.

  Non-vacuity: this is a quantitative restriction on the one threshold. -/
  eps_le_one : ε₀ ≤ 1
  /-- `03-torus.tex:104-106`: `2ε²<T`, before `t_ε` is defined.

  Exact quantifier order: first `ε∈(0,ε₀]`, then the inequality.
  Non-vacuity: it gives `t_ε>0`, so positive-time force norms contain the
  complete rescaled temporal support. -/
  eps_time : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < T
  /-- `03-torus.tex:104-105`: `x₀+εK_*⊆B`.

  Exact quantifier order: first `ε∈(0,ε₀]`, then every `y∈Kstar`.
  Non-vacuity: together with `chartBall_in_cube`, this is precisely the
  support-versus-scale condition used by the single-copy conclusions. -/
  eps_space : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ y ∈ Kstar,
    x₀ + ε • y ∈ Metric.ball chartCenter chartRadius

/-! ## Proposition 3.3 -/

/-- The reconciled statement of scaling at fixed viscosity,
`paper/sections/03-torus.tex:101-159`, for one energy-enhanced packet and the
shared placement data that T17 and T18 will consume.

The record is Type-valued because `sobolevConst` is selected as data before
every scale.  Every totalized lattice sum, Haar integral, and Bochner norm used
by an identity below has its corresponding explicit honesty guard. -/
structure ScalingAPI {ν : ℝ} (P : PacketImportAPI ν)
    (place : PlacementData P.toPacketAPI) where
  /-- `03-torus.tex:22-98,150-158`: the T13 localization witness used to
  transfer the whole-space packet estimates to the single torus copy.

  Exact quantifier order: this witness is structure data, fixed after `P` and
  `place` and before every scale.
  Non-vacuity: this is T13's concrete six-field API, whose localization and
  endpoint fields constrain explicit norms and periodization. -/
  localization : LocalizationAPI

  /-- `03-torus.tex:120`: at every admissible scale, presingular time, and
  spatial point, the velocity lattice family is summable.

  Exact quantifier order: `∀ ε ∈ (0,place.ε₀]`, `∀ t<T`, then `∀ x`.
  Non-vacuity: this guard prevents the totalized `tsum` in
  `periodizedScaledVelocity` from taking its nonsummable junk value. -/
  velocity_summable : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ∀ t : ℝ, t < place.T → ∀ x : Space,
      Summable (fun n : PeriodicFrequency ↦
        scaledVelocity P place.x₀ place.T ε (t, x - latticeVector n))

  /-- `03-torus.tex:120`: at every admissible scale, presingular time, and
  spatial point, the raw pressure lattice family is summable.

  Exact quantifier order matches `velocity_summable`.
  Non-vacuity: this guard makes the raw pressure `tsum`, and hence the mean
  later taken from it, an honest lattice sum. -/
  pressure_summable : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ∀ t : ℝ, t < place.T → ∀ x : Space,
      Summable (fun n : PeriodicFrequency ↦
        scaledPressure P place.x₀ place.T ε (t, x - latticeVector n))

  /-- `03-torus.tex:108-120`: at every admissible scale and every spacetime
  point, the globally defined force lattice family is summable.

  Exact quantifier order: `∀ ε ∈ (0,place.ε₀]`, `∀ t`, then `∀ x`.
  Non-vacuity: this guard prevents a nonsummable force family from being
  totalized to the junk value used by `tsum`. -/
  force_summable : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ∀ t : ℝ, ∀ x : Space,
      Summable (fun n : PeriodicFrequency ↦
        scaledForce P place.x₀ place.T ε (t, x - latticeVector n))

  /-- `03-torus.tex:120`: on the fixed fundamental cube, the velocity
  periodization is its single zero-lattice copy.

  Exact quantifier order: `ε`, admissibility, `t<T`, then `x∈Q`.
  Non-vacuity: this is equality of the explicit lattice sum and rescaling, with
  `velocity_summable` making the sum honest. -/
  velocity_singleCopy : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ∀ t : ℝ, t < place.T → ∀ x ∈ fundamentalCube,
      periodizedScaledVelocity P place.x₀ place.T ε (t, x) =
        scaledVelocity P place.x₀ place.T ε (t, x)

  /-- `03-torus.tex:120`: on the fixed fundamental cube, the raw pressure
  periodization is its single zero-lattice copy.

  Exact quantifier order matches `velocity_singleCopy`.
  Non-vacuity: this is a concrete equality before mean normalization, with
  `pressure_summable` validating the lattice sum. -/
  pressure_singleCopy : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ∀ t : ℝ, t < place.T → ∀ x ∈ fundamentalCube,
      periodizedScaledPressure P place.x₀ place.T ε (t, x) =
        scaledPressure P place.x₀ place.T ε (t, x)

  /-- `03-torus.tex:120`: on the fixed fundamental cube, the force
  periodization is its single zero-lattice copy at every real time.

  Exact quantifier order: `ε`, admissibility, `t`, then `x∈Q`.
  Non-vacuity: this is the concrete equality transferring the whole-space
  force norms to the torus, and `force_summable` makes its sum honest. -/
  force_singleCopy : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ∀ t : ℝ, ∀ x ∈ fundamentalCube,
      periodizedScaledForce P place.x₀ place.T ε (t, x) =
        scaledForce P place.x₀ place.T ε (t, x)

  /-- `03-torus.tex:108-123` and `02-preliminaries.tex:10,23-26`: each
  periodized rescaled force is smooth, unit-periodic, and compactly supported
  in positive time, i.e. it belongs to `F_T`.

  Exact quantifier order: `∀ ε ∈ (0,place.ε₀]`.
  Non-vacuity: `MemForceT` expands to concrete smoothness, periodicity, and a
  compact positive-time support witness for this explicit force. -/
  force_mem : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    MemForceT (periodizedScaledForce P place.x₀ place.T ε)

  /-- `03-torus.tex:122-123,141` and `02-preliminaries.tex:28-36,75-115`:
  at every admissible scale, the explicit periodized fields form a periodic
  classical solution at the unchanged viscosity `ν`, with zero initial datum
  and the mean-zero pressure representative.

  Exact quantifier order: `∀ ε ∈ (0,place.ε₀]`, then one
  `ClassicalSolutionT ν 0 F_ε place.T`, followed by both field-pinning
  equations.
  Non-vacuity: the two equations forbid substitution of unrelated solution
  fields; `ClassicalSolutionT` concretely includes regularity, divergence,
  momentum, Sobolev paths, pressure-gradient membership, periodicity, initial
  data, and the pressure gauge. -/
  solution : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ∃ S : ClassicalSolutionT ν (0 : SpatialField)
        (periodizedScaledForce P place.x₀ place.T ε) place.T,
      S.velocity = periodizedScaledVelocity P place.x₀ place.T ε ∧
        S.pressure = normalizedScaledPressure P place.x₀ place.T ε

  /-- `03-torus.tex:123` and `02-preliminaries.tex:28,84-88`: every raw
  periodized pressure slice on `[0,T)` is Haar-integrable.

  Exact quantifier order: `ε`, admissibility, then `t∈[0,T)`.
  Non-vacuity: this is the guard that makes the Bochner integral in
  `pressureMeanT`, hence the pressure normalization and gauge carried by
  `solution`, honest rather than the nonintegrable junk value. -/
  pressureSlice_integrable : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ∀ t ∈ Ico (0 : ℝ) place.T,
      Integrable
        (torusLift
          (fun x ↦ periodizedScaledPressure P place.x₀ place.T ε (t, x)))
        periodicTorusMeasure

  /-- `03-torus.tex:123,142-143`: the explicit periodized velocity has
  unbounded speed in every left neighborhood of `place.T`.

  Exact quantifier order: scale first, then `SpeedUnboundedAt`'s
  `M>0`, `δ>0`, and witnesses `t,x`.
  Non-vacuity: this constrains the actual periodized velocity and approaches
  the prescribed terminal time, rather than asserting unboundedness somewhere
  on an unrelated interval. -/
  unboundedSpeed : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    SpeedUnboundedAt place.T
      (periodizedScaledVelocity P place.x₀ place.T ε)

  /-- `03-torus.tex:125-128`: every velocity and full-gradient slice in the
  two packet-energy identities is an honest Haar-`L²(T³)` function.

  Exact quantifier order: `∀ ε ∈ (0,place.ε₀]`, with the slice-time
  quantifiers inside `EnergySlicesMemLpT`.
  Non-vacuity: this is the `MemLp` guard for both `energyEssSupT` and
  `energyGradientT`; it supplies the strong measurability/integrability that
  a finite-looking totalized expression alone would not provide. -/
  energySlices_memLp : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    EnergySlicesMemLpT place.T
      (periodizedScaledVelocity P place.x₀ place.T ε)

  /-- `03-torus.tex:125-126,145`, the first identity of
  `eq:packetEscale`: `‖U_ε‖_{L∞_tL²_x}=ε^{1/2}M`.

  Exact quantifier order: `∀ ε ∈ (0,place.ε₀]`.
  Non-vacuity: this is an equality in `ℝ≥0∞` with
  `M=P.energyBound`; `energySlices_memLp` is the guard making its spatial
  Bochner norms honest. -/
  packetEnergyIdentity : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    energyEssSupT place.T
        (periodizedScaledVelocity P place.x₀ place.T ε) =
      ENNReal.ofReal (ε ^ ((1 : ℝ) / 2) * P.energyBound)

  /-- `03-torus.tex:127-128,145-146`, the second identity of
  `eq:packetEscale`: `‖∇U_ε‖_{L²_tL²_x}=ε^{1/2}D`.

  Exact quantifier order: `∀ ε ∈ (0,place.ε₀]`.
  Non-vacuity: this independent equality uses `D=P.dissipationBound`;
  `energySlices_memLp` is the guard that makes every gradient slice honest. -/
  packetDissipationIdentity : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    energyGradientT place.T
        (periodizedScaledVelocity P place.x₀ place.T ε) =
      ENNReal.ofReal (ε ^ ((1 : ℝ) / 2) * P.dissipationBound)

  /-- `03-torus.tex:129-133,148-149`: both sides of every mixed-norm
  identity have honest Bochner `MemLp` representatives, including the
  essential-supremum endpoints.

  Exact quantifier order: `∀ p q`, the `Fact (1≤p)` instance, `1≤q`,
  the source witness, then every admissible scale's torus witness.
  Non-vacuity: this is the guard that prevents `packetMixedScaling` from
  degenerating to the totalized equality `⊤=⊤`. -/
  mixed_memLp : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    MemMixedLebesgueR q p P.force ∧
      ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
        MemMixedLebesgueT q p
          (periodizedScaledForce P place.x₀ place.T ε)

  /-- `03-torus.tex:129-133,148-149`, equation `eq:packetFscale`:
  `‖F_ε‖_{L^q_tL^p(T³)}=ε^{α(p,q)}‖F‖_{L^q_tL^p(R³)}` for every
  `1≤p,q≤∞`, with `α=-3+3/p+2/q`.

  Exact quantifier order: `∀ p q`, `Fact (1≤p)`, `1≤q`, then
  `∀ ε ∈ (0,place.ε₀]`.
  Non-vacuity: `mixed_memLp` supplies the honest Bochner paths on both sides;
  the right side is the unrescaled source force's registered whole-space norm. -/
  packetMixedScaling : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      mixedLebesgueENormT q p
          (periodizedScaledForce P place.x₀ place.T ε) =
        ENNReal.ofReal (ε ^ alphaT p q) * mixedLebesgueENorm q p P.force

  /-- `03-torus.tex:133-136`: the family `s↦C_s`, selected as data before
  every scale.

  Exact quantifier order: the whole function is a structure field before the
  later `s` and `ε` quantifiers.
  Non-vacuity: `sobolevConst_pos` and `packetSobolevBound` constrain this
  concrete family on all of `[0,1]`. -/
  sobolevConst : ℝ → ℝ

  /-- `03-torus.tex:133-136`: `C_s>0` at every `0≤s≤1`.

  Exact quantifier order: `∀ s`, then its lower and upper range proofs.
  Non-vacuity: strict positivity excludes a junk negative constant whose
  `ENNReal.ofReal` image would collapse the displayed upper bound. -/
  sobolevConst_pos : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → 0 < sobolevConst s

  /-- `03-torus.tex:133-138,150-158`: each rescaled force has an honest
  `L¹(0,∞;H^s(T³))` Fourier-data path for `0≤s≤1`.

  Exact quantifier order: `∀ s`, its two range proofs, then
  `∀ ε ∈ (0,place.ε₀]`.
  Non-vacuity: this is the guard that makes the Bochner infimum in
  `forceSobolevENormT` honest; its path uses registered `IsPeriodicDatum`,
  including the Haar-integrability conjunct. -/
  forceSobolev_memLp : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      MemForceSobolevT 1 s
        (periodizedScaledForce P place.x₀ place.T ε)

  /-- `03-torus.tex:133-137,150-158`, equation `eq:packetHs`:
  `‖F_ε‖_{L¹_tH^s(T³)}≤C_s(ε^{1/2}+ε^{1/2-s})` for `0≤s≤1`.

  Exact quantifier order: `∀ s`, both range proofs, then every admissible
  `ε`, so the carried `C_s` is uniform in scale.
  Non-vacuity: `forceSobolev_memLp` is the guard making the Bochner integral
  honest, and `sobolevConst_pos` makes the finite real upper bound meaningful. -/
  packetSobolevBound : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      forceSobolevENormT 1 s
          (periodizedScaledForce P place.x₀ place.T ε) ≤
        ENNReal.ofReal (sobolevConst s *
          (ε ^ ((1 : ℝ) / 2) + ε ^ ((1 : ℝ) / 2 - s)))

  /-- `03-torus.tex:129-138,148-158`: the promoted subcritical convergence
  conclusion, in the lane-required registered threshold shape:
  for `q∈{1,2}` and `s<criticalOrder(q)=2/q-3/2`, the force norm tends to
  zero as `ε↓0`.  At `q=1` this is exactly the proposition's “in
  particular” clause `03-torus.tex:138`, including every negative `s`.

  Exact quantifier order: `q : ℝ≥0∞`, its disjunction, `s`, the strict
  threshold, then the right-neighborhood limit.
  Non-vacuity: the limit concerns the same explicit force family; convergence
  to finite zero in `ℝ≥0∞` rules out an eventually-`⊤` totalized norm, while
  `forceSobolev_memLp` gives the direct Bochner guard on the displayed
  `q=1`, `0≤s≤1` range. -/
  forceConvergence : ∀ (q : ℝ≥0∞), (q = 1 ∨ q = 2) → ∀ s : ℝ,
    s < criticalOrder q.toReal →
      Tendsto
        (fun ε : ℝ ↦ forceSobolevENormT q s
          (periodizedScaledForce P place.x₀ place.T ε))
        (𝓝[>] 0) (𝓝 0)

end BlowupDensity.T15.ScalingCanonicalProbe.Spec

namespace BlowupDensity.T15.ScalingCanonicalProbe

open Set MeasureTheory
open BlowupDensity.Contracts.V1
open scoped ENNReal

/-! ## Definitional bridges to the canonical rescaling vocabulary -/

theorem scaledStartTime_eq (T ε : ℝ) :
    BlowupDensity.T15.ScalingCanonicalProbe.Spec.scaledStartTime T ε = NSFormalization.Section3.T15.scaledStartTime T ε := rfl

theorem scaledSourcePoint_eq (x₀ : Space) (T ε : ℝ) (z : SpaceTime) :
    BlowupDensity.T15.ScalingCanonicalProbe.Spec.scaledSourcePoint x₀ T ε z = NSFormalization.Section3.T15.scaledSourcePoint x₀ T ε z := rfl

theorem scaledVelocity_eq {ν : ℝ} (P : PacketImportAPI ν)
    (x₀ : Space) (T ε : ℝ) :
    BlowupDensity.T15.ScalingCanonicalProbe.Spec.scaledVelocity P x₀ T ε = NSFormalization.Section3.T15.scaledVelocity P.velocity x₀ T ε := rfl

theorem scaledPressure_eq {ν : ℝ} (P : PacketImportAPI ν)
    (x₀ : Space) (T ε : ℝ) :
    BlowupDensity.T15.ScalingCanonicalProbe.Spec.scaledPressure P x₀ T ε = NSFormalization.Section3.T15.scaledPressure P.pressure x₀ T ε := rfl

theorem scaledForce_eq {ν : ℝ} (P : PacketImportAPI ν)
    (x₀ : Space) (T ε : ℝ) :
    BlowupDensity.T15.ScalingCanonicalProbe.Spec.scaledForce P x₀ T ε = NSFormalization.Section3.T15.scaledForce P.force x₀ T ε := rfl

theorem periodizedScaledVelocity_eq {ν : ℝ} (P : PacketImportAPI ν)
    (x₀ : Space) (T ε : ℝ) :
    BlowupDensity.T15.ScalingCanonicalProbe.Spec.periodizedScaledVelocity P x₀ T ε =
      NSFormalization.Section3.T15.periodizedScaledVelocity P.velocity x₀ T ε := rfl

theorem periodizedScaledPressure_eq {ν : ℝ} (P : PacketImportAPI ν)
    (x₀ : Space) (T ε : ℝ) :
    BlowupDensity.T15.ScalingCanonicalProbe.Spec.periodizedScaledPressure P x₀ T ε =
      NSFormalization.Section3.T15.periodizedScaledPressure P.pressure x₀ T ε := rfl

theorem periodizedScaledForce_eq {ν : ℝ} (P : PacketImportAPI ν)
    (x₀ : Space) (T ε : ℝ) :
    BlowupDensity.T15.ScalingCanonicalProbe.Spec.periodizedScaledForce P x₀ T ε =
      NSFormalization.Section3.T15.periodizedScaledForce P.force x₀ T ε := rfl

theorem normalizedScaledPressure_eq {ν : ℝ} (P : PacketImportAPI ν)
    (x₀ : Space) (T ε : ℝ) :
    BlowupDensity.T15.ScalingCanonicalProbe.Spec.normalizedScaledPressure P x₀ T ε =
      NSFormalization.Section3.T15.normalizedScaledPressure P.pressure x₀ T ε := rfl

theorem alphaT_eq (p q : ℝ≥0∞) :
    BlowupDensity.T15.ScalingCanonicalProbe.Spec.alphaT p q =
      NSFormalization.Section3.T15.alphaT p q := rfl

/-! ## `PlacementData` structure exception -/

/-- Spec placement to the raw canonical placement. -/
def placementOfSpec {ν : ℝ} {P : PacketAPI ν} (place : BlowupDensity.T15.ScalingCanonicalProbe.Spec.PlacementData P) :
    NSFormalization.Section3.T15.PlacementData P.velocity P.pressure P.force P.carrier :=
  { T := place.T
    time_pos := place.time_pos
    chartCenter := place.chartCenter
    chartRadius := place.chartRadius
    chartRadius_pos := place.chartRadius_pos
    chartBall_in_cube := place.chartBall_in_cube
    x₀ := place.x₀
    x₀_mem := place.x₀_mem
    Kstar := place.Kstar
    Kstar_compact := place.Kstar_compact
    carrier_subset := place.carrier_subset
    force_projection_subset := place.force_projection_subset
    ε₀ := place.ε₀
    eps_pos := place.eps_pos
    eps_le_one := place.eps_le_one
    eps_time := place.eps_time
    eps_space := place.eps_space }

/-- Raw canonical placement to the Spec placement for an assembled packet. -/
def placementToSpec {ν : ℝ} {P : PacketAPI ν}
    (place : NSFormalization.Section3.T15.PlacementData P.velocity P.pressure P.force P.carrier) :
    BlowupDensity.T15.ScalingCanonicalProbe.Spec.PlacementData P :=
  { T := place.T
    time_pos := place.time_pos
    chartCenter := place.chartCenter
    chartRadius := place.chartRadius
    chartRadius_pos := place.chartRadius_pos
    chartBall_in_cube := place.chartBall_in_cube
    x₀ := place.x₀
    x₀_mem := place.x₀_mem
    Kstar := place.Kstar
    Kstar_compact := place.Kstar_compact
    carrier_subset := place.carrier_subset
    force_projection_subset := place.force_projection_subset
    ε₀ := place.ε₀
    eps_pos := place.eps_pos
    eps_le_one := place.eps_le_one
    eps_time := place.eps_time
    eps_space := place.eps_space }

theorem placementToSpec_ofSpec {ν : ℝ} {P : PacketAPI ν}
    (place : BlowupDensity.T15.ScalingCanonicalProbe.Spec.PlacementData P) : placementToSpec (placementOfSpec place) = place := rfl

theorem placementOfSpec_toSpec {ν : ℝ} {P : PacketAPI ν}
    (place : NSFormalization.Section3.T15.PlacementData P.velocity P.pressure P.force P.carrier) :
    placementOfSpec (placementToSpec place) = place := rfl

/-! ## All 21 `ScalingAPI` fields, Spec to canonical -/

def ofSpec {ν : ℝ} {P : PacketImportAPI ν}
    {place : BlowupDensity.T15.ScalingCanonicalProbe.Spec.PlacementData P.toPacketAPI} (h : BlowupDensity.T15.ScalingCanonicalProbe.Spec.ScalingAPI P place) :
    NSFormalization.Section3.T15.ScalingAPI (ν := ν) P.velocity P.pressure P.force P.carrier
      P.energyBound P.dissipationBound (placementOfSpec place) :=
  { localization := h.localization
    velocity_summable := h.velocity_summable
    pressure_summable := h.pressure_summable
    force_summable := h.force_summable
    velocity_singleCopy := h.velocity_singleCopy
    pressure_singleCopy := h.pressure_singleCopy
    force_singleCopy := h.force_singleCopy
    force_mem := h.force_mem
    solution := h.solution
    pressureSlice_integrable := h.pressureSlice_integrable
    unboundedSpeed := h.unboundedSpeed
    energySlices_memLp := h.energySlices_memLp
    packetEnergyIdentity := h.packetEnergyIdentity
    packetDissipationIdentity := h.packetDissipationIdentity
    mixed_memLp := h.mixed_memLp
    packetMixedScaling := h.packetMixedScaling
    sobolevConst := h.sobolevConst
    sobolevConst_pos := h.sobolevConst_pos
    forceSobolev_memLp := h.forceSobolev_memLp
    packetSobolevBound := h.packetSobolevBound
    forceConvergence := h.forceConvergence }

/-! ## All 21 fields, canonical to Spec after assembling raw hypotheses -/

/-- Once the raw packet hypotheses have been assembled into `P`, a canonical
raw-field API transports back to the Spec API field by field. -/
def toSpec {ν : ℝ} {P : PacketImportAPI ν}
    {place : NSFormalization.Section3.T15.PlacementData P.velocity P.pressure P.force P.carrier}
    (h : NSFormalization.Section3.T15.ScalingAPI (ν := ν) P.velocity P.pressure P.force P.carrier
      P.energyBound P.dissipationBound place) :
    BlowupDensity.T15.ScalingCanonicalProbe.Spec.ScalingAPI P (placementToSpec place) :=
  { localization := h.localization
    velocity_summable := h.velocity_summable
    pressure_summable := h.pressure_summable
    force_summable := h.force_summable
    velocity_singleCopy := h.velocity_singleCopy
    pressure_singleCopy := h.pressure_singleCopy
    force_singleCopy := h.force_singleCopy
    force_mem := h.force_mem
    solution := h.solution
    pressureSlice_integrable := h.pressureSlice_integrable
    unboundedSpeed := h.unboundedSpeed
    energySlices_memLp := h.energySlices_memLp
    packetEnergyIdentity := h.packetEnergyIdentity
    packetDissipationIdentity := h.packetDissipationIdentity
    mixed_memLp := h.mixed_memLp
    packetMixedScaling := h.packetMixedScaling
    sobolevConst := h.sobolevConst
    sobolevConst_pos := h.sobolevConst_pos
    forceSobolev_memLp := h.forceSobolev_memLp
    packetSobolevBound := h.packetSobolevBound
    forceConvergence := h.forceConvergence }

theorem toSpec_ofSpec {ν : ℝ} {P : PacketImportAPI ν}
    {place : BlowupDensity.T15.ScalingCanonicalProbe.Spec.PlacementData P.toPacketAPI}
    (h : BlowupDensity.T15.ScalingCanonicalProbe.Spec.ScalingAPI P place) :
    toSpec (ofSpec h) = h := by
  cases h
  rfl

theorem ofSpec_toSpec {ν : ℝ} {P : PacketImportAPI ν}
    {place : NSFormalization.Section3.T15.PlacementData
      P.velocity P.pressure P.force P.carrier}
    (h : NSFormalization.Section3.T15.ScalingAPI (ν := ν)
      P.velocity P.pressure P.force P.carrier
      P.energyBound P.dissipationBound place) :
    ofSpec (toSpec h) = h := by
  cases h
  rfl

end BlowupDensity.T15.ScalingCanonicalProbe
