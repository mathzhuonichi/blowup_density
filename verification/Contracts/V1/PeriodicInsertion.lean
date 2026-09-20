import Contracts.V1.Correction3
import Contracts.V1.PacketImport
import Contracts.V1.Localization
import Contracts.V1.TorusLocalTheory
import Contracts.V1.MaximalPartial
import Contracts.V1.Scaling

/-! T18 U12. The T15 ScalingAPI below is verbatim from research/T18/Spec.lean.
It is a threaded hypothesis pending T15 U15. Placement and correction use the
registered Correction3 packet interface through compatibility exports.
T13, T14 and T16 vocabulary resolves to registered contracts through compatibility aliases.
The 45-field T18 record and existence statement retain the reconciled Spec text. -/
noncomputable section
open BlowupDensity.Contracts.V1.TorusLocalTheory
namespace BlowupDensity.T10.Draft
end BlowupDensity.T10.Draft
namespace BlowupDensity.T13.Spec
export BlowupDensity.Contracts.V1 (fundamentalCube SupportedInBall latticeVector periodize fractionalRadialKernel cFrac periodicKernel IReal ITorus gradientENorm LocalizationAPI)
end BlowupDensity.T13.Spec
namespace BlowupDensity.T14.Draft
export BlowupDensity.Contracts.V1 (PacketImportAPI)
end BlowupDensity.T14.Draft
namespace BlowupDensity.T16.Draft
export BlowupDensity.Contracts.V1 (latticeVector periodicSet periodicScaledPacket correctedBackground CutoffData LocalPotentialAPI)
end BlowupDensity.T16.Draft
namespace BlowupDensity.T15.Draft

open Set MeasureTheory Filter Topology
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.T10.Draft
open BlowupDensity.T13.Spec
open BlowupDensity.T14.Draft
open scoped ContDiff ENNReal BigOperators Topology

/-! ## Definitional drift checks -/

/-- `Contracts/V1/Data.lean:743-744`: the registered inhomogeneous
abbreviation is definitionally `CompletedDenseVia` with `IsSobolevPath`. -/
example (q : ℝ≥0∞) (s : ℝ) (S : Set SpaceTimeField) :
    CompletedDense q s S = CompletedDenseVia q s (IsSobolevPath s) S := rfl

/-- `Contracts/V1/Data.lean:752-753`: the registered homogeneous
abbreviation is definitionally `CompletedDenseVia` with
`IsHomogeneousPath`. -/
example (q : ℝ≥0∞) (s : ℝ) (S : Set SpaceTimeField) :
    CompletedDenseHomogeneous q s S =
      CompletedDenseVia q s (IsHomogeneousPath s) S := rfl

/-! ## Explicit scaling and lattice periodization -/

/-- `03-torus.tex:106`: the shifted packet start time `t_ε=T-ε²`. -/
def scaledStartTime (T ε : ℝ) : ℝ := T - ε ^ 2

/-- `03-torus.tex:112-118`: the time-first source point
`((t-t_ε)/ε²,(x-x₀)/ε)`, written with the same inverse-scale tokens as
`Contracts.V1.dilateField`. -/
def scaledSourcePoint (x₀ : Space) (T ε : ℝ) (z : SpaceTime) : SpaceTime :=
  ((ε⁻¹) ^ 2 * (z.1 - scaledStartTime T ε), ε⁻¹ • (z.2 - x₀))

/-- `03-torus.tex:108-114`: the velocity formula of `eq:scaling`, using
the packet's smooth negative-time zero extension. -/
def scaledVelocity {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space) (T ε : ℝ) :
    SpaceTimeField :=
  fun z ↦ ε⁻¹ • zeroPastField P.velocity (scaledSourcePoint x₀ T ε z)

/-- `03-torus.tex:108-116`: the pressure formula of `eq:scaling`, using
the packet's smooth negative-time zero extension. -/
def scaledPressure {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space) (T ε : ℝ) :
    SpaceTimeScalar :=
  fun z ↦ (ε⁻¹) ^ 2 *
    zeroPastField P.pressure (scaledSourcePoint x₀ T ε z)

/-- `03-torus.tex:108-109,117-118`: the force formula of `eq:scaling`;
the packet force is already its globally smooth zero extension. -/
def scaledForce {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space) (T ε : ℝ) :
    SpaceTimeField :=
  fun z ↦ (ε⁻¹) ^ 3 • P.force (scaledSourcePoint x₀ T ε z)

/-- The local velocity rescaling is definitionally the registered
`I03.scaling` rescaling, `03-torus.tex:112-114`. -/
example {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space) (T ε : ℝ) :
    scaledVelocity P x₀ T ε =
      BlowupDensity.Contracts.V1.scaledPacket P.velocity x₀ T ε := rfl

/-- The local pressure rescaling is definitionally the registered
`I03.scaling` rescaling, `03-torus.tex:115-116`. -/
example {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space) (T ε : ℝ) :
    scaledPressure P x₀ T ε =
      BlowupDensity.Contracts.V1.scaledPressure P.pressure x₀ T ε := rfl

/-- The local force rescaling is definitionally the registered
`I03.scaling` rescaling, `03-torus.tex:117-118`. -/
example {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space) (T ε : ℝ) :
    scaledForce P x₀ T ε =
      BlowupDensity.Contracts.V1.scaledForce P.force x₀ T ε := rfl

/-- `03-torus.tex:120`: the spatial lattice sum of the scaled velocity. -/
def periodizedScaledVelocity {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space)
    (T ε : ℝ) : SpaceTimeField :=
  fun z ↦ periodize (fun x ↦ scaledVelocity P x₀ T ε (z.1, x)) z.2

/-- `03-torus.tex:120`: the spatial lattice sum of the raw scaled pressure. -/
def periodizedScaledPressure {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space)
    (T ε : ℝ) : SpaceTimeScalar :=
  fun z ↦ ∑' n : PeriodicFrequency,
    scaledPressure P x₀ T ε (z.1, z.2 - latticeVector n)

/-- `03-torus.tex:120`: the spatial lattice sum of the scaled force. -/
def periodizedScaledForce {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space)
    (T ε : ℝ) : SpaceTimeField :=
  fun z ↦ periodize (fun x ↦ scaledForce P x₀ T ε (z.1, x)) z.2

/-- `03-torus.tex:123`: subtract the normalized Haar mean from every raw
pressure slice.  The subtracted value is spatially constant by definition. -/
def normalizedScaledPressure {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space)
    (T ε : ℝ) : SpaceTimeScalar :=
  normalizePressureT (periodizedScaledPressure P x₀ T ε)

/-- The pressure-adjustment formula dropped as a structure field is
definitionally true, `03-torus.tex:123`. -/
example {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space) (T ε t : ℝ) (x : Space) :
    normalizedScaledPressure P x₀ T ε (t, x) =
      periodizedScaledPressure P x₀ T ε (t, x) -
        pressureMeanT (periodizedScaledPressure P x₀ T ε) t := rfl

/-! ## Honest mixed, Sobolev, and energy carriers -/

/-- `03-torus.tex:129-133`: `G(t)` is the normalized-Haar `L^p(T³)`
slice of the periodic physical field. -/
def IsPeriodicLebesgueSlicePath (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) (G : ℝ → Lp Space p periodicTorusMeasure) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    (G t : PeriodicTorus → Space) =ᵐ[periodicTorusMeasure]
      torusLift (fun x ↦ f (t, x))

/-- `03-torus.tex:129-133`: the torus
`L^q(0,∞;L^p(T³))` extended norm. -/
def mixedLebesgueENormT (q p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) : ℝ≥0∞ :=
  ⨅ G : {G : ℝ → Lp Space p periodicTorusMeasure //
      IsPeriodicLebesgueSlicePath p f G ∧
        AEStronglyMeasurable G forceTimeMeasure},
    eLpNorm G.1 q forceTimeMeasure

/-- `03-torus.tex:129-133`: an honest whole-space mixed Bochner path;
`MemLp` supplies both strong measurability and finiteness. -/
def MemMixedLebesgueR (q p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) : Prop :=
  ∃ G : ℝ → Lp Space p (volume : Measure Space),
    IsLebesgueSlicePath p f G ∧ MemLp G q forceTimeMeasure

/-- `03-torus.tex:129-133`: an honest torus mixed Bochner path; this guard
prevents the mixed identity from degenerating to `⊤=⊤`. -/
def MemMixedLebesgueT (q p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) : Prop :=
  ∃ G : ℝ → Lp Space p periodicTorusMeasure,
    IsPeriodicLebesgueSlicePath p f G ∧ MemLp G q forceTimeMeasure

/-- `03-torus.tex:133-138`: an honest periodic Sobolev Bochner path; the
registered `IsPeriodicDatum` includes Haar integrability. -/
def MemForceSobolevT (q : ℝ≥0∞) (s : ℝ) (f : SpaceTimeField) : Prop :=
  ∃ G : ℝ → PeriodicSobolev s,
    IsPeriodicSobolevPath s f G ∧ MemLp G q forceTimeMeasure

/-- `03-torus.tex:125-128`: honest Haar-`L²` velocity and full-gradient
slices for both packet-energy identities. -/
def EnergySlicesMemLpT (T : ℝ) (u : SpaceTimeField) : Prop :=
  (∀ t ∈ Ioo (0 : ℝ) T,
      MemLp (torusLift (fun x ↦ u (t, x))) 2 periodicTorusMeasure) ∧
    ∀ t ∈ Ioo (0 : ℝ) T,
      MemLp (torusLift (fun x ↦ spatialGradient u t x)) 2 periodicTorusMeasure

/-- `03-torus.tex:130-131`: `α(p,q)=-3+3/p+2/q`, with
`ENNReal.toReal ⊤=0`. -/
def alphaT (p q : ℝ≥0∞) : ℝ := -3 + 3 / p.toReal + 2 / q.toReal

/-- The torus exponent is definitionally the registered `I03.scaling`
exponent, `03-torus.tex:130-131`. -/
example (p q : ℝ≥0∞) :
    alphaT p q = BlowupDensity.Contracts.V1.alpha p q := rfl

/-! ## Placement data fixed before every scale -/

/- The choices and smallness conditions made at `03-torus.tex:101-107`.
`Kstar` contains both spatial packet supports.  Its scaled translate lies in a
fixed coordinate ball whose closure is inside the fundamental cube; this is
the hypothesis that makes the lattice sum a single copy on that cube. -/
export BlowupDensity.Contracts.V1.Correction3.Packet (PlacementData)

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

/-! ## Existential form -/

end BlowupDensity.T15.Draft
namespace BlowupDensity.T15.Spec
export BlowupDensity.T15.Draft (IsPeriodicLebesgueSlicePath mixedLebesgueENormT
  MemForceSobolevT alphaT PlacementData)
end BlowupDensity.T15.Spec
namespace BlowupDensity.T17.Spec
-- The registered packet-indexed T17 vocabulary, in the Spec's historical namespace.
export BlowupDensity.Contracts.V1.Correction3.Packet
  (PlacementData fixedProfileCylinder correctionChartPoint rescaledReference
   rescaledPotential rescaledCorrectionProfile rescaledForceProfile correctionForce
   torusSpaceTimeLift torusSpatialSupport torusTemporalSupport CorrectionAPI)
end BlowupDensity.T17.Spec
namespace BlowupDensity.T18.Spec

open Set MeasureTheory Filter Topology
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.TorusLocalTheory
open BlowupDensity.T14.Draft
open BlowupDensity.T15.Draft
open BlowupDensity.T16.Draft
open BlowupDensity.T17.Spec
open scoped ContDiff ENNReal BigOperators Topology

/-- Drift check `03-torus.tex:130-131`: the copied `T15.Draft` exponent is
definitionally the registered `Contracts.V1.alpha` the statement is written in;
`check rfl`. -/
example (p q : ℝ≥0∞) :
    BlowupDensity.T15.Draft.alphaT p q = BlowupDensity.Contracts.V1.alpha p q := rfl

/-- Drift check `03-torus.tex:129-133`: the `MemMixedLebesgueT`-guarded
`mixedLebesgueENormT` (from `T15.Draft`) is definitionally the `T15.Spec` mixed
norm the copied `CorrectionAPI` block is written in; `check rfl`. -/
example (q p : ℝ≥0∞) [Fact (1 ≤ p)] (f : SpaceTimeField) :
    BlowupDensity.T15.Draft.mixedLebesgueENormT q p f
      = BlowupDensity.T15.Spec.mixedLebesgueENormT q p f := rfl

/-- **Theorem `thm:insertion` (exact local insertion on `T³`),
`paper/sections/03-torus.tex:287-311`, proof `:312-346`, for one `ε`-family.**

Parameters (the objects the proof is *given*, none of them an inhabited
registered contract, `:287-289,312-314`): the viscosity `ν`; the fixed
energy-enhanced whole-space packet `P` (`prop:scaling` rescales it, and `M,D`
are its `energyBound`/`dissipationBound`); the placement `place` of
`lem:localization`/`prop:scaling`; the torus scaling record `scaling`
(`prop:scaling`, threaded because the torus T15 chain is not yet a registered
contract — it delivers the periodized packet and its energy/mixed/Sobolev
scaling identities); the initial velocity `a` and reference force `g`; the
coordinate-ball radius `r` and regularity margin `δ`; the cutoff data `D` of
`lem:potential`; the reference solution `reference` regular through `place.T+δ`;
and the `lem:correction` record `correction` (`w_ε`, `H_ε`, and every bound of
`eq:wE`, `eq:Hmixed`, `eq:HHs`).  T11 local theory / continuation and the T12
calculus are **not** threaded: the lifespan argument consumes the registered,
inhabited `torusLocalTheoryAPI` / `torusContinuationH3API`, and `H²↪L∞` is a
Mathlib fact.  This mirrors R42's `InsertionFamilyAPI (ν) (P)`
(`Contracts/V1/InsertionFamily.lean`) whose one `scaling` field bundles the
ambient data; here that bundle is split across `place`, `scaling` and
`correction`.

Fields are the clauses of the theorem plus the paper hypotheses not forced by
the parameter types; every scale-dependent field is guarded by `ε ∈ Ioc 0 ε₀`,
and every totalized Bochner norm carries the integrability/class guard
(`MemMixedLebesgueT` / `MemForceSobolevT`) that makes it honest.  Differences
from the `R42`/`R42.v2` template are marked `TORUS:` and tabulated in
`research/T18/COMPARISON.md`. -/
structure PeriodicInsertionAPI (ν : ℝ) (P : PacketImportAPI ν)
    (place : BlowupDensity.T15.Draft.PlacementData P.toPacketAPI)
    (scaling : ScalingAPI P place)
    (a : SpatialField) (g : SpaceTimeField) (r δ : ℝ)
    (D : BlowupDensity.T16.Draft.CutoffData)
    (reference : ClassicalSolutionT ν a g (place.T + δ))
    (correction :
      BlowupDensity.T17.Spec.CorrectionAPI ν place reference.velocity r δ D) :
    Type where
  -- ### Paper hypotheses not already forced by the parameter types
  /-- `03-torus.tex:288`: `δ > 0`, so the reference is regular strictly past `T`.
  Quantifier order: none.  Non-vacuity: a strict inequality on the real margin
  used in `reference`'s horizon `place.T + δ`. -/
  delta_pos : 0 < δ
  /-- `03-torus.tex:289`: `g ∈ 𝓕`, the reference force is a torus force.
  Quantifier order: none.  Non-vacuity: `forceClassT` membership is the smooth
  compact-in-`(0,∞)` class, not a trivial set. -/
  reference_force_mem : g ∈ forceClassT
  /-- `03-torus.tex:289`: `v(0)=a ∈ 𝓧`, the initial velocity is a smooth
  divergence-free torus field.  Quantifier order: none.  Non-vacuity:
  `initialClassT` fixes smoothness, periodicity and solenoidality. -/
  initial_mem : a ∈ initialClassT

  -- ### The single scale threshold `03-torus.tex:290` "For all sufficiently small ε>0"
  /-- `03-torus.tex:290`: the family threshold `ε₀`.
  Non-vacuity: real data used by every clause below through `Ioc 0 ε₀`. -/
  ε₀ : ℝ
  /-- `03-torus.tex:290`: `ε₀ > 0`.  Non-vacuity: `(0,ε₀]` is nonempty. -/
  eps_pos : 0 < ε₀
  /-- `03-torus.tex:290,103`: the inserted family shrinks the scaling threshold,
  so every `prop:scaling` bound (quantified over `Ioc 0 place.ε₀`) holds on
  `(0,ε₀]`.  Quantifier order: none.  Non-vacuity: a genuine `≤` between the two
  thresholds. -/
  eps_le_scaling : ε₀ ≤ place.ε₀
  /-- `03-torus.tex:290,312`: the inserted family is also a sub-family of the
  correction family, so every `lem:correction` bound holds on `(0,ε₀]`.
  Quantifier order: none.  Non-vacuity: a genuine `≤` between the two
  thresholds. -/
  eps_le_cutoff : ε₀ ≤ D.ε₀

  -- ### The inserted triple and the three displays `eq:insertion` `03-torus.tex:314`
  /-- `03-torus.tex:314`: `ε ↦ u_ε`, the inserted velocity. -/
  velocity : ℝ → VelocityField
  /-- `03-torus.tex:314,318-320`: `ε ↦ p_ε`, the inserted pressure. -/
  pressure : ℝ → SpaceTimeScalar
  /-- `03-torus.tex:314`: `ε ↦ g_ε`, the inserted force. -/
  force : ℝ → VelocityField
  /-- `03-torus.tex:314` `eq:insertion`, first display: `u_ε = v + w_ε + U_ε`,
  with `v = reference.velocity`, `w_ε = D.correction ε` (`lem:potential`), and
  `U_ε = periodizedScaledVelocity P x₀ T ε` the periodized rescaled packet
  (`prop:scaling`).  Quantifier order: `∀ ε, ∀ z`.  Non-vacuity: a pointwise
  field equation fixing `velocity` on all spacetime, not an existential shadow. -/
  velocity_formula : ∀ ε : ℝ, ∀ z : SpaceTime,
    velocity ε z = reference.velocity z + D.correction ε z +
      periodizedScaledVelocity P place.x₀ place.T ε z
  /-- `03-torus.tex:314,318-320` `eq:insertion`, second display: `p_ε = π + P_ε`
  normalized by subtracting its torus mean ("subtract its spatial mean to
  normalize `p_ε`", `:318-320`), where `π = reference.pressure` and
  `P_ε = periodizedScaledPressure P x₀ T ε` is the scaling record's periodized
  raw packet pressure.  TORUS: the `∫_{T³}p=0` gauge (`normalizePressureT`) is
  imposed; the `R42` twin keeps the compact gauge `π + P_ε`
  (`InsertionFamily.lean:183`).  Because `reference` carries `pressure_gauge`
  (`π` mean-zero), `normalize(π + P_ε) = π + normalize(P_ε)`.
  Quantifier order: `∀ ε`.  Non-vacuity: fixes `pressure ε` as a concrete
  normalized field. -/
  pressure_formula : ∀ ε : ℝ,
    pressure ε = normalizePressureT
      (fun z => reference.pressure z +
        periodizedScaledPressure P place.x₀ place.T ε z)
  /-- `03-torus.tex:314` `eq:insertion`, third display: `g_ε = g + H_ε + F_ε`,
  with `H_ε = correctionForce ν v D ε` (`lem:correction`, `eq:H`) and
  `F_ε = periodizedScaledForce P x₀ T ε` the periodized rescaled packet force
  (`prop:scaling`).  Quantifier order: `∀ ε, ∀ z`.  Non-vacuity: a pointwise
  field equation. -/
  force_formula : ∀ ε : ℝ, ∀ z : SpaceTime,
    force ε z = g z + correctionForce ν reference.velocity D ε z +
      periodizedScaledForce P place.x₀ place.T ε z

  -- ### Class memberships `03-torus.tex:289,338-341`
  /-- `03-torus.tex:289,338-341`: `g_ε ∈ 𝓕`.  "Their time supports remain
  compact subsets of `(0,∞)` … Therefore `g_ε ∈ 𝓕`."
  Quantifier order: `∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: membership in the smooth
  compact torus force class for the actual inserted force. -/
  force_mem : ∀ ε ∈ Ioc (0 : ℝ) ε₀, force ε ∈ forceClassT
  /-- `03-torus.tex:338-341`: the force perturbation `g_ε - g = H_ε + F_ε` is
  itself a torus force (compact time support in `(0,∞)`, smooth across `T`).
  Quantifier order: `∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: `forceClassT` membership of
  the actual difference field. -/
  forceDifference_mem : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    (fun z => force ε z - g z) ∈ forceClassT

  -- ### A classical torus trajectory on `[0,T)` `03-torus.tex:329-345`
  /-- `03-torus.tex:337`: `u_ε` is smooth on `[0,T) × R³`, one-sided at `t = 0`.
  Quantifier order: `∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: `ContDiffOn` on the
  closed-at-zero, open-at-`T` slab of the actual `velocity ε`. -/
  velocity_smooth : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ContDiffOn ℝ ∞ (velocity ε) (Ico (0 : ℝ) place.T ×ˢ (univ : Set Space))
  /-- `03-torus.tex:337`: `p_ε` is smooth on `[0,T) × R³`.
  Quantifier order: `∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: `ContDiffOn` of the actual
  `pressure ε`. -/
  pressure_smooth : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ContDiffOn ℝ ∞ (pressure ε) (Ico (0 : ℝ) place.T ×ˢ (univ : Set Space))
  /-- `03-torus.tex:333-334`: `u_ε(·,0) = a`, "the initial datum … [is]
  unchanged".  Quantifier order: `∀ ε ∈ Ioc 0 ε₀, ∀ x`.  Non-vacuity: pointwise
  equality of physical vectors. -/
  initial : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ x : Space, velocity ε (0, x) = a x
  /-- `03-torus.tex:332-334`: `div u_ε = 0` on `[0,T)`, including `t = 0`.
  Quantifier order: `∀ ε ∈ Ioc 0 ε₀, ∀ t ∈ Ico 0 T, ∀ x`.  Non-vacuity: the
  registered physical divergence vanishes pointwise. -/
  incompressible : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) place.T, ∀ x : Space,
      spatialDivergence (velocity ε) t x = 0
  /-- `03-torus.tex:329-331`: the momentum equation `eq:NS` holds exactly for
  `(u_ε, p_ε, g_ε)` at interior times, "the equation is exact on `[0,T)`".
  Quantifier order: `∀ ε ∈ Ioc 0 ε₀, ∀ t ∈ Ioo 0 T, ∀ x`.  Non-vacuity: the NS
  residual equals the inserted force pointwise, at the reference's own `ν`. -/
  momentum : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ioo (0 : ℝ) place.T, ∀ x : Space,
      navierStokesResidual ν (velocity ε) (pressure ε) t x = force ε (t, x)
  /-- `03-torus.tex:294` clause (ii): `u_ε = v` for `0 ≤ t ≤ T - 2ε²`.
  Quantifier order: `∀ ε ∈ Ioc 0 ε₀, ∀ t, 0 ≤ t, t ≤ T - 2ε², ∀ x`.
  Non-vacuity: pointwise equality on the entire quiet initial slab. -/
  history : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t : ℝ, 0 ≤ t →
    t ≤ place.T - 2 * ε ^ 2 → ∀ x : Space,
      velocity ε (t, x) = reference.velocity (t, x)
  /-- `03-torus.tex:2-4,337`: `u_ε` has unit spatial periods on `[0,T)`.
  Quantifier order: that of `IsPeriodicOn`.  Non-vacuity: the actual periodicity
  used for the torus solution and its lifted norms. -/
  velocity_periodic : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    IsPeriodicOn (Ico (0 : ℝ) place.T) (velocity ε)

  -- ### The bundled classical solution, maximal identification and lifespan `03-torus.tex:338-345`
  /-- `03-torus.tex:338,344-345`: for each `ε` the inserted pair `(u_ε, p_ε)` is
  a torus classical solution on the full horizon `[0,T)` (carrying `sobolev`,
  the pressure gauge, and `∇p_ε ∈ L²`).  Mirrors `InsertionLifespanV2API.solution`
  (`Contracts/V2/InsertionLifespan.lean`).  Quantifier order: `∀ ε ∈ Ioc 0 ε₀`,
  then `∃ w`.  Non-vacuity: the witness is a full `ClassicalSolutionT` with
  velocity and pressure equal to the inserted fields. -/
  solution : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∃ w : ClassicalSolutionT ν a (force ε) place.T,
      w.velocity = velocity ε ∧ w.pressure = pressure ε
  /-- `03-torus.tex:342-344`: "Uniqueness in Proposition `prop:local` identifies
  the constructed velocity with the maximal solution."  The inserted pair *is*
  the maximal periodic solution of `(ν, a, g_ε)`, in the registered
  `IsMaximalPeriodicSolution` vocabulary.  TORUS: uses `TorusLocalTheory`'s
  torus maximal-solution predicate, not `R³`'s `IsMaximalSolution`.
  Quantifier order: `∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: the actual inserted fields
  are the maximal solution, not merely one solution. -/
  maximal : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    IsMaximalPeriodicSolution ν a (force ε) (velocity ε) (pressure ε)
  /-- `03-torus.tex:291,344-345` clause (i): `T_max^ν(a, g_ε) = T`, "its lifespan
  is exactly `T`".  Quantifier order: `∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: an
  equality in `ℝ≥0∞` of the registered maximal lifespan with `ofReal T`, not a
  one-sided bound. -/
  lifespan : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    maximalLifespanT ν a (force ε) = ENNReal.ofReal place.T
  /-- `03-torus.tex:291-292` clause (i): `limsup_{t↑T} ‖u_ε(t)‖_∞ = ∞`, in the
  pointwise `SpeedUnboundedAt` form the packet/rescaling produce.
  Quantifier order: `∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: at every level `M` and every
  left neighbourhood of `T`, a presingular time and point exceed `M`. -/
  blowup : ∀ ε ∈ Ioc (0 : ℝ) ε₀, SpeedUnboundedAt place.T (velocity ε)
  /-- `03-torus.tex:291-292` clause (i): the essential-supremum form of the same
  display, `limsup_{t↑T} ‖u_ε(t)‖_{L^∞} = ⊤`, in the frozen
  `Contracts.V1.MaximalPartial` vocabulary (`limsupLeft`/`speedENorm`).  Mirrors
  `InsertionLifespanV2API.blowup_limsup`.  Quantifier order: `∀ ε ∈ Ioc 0 ε₀`.
  Non-vacuity: the left `limsup` of the concrete `L^∞` slice norm is exactly
  `⊤`. -/
  blowup_limsup : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    BlowupDensity.Contracts.V1.MaximalPartial.limsupLeft place.T
        (fun t => BlowupDensity.Contracts.V1.MaximalPartial.speedENorm
          (fun x : Space => velocity ε (t, x))) = ⊤

  -- ### The two vanishing cross-transport terms `03-torus.tex:322-328` (proof of `eq:insertion`)
  /-- `03-torus.tex:322-328`: the first cross-advection term `(b_ε·∇)U_ε` is
  identically zero, where `b_ε = v + w_ε` (`correctedBackground`) is the
  corrected background and `U_ε = periodizedScaledVelocity P x₀ T ε` the
  periodized packet.  TORUS: the periodic form of the whole-space cancellation
  used in Theorem 4.2's proof.  Quantifier order: `∀ ε ∈ Ioc 0 ε₀,
  ∀ t ∈ Ico 0 T, ∀ x`.  Non-vacuity: the directional (Fréchet) derivative of the
  actual packet in the actual background direction vanishes pointwise. -/
  crossTransport_background_advects_packet : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) place.T, ∀ x : Space,
      spatialDerivative
          (periodizedScaledVelocity P place.x₀ place.T ε) t x
          (correctedBackground reference.velocity D.correction ε (t, x)) = 0
  /-- `03-torus.tex:322-328`: the second cross-advection term `(U_ε·∇)b_ε` is
  identically zero.  Quantifier order: `∀ ε ∈ Ioc 0 ε₀, ∀ t ∈ Ico 0 T, ∀ x`.
  Non-vacuity: the directional derivative of the actual background in the actual
  packet direction vanishes pointwise, so that (with the previous field) the
  momentum equation is exact. -/
  crossTransport_packet_advects_background : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) place.T, ∀ x : Space,
      spatialDerivative
          (correctedBackground reference.velocity D.correction ε) t x
          (periodizedScaledVelocity P place.x₀ place.T ε (t, x)) = 0

  -- ### Localization of the velocity difference `03-torus.tex:293-295` clause (iii)
  /-- `03-torus.tex:295`: `u_ε - v` is divergence free at every `t < T`,
  including `t = 0`.  Quantifier order: `∀ ε ∈ Ioc 0 ε₀, ∀ t ∈ Ico 0 T, ∀ x`.
  Non-vacuity: the physical divergence of the actual difference vanishes. -/
  velocityDifference_divFree : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) place.T, ∀ x : Space,
      spatialDivergence (fun z => velocity ε z - reference.velocity z) t x = 0
  /-- `03-torus.tex:293-295`: the fixed radius scale `ρ` giving the `O(ε)`
  support diameter.  Non-vacuity: `diffSupportRadius_pos` forces it positive. -/
  diffSupportRadius : ℝ
  /-- `03-torus.tex:293-295`: `ρ > 0`.  Non-vacuity: excludes a degenerate ball. -/
  diffSupportRadius_pos : 0 < diffSupportRadius
  /-- `03-torus.tex:293-295` clause (iii): for every `t < T` the (torus-lifted)
  support of `u_ε - v` lies in the integer translates of the ball of radius
  `ε · ρ` about `x₀` — a set of diameter `O(ε)`.  TORUS: a periodic (single-copy)
  support, via `periodicSet`, rather than the whole-space single ball of `R42`
  (a periodic difference is never contained in one bounded ball).
  Quantifier order: `∀ ε ∈ Ioc 0 ε₀, ∀ t ∈ Ico 0 T`.  Non-vacuity: an actual
  `tsupport ⊆ periodicSet (ball …)` inclusion. -/
  velocityDifference_support : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) place.T,
      tsupport (fun x : Space => velocity ε (t, x) - reference.velocity (t, x)) ⊆
        periodicSet (Metric.ball place.x₀ (ε * diffSupportRadius))
  /-- `03-torus.tex:293-295` clause (iii), "inside the chosen ball": the
  `O(ε)`-ball lies in the placement chart ball `B`.  Quantifier order:
  `∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: an actual metric-ball inclusion in `B`. -/
  diffSupport_in_chart : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    Metric.ball place.x₀ (ε * diffSupportRadius) ⊆
      Metric.ball place.chartCenter place.chartRadius

  -- ### The three closeness rates `03-torus.tex:296-306` clause (iv)
  /-- `03-torus.tex:300-302` `eq:Eclose`: `‖u_ε - v‖_{E_T} ≤ (M+D)ε^{1/2} +
  Cε^{3/2}`, with `M = P.energyBound`, `D = P.dissipationBound` (`lem:packetenergy`,
  carried by the energy-enhanced `P`) and `C = correction.energyConst` (`eq:wE`).
  The norm is the registered torus `energyENormT` (`essSup + lintegral`, so no
  representative infimum and no `MemLp` guard is needed).  Quantifier order:
  `∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: an `ℝ≥0∞` inequality on the actual energy norm
  of the actual difference. -/
  energyRate : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    energyENormT place.T (fun z => velocity ε z - reference.velocity z) ≤
      ENNReal.ofReal ((P.energyBound + P.dissipationBound) * ε ^ ((1 : ℝ) / 2) +
        correction.energyConst * ε ^ ((3 : ℝ) / 2))
  /-- `03-torus.tex:303-304` `eq:Fclose`: the mixed-norm constant `C_{p,q}`, real
  data fixed before `ε`.  Non-vacuity: `forceDiffMixedConst_nonneg` prevents a
  negative witness erased by `ENNReal.ofReal`. -/
  forceDiffMixedConst : ℝ≥0∞ → ℝ≥0∞ → ℝ
  /-- `03-torus.tex:303-304`: `C_{p,q} ≥ 0` on `1 ≤ p, q`.  Quantifier order:
  `∀ p q, 1 ≤ p, 1 ≤ q`.  Non-vacuity: on the exact range of the bound. -/
  forceDiffMixedConst_nonneg : ∀ (p q : ℝ≥0∞), 1 ≤ p → 1 ≤ q →
    0 ≤ forceDiffMixedConst p q
  /-- `03-torus.tex:303-304`: honest torus mixed Bochner path of `g_ε - g`,
  `MemMixedLebesgueT q p` — an `L^q(0,∞)` time-path of `L^p(T³)` slices.  TORUS:
  the per-slice `MemLp` guard of draft B does not exclude the
  `mixedLebesgueENormT = ⨅ = ⊤` trap; the `∃ time-path` guard does.
  Quantifier order: `∀ p q [Fact (1≤p)], 1 ≤ q, ∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity:
  the actual difference has a strongly measurable finite-`L^q` mixed path. -/
  forceDifference_mixed_memLp : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      MemMixedLebesgueT q p (fun z => force ε z - g z)
  /-- `03-torus.tex:303-304` `eq:Fclose`: `‖g_ε - g‖_{L^q_tL^p_x} ≤
  C_{p,q}(ε^{α(p,q)} + ε^{α(p,q)+1})`, `α(p,q) = -3+3/p+2/q` (registered
  `Contracts.V1.alpha`).  The `ε^{α}` term is `F_ε` (`eq:packetFscale`), the
  `ε^{α+1}` term is `H_ε` (`eq:Hmixed`); force norms over `(0,∞)`.  Quantifier
  order: `∀ p q [Fact (1≤p)], 1 ≤ q, ∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: the previous
  field guards honesty; the norm is the copied `mixedLebesgueENormT`. -/
  forceDifference_mixed_bound : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      mixedLebesgueENormT q p (fun z => force ε z - g z) ≤
        ENNReal.ofReal (forceDiffMixedConst p q *
          (ε ^ (BlowupDensity.Contracts.V1.alpha p q) +
            ε ^ (BlowupDensity.Contracts.V1.alpha p q + 1)))
  /-- `03-torus.tex:305-306` `eq:Hsclose`: the Sobolev constant `C_s`, real data
  fixed before `ε`.  Non-vacuity: `forceDiffSobolevConst_pos` forces it positive
  on the used range. -/
  forceDiffSobolevConst : ℝ → ℝ
  /-- `03-torus.tex:305-306`: `C_s > 0` on `0 ≤ s < 1/2`.  Quantifier order:
  `∀ s, 0 ≤ s, s < 1/2`.  TORUS: the range stops at `1/2` (`eq:Hsclose`), not at
  `1` (`eq:HHs`).  Non-vacuity: a strict positivity on the exact used range. -/
  forceDiffSobolevConst_pos : ∀ s : ℝ, 0 ≤ s → s < 1 / 2 →
    0 < forceDiffSobolevConst s
  /-- `03-torus.tex:305-306`: honest `L¹_tH^s_x` Fourier-data path of `g_ε - g`,
  making the Bochner infimum in `forceSobolevENormT` honest.  Quantifier order:
  `∀ s, 0 ≤ s, s < 1/2, ∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: the actual difference has
  a strongly-measurable `H^s` representing path. -/
  forceDifference_sobolev_memLp : ∀ s : ℝ, 0 ≤ s → s < 1 / 2 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      MemForceSobolevT 1 s (fun z => force ε z - g z)
  /-- `03-torus.tex:305-306` `eq:Hsclose`: `‖g_ε - g‖_{L¹_tH^s_x} ≤
  C_s(ε^{1/2-s} + ε^{3/2-s})` for `0 ≤ s < 1/2`.  The `ε^{1/2-s}` term is `F_ε`
  (`eq:packetHs`), the `ε^{3/2-s}` term is `H_ε` (`eq:HHs`); the lower-order
  `ε^{1/2}, ε^{3/2}` terms are absorbed since `0 ≤ s`, `0 < ε ≤ 1`.  Force norm
  over `(0,∞)` via the registered `forceSobolevENormT`.  Quantifier order:
  `∀ s, 0 ≤ s, s < 1/2, ∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: the previous field guards
  honesty. -/
  forceDifference_sobolev_bound : ∀ s : ℝ, 0 ≤ s → s < 1 / 2 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      forceSobolevENormT 1 s (fun z => force ε z - g z) ≤
        ENNReal.ofReal (forceDiffSobolevConst s *
          (ε ^ ((1 : ℝ) / 2 - s) + ε ^ ((3 : ℝ) / 2 - s)))
  /-- `03-torus.tex:309-310`: "For `s < 0`, the force difference also tends to
  zero in `L¹_tH^s_x`."  Quantifier order: `∀ s, s < 0`, then the `Tendsto`.
  Non-vacuity: convergence of the registered `forceSobolevENormT 1 s` of the
  actual difference to `0` as `ε ↓ 0`. -/
  forceDifference_negativeSobolev_tendsto : ∀ s : ℝ, s < 0 →
    Tendsto (fun ε : ℝ => forceSobolevENormT 1 s (fun z => force ε z - g z))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞))
  /-- `03-torus.tex:309-310`: honest negative-order `L¹_tH^s_x` paths for the
  `s<0` tail.  TORUS: convergence of an `⨅`-norm to `0` needs the norm eventually
  `< ⊤`; this `MemForceSobolevT 1 s` guard makes the limit non-vacuous.
  Quantifier order: `∀ s, s < 0, ∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: each totalized
  negative-order norm has an actual representing path. -/
  negative_s_memLp : ∀ s : ℝ, s < 0 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      MemForceSobolevT 1 s (fun z => force ε z - g z)

/-- **The existential form of `thm:insertion`,
`paper/sections/03-torus.tex:287-311`.**  Paper quantifier order (`:287-290`):
for every viscosity `ν > 0`, every energy-enhanced whole-space packet `P`,
placement, torus scaling record, initial datum `a`, reference force `g`, radii
`r`, margin `δ`, cutoff data `D`, reference solution regular through `T+δ`, and
correction record, with `δ > 0`, `g ∈ 𝓕`, `a ∈ 𝓧`, there is an inserted family:
`Nonempty` of the API, which carries the threshold `ε₀` as a field.  Introducing
this definition asserts nothing. -/
def periodicInsertionStatement : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (P : PacketImportAPI ν)
    (place : BlowupDensity.T15.Draft.PlacementData P.toPacketAPI)
    (scaling : ScalingAPI P place)
    (a : SpatialField) (g : SpaceTimeField) (r δ : ℝ)
    (D : BlowupDensity.T16.Draft.CutoffData)
    (reference : ClassicalSolutionT ν a g (place.T + δ))
    (correction :
      BlowupDensity.T17.Spec.CorrectionAPI ν place reference.velocity r δ D),
    0 < δ → g ∈ forceClassT → a ∈ initialClassT →
      Nonempty (PeriodicInsertionAPI ν P place scaling a g r δ D reference correction)

end BlowupDensity.T18.Spec
