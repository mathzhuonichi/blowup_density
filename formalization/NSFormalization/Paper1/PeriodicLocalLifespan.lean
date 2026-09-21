import NSFormalization.Paper1.PeriodicDensityDichotomy
import NSFormalization.Paper1.PeriodicPressureNormalization
import NSFormalization.Paper1.PeriodicFlowRestriction
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Local and maximal periodic solutions for Paper 1

This is the concrete statement interface for `prop:local` in
`final/paper_1_theory.tex`. It uses the existing periodic `Flow`, its actual
Fourier `H²` norm, and the supremum `lifespan`; it introduces no ordinary
whole-space `L²` representative. The local construction, normalized uniqueness,
maximal gluing, and squared-`H²` continuation proofs are explicit `sorry`
obligations. The intended proof follows the manuscript's common `H³` Picard
interval and uniform higher-order bounds.
-/
noncomputable section

namespace NSFormalization.Paper1.PeriodicLocalLifespan

open Set MeasureTheory Filter
open NavierStokes NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open NSFormalization.Paper1.PeriodicInitialData
open NSFormalization.Paper1.PeriodicForceSpace
open NSFormalization.Paper1.PeriodicForceConvergence
open NSFormalization.Paper1.PeriodicDensityDichotomy
open NSFormalization.Paper1.PeriodicLifespan
open NSFormalization.Paper1.PeriodicPressureNormalization
open scoped ENNReal ContDiff Topology

/-- The force class of `prop:local`: spatially unit-periodic for nonnegative
time and jointly smooth on every closed, finite, nonnegative time slab.
Smoothness at time zero is relative to the physical half-line. -/
structure IsSmoothPeriodicForce (f : VelocityField) : Prop where
  smooth : ∀ S : ℝ, 0 < S → ContDiffOn ℝ ∞ f (Icc (0 : ℝ) S ×ˢ univ)
  periodic : UnitSpatialPeriodsOn (Ici (0 : ℝ)) f

/-- The manuscript's test-force class is contained in the local-theory class. -/
theorem IsTestForce.to_smoothPeriodic {f : VelocityField} (hf : IsTestForce f) :
    IsSmoothPeriodicForce f :=
  ⟨fun _ _ => hf.smooth.contDiffOn, fun t _ => hf.periodic t (mem_univ t)⟩

/-- Pressure normalization is imposed on the entire half-open flow horizon. -/
def IsNormalized {ν S : ℝ} {a : Space → Space} {f : VelocityField}
    (U : Flow ν a f S) : Prop :=
  ∀ t ∈ Ico (0 : ℝ) S, cubeIntegral (fun x => U.pressure (t, x)) = 0

theorem normalizedFlow_isNormalized {ν S : ℝ} {a : Space → Space}
    {f : VelocityField} (U : Flow ν a f S) : IsNormalized (normalizedFlow U) :=
  fun _ ht => normalizedFlow_mean_zero U ht

/-- The actual squared periodic Bessel `H²` norm used in `eq:criterion`. -/
def h2SquaredProfile {ν S : ℝ} {a : Space → Space} {f : VelocityField}
    (U : Flow ν a f S) (t : ℝ) : ℝ :=
  (periodicVectorSobolevNorm 2 U.velocity t) ^ 2

/-- `IntegrableOn` records finiteness and measurability of the squared norm,
so this criterion cannot hold merely because a divergent Bochner integral is
totalized to zero. The endpoint values do not affect the integral. -/
def FiniteH2Energy {ν S : ℝ} {a : Space → Space} {f : VelocityField}
    (U : Flow ν a f S) : Prop :=
  IntegrableOn (h2SquaredProfile U) (Ioc (0 : ℝ) S) volume

/-! ## Explicit analytic-construction contracts

The finite-order cylinder solver in `PeriodicFiniteOrderMild` does not yet
construct a `Flow`: it has no pressure recovery or pointwise smoothness
bridge.  We therefore record the two missing analytic implications as an
ordinary structure rather than hiding them in an axiom.  This gives downstream
developments a usable conditional interface while keeping the unconditional
theorems below honest about their remaining proof obligations.
-/
structure ClassicalPeriodicLocalTheory : Prop where
  local_flow : ∀ {ν : ℝ}, 0 < ν → ∀ {a : Space → Space},
    IsAdmissibleInitialData a → ∀ {f : VelocityField},
    IsSmoothPeriodicForce f → ∃ S : ℝ, Nonempty (Flow ν a f S)
  finite_h2_extension : ∀ {ν S : ℝ}, 0 < ν → ∀ {a : Space → Space}
    {f : VelocityField}, IsSmoothPeriodicForce f → (W : Flow ν a f S) →
    FiniteH2Energy W → ∃ T : ℝ, S < T ∧ ∃ V : Flow ν a f T,
      IsNormalized V ∧ ∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
        V.velocity (t, x) = W.velocity (t, x) ∧
        V.pressure (t, x) = normalizedPressure W.pressure (t, x)

theorem exists_periodic_local_flow_of_classicalTheory
    (H : ClassicalPeriodicLocalTheory) {ν : ℝ} (hν : 0 < ν)
    {a : Space → Space} (ha : IsAdmissibleInitialData a) {f : VelocityField}
    (hf : IsSmoothPeriodicForce f) :
    ∃ S : ℝ, Nonempty (Flow ν a f S) :=
  H.local_flow hν ha hf

/-! The conditional local theory also supplies all shorter positive horizons.
This is the restriction-stability half of the local-existence interface.  It
is useful independently of the unresolved analytic construction of the first
classical witness, and makes the quantifier order explicit for later lifespan
arguments. -/
theorem exists_periodic_local_flow_shorter_of_classicalTheory
    (H : ClassicalPeriodicLocalTheory) {ν : ℝ} (hν : 0 < ν)
    {a : Space → Space} (ha : IsAdmissibleInitialData a) {f : VelocityField}
    (hf : IsSmoothPeriodicForce f) :
    ∃ S : ℝ, 0 < S ∧ ∃ U : Flow ν a f S,
      ∀ R : ℝ, 0 < R → R ≤ S → Nonempty (Flow ν a f R) := by
  obtain ⟨S, hU⟩ := H.local_flow hν ha hf
  refine ⟨S, hU.some.horizon_pos, hU.some, ?_⟩
  intro R hR hRS
  exact Flow.nonempty_restrict hU.some hR hRS

theorem exists_normalized_periodic_local_flow_shorter_of_classicalTheory
    (H : ClassicalPeriodicLocalTheory) {ν : ℝ} (hν : 0 < ν)
    {a : Space → Space} (ha : IsAdmissibleInitialData a) {f : VelocityField}
    (hf : IsSmoothPeriodicForce f) :
    ∃ S : ℝ, 0 < S ∧ ∃ U : Flow ν a f S, IsNormalized U ∧
      ∀ R : ℝ, 0 < R → R ≤ S → ∃ V : Flow ν a f R, IsNormalized V := by
  obtain ⟨S, hU⟩ := H.local_flow hν ha hf
  let U : Flow ν a f S := normalizedFlow hU.some
  have hUn : IsNormalized U := normalizedFlow_isNormalized hU.some
  refine ⟨S, U.horizon_pos, U, hUn, ?_⟩
  intro R hR hRS
  refine ⟨U.restrict hR hRS, ?_⟩
  intro t ht
  exact hUn t ⟨ht.1, ht.2.trans_le hRS⟩

theorem exists_periodic_extension_of_classicalTheory
    (H : ClassicalPeriodicLocalTheory) {ν S : ℝ} (hν : 0 < ν)
    {a : Space → Space} {f : VelocityField} (hf : IsSmoothPeriodicForce f)
    (W : Flow ν a f S) (hfinite : FiniteH2Energy W) :
    ∃ T : ℝ, S < T ∧ ∃ V : Flow ν a f T, IsNormalized V ∧
      ∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
        V.velocity (t, x) = W.velocity (t, x) ∧
        V.pressure (t, x) = normalizedPressure W.pressure (t, x) :=
  H.finite_h2_extension hν hf W hfinite

/-- Arbitrary admissible data and the local-theory force class produce a
positive-horizon classical flow. The common `H³` interval and higher-order
persistence are the remaining analytic construction. -/
theorem exists_periodic_local_flow
    (H : ClassicalPeriodicLocalTheory)
    {ν : ℝ} (hν : 0 < ν) {a : Space → Space}
    (ha : IsAdmissibleInitialData a) {f : VelocityField}
    (hf : IsSmoothPeriodicForce f) :
    ∃ S : ℝ, Nonempty (Flow ν a f S) :=
  exists_periodic_local_flow_of_classicalTheory H hν ha hf

/-- The existing normalization operation supplies the pressure gauge in the
local existence conclusion without changing the velocity or the equation. -/
theorem exists_normalized_periodic_local_flow
    (H : ClassicalPeriodicLocalTheory)
    {ν : ℝ} (hν : 0 < ν) {a : Space → Space}
    (ha : IsAdmissibleInitialData a) {f : VelocityField}
    (hf : IsSmoothPeriodicForce f) :
    ∃ S : ℝ, ∃ U : Flow ν a f S, IsNormalized U := by
  obtain ⟨S, ⟨U⟩⟩ := exists_periodic_local_flow H hν ha hf
  exact ⟨S, normalizedFlow U, normalizedFlow_isNormalized U⟩

/-- The exact unforced premise consumed by the existing density dichotomy. -/
theorem periodic_unforced_local_existence
    (H : ClassicalPeriodicLocalTheory)
    {ν : ℝ} (hν : 0 < ν) : UnforcedLocalExistence ν := by
  intro a ha
  exact exists_periodic_local_flow H hν ha
    (IsTestForce.to_smoothPeriodic (f := (0 : VelocityField)) isTestForce_zero)

/-- Positive lifespan for every force covered by the local theorem. -/
theorem lifespan_pos
    (H : ClassicalPeriodicLocalTheory)
    {ν : ℝ} (hν : 0 < ν) {a : Space → Space}
    (ha : IsAdmissibleInitialData a) {f : VelocityField}
    (hf : IsSmoothPeriodicForce f) : 0 < lifespan ν a f := by
  obtain ⟨S, ⟨U⟩⟩ := exists_periodic_local_flow H hν ha hf
  exact lifespan_pos_of_flow U

/-- The velocity part of normalized-flow agreement follows directly from the
existing periodic uniqueness theorem.  This helper is deliberately stated
without pressure normalization, since uniqueness of the pressure representative
requires a separate mean-zero argument. -/
theorem flow_velocity_agree_on_common_interval
    {ν S T : ℝ} (hν : 0 < ν) {a : Space → Space} {f : VelocityField}
    (U : Flow ν a f S) (V : Flow ν a f T) :
    ∀ t ∈ Ico (0 : ℝ) (min S T), ∀ x : Space,
      U.velocity (t, x) = V.velocity (t, x) := by
  intro t ht x
  let b : ℝ := t
  have hsubU : PeriodicUniqueness.slab 0 b ⊆ Ico (0 : ℝ) S ×ˢ (univ : Set Space) := by
    intro z hz
    have hbt : z.1 < S := by
      exact lt_of_le_of_lt (show z.1 ≤ t by simpa [b] using hz.1.2)
        (lt_of_lt_of_le ht.2 (min_le_left S T))
    exact ⟨⟨hz.1.1, hbt⟩, hz.2⟩
  have hsubV : PeriodicUniqueness.slab 0 b ⊆ Ico (0 : ℝ) T ×ˢ (univ : Set Space) := by
    intro z hz
    have hbt : z.1 < T := by
      exact lt_of_le_of_lt (show z.1 ≤ t by simpa [b] using hz.1.2)
        (lt_of_lt_of_le ht.2 (min_le_right S T))
    exact ⟨⟨hz.1.1, hbt⟩, hz.2⟩
  have he := NSFormalization.Paper1.PeriodicUniqueness.classical_uniqueness_on_Icc hν
    (U.velocity_smooth.mono hsubU) (V.velocity_smooth.mono hsubV)
    (U.pressure_smooth.mono hsubU) (V.pressure_smooth.mono hsubV)
    (fun s hs y i => U.velocity_periodic s ⟨hs.1,
      lt_of_le_of_lt (show s ≤ t by simpa [b] using hs.2)
        (lt_of_lt_of_le ht.2 (min_le_left S T))⟩ y i)
    (fun s hs y i => V.velocity_periodic s ⟨hs.1,
      lt_of_le_of_lt (show s ≤ t by simpa [b] using hs.2)
        (lt_of_lt_of_le ht.2 (min_le_right S T))⟩ y i)
    (fun s hs y i => U.pressure_periodic s ⟨hs.1,
      lt_of_le_of_lt (show s ≤ t by simpa [b] using hs.2)
        (lt_of_lt_of_le ht.2 (min_le_left S T))⟩ y i)
    (fun s hs y i => V.pressure_periodic s ⟨hs.1,
      lt_of_le_of_lt (show s ≤ t by simpa [b] using hs.2)
        (lt_of_lt_of_le ht.2 (min_le_right S T))⟩ y i)
    (fun s hs y => U.divergence s ⟨le_of_lt hs.1,
      (show s < t by simpa [b] using hs.2).trans
        (lt_of_lt_of_le ht.2 (min_le_left S T))⟩ y)
    (fun s hs y => V.divergence s ⟨le_of_lt hs.1,
      (show s < t by simpa [b] using hs.2).trans
        (lt_of_lt_of_le ht.2 (min_le_right S T))⟩ y)
    (fun s hs y => U.equation s ⟨hs.1,
      (show s < t by simpa [b] using hs.2).trans
        (lt_of_lt_of_le ht.2 (min_le_left S T))⟩ y)
    (fun s hs y => V.equation s ⟨hs.1,
      (show s < t by simpa [b] using hs.2).trans
        (lt_of_lt_of_le ht.2 (min_le_right S T))⟩ y)
    (fun y => (U.initial y).trans (V.initial y).symm)
  have htb : t ∈ Icc (0 : ℝ) b := by
    exact ⟨ht.1, by simp [b]⟩
  exact he t htb x


/-- Two normalized actual flows agree on their common physical interval.
The pressure equality is included only after fixing its spatial mean. -/
theorem normalized_flows_agree
    {ν S T : ℝ} (hν : 0 < ν) {a : Space → Space} {f : VelocityField}
    (U : Flow ν a f S) (V : Flow ν a f T)
    (hU : IsNormalized U) (hV : IsNormalized V) :
    ∀ t ∈ Ico (0 : ℝ) (min S T), ∀ x : Space,
      U.velocity (t, x) = V.velocity (t, x) ∧
      U.pressure (t, x) = V.pressure (t, x) := by
  have hvel : ∀ t ∈ Ico (0 : ℝ) (min S T), ∀ x : Space,
      U.velocity (t, x) = V.velocity (t, x) :=
    flow_velocity_agree_on_common_interval hν U V
  have hpos : ∀ t ∈ Ioo (0 : ℝ) (min S T), ∀ x : Space,
      U.pressure (t, x) = V.pressure (t, x) := by
    intro t ht x
    have huv : ∀ y : Space, U.velocity =ᶠ[𝓝 (t, y)] V.velocity := by
      intro y
      filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds
        ⟨ht, mem_univ y⟩] with z hz
      exact hvel z.1 ⟨hz.1.1.le, hz.1.2⟩ z.2
    have hgrad : ∀ y : Space,
        pressureGradient U.pressure t y = pressureGradient V.pressure t y := by
      intro y
      have heq : Source.residual ν U.velocity U.pressure t y =
          Source.residual ν V.velocity V.pressure t y := by
        rw [U.equation t ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left S T)⟩ y,
          V.equation t ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_right S T)⟩ y]
      unfold Source.residual at heq
      rw [NavierStokes.ResidualRegularity.temporalDerivative_congr (huv y),
        NavierStokes.ResidualRegularity.advection_congr (huv y),
        NavierStokes.ResidualRegularity.spatialLaplacian_congr (huv y)] at heq
      have heq' := add_left_cancel heq
      exact heq'
    have hpU : ContDiff ℝ ∞ (fun y : Space => U.pressure (t, y)) :=
      U.pressure_smooth.comp_contDiff (contDiff_const.prodMk contDiff_id)
        (fun y => ⟨⟨ht.1.le, ht.2.trans_le (min_le_left S T)⟩, mem_univ y⟩)
    have hpV : ContDiff ℝ ∞ (fun y : Space => V.pressure (t, y)) :=
      V.pressure_smooth.comp_contDiff (contDiff_const.prodMk contDiff_id)
        (fun y => ⟨⟨ht.1.le, ht.2.trans_le (min_le_right S T)⟩, mem_univ y⟩)
    have hfd : ∀ y : Space,
        fderiv ℝ (fun z : Space => U.pressure (t, z) - V.pressure (t, z)) y = 0 := by
      intro y
      ext w
      have hpg : pressureGradient (fun z => U.pressure z - V.pressure z) t y = 0 := by
        change pressureGradient (U.pressure - V.pressure) t y = 0
        rw [NavierStokes.PeriodicUniqueness.pressureGradient_sub hpU hpV,
          hgrad y, sub_self]
      have hi := NavierStokes.PeriodicUniqueness.inner_pressureGradient
        (fun z => U.pressure z - V.pressure z) t y w
      rw [hpg, inner_zero_right] at hi
      exact hi.symm
    have hconst : ∀ y : Space,
        U.pressure (t, y) - V.pressure (t, y) =
          U.pressure (t, 0) - V.pressure (t, 0) := by
      intro y
      exact is_const_of_fderiv_eq_zero
        (fun z => (hpU.sub hpV).differentiable (by simp) z) hfd y 0
    have hmean : cubeIntegral (fun y : Space =>
        U.pressure (t, y) - V.pressure (t, y)) = 0 := by
      rw [cubeIntegral_sub hpU.continuous hpV.continuous,
        hU t ⟨ht.1.le, lt_of_lt_of_le ht.2 (min_le_left S T)⟩,
        hV t ⟨ht.1.le, lt_of_lt_of_le ht.2 (min_le_right S T)⟩]
      simp
    have hc : U.pressure (t, 0) - V.pressure (t, 0) = 0 := by
      rw [show (fun y : Space => U.pressure (t, y) - V.pressure (t, y)) =
          (fun _ : Space => U.pressure (t, 0) - V.pressure (t, 0)) by
        funext y; exact hconst y] at hmean
      simpa [cubeIntegral, cubeMeasure, cube, Measure.real] using hmean
    exact sub_eq_zero.mp ((hconst x).trans (by simpa using hc))
  intro t ht x
  refine ⟨hvel t ht x, ?_⟩
  have hm : 0 < min S T := lt_min U.horizon_pos V.horizon_pos
  have hcontU : ContinuousOn (fun s : ℝ => U.pressure (s,x))
      (Ico (0 : ℝ) (min S T)) := by
    apply U.pressure_smooth.continuousOn.comp'
      (continuousOn_id.prodMk continuousOn_const)
    intro s hs
    exact ⟨⟨hs.1, hs.2.trans_le (min_le_left S T)⟩, mem_univ x⟩
  have hcontV : ContinuousOn (fun s : ℝ => V.pressure (s,x))
      (Ico (0 : ℝ) (min S T)) := by
    apply V.pressure_smooth.continuousOn.comp'
      (continuousOn_id.prodMk continuousOn_const)
    intro s hs
    exact ⟨⟨hs.1, hs.2.trans_le (min_le_right S T)⟩, mem_univ x⟩
  have heqOn : EqOn (fun s : ℝ => U.pressure (s, x))
      (fun s : ℝ => V.pressure (s, x)) (Ico (0 : ℝ) (min S T)) :=
    Set.EqOn.of_subset_closure (fun s hs => hpos s hs x)
      hcontU hcontV Ioo_subset_Ico_self (fun s hs => by
        rw [closure_Ioo hm.ne]
        exact ⟨hs.1, hs.2.le⟩)
  exact heqOn ht

/- A small overlap interface for later gluing arguments.  The pointwise
agreement theorem above is enough to transport every local smoothness field
to a common horizon; this wrapper records the domain restriction explicitly
so downstream constructions need not repeat the product-set bookkeeping. -/
theorem common_interval_smooth_of_agree
    {ν S T : ℝ} {a : Space → Space} {f : VelocityField}
    (U : Flow ν a f S) (V : Flow ν a f T)
    {w : VelocityField} (hw : ∀ z ∈ Ico (0 : ℝ) (min S T) ×ˢ (univ : Set Space),
      w z = U.velocity z) :
    ContDiffOn ℝ ∞ w (Ico (0 : ℝ) (min S T) ×ˢ (univ : Set Space)) := by
  apply U.velocity_smooth.congr_mono hw
  intro z hz
  exact ⟨⟨hz.1.1, hz.1.2.trans_le (min_le_left S T)⟩, hz.2⟩

theorem common_interval_pressure_smooth_of_agree
    {ν S T : ℝ} {a : Space → Space} {f : VelocityField}
    (U : Flow ν a f S) (V : Flow ν a f T)
    {q : PressureField} (hq : ∀ z ∈ Ico (0 : ℝ) (min S T) ×ˢ (univ : Set Space),
      q z = U.pressure z) :
    ContDiffOn ℝ ∞ q (Ico (0 : ℝ) (min S T) ×ˢ (univ : Set Space)) := by
  apply U.pressure_smooth.congr_mono hq
  intro z hz
  exact ⟨⟨hz.1.1, hz.1.2.trans_le (min_le_left S T)⟩, hz.2⟩

/-! The normalization projection is idempotent on the physical slab.  This is
the concrete gauge-compatibility fact needed when a normalized local witness is
normalized again during overlap gluing.  The statement is restricted to
`Ico (0,S)`, where the pressure gauge is defined; it makes no claim about
values outside the flow horizon. -/
theorem normalizedPressure_idempotent_on_Ico
    {S : ℝ} {p : PressureField}
    (hp : ContDiffOn ℝ ∞ p (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) S) (x : Space) :
    normalizedPressure (normalizedPressure p) (t, x) =
      normalizedPressure p (t, x) := by
  have hm : pressureMean (normalizedPressure p) t = 0 := by
    simpa only [pressureMean] using pressureMean_zero_normalized_slice hp ht
  simp [normalizedPressure, hm]

theorem normalizedFlow_pressure_idempotent_on_Ico
    {ν S : ℝ} {a : Space → Space} {f : VelocityField}
    (W : Flow ν a f S) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) S) (x : Space) :
    (normalizedFlow (normalizedFlow W)).pressure (t, x) =
      (normalizedFlow W).pressure (t, x) := by
  exact normalizedPressure_idempotent_on_Ico W.pressure_smooth ht x

/-- The normalized maximal trajectory, represented by common actual fields.
Its restrictions exist at every finite positive horizon at or below its
endpoint; at a finite endpoint this is exactly smoothness on `[0,Tmax)`.
Equality with the supremum lifespan rules out every larger actual horizon. -/
structure MaximalSolution (ν : ℝ) (a : Space → Space) (f : VelocityField) where
  endpoint : ℝ≥0∞
  endpoint_pos : 0 < endpoint
  endpoint_eq_lifespan : endpoint = lifespan ν a f
  velocity : VelocityField
  pressure : PressureField
  flow : ∀ S : ℝ, 0 < S → ENNReal.ofReal S < endpoint → Flow ν a f S
  velocity_eq : ∀ S hS hSE, (flow S hS hSE).velocity = velocity
  pressure_eq : ∀ S hS hSE, (flow S hS hSE).pressure = pressure
  normalized : ∀ S hS hSE, IsNormalized (flow S hS hSE)

/-- Common fields obtained by choosing an actual normalized flow at each time.
Values outside every actual horizon are immaterial to the maximal solution. -/
private def gluedFields (ν : ℝ) (a : Space → Space) (f : VelocityField)
    (z : SpaceTime) : Space × ℝ :=
  by
    classical
    exact if h : ∃ S : ℝ, ∃ U : Flow ν a f S, z.1 < S ∧ IsNormalized U then
    let U := h.choose_spec.choose
    (U.velocity z, U.pressure z)
    else (0, 0)

/-- Uniqueness makes the pointwise choices agree on every actual horizon. -/
private theorem gluedFields_agree
    {ν S : ℝ} (hν : 0 < ν) {a : Space → Space} {f : VelocityField}
    (U : Flow ν a f S) (hU : IsNormalized U) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) S) (x : Space) :
    gluedFields ν a f (t, x) = (U.velocity (t, x), U.pressure (t, x)) := by
  classical
  have h : ∃ T : ℝ, ∃ V : Flow ν a f T, t < T ∧ IsNormalized V :=
    ⟨S, U, ht.2, hU⟩
  simp only [gluedFields, dif_pos h]
  apply Prod.ext
  · exact (normalized_flows_agree hν h.choose_spec.choose U
      h.choose_spec.choose_spec.2 hU t
      ⟨ht.1, lt_min h.choose_spec.choose_spec.1 ht.2⟩ x).1
  · exact (normalized_flows_agree hν h.choose_spec.choose U
      h.choose_spec.choose_spec.2 hU t
      ⟨ht.1, lt_min h.choose_spec.choose_spec.1 ht.2⟩ x).2

/-- Positive lifespan and normalized uniqueness suffice for maximal gluing.
This construction does not invoke arbitrary-data local existence. -/
theorem exists_maximal_periodic_solution_of_lifespan_pos
    {ν : ℝ} (hν : 0 < ν) {a : Space → Space} {f : VelocityField}
    (hpos : 0 < lifespan ν a f) : Nonempty (MaximalSolution ν a f) := by
  classical
  let u : VelocityField := fun z => (gluedFields ν a f z).1
  let p : PressureField := fun z => (gluedFields ν a f z).2
  have hagree {T : ℝ} (U : Flow ν a f T) (hU : IsNormalized U)
      {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (x : Space) :
      u (t, x) = U.velocity (t, x) ∧ p (t, x) = U.pressure (t, x) := by
    have heq := gluedFields_agree hν U hU ht x
    exact ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
  have hflows : ∀ S : ℝ, 0 < S → ENNReal.ofReal S < lifespan ν a f →
      ∃ U : Flow ν a f S, U.velocity = u ∧ U.pressure = p ∧ IsNormalized U := by
    intro S hS hSE
    obtain hbad | ⟨T, hST, ⟨V⟩⟩ := bad_or_regular_reference hS.le a f
    · exact False.elim ((not_le_of_gt hSE) hbad)
    let W := normalizedFlow V
    have hW : IsNormalized W := normalizedFlow_isNormalized V
    have hv : ∀ z ∈ Ico (0 : ℝ) S ×ˢ (univ : Set Space), u z = W.velocity z :=
      fun z hz => (hagree W hW ⟨hz.1.1, hz.1.2.trans hST⟩ z.2).1
    have hp : ∀ z ∈ Ico (0 : ℝ) S ×ˢ (univ : Set Space), p z = W.pressure z :=
      fun z hz => (hagree W hW ⟨hz.1.1, hz.1.2.trans hST⟩ z.2).2
    have hsub : Ico (0 : ℝ) S ×ˢ (univ : Set Space) ⊆ Ico (0 : ℝ) T ×ˢ univ :=
      fun z hz => ⟨⟨hz.1.1, hz.1.2.trans hST⟩, hz.2⟩
    let U : Flow ν a f S :=
      { velocity := u
        pressure := p
        horizon_pos := hS
        velocity_smooth := W.velocity_smooth.congr_mono hv hsub
        pressure_smooth := W.pressure_smooth.congr_mono hp hsub
        velocity_periodic := by
          intro t ht x i
          rw [hv _ ⟨ht, mem_univ _⟩, hv _ ⟨ht, mem_univ _⟩]
          exact W.velocity_periodic t ⟨ht.1, ht.2.trans hST⟩ x i
        pressure_periodic := by
          intro t ht x i
          rw [hp _ ⟨ht, mem_univ _⟩, hp _ ⟨ht, mem_univ _⟩]
          exact W.pressure_periodic t ⟨ht.1, ht.2.trans hST⟩ x i
        initial := by
          intro x
          exact (hv _ ⟨⟨le_rfl, hS⟩, mem_univ x⟩).trans (W.initial x)
        divergence := by
          intro t ht x
          have heq : (fun y => u (t, y)) = (fun y => W.velocity (t, y)) :=
            funext (fun y => hv _ ⟨ht, mem_univ y⟩)
          simpa only [spatialDivergence, spatialDerivative, heq] using
            W.divergence t ⟨ht.1, ht.2.trans hST⟩ x
        equation := by
          intro t ht x
          have hue : u =ᶠ[𝓝 (t, x)] W.velocity := by
            filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds
              ⟨ht, mem_univ x⟩] with z hz
            exact hv z ⟨⟨hz.1.1.le, hz.1.2⟩, hz.2⟩
          have hpe : p =ᶠ[𝓝 (t, x)] W.pressure := by
            filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds
              ⟨ht, mem_univ x⟩] with z hz
            exact hp z ⟨⟨hz.1.1.le, hz.1.2⟩, hz.2⟩
          exact (Source.LocalReferenceHelpers.residual_congr ν hue hpe).trans
            (W.equation t ⟨ht.1, ht.2.trans hST⟩ x) }
    refine ⟨U, rfl, rfl, ?_⟩
    intro t ht
    change cubeIntegral (fun x => p (t, x)) = 0
    have heq : (fun x => p (t, x)) = (fun x => W.pressure (t, x)) :=
      funext (fun x => hp _ ⟨ht, mem_univ x⟩)
    rw [heq]
    exact hW t ⟨ht.1, ht.2.trans hST⟩
  choose flow hvelocity hpressure hnormalized using hflows
  exact ⟨{
    endpoint := lifespan ν a f
    endpoint_pos := hpos
    endpoint_eq_lifespan := rfl
    velocity := u
    pressure := p
    flow := flow
    velocity_eq := hvelocity
    pressure_eq := hpressure
    normalized := hnormalized }⟩

/-- Local existence and unique gluing produce the maximal normalized solution.
This theorem states the maximal construction rather than assuming it as data. -/
theorem exists_maximal_periodic_solution
    (H : ClassicalPeriodicLocalTheory)
    {ν : ℝ} (hν : 0 < ν) {a : Space → Space}
    (ha : IsAdmissibleInitialData a) {f : VelocityField}
    (hf : IsSmoothPeriodicForce f) :
    Nonempty (MaximalSolution ν a f) := by
  exact exists_maximal_periodic_solution_of_lifespan_pos hν (lifespan_pos H hν ha hf)

/-- No actual flow can exist at a horizon strictly beyond the maximal
endpoint. This is an immediate consequence of endpoint equality with the
supremum, and does not assert that a flow exists at the endpoint itself. -/
theorem maximal_no_later_flow
    {ν : ℝ} {a : Space → Space} {f : VelocityField}
    (U : MaximalSolution ν a f) {T : ℝ} (_hT : 0 < T)
    (hET : U.endpoint < ENNReal.ofReal T) :
    IsEmpty (Flow ν a f T) := by
  refine ⟨fun V => ?_⟩
  have hhor : ENNReal.ofReal T ≤ lifespan ν a f := horizon_le_lifespan V
  have hle : ENNReal.ofReal T ≤ U.endpoint := by
    simpa only [U.endpoint_eq_lifespan] using hhor
  exact (not_le_of_gt hET) hle

/-- Uniqueness is equality on the physical lifespan, rather than equality of
arbitrarily chosen values outside that lifespan. -/
theorem maximal_solutions_agree
    {ν : ℝ} (hν : 0 < ν) {a : Space → Space} {f : VelocityField}
    (U V : MaximalSolution ν a f) :
    U.endpoint = V.endpoint ∧
    ∀ S : ℝ, 0 < S → ENNReal.ofReal S < U.endpoint →
      ∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
        U.velocity (t, x) = V.velocity (t, x) ∧
        U.pressure (t, x) = V.pressure (t, x) := by
  have he : U.endpoint = V.endpoint := U.endpoint_eq_lifespan.trans V.endpoint_eq_lifespan.symm
  refine ⟨he, ?_⟩
  intro S hS hSE t ht x
  have hVE : ENNReal.ofReal S < V.endpoint := by simpa [he] using hSE
  have h := normalized_flows_agree hν (U.flow S hS hSE) (V.flow S hS hVE)
    (U.normalized S hS hSE) (V.normalized S hS hVE) t (by simpa using ht) x
  simpa only [U.velocity_eq, V.velocity_eq, U.pressure_eq, V.pressure_eq] using h

/-- The squared-`H²` continuation criterion of `prop:local`. Smooth forcing
beyond `S` is essential. The returned normalized solution preserves the old
velocity and the normalized old pressure throughout `[0,S)`. No endpoint value
at `S` or uniform higher-order bound is assumed. -/
theorem exists_periodic_extension_of_finite_h2
    (H : ClassicalPeriodicLocalTheory)
    {ν S : ℝ} (hν : 0 < ν) {a : Space → Space} {f : VelocityField}
    (hf : IsSmoothPeriodicForce f) (W : Flow ν a f S)
    (hfinite : FiniteH2Energy W) :
    ∃ T : ℝ, S < T ∧ ∃ V : Flow ν a f T, IsNormalized V ∧
      ∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
        V.velocity (t, x) = W.velocity (t, x) ∧
        V.pressure (t, x) = normalizedPressure W.pressure (t, x) := by
  exact exists_periodic_extension_of_classicalTheory H hν hf W hfinite

/-- A finite squared-`H²` integral rules out a terminal classical horizon. -/
theorem lifespan_not_le_of_finite_h2
    (H : ClassicalPeriodicLocalTheory)
    {ν S : ℝ} (hν : 0 < ν) {a : Space → Space} {f : VelocityField}
    (hf : IsSmoothPeriodicForce f) (W : Flow ν a f S)
    (hfinite : FiniteH2Energy W) :
    ¬ lifespan ν a f ≤ ENNReal.ofReal S := by
  obtain ⟨T, hTS, V, _, _⟩ :=
    exists_periodic_extension_of_finite_h2 H hν hf W hfinite
  intro hupper
  have hle := (horizon_le_lifespan V).trans hupper
  have : T ≤ S := (ENNReal.ofReal_le_ofReal_iff W.horizon_pos.le).mp hle
  exact (not_le_of_gt hTS) this

/-! A restart witness agrees with the old normalized flow on every strictly
shorter common interval.  This packages the overlap step used in the
manuscript's maximal-lifespan continuation argument and avoids redoing the
endpoint bookkeeping at each restart. -/
theorem extension_agrees_on_common_interval
    {ν S T : ℝ} (hν : 0 < ν) {a : Space → Space} {f : VelocityField}
    (W : Flow ν a f S) (V : Flow ν a f T)
    (hW : IsNormalized W) (hV : IsNormalized V)
    (hST : S ≤ T) :
    ∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
      V.velocity (t, x) = W.velocity (t, x) ∧
      V.pressure (t, x) = W.pressure (t, x) := by
  intro t ht x
  have hcommon : t ∈ Ico (0 : ℝ) (min S T) := by
    exact ⟨ht.1, lt_min ht.2 (lt_of_lt_of_le ht.2 hST)⟩
  have h' : t ∈ Ico (0 : ℝ) (min T S) := by simpa [min_comm] using hcommon
  exact normalized_flows_agree hν V W hV hW t h' x


/-- Endpoint form of the finite-energy restart argument.  This is the useful
maximal-solution interface: a finite squared-`H²` witness on `[0,S)` forces
the maximal endpoint strictly past `S`.  The analytic extension premise remains
explicit in `ClassicalPeriodicLocalTheory`. -/
theorem maximal_endpoint_gt_of_finite_h2
    (H : ClassicalPeriodicLocalTheory)
    {ν : ℝ} (hν : 0 < ν) {a : Space → Space} {f : VelocityField}
    (hf : IsSmoothPeriodicForce f) (U : MaximalSolution ν a f)
    {S : ℝ} (hS : 0 < S) (W : Flow ν a f S)
    (hfinite : FiniteH2Energy W) :
    ENNReal.ofReal S < U.endpoint := by
  have hnot : ¬ lifespan ν a f ≤ ENNReal.ofReal S :=
    lifespan_not_le_of_finite_h2 H hν hf W hfinite
  have hnot' : ¬ U.endpoint ≤ ENNReal.ofReal S := by
    intro hle
    apply hnot
    simpa only [U.endpoint_eq_lifespan] using hle
  exact lt_of_not_ge hnot'

/-- Horizon restriction is transitive.  This fieldwise identity is the
restart invariant needed when a continuation witness is shortened in stages. -/
theorem Flow.restrict_restrict_eq_restrict
    {ν S R Q : ℝ} {a : Space → Space} {f : VelocityField}
    (W : Flow ν a f S) (hR : 0 < R) (hRS : R ≤ S)
    (hQ : 0 < Q) (hQR : Q ≤ R) :
    (W.restrict hR hRS).restrict hQ hQR = W.restrict hQ (hQR.trans hRS) := by
  rfl

end NSFormalization.Paper1.PeriodicLocalLifespan

