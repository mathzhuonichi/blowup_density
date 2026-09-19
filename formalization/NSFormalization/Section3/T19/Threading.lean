import NSFormalization.Section3.T18.Assembly
import NSFormalization.Section3.T15.Assembly
import NSFormalization.Section3.T17.SlabBridge2
import Bindings.PacketImport

/-! Construct the T18 insertion once from a regular classical reference.
The zero extension supplies the global periodicity required by T17 while
preserving every classical-solution field on its original lifespan. -/
noncomputable section
namespace NSFormalization.Section3.T19
open Set MeasureTheory Filter Topology Metric
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T15
open NSFormalization.Section3.T16 NSFormalization.Section3.T17 NSFormalization.Section3.T18
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open scoped ContDiff ENNReal

theorem zeroExtension_eventuallyEq {E : Type*} [Zero E] (v : SpaceTime → E)
    {S : ℝ} {z : SpaceTime} (hz : z.1 ∈ Ioo (0 : ℝ) S) :
    (fun y => if y.1 ∈ Ico (0 : ℝ) S then v y else 0) =ᶠ[𝓝 z] v := by
  filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (Ioo_mem_nhds hz.1 hz.2)] with y hy
  exact ite_eq_left ⟨hy.1.le, hy.2⟩

def extendByZero {ν S : ℝ} {a : SpatialField} {g : SpaceTimeField}
    (reference : ClassicalSolutionT ν a g S) : ClassicalSolutionT ν a g S where
  velocity := fun z => if z.1 ∈ Ico (0 : ℝ) S then reference.velocity z else 0
  pressure := fun z => if z.1 ∈ Ico (0 : ℝ) S then reference.pressure z else 0
  horizon_pos := reference.horizon_pos
  velocity_smooth := reference.velocity_smooth.congr (fun z hz => ite_eq_left hz.1)
  pressure_smooth := reference.pressure_smooth.congr (fun z hz => ite_eq_left hz.1)
  initial := by simpa only [ite_eq_left (show (0 : ℝ) ∈ Ico 0 S from ⟨le_rfl, reference.horizon_pos⟩)] using reference.initial
  divergence := by
    intro t ht x
    simpa only [spatialDivergence, spatialDerivative, ite_eq_left ht] using reference.divergence t ht x
  momentum := by
    intro t ht x
    exact (NSFormalization.Source.PacketScaling.residual_congr_local ν
      (zeroExtension_eventuallyEq reference.velocity (z := (t,x)) ht)
      (zeroExtension_eventuallyEq reference.pressure (z := (t,x)) ht)).trans (reference.momentum t ht x)
  sobolev := by
    intro m
    obtain ⟨G, hG, h⟩ := reference.sobolev m
    exact ⟨G, hG, fun t ht => by simpa only [ite_eq_left ht] using h t ht⟩
  pressure_gradient := by
    intro t ht
    simpa only [pressureGradient, ite_eq_left ht] using reference.pressure_gradient t ht
  velocity_periodic := by
    intro t ht x i
    simpa only [ite_eq_left ht] using reference.velocity_periodic t ht x i
  pressure_periodic := by
    intro t ht x i
    simpa only [ite_eq_left ht] using reference.pressure_periodic t ht x i
  pressure_gauge := by
    intro t ht
    simpa only [pressureMeanT, ite_eq_left ht] using reference.pressure_gauge t ht

theorem extendByZero_velocity_eqOn {ν S : ℝ} {a : SpatialField} {g : SpaceTimeField}
    (reference : ClassicalSolutionT ν a g S) :
    EqOn (extendByZero reference).velocity reference.velocity (Ico (0 : ℝ) S ×ˢ univ) :=
  fun _ hz => ite_eq_left hz.1

theorem extendByZero_periodic {ν S : ℝ} {a : SpatialField} {g : SpaceTimeField}
    (reference : ClassicalSolutionT ν a g S) :
    IsPeriodicOn univ (extendByZero reference).velocity := by
  intro t _ x i
  by_cases ht : t ∈ Ico (0 : ℝ) S
  · simpa only [extendByZero, ite_eq_left ht] using reference.velocity_periodic t ht x i
  · simp only [extendByZero, ite_eq_right ht]

theorem extendByZero_smooth {ν S : ℝ} {a : SpatialField} {g : SpaceTimeField}
    (reference : ClassicalSolutionT ν a g S) :
    ContDiffOn ℝ ∞ (extendByZero reference).velocity (Ioo (0 : ℝ) S ×ˢ univ) :=
  (extendByZero reference).velocity_smooth.mono (prod_mono Ioo_subset_Ico_self Subset.rfl)

variable {ν : ℝ} (hν : 0 < ν) {a : SpatialField} {g : SpaceTimeField}
  (ha : a ∈ initialClassT) (hg : g ∈ forceClassT) {T δ : ℝ}
  (hT : 0 < T) (hδ : 0 < δ) (reference : ClassicalSolutionT ν a g (T + δ))

def insertionData : InsertionData := by
  let P := BlowupDensity.Bindings.packetImportFamily.select ν hν
  let place := placementData (u := P.velocity) (p := P.pressure)
    P.carrier_compact P.force_support.1 T hT
  let scaling := scalingAPI
    (ν := ν)
    ⟨P.velocity_extension_smooth, P.carrier_compact, P.velocity_support,
      P.square_integrable, P.zero_initial_velocity, P.energy_isLUB,
      P.dissipation_integrable, P.dissipation_eq⟩
    P.pressure_support P.pressure_extension_smooth P.force_smooth P.force_support
    P.force_zero_nonpos P.extension_navier_stokes P.extension_divergence_free
    P.speed_unbounded place
  have hc := correctionStatementSlab'_holds ν P.velocity P.pressure P.force P.carrier
    place (extendByZero reference).velocity (1 / 4) δ hν (by norm_num) (by norm_num)
    hδ (extendByZero_periodic reference) (extendByZero_smooth reference)
    (fun t ht x _ => (extendByZero reference).divergence t ⟨ht.1.le, ht.2⟩ x)
    (fun t ht => P.velocity_support t ⟨ht.1.le, ht.2⟩)
    (ball_subset_ball (by change (1 / 4 : ℝ) ≤ 3 / 8; norm_num))
  exact {
    ν := ν
    packetVelocity := P.velocity
    packetPressure := P.pressure
    packetForce := P.force
    carrier := P.carrier
    energyBound := P.energyBound
    dissipationBound := P.dissipationBound
    place := place
    scaling := scaling
    a := a
    g := g
    r := 1 / 4
    δ := δ
    D := Classical.choose hc
    reference := extendByZero reference
    correction := Classical.choice (Classical.choose_spec hc).2
    hδ := hδ
    hg := hg
    ha := ha }

theorem insertionData_rawPremises : RawPremises (insertionData hν ha hg hT hδ reference) := by
  let P := BlowupDensity.Bindings.packetImportFamily.select ν hν
  refine ⟨P.velocity_support, ?_, ?_⟩
  · exact (Real.sqrt_nonneg _).trans (P.energy_isLUB.1 ⟨0, ⟨le_rfl, zero_lt_one⟩, rfl⟩)
  · change 0 ≤ P.dissipationBound
    rw [P.dissipation_eq]
    exact Real.sqrt_nonneg _

def insertion : PeriodicInsertionAPI (insertionData hν ha hg hT hδ reference) :=
  assemble _ (insertionData_rawPremises hν ha hg hT hδ reference)

local notation "ins" => insertion hν ha hg hT hδ reference

theorem insertion_eps_pos : 0 < (ins).ε₀ :=
  (ins).eps_pos

theorem force_mem : ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀, (ins).force ε ∈ forceClassT :=
  (ins).force_mem

theorem forceDifference_mem : ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
    (fun z => (ins).force ε z - g z) ∈ forceClassT :=
  (ins).forceDifference_mem

theorem lifespan : ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
    maximalLifespanT ν a ((ins).force ε) = ENNReal.ofReal T :=
  (ins).lifespan

theorem solution : ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
    ∃ w : ClassicalSolutionT ν a ((ins).force ε) T,
      w.velocity = (ins).velocity ε ∧ w.pressure = (ins).pressure ε :=
  (ins).solution

theorem blowup_limsup : ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
    NSFormalization.Section4.A02.limsupLeft T
        (fun t => NSFormalization.Section4.A02.speedENorm
          (fun x : Space => (ins).velocity ε (t, x))) = ⊤ :=
  (ins).blowup_limsup

theorem energyRate : ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
    energyENormT T (fun z => (ins).velocity ε z - (extendByZero reference).velocity z) ≤
      ENNReal.ofReal (((BlowupDensity.Bindings.packetImportFamily.select ν hν).energyBound +
        (BlowupDensity.Bindings.packetImportFamily.select ν hν).dissipationBound) * ε ^ ((1 : ℝ) / 2) +
        (insertionData hν ha hg hT hδ reference).correction.energyConst * ε ^ ((3 : ℝ) / 2)) :=
  (ins).energyRate

theorem forceDiffMixedConst_nonneg : ∀ (p q : ℝ≥0∞), 1 ≤ p → 1 ≤ q →
    0 ≤ (ins).forceDiffMixedConst p q :=
  (ins).forceDiffMixedConst_nonneg

theorem forceDifference_mixed_memLp : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
      MemMixedLebesgueT q p (fun z => (ins).force ε z - g z) :=
  (ins).forceDifference_mixed_memLp

theorem forceDifference_mixed_bound : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
      mixedLebesgueENormT q p (fun z => (ins).force ε z - g z) ≤
        ENNReal.ofReal ((ins).forceDiffMixedConst p q *
          (ε ^ (alphaT p q) +
            ε ^ (alphaT p q + 1))) :=
  (ins).forceDifference_mixed_bound

theorem forceDiffSobolevConst_pos : ∀ s : ℝ, 0 ≤ s → s < 1 / 2 →
    0 < (ins).forceDiffSobolevConst s :=
  (ins).forceDiffSobolevConst_pos

theorem forceDifference_sobolev_memLp : ∀ s : ℝ, 0 ≤ s → s < 1 / 2 →
    ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
      MemForceSobolevT 1 s (fun z => (ins).force ε z - g z) :=
  (ins).forceDifference_sobolev_memLp

theorem forceDifference_sobolev_bound : ∀ s : ℝ, 0 ≤ s → s < 1 / 2 →
    ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
      forceSobolevENormT 1 s (fun z => (ins).force ε z - g z) ≤
        ENNReal.ofReal ((ins).forceDiffSobolevConst s *
          (ε ^ ((1 : ℝ) / 2 - s) + ε ^ ((3 : ℝ) / 2 - s))) :=
  (ins).forceDifference_sobolev_bound

theorem forceDifference_negativeSobolev_tendsto : ∀ s : ℝ, s < 0 →
    Tendsto (fun ε : ℝ => forceSobolevENormT 1 s (fun z => (ins).force ε z - g z))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) :=
  (ins).forceDifference_negativeSobolev_tendsto

theorem negative_s_memLp : ∀ s : ℝ, s < 0 →
    ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
      MemForceSobolevT 1 s (fun z => (ins).force ε z - g z) :=
  (ins).negative_s_memLp

/-- One subcritical limit, shared by the density and trajectory routes. -/
theorem forceDifference_sobolev_tendsto (s : ℝ) (hs : s < 1 / 2) :
    Tendsto (fun ε : ℝ => forceSobolevENormT 1 s (fun z => (ins).force ε z - g z))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
  by_cases hs0 : s < 0
  · exact (ins).forceDifference_negativeSobolev_tendsto s hs0
  have hupper : Tendsto
      (fun ε : ℝ => ENNReal.ofReal ((ins).forceDiffSobolevConst s *
        (ε ^ ((1 : ℝ) / 2 - s) + ε ^ ((3 : ℝ) / 2 - s))))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    have hr := (NSFormalization.Paper1.sobolev_error_tendsto_zero
      s ((ins).forceDiffSobolevConst s) hs).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Eventually.of_forall (fun _ => bot_le)
  · filter_upwards [Ioc_mem_nhdsGT (ins).eps_pos] with ε hε
    exact (ins).forceDifference_sobolev_bound s (le_of_not_gt hs0) hs ε hε

include hν ha hg hT in
/-- A regular reference admits an arbitrarily close force with exact lifespan T. -/
theorem exists_force_close (hreg : RegularThroughT ν a g T)
    (s : ℝ) (hs : s < 1 / 2) (r' : ℝ) (hr' : 0 < r') :
    ∃ f ∈ forceClassT, maximalLifespanT ν a f = ENNReal.ofReal T ∧
      forceSobolevENormT 1 s (fun z => f z - g z) < ENNReal.ofReal r' := by
  obtain ⟨δ, hδ, ⟨reference⟩⟩ := hreg
  let A := insertion hν ha hg hT hδ reference
  have hc := forceDifference_sobolev_tendsto hν ha hg hT hδ reference s hs
  have hd := hc.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hr'))
  have hw : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioc (0 : ℝ) A.ε₀ :=
    Ioc_mem_nhdsGT A.eps_pos
  obtain ⟨ε, hε, hclose⟩ := (hw.and hd).exists
  exact ⟨A.force ε, A.force_mem ε hε, A.lifespan ε hε, hclose⟩

end NSFormalization.Section3.T19
