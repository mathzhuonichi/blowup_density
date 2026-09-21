import NSFormalization.Section3.T19.Threading
import NSFormalization.Section3.T19.Closure
import NSFormalization.Section3.T15.PlacementAt

/-! Theorem 3.6 (`03-torus.tex:199-207`): "Fix any nonempty coordinate ball.
For all sufficiently small ε > 0" the insertion has clauses (i)–(iv).
This construction preserves the prescribed centre and radius. -/
noncomputable section
namespace NSFormalization.Section3.T19
namespace At
open Set MeasureTheory Filter Topology Metric
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T15
open NSFormalization.Section3.T16 NSFormalization.Section3.T17 NSFormalization.Section3.T18
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open scoped ContDiff ENNReal

variable (center : Space) (radius : ℝ) (hρ : 0 < radius)
  (hcube : closure (Metric.ball center radius) ⊆ interior NSFormalization.Section3.T13.fundamentalCube)
variable {ν : ℝ} (hν : 0 < ν) {a : SpatialField} {g : SpaceTimeField}
  (ha : a ∈ initialClassT) (hg : g ∈ forceClassT) {T δ : ℝ}
  (hT : 0 < T) (hδ : 0 < δ) (reference : ClassicalSolutionT ν a g (T + δ))

def insertionDataAt : InsertionData := by
  let P := BlowupDensity.Bindings.packetImportFamily.select ν hν
  let place := placementDataAt (u := P.velocity) (p := P.pressure) center radius hρ hcube
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
    place (extendByZero reference).velocity (min (radius / 2) (1 / 4)) δ hν (lt_min (by positivity) (by norm_num))
    (lt_of_le_of_lt (min_le_right _ _) (by norm_num))
    hδ (extendByZero_periodic reference) (extendByZero_smooth reference)
    (fun t ht x _ => (extendByZero reference).divergence t ⟨ht.1.le, ht.2⟩ x)
    (fun t ht => P.velocity_support t ⟨ht.1.le, ht.2⟩)
    (ball_subset_ball ((min_le_left _ _).trans (by change radius / 2 ≤ radius; linarith)))
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
    r := min (radius / 2) (1 / 4)
    δ := δ
    D := Classical.choose hc
    reference := extendByZero reference
    correction := Classical.choice (Classical.choose_spec hc).2
    hδ := hδ
    hg := hg
    ha := ha }

theorem insertionDataAt_rawPremises : RawPremises (insertionDataAt center radius hρ hcube hν ha hg hT hδ reference) := by
  let P := BlowupDensity.Bindings.packetImportFamily.select ν hν
  refine ⟨P.velocity_support, ?_, ?_⟩
  · exact (Real.sqrt_nonneg _).trans (P.energy_isLUB.1 ⟨0, ⟨le_rfl, zero_lt_one⟩, rfl⟩)
  · change 0 ≤ P.dissipationBound
    rw [P.dissipation_eq]
    exact Real.sqrt_nonneg _

def insertionAt : PeriodicInsertionAPI (insertionDataAt center radius hρ hcube hν ha hg hT hδ reference) :=
  assemble _ (insertionDataAt_rawPremises center radius hρ hcube hν ha hg hT hδ reference)

local notation "ins" => insertionAt center radius hρ hcube hν ha hg hT hδ reference

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

theorem energyRate_zeroExtension : ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
    energyENormT T (fun z => (ins).velocity ε z - (extendByZero reference).velocity z) ≤
      ENNReal.ofReal (((BlowupDensity.Bindings.packetImportFamily.select ν hν).energyBound +
        (BlowupDensity.Bindings.packetImportFamily.select ν hν).dissipationBound) * ε ^ ((1 : ℝ) / 2) +
        (insertionDataAt center radius hρ hcube hν ha hg hT hδ reference).correction.energyConst * ε ^ ((3 : ℝ) / 2)) :=
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

/-- A periodic set contained in the chart has only its zero copy on the cube. -/
theorem periodicSet_inter_cube {S : Set Space}
    (hS : S ⊆ interior NSFormalization.Section3.T13.fundamentalCube) :
    periodicSet S ∩ NSFormalization.Section3.T13.fundamentalCube ⊆ S := by
  rintro x ⟨⟨k, hk⟩, hx⟩
  have hk0 : k = 0 := by
    by_contra hn
    have hI := NSFormalization.Section3.T13.interior_subset_fundamentalCubeInterior (hS hk)
    obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := Function.ne_iff.mp hn
    have hxi := hx i
    have hIi := hI i
    change 0 < x i - (k i : ℝ) ∧ x i - (k i : ℝ) < 1 at hIi
    rcases lt_or_gt_of_ne hi with hneg | hpos
    · have hz : (1 : ℤ) ≤ -k i := by omega
      have hz' : (1 : ℝ) ≤ -(k i : ℝ) := by exact_mod_cast hz
      linarith [hxi.2, hIi.2]
    · have hz : (1 : ℤ) ≤ k i := by omega
      have hz' : (1 : ℝ) ≤ (k i : ℝ) := by exact_mod_cast hz
      linarith [hxi.1, hIi.1]
  simpa only [hk0, NSFormalization.Section3.T16.latticeVector_zero, sub_zero] using hk

include hδ in
/-- Identify the zero extension on every relevant spatial slice. -/
theorem reference_slice (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) :
    (fun x => (extendByZero reference).velocity (t, x)) = reference.velocity ∘ (fun x => (t, x)) := by
  funext x
  exact extendByZero_velocity_eqOn reference ⟨⟨ht.1, by linarith [ht.2]⟩, mem_univ x⟩

theorem history : ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀, ∀ t : ℝ, 0 ≤ t →
    t ≤ T - 2 * ε ^ 2 → ∀ x : Space,
      (ins).velocity ε (t, x) = reference.velocity (t, x) := by
  intro ε hε t ht htT x
  have ht' : t ∈ Ico (0 : ℝ) T := ⟨ht, by nlinarith [sq_pos_of_pos hε.1]⟩
  exact ((ins).history ε hε t ht htT x).trans
    (congrFun (reference_slice hδ reference t ht') x)

theorem velocityDifference_divFree : ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
      spatialDivergence (fun z => (ins).velocity ε z - reference.velocity z) t x = 0 := by
  intro ε hε t ht x
  have h := (ins).velocityDifference_divFree ε hε t ht x
  change spatialDivergence
    (fun z => (ins).velocity ε z - (extendByZero reference).velocity z) t x = 0 at h
  simpa only [spatialDivergence, spatialDerivative, show ∀ y, (extendByZero reference).velocity (t, y) = reference.velocity (t, y) from
      fun y => congrFun (reference_slice hδ reference t ht) y,
    Function.comp_apply] using h

theorem diffSupport_in_chart : ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
    ball center (ε * (ins).diffSupportRadius) ⊆ ball center radius :=
  (ins).diffSupport_in_chart

/-- Clause (iii) in a single fundamental chart; its radius is ε times a fixed constant. -/
theorem velocityDifference_support : ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
    ∀ t ∈ Ico (0 : ℝ) T,
      tsupport (fun x : Space => (ins).velocity ε (t, x) - reference.velocity (t, x)) ∩
        NSFormalization.Section3.T13.fundamentalCube ⊆
          ball center (ε * (ins).diffSupportRadius) := by
  intro ε hε t ht x hx
  apply periodicSet_inter_cube
    (((ins).diffSupport_in_chart ε hε).trans (subset_closure.trans hcube))
  refine ⟨(ins).velocityDifference_support ε hε t ht ?_, hx.2⟩
  change x ∈ tsupport (fun y => (ins).velocity ε (t, y) - (extendByZero reference).velocity (t, y))
  simpa only [show ∀ y, (extendByZero reference).velocity (t, y) = reference.velocity (t, y) from
      fun y => congrFun (reference_slice hδ reference t ht) y, Function.comp_apply] using hx.1

theorem energyRate : ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
    energyENormT T (fun z => (ins).velocity ε z - reference.velocity z) ≤
      ENNReal.ofReal (((BlowupDensity.Bindings.packetImportFamily.select ν hν).energyBound +
        (BlowupDensity.Bindings.packetImportFamily.select ν hν).dissipationBound) * ε ^ ((1 : ℝ) / 2) +
        (insertionDataAt center radius hρ hcube hν ha hg hT hδ reference).correction.energyConst * ε ^ ((3 : ℝ) / 2)) := by
  intro ε hε
  have heq : energyENormT T (fun z => (ins).velocity ε z - reference.velocity z) =
      energyENormT T (fun z => (ins).velocity ε z - (extendByZero reference).velocity z) := by
    apply energyENormT_congr_Ico
    intro z hz
    change (ins).velocity ε z - reference.velocity z =
      (ins).velocity ε z - (extendByZero reference).velocity z
    rw [extendByZero_velocity_eqOn reference
      (show z ∈ Ico (0 : ℝ) (T + δ) ×ˢ univ from
        ⟨⟨hz.1.1, by linarith [hz.1.2]⟩, hz.2⟩)]
  rw [heq]
  exact (ins).energyRate ε hε

include center radius hρ hcube hν ha hg hT in
/-- A regular reference admits an arbitrarily close force with exact lifespan T. -/
theorem exists_force_close_at (hreg : RegularThroughT ν a g T)
    (s : ℝ) (hs : s < 1 / 2) (r' : ℝ) (hr' : 0 < r') :
    ∃ f ∈ forceClassT, maximalLifespanT ν a f = ENNReal.ofReal T ∧
      forceSobolevENormT 1 s (fun z => f z - g z) < ENNReal.ofReal r' := by
  obtain ⟨δ, hδ, ⟨reference⟩⟩ := hreg
  let A := insertionAt center radius hρ hcube hν ha hg hT hδ reference
  have hc := forceDifference_sobolev_tendsto center radius hρ hcube hν ha hg hT hδ reference s hs
  have hd := hc.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hr'))
  have hw : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioc (0 : ℝ) A.ε₀ :=
    Ioc_mem_nhdsGT A.eps_pos
  obtain ⟨ε, hε, hclose⟩ := (hw.and hd).exists
  exact ⟨A.force ε, A.force_mem ε hε, A.lifespan ε hε, hclose⟩

end At

export At (insertionDataAt insertionDataAt_rawPremises insertionAt exists_force_close_at)
end NSFormalization.Section3.T19
