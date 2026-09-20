import NSFormalization.Section3.T15.HaarBridge
import NSFormalization.Section3.T17.Transport
import NSFormalization.Paper1.InsertionEnergy

/-!
# T17, unit U9: the torus energy bound `‖w_ε‖_{E_T} ≤ C ε^{3/2}` and its two
honest `MemLp` slice guards

`research/T17/T17_SPLIT.md` unit U9 targets the four `CorrectionAPI` fields
`correction_slice_memLp`, `correction_gradient_memLp`, `energyConst`
(+ `energyConst_nonneg`) and `correction_energy_bound`
(`Section3/T17/Correction.lean:223-241`, `research/T17/Spec.lean:900-920`).

## Route

The concrete correction is U2's `correctionData`, whose `correction ε` is by
construction the lattice lift of the single Euclidean copy
(`correctionData_correction`, `rfl`):

```
(correctionData v x₀ T θ η O θR ε₀).correction ε
  = latticeLift (physicalCorrection v x₀ T θ η ε)
```

Each spatial slice of a lattice lift is *definitionally* T13's spatial
periodization of the corresponding slice of the single copy
(`correction_slice_eq`, `rfl`: `latticeVector` agrees on the nose with T16's,
and both sums range over `PeriodicFrequency`).  Since `physicalCorrection` is
supported in `ball x₀ (ε·θRadius) ⊆ ball x₀ r`, whose closure the placement
puts inside `interior fundamentalCube`, T15's U-TB1 Haar/Lebesgue bridges apply
slicewise and give the two norm identities of §3:

* `eLpNorm (torusLift (slice of w_ε)) 2 periodicTorusMeasure
    = eLpNorm (slice of the single copy) 2 volume`;
* the same with `spatialGradient` on both sides.

`energyENormT` and `Contracts.V1.Data.energyENorm` are built from exactly these
two quantities (an `essSup` over `Ioo 0 T` and an `∫⁻` over `Ioo 0 T`), so the
torus energy norm of `w_ε` is the whole-space energy norm of the single copy,
and the registered Section 4 bound (`I02.energyEssSup_le` / `I02.energyGradient_le`
over Paper1's `CorrectionEnergy.physicalCorrection_uniform_energy` and
`InsertionEnergy.correction_gradientSquare_bound`, the two theorems that
`verification/Bindings/Correction.lean:455-466` uses to discharge
`I02.correction_energy_bound`) transports verbatim.  The constant is the same
one the Section 4 binding registers:
`energyConst = √A + √D`, `A`, `D` the two Paper1 `ε³` constants.

The `MemLp` fields do not go through the bridges at all: the lift of a
continuous field is bounded on the (compact) torus, so §1 upgrades
`Paper1.memLp_torusLift` from `ℂ` to an arbitrary normed value type and both
fields follow from smoothness of `latticeLift` and continuity of its spatial
gradient.

## Premises

`hv : ContDiff ℝ ∞ v` is the documented G1 premise of
`research/T17/SPEC_ISSUES.md` (the canonical `CorrectionAPI` carries only
`reference_periodic`); it is needed here because Paper1's two Euclidean energy
bounds and `physical_smooth` are stated for a globally smooth reference.  The
only other placement premise beyond lane 425's cutoff block is
`hcube : closure (ball x₀ r) ⊆ interior fundamentalCube`, which is *not* a new
assumption: it is `place.chartBall_in_cube` composed with
`CorrectionAPI.ball_in_chart` (`research/T17/probes/energy_closes.lean`
derives it).

Every declaration below is fully proved: no incomplete tactic block, no new
logical assumption, no named input, no `set_option`.
-/

noncomputable section

namespace NSFormalization.Section3.T17

open Set MeasureTheory Metric
open NavierStokes NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (Coords toSpace)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13 (fundamentalCube periodize gradientENorm)
open NSFormalization.Section3.T15
open NSFormalization.Section3.T16
open NSFormalization.Section4.I02 (spatialGradient)
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField)
open NSFormalization.Paper1.CorrectionProfile (physicalCorrection)
open NSFormalization.Source.PhysicalRemoval (physical_support physical_smooth)
open scoped ContDiff ENNReal Topology BigOperators

/-! ## §1  `MemLp` of a torus lift, for an arbitrary value type

`NSFormalization.Paper1.memLp_torusLift` (`Paper1/TorusCube.lean:58`) is stated
only for `ℂ`-valued fields.  The two `MemLp` fields of U9 need `Space`-valued
and `WithLp 2 (Fin 3 → Space)`-valued lifts, so the same proof is repeated once
in the value-type-generic form.  The measurability step uses
`Continuous.comp_aestronglyMeasurable` instead of `Measurable.comp`, so no
`BorelSpace`/`SecondCountableTopology` assumption on the value type is
needed. -/

/-- The chart underlying `torusLift`: it is measurable into `Space`. -/
theorem measurable_torusChart :
    Measurable (fun z : PeriodicTorus =>
      toSpace ((UnitAddTorus.measurableEquivPiIoc (0 : Coords) z).val)) :=
  toSpace.continuous.measurable.comp
    (measurable_subtype_coe.comp (UnitAddTorus.measurableEquivPiIoc (0 : Coords)).measurable)

/-- Value-type-generic form of `Paper1.memLp_torusLift`: the torus lift of a
continuous field lies in every `L^q` of the Haar measure. -/
theorem memLp_torusLift_of_continuous {E : Type*} [NormedAddCommGroup E]
    {f : Space → E} (hf : Continuous f) (q : ℝ≥0∞) :
    MemLp (torusLift f) q periodicTorusMeasure := by
  obtain ⟨M, hM⟩ := ((isCompact_Icc : IsCompact (Icc (0 : Coords) 1)).image
    (hf.comp toSpace.continuous)).isBounded.exists_norm_le
  refine MemLp.of_bound
    (hf.comp_aestronglyMeasurable measurable_torusChart.aestronglyMeasurable) M
    (Filter.Eventually.of_forall (fun z => ?_))
  refine hM _ ⟨(UnitAddTorus.measurableEquivPiIoc (0 : Coords) z).val, ?_, rfl⟩
  constructor <;> intro i
  · exact ((UnitAddTorus.measurableEquivPiIoc (0 : Coords) z).property i).1.le
  · simpa using ((UnitAddTorus.measurableEquivPiIoc (0 : Coords) z).property i).2

/-! ## §2  The single-copy slice geometry -/

/-- Each spatial slice of the concrete correction is, definitionally, T13's
spatial periodization of the corresponding slice of the single Euclidean copy.
This is the structural fact the whole unit rests on. -/
theorem correction_slice_eq (v : SpaceTimeField) (x₀ : Space) (T : ℝ) (θ : Space → ℝ)
    (η : ℝ → ℝ) (O : Set Space) (θR ε₀ ε : ℝ) (t : ℝ) :
    (fun y : Space => (correctionData v x₀ T θ η O θR ε₀).correction ε (t, y))
      = periodize (fun y : Space => physicalCorrection v x₀ T θ η ε (t, y)) := rfl

/-- Every value of the single copy sits over the small ball; the shape required
by `latticeLift_smooth` and by `physical_support`'s slice form. -/
theorem physicalCorrection_slice_ball {v : SpaceTimeField} {x₀ : Space} {T : ℝ}
    {θ : Space → ℝ} {η : ℝ → ℝ} {θR ε : ℝ} (hε : 0 < ε)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR) (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (z : SpaceTime) : physicalCorrection v x₀ T θ η ε z ≠ 0 → z.2 ∈ ball x₀ (ε * θR) :=
  fun hz => (physical_support hε v x₀ T hθc hηc hθsupp hηsupp (subset_tsupport _ hz)).2

/-- The slice of the single copy is supported in the interior of the
fundamental cube: its support sits in `ball x₀ (ε·θRadius) ⊆ ball x₀ r`, whose
closure the placement puts inside the chart. -/
theorem physicalCorrection_slice_tsupport_cube {v : SpaceTimeField} {x₀ : Space} {T : ℝ}
    {θ : Space → ℝ} {η : ℝ → ℝ} {θR r ε : ℝ} (hε : 0 < ε)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR) (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hρ : ε * θR < r) (hcube : closure (ball x₀ r) ⊆ interior fundamentalCube) (t : ℝ) :
    tsupport (fun y : Space => physicalCorrection v x₀ T θ η ε (t, y))
      ⊆ interior fundamentalCube := by
  refine subset_trans (closure_mono ?_) hcube
  intro y hy
  exact ball_subset_ball hρ.le
    (physicalCorrection_slice_ball hε hθc hηc hθsupp hηsupp (t, y) hy)

/-! ## §3  The two Haar/Lebesgue norm identities -/

/-- The Haar `L²` norm of a torus slice of the periodized correction is the
whole-space `L²` norm of the same slice of the single Euclidean copy.
T15 U-TB1 `eLpNorm_torusLift_periodize`, applied slicewise. -/
theorem eLpNorm_torusLift_correction_slice {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ} (O : Set Space) {θR r ε₀ : ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR) (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hcube : closure (ball x₀ r) ⊆ interior fundamentalCube)
    {ε : ℝ} (hε : 0 < ε) (hρ : ε * θR < r) (t : ℝ) :
    eLpNorm (torusLift
        (fun x : Space => (correctionData v x₀ T θ η O θR ε₀).correction ε (t, x))) 2
        periodicTorusMeasure
      = eLpNorm (fun x : Space => physicalCorrection v x₀ T θ η ε (t, x)) 2 volume := by
  rw [correction_slice_eq v x₀ T θ η O θR ε₀ ε t]
  exact eLpNorm_torusLift_periodize _
    ((physical_smooth hv x₀ T ε hθ hη).comp (contDiff_const.prodMk contDiff_id))
    (physicalCorrection_slice_tsupport_cube hε hθc hηc hθsupp hηsupp hρ hcube t)

/-- The gradient companion: the Haar `L²` norm of the torus-lifted spatial
gradient of the periodized correction is the whole-space `L²` norm of the
spatial gradient of the single Euclidean copy. -/
theorem eLpNorm_torusLift_correction_gradient {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ} (O : Set Space) {θR r ε₀ : ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR) (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hcube : closure (ball x₀ r) ⊆ interior fundamentalCube)
    {ε : ℝ} (hε : 0 < ε) (hρ : ε * θR < r) (t : ℝ) :
    eLpNorm (torusLift (fun x : Space =>
        spatialGradient ((correctionData v x₀ T θ η O θR ε₀).correction ε) t x)) 2
        periodicTorusMeasure
      = eLpNorm (fun x : Space =>
          spatialGradient (physicalCorrection v x₀ T θ η ε) t x) 2 volume := by
  have hslice : ContDiff ℝ ∞ (fun y : Space => physicalCorrection v x₀ T θ η ε (t, y)) :=
    (physical_smooth hv x₀ T ε hθ hη).comp (contDiff_const.prodMk contDiff_id)
  have hsupp := physicalCorrection_slice_tsupport_cube (v := v) (T := T)
    hε hθc hηc hθsupp hηsupp hρ hcube t
  calc eLpNorm (torusLift (fun x : Space =>
          spatialGradient ((correctionData v x₀ T θ η O θR ε₀).correction ε) t x)) 2
        periodicTorusMeasure
      = eLpNorm (torusLift (fun x : Space =>
          spatialGradient
            (fun p : SpaceTime =>
              periodize (fun y : Space => physicalCorrection v x₀ T θ η ε (t, y)) p.2)
            t x)) 2 periodicTorusMeasure := rfl
    _ = gradientENorm (fun y : Space => physicalCorrection v x₀ T θ η ε (t, y)) volume :=
        eLpNorm_torusLift_spatialGradient_periodize _ hslice t hsupp
    _ = eLpNorm (fun x : Space =>
          spatialGradient (physicalCorrection v x₀ T θ η ε) t x) 2 volume :=
        (eLpNorm_gradientVector_eq_gradientENorm hslice volume).symm

/-! ## §4  The two honest slice fields -/

/-- Smoothness of the concrete correction, from `latticeLift_smooth`. -/
theorem correction_contDiff {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ} (O : Set Space) {θR ε₀ : ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR) (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ ((correctionData v x₀ T θ η O θR ε₀).correction ε) := by
  rw [correctionData_correction]
  exact latticeLift_smooth (physical_smooth hv x₀ T ε hθ hη)
    (physicalCorrection_slice_ball hε hθc hηc hθsupp hηsupp)

/-- `Spec.lean:902` / `Correction.lean:223`: every torus slice of `w_ε` is an
honest Haar-`L²` element, so `energyEssSupT`'s inner norm is a genuine `L²`
norm and not a lower integral. -/
theorem correction_slice_memLp {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ} (O : Set Space) (θR ε₀ : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR) (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2) :
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀, ∀ t : ℝ,
      MemLp (torusLift
          (fun x : Space => (correctionData v x₀ T θ η O θR ε₀).correction ε (t, x))) 2
        periodicTorusMeasure := by
  intro ε hε t
  refine memLp_torusLift_of_continuous ?_ 2
  exact (correction_contDiff hv x₀ T O hθ hη hθc hηc hθsupp hηsupp hε.1).continuous.comp
    (continuous_const.prodMk continuous_id)

/-- `Spec.lean:906` / `Correction.lean:227`: every torus slice of `∇w_ε` is an
honest Haar-`L²` element, the second honesty guard of `energyENormT`. -/
theorem correction_gradient_memLp {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ} (O : Set Space) (θR ε₀ : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR) (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2) :
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀, ∀ t : ℝ,
      MemLp (torusLift (fun x : Space =>
          spatialGradient ((correctionData v x₀ T θ η O θR ε₀).correction ε) t x)) 2
        periodicTorusMeasure := by
  intro ε hε t
  exact memLp_torusLift_of_continuous
    (NSFormalization.Section4.I02.continuous_spatialGradient
      (correction_contDiff hv x₀ T O hθ hη hθc hηc hθsupp hηsupp hε.1) t) 2

/-! ## §5  The constant and the bound -/

/-- `03-torus.tex:234,242`: the energy constant of `eq:wE`, fixed before `ε`.
It is the constant the Section 4 binding registers for
`I02.correction_energy_bound` (`verification/Bindings/Correction.lean:349`):
the sum of the square roots of Paper1's two `ε³` constants, the uniform
`L²` energy constant and the time-integrated gradient constant. -/
def energyConst {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T : ℝ)
    {θ : Space → ℝ} {η : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) : ℝ :=
  Real.sqrt (Classical.choose
      (NSFormalization.Paper1.CorrectionEnergy.physicalCorrection_uniform_energy
        hv x₀ T hθ hη hθc hηc)) +
    Real.sqrt (Classical.choose
      (NSFormalization.Paper1.InsertionEnergy.correction_gradientSquare_bound
        hv x₀ T hθ hη hθc hηc))

/-- `03-torus.tex:234,242`: the energy constant is nonnegative, so the
`ENNReal.ofReal` on the right of `eq:wE` cannot hide a negative witness. -/
theorem energyConst_nonneg {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T : ℝ)
    {θ : Space → ℝ} {η : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) :
    0 ≤ energyConst hv x₀ T hθ hη hθc hηc :=
  add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- `03-torus.tex:234`, `eq:wE`: `‖w_ε‖_{E_T} ≤ C ε^{3/2}` in T10's torus
energy norm, for the concrete periodized correction.

Both summands of `energyENormT` are identified slicewise with the corresponding
summands of the whole-space `Contracts.V1.Data.energyENorm` of the single
Euclidean copy (§3), where the registered Section 4 bound applies. -/
theorem correction_energy_bound {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ} (O : Set Space) {θR r ε₀ : ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR) (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hcube : closure (ball x₀ r) ⊆ interior fundamentalCube)
    (hε₀ : ε₀ ≤ 1) (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r) :
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
      energyENormT T ((correctionData v x₀ T θ η O θR ε₀).correction ε) ≤
        ENNReal.ofReal (energyConst hv x₀ T hθ hη hθc hηc * ε ^ ((3 : ℝ) / 2)) := by
  intro ε hε
  have hAspec := Classical.choose_spec
    (NSFormalization.Paper1.CorrectionEnergy.physicalCorrection_uniform_energy
      hv x₀ T hθ hη hθc hηc)
  have hDspec := Classical.choose_spec
    (NSFormalization.Paper1.InsertionEnergy.correction_gradientSquare_bound
      hv x₀ T hθ hη hθc hηc)
  set A := Classical.choose
    (NSFormalization.Paper1.CorrectionEnergy.physicalCorrection_uniform_energy
      hv x₀ T hθ hη hθc hηc) with hAdef
  set D := Classical.choose
    (NSFormalization.Paper1.InsertionEnergy.correction_gradientSquare_bound
      hv x₀ T hθ hη hθc hηc) with hDdef
  obtain ⟨hA, hAb⟩ := hAspec
  obtain ⟨hD, hDb⟩ := hDspec
  have hεIoc : ε ∈ Ioc (0 : ℝ) 1 := ⟨hε.1, hε.2.trans hε₀⟩
  have hρ : ε * θR < r := hεspace ε hε
  have hWsm : ContDiff ℝ ∞ (physicalCorrection v x₀ T θ η ε) := physical_smooth hv x₀ T ε hθ hη
  have hWcs : HasCompactSupport (physicalCorrection v x₀ T θ η ε) :=
    NSFormalization.Source.PhysicalRemoval.physical_compact hε.1.ne' v x₀ T hθc hηc
  -- the `L^∞_t L²_x` half
  have hess : energyEssSupT T ((correctionData v x₀ T θ η O θR ε₀).correction ε)
      ≤ ENNReal.ofReal (Real.sqrt (A * ε ^ 3)) := by
    have hfun : (fun t : ℝ => eLpNorm (torusLift
          (fun x : Space => (correctionData v x₀ T θ η O θR ε₀).correction ε (t, x))) 2
          periodicTorusMeasure)
        = fun t : ℝ => eLpNorm (fun x : Space => physicalCorrection v x₀ T θ η ε (t, x)) 2
            volume := by
      funext t
      exact eLpNorm_torusLift_correction_slice hv x₀ T O hθ hη hθc hηc hθsupp hηsupp
        hcube hε.1 hρ t
    show essSup (fun t : ℝ => eLpNorm (torusLift
        (fun x : Space => (correctionData v x₀ T θ η O θR ε₀).correction ε (t, x))) 2
        periodicTorusMeasure) (volume.restrict (Ioo (0 : ℝ) T)) ≤ _
    rw [hfun]
    exact NSFormalization.Section4.I02.energyEssSup_le hWsm hWcs (fun t => hAb ε hεIoc t)
  -- the `L²_t Ḣ¹_x` half
  have hgrad : energyGradientT T ((correctionData v x₀ T θ η O θR ε₀).correction ε)
      ≤ ENNReal.ofReal (Real.sqrt (D * ε ^ 3)) := by
    have hfun : ∀ t : ℝ, eLpNorm (torusLift (fun x : Space =>
          spatialGradient ((correctionData v x₀ T θ η O θR ε₀).correction ε) t x)) 2
          periodicTorusMeasure
        = eLpNorm (fun x : Space =>
            spatialGradient (physicalCorrection v x₀ T θ η ε) t x) 2 volume :=
      fun t => eLpNorm_torusLift_correction_gradient hv x₀ T O hθ hη hθc hηc hθsupp hηsupp
        hcube hε.1 hρ t
    show (∫⁻ t in Ioo (0 : ℝ) T, (eLpNorm (torusLift (fun x : Space =>
        spatialGradient ((correctionData v x₀ T θ η O θR ε₀).correction ε) t x)) 2
        periodicTorusMeasure) ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) ≤ _
    simp_rw [hfun]
    exact NSFormalization.Section4.I02.energyGradient_le hWsm hWcs (hDb ε hεIoc).1
      (hDb ε hεIoc).2
  refine le_trans (add_le_add hess hgrad) (le_of_eq ?_)
  rw [← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
  congr 1
  rw [NSFormalization.Section4.I02.sqrt_mul_cube hA hε.1.le,
    NSFormalization.Section4.I02.sqrt_mul_cube hD hε.1.le, energyConst]
  ring

end NSFormalization.Section3.T17
