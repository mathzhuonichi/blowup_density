import Contracts.V1.Correction
import NSFormalization.Section4.I02.Energy
import NSFormalization.Section4.I03.Energy
import NSFormalization.Source.PacketScaling
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Prod

/-! # Subadditivity of the Section 4 energy norm `E_T`

`paper/sections/04-whole-space.tex:39-41` states eq:REclose,
`‖u_ε − v‖_{E_T} ≤ C ε^{1/2}`, and `04-whole-space.tex:55` proves it from
eq:packetEscale together with the correction estimate of lem:correction
"**by the triangle inequality**", the splitting being
`u_ε − v = w_ε + U_ε`.

This module supplies exactly that triangle inequality for the canonical norm
`BlowupDensity.Contracts.V1.Data.energyENorm`
(`01-introduction.tex:143` eq:Enorm,
`‖z‖_{E_T} = ‖z‖_{L^∞(0,T;L²)} + ‖∇z‖_{L²(0,T;L²)}`), summand by summand:

* `energyEssSup_add_le` — Minkowski in space, then `essSup` monotonicity;
* `spatialGradient_add` — additivity of the Frobenius gradient vector;
* `energyGradient_add_le` — Minkowski in space, then Minkowski in time;
* `energyENorm_add_le` — the combination, which is the display used at
  `04-whole-space.tex:55`.

The two summands the paper actually adds are `w_ε`, which is globally smooth
with compact support, and `U_ε` (`Contracts.V1.scaledPacket`, i.e.
`NSFormalization.Source.parabolicVelocity ε⁻¹ (T − ε²) x₀ (zeroPastField U)`),
which is only smooth on the open slab below the singular time — the packet
velocity it rescales is constrained only on `Ico 0 1 ×ˢ univ`, so nothing at all
is known about `U_ε` at times `≥ T`.  Every per-slice hypothesis above is
therefore quantified over `Ioo 0 T`, the only interval `E_T` looks at.
Sections 5 and 6 discharge those hypotheses for the two shapes:
`aemeasurable_eLpNorm_spatialGradient_of_contDiff` and
`aemeasurable_eLpNorm_spatialGradient_of_contDiffOn` for the time-measurability
clause, and the `..._slice_of_contDiff(On)` lemmas for the slice clauses.

Nothing here re-proves an estimate: every bound is the abstract triangle
inequality, so the module is safe to reuse wherever `E_T` is split.
-/

noncomputable section

namespace BlowupDensity.Bindings

open Set MeasureTheory Filter
open scoped ContDiff ENNReal Topology

/-! ## 1. The `L^∞_t L²_x` half -/

/-- eq:Enorm, first summand: `‖·‖_{L^∞(0,T;L²)}` is subadditive.  Minkowski in
space at each fixed time, then monotonicity of the essential supremum against
the two individual essential suprema. -/
theorem energyEssSup_add_le (T : ℝ) {z w : Contracts.V1.VelocityField}
    (hz : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      AEStronglyMeasurable (fun x : Contracts.V1.Space => z (t, x)) volume)
    (hw : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      AEStronglyMeasurable (fun x : Contracts.V1.Space => w (t, x)) volume) :
    Contracts.V1.Data.energyEssSup T (fun p => z p + w p) ≤
      Contracts.V1.Data.energyEssSup T z + Contracts.V1.Data.energyEssSup T w := by
  simp only [Contracts.V1.Data.energyEssSup]
  refine essSup_le_of_ae_le _ ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ENNReal.ae_le_essSup (μ := volume.restrict (Ioo (0 : ℝ) T))
      (fun t => eLpNorm (fun x : Contracts.V1.Space => z (t, x)) 2 volume),
    ENNReal.ae_le_essSup (μ := volume.restrict (Ioo (0 : ℝ) T))
      (fun t => eLpNorm (fun x : Contracts.V1.Space => w (t, x)) 2 volume)] with t ht h1 h2
  exact (eLpNorm_add_le (hz t ht) (hw t ht) (by norm_num)).trans (add_le_add h1 h2)

/-! ## 2. Additivity of the gradient vector -/

/-- eq:Enorm, second summand, pointwise: the Frobenius gradient three-vector of
a sum is the sum of the gradient three-vectors, wherever both slices are
differentiable. -/
theorem spatialGradient_add (t : ℝ) (x : Contracts.V1.Space) {z w : Contracts.V1.VelocityField}
    (hz : DifferentiableAt ℝ (fun y : Contracts.V1.Space => z (t, y)) x)
    (hw : DifferentiableAt ℝ (fun y : Contracts.V1.Space => w (t, y)) x) :
    Contracts.V1.Data.spatialGradient (fun p => z p + w p) t x =
      Contracts.V1.Data.spatialGradient z t x + Contracts.V1.Data.spatialGradient w t x := by
  have hd : fderiv ℝ (fun y : Contracts.V1.Space => z (t, y) + w (t, y)) x =
      fderiv ℝ (fun y : Contracts.V1.Space => z (t, y)) x +
        fderiv ℝ (fun y : Contracts.V1.Space => w (t, y)) x :=
    fderiv_add hz hw
  have key : (fun i : Fin 3 =>
        fderiv ℝ (fun y : Contracts.V1.Space => z (t, y) + w (t, y)) x
          (Contracts.V1.coordinateVector i)) =
      (fun i : Fin 3 => fderiv ℝ (fun y : Contracts.V1.Space => z (t, y)) x
          (Contracts.V1.coordinateVector i)) +
        fun i : Fin 3 => fderiv ℝ (fun y : Contracts.V1.Space => w (t, y)) x
          (Contracts.V1.coordinateVector i) := by
    funext i
    rw [hd]
    rfl
  exact congrArg (WithLp.toLp 2) key

/-! ## 3. The `L²_t Ḣ¹_x` half -/

/-- eq:Enorm, second summand: `‖∇·‖_{L²(0,T;L²)}` is subadditive.  Minkowski in
space at each fixed time turns the gradient of the sum into the sum of the two
spatial `L²` seminorms; Minkowski in time (`ENNReal.lintegral_Lp_add_le` at
`p = 2`) then separates them. -/
theorem energyGradient_add_le (T : ℝ) {z w : Contracts.V1.VelocityField}
    (hdz : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : Contracts.V1.Space,
      DifferentiableAt ℝ (fun y : Contracts.V1.Space => z (t, y)) x)
    (hdw : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : Contracts.V1.Space,
      DifferentiableAt ℝ (fun y : Contracts.V1.Space => w (t, y)) x)
    (hmz : ∀ t ∈ Set.Ioo (0 : ℝ) T, AEStronglyMeasurable
      (fun x : Contracts.V1.Space => Contracts.V1.Data.spatialGradient z t x) volume)
    (hmw : ∀ t ∈ Set.Ioo (0 : ℝ) T, AEStronglyMeasurable
      (fun x : Contracts.V1.Space => Contracts.V1.Data.spatialGradient w t x) volume)
    (haz : AEMeasurable (fun t => eLpNorm
      (fun x : Contracts.V1.Space => Contracts.V1.Data.spatialGradient z t x) 2 volume)
      (volume.restrict (Set.Ioo (0 : ℝ) T)))
    (haw : AEMeasurable (fun t => eLpNorm
      (fun x : Contracts.V1.Space => Contracts.V1.Data.spatialGradient w t x) 2 volume)
      (volume.restrict (Set.Ioo (0 : ℝ) T))) :
    Contracts.V1.Data.energyGradient T (fun p => z p + w p) ≤
      Contracts.V1.Data.energyGradient T z + Contracts.V1.Data.energyGradient T w := by
  have key : ∀ t ∈ Ioo (0 : ℝ) T,
      eLpNorm (fun x : Contracts.V1.Space =>
          Contracts.V1.Data.spatialGradient (fun p => z p + w p) t x) 2 volume ≤
        eLpNorm (fun x : Contracts.V1.Space => Contracts.V1.Data.spatialGradient z t x) 2 volume +
          eLpNorm (fun x : Contracts.V1.Space =>
            Contracts.V1.Data.spatialGradient w t x) 2 volume := by
    intro t ht
    have hpt : ∀ x : Contracts.V1.Space,
        Contracts.V1.Data.spatialGradient (fun p => z p + w p) t x =
          Contracts.V1.Data.spatialGradient z t x + Contracts.V1.Data.spatialGradient w t x :=
      fun x => spatialGradient_add t x (hdz t ht x) (hdw t ht x)
    calc eLpNorm (fun x : Contracts.V1.Space =>
            Contracts.V1.Data.spatialGradient (fun p => z p + w p) t x) 2 volume
        = eLpNorm (fun x : Contracts.V1.Space => Contracts.V1.Data.spatialGradient z t x +
            Contracts.V1.Data.spatialGradient w t x) 2 volume := by simp_rw [hpt]
      _ ≤ _ := eLpNorm_add_le (hmz t ht) (hmw t ht) (by norm_num)
  have hmono : (∫⁻ t in Ioo (0 : ℝ) T, (eLpNorm (fun x : Contracts.V1.Space =>
        Contracts.V1.Data.spatialGradient (fun p => z p + w p) t x) 2 volume) ^ (2 : ℝ)) ≤
      ∫⁻ t in Ioo (0 : ℝ) T,
        (eLpNorm (fun x : Contracts.V1.Space =>
            Contracts.V1.Data.spatialGradient z t x) 2 volume +
          eLpNorm (fun x : Contracts.V1.Space =>
            Contracts.V1.Data.spatialGradient w t x) 2 volume) ^ (2 : ℝ) := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact ENNReal.rpow_le_rpow (key t ht) (by norm_num)
  have hmink : (∫⁻ t in Ioo (0 : ℝ) T,
        (eLpNorm (fun x : Contracts.V1.Space =>
            Contracts.V1.Data.spatialGradient z t x) 2 volume +
          eLpNorm (fun x : Contracts.V1.Space =>
            Contracts.V1.Data.spatialGradient w t x) 2 volume) ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) ≤
      (∫⁻ t in Ioo (0 : ℝ) T, (eLpNorm (fun x : Contracts.V1.Space =>
          Contracts.V1.Data.spatialGradient z t x) 2 volume) ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) +
        (∫⁻ t in Ioo (0 : ℝ) T, (eLpNorm (fun x : Contracts.V1.Space =>
          Contracts.V1.Data.spatialGradient w t x) 2 volume) ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) := by
    have h := ENNReal.lintegral_Lp_add_le (p := (2 : ℝ)) haz haw (by norm_num)
    simpa [Pi.add_apply, one_div] using h
  simp only [Contracts.V1.Data.energyGradient]
  exact (ENNReal.rpow_le_rpow hmono (by norm_num)).trans hmink

/-! ## 4. The triangle inequality for `E_T` -/

/-- `04-whole-space.tex:55`: the triangle inequality for the Section 4 energy
norm `E_T` of eq:Enorm, which is what turns eq:packetEscale plus lem:correction
into eq:REclose along `u_ε − v = w_ε + U_ε`. -/
theorem energyENorm_add_le (T : ℝ) {z w : Contracts.V1.VelocityField}
    (hz : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      AEStronglyMeasurable (fun x : Contracts.V1.Space => z (t, x)) volume)
    (hw : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      AEStronglyMeasurable (fun x : Contracts.V1.Space => w (t, x)) volume)
    (hdz : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : Contracts.V1.Space,
      DifferentiableAt ℝ (fun y : Contracts.V1.Space => z (t, y)) x)
    (hdw : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : Contracts.V1.Space,
      DifferentiableAt ℝ (fun y : Contracts.V1.Space => w (t, y)) x)
    (hmz : ∀ t ∈ Set.Ioo (0 : ℝ) T, AEStronglyMeasurable
      (fun x : Contracts.V1.Space => Contracts.V1.Data.spatialGradient z t x) volume)
    (hmw : ∀ t ∈ Set.Ioo (0 : ℝ) T, AEStronglyMeasurable
      (fun x : Contracts.V1.Space => Contracts.V1.Data.spatialGradient w t x) volume)
    (haz : AEMeasurable (fun t => eLpNorm
      (fun x : Contracts.V1.Space => Contracts.V1.Data.spatialGradient z t x) 2 volume)
      (volume.restrict (Set.Ioo (0 : ℝ) T)))
    (haw : AEMeasurable (fun t => eLpNorm
      (fun x : Contracts.V1.Space => Contracts.V1.Data.spatialGradient w t x) 2 volume)
      (volume.restrict (Set.Ioo (0 : ℝ) T))) :
    Contracts.V1.Data.energyENorm T (fun p => z p + w p) ≤
      Contracts.V1.Data.energyENorm T z + Contracts.V1.Data.energyENorm T w := by
  simp only [Contracts.V1.Data.energyENorm]
  calc Contracts.V1.Data.energyEssSup T (fun p => z p + w p) +
        Contracts.V1.Data.energyGradient T (fun p => z p + w p)
      ≤ (Contracts.V1.Data.energyEssSup T z + Contracts.V1.Data.energyEssSup T w) +
        (Contracts.V1.Data.energyGradient T z + Contracts.V1.Data.energyGradient T w) :=
        add_le_add (energyEssSup_add_le T hz hw)
          (energyGradient_add_le T hdz hdw hmz hmw haz haw)
    _ = (Contracts.V1.Data.energyEssSup T z + Contracts.V1.Data.energyGradient T z) +
        (Contracts.V1.Data.energyEssSup T w + Contracts.V1.Data.energyGradient T w) :=
        add_add_add_comm _ _ _ _

/-! ## 5. Discharging the time-measurability hypothesis -/

/-- The spatial `L²` seminorm of a gradient slice, written as an explicit
`lintegral`, so that its measurability in time is a Tonelli statement. -/
theorem eLpNorm_spatialGradient_eq_lintegral (z : Contracts.V1.VelocityField) (t : ℝ) :
    eLpNorm (fun x : Contracts.V1.Space => Contracts.V1.Data.spatialGradient z t x) 2 volume =
      (∫⁻ x : Contracts.V1.Space,
        ‖Contracts.V1.Data.spatialGradient z t x‖ₑ ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) := by
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), h2, one_div]

/-- Wherever the field is `C^∞` as a function of spacetime, the *slice*
derivative `fderiv ℝ (z (t, ·)) x` is `C^∞` in `(t, x)` jointly.  This is the
crux of the two measurability lemmas below: `spatialGradient` is a fixed-time
derivative, so its joint regularity is not `ContDiff.fderiv_right`. -/
theorem contDiffAt_fderiv_slice {z : Contracts.V1.VelocityField}
    {p : Contracts.V1.SpaceTime} (hz : ContDiffAt ℝ ∞ z p) :
    ContDiffAt ℝ ∞ (fun q : Contracts.V1.SpaceTime =>
      fderiv ℝ (fun y : Contracts.V1.Space => z (q.1, y)) q.2) p := by
  have huc : ContDiffAt ℝ ∞ (Function.uncurry
      (fun (q : Contracts.V1.SpaceTime) (y : Contracts.V1.Space) => z (q.1, y))) (p, p.2) :=
    hz.comp₂ (f₁ := fun r : Contracts.V1.SpaceTime × Contracts.V1.Space => r.1.1)
      (f₂ := fun r : Contracts.V1.SpaceTime × Contracts.V1.Space => r.2)
      contDiffAt_fst.fst contDiffAt_snd
  exact huc.fderiv contDiffAt_snd (by simp)

/-- Continuity of the gradient three-vector in `(t, x)` follows from continuity
of the slice derivative, because assembling the three coordinate derivatives
into a `PiLp 2` vector is continuous. -/
theorem continuousAt_spatialGradient_of_fderiv {z : Contracts.V1.VelocityField}
    {p : Contracts.V1.SpaceTime}
    (h : ContinuousAt (fun q : Contracts.V1.SpaceTime =>
      fderiv ℝ (fun y : Contracts.V1.Space => z (q.1, y)) q.2) p) :
    ContinuousAt (fun q : Contracts.V1.SpaceTime =>
      Contracts.V1.Data.spatialGradient z q.1 q.2) p := by
  have hpi : ContinuousAt (fun q : Contracts.V1.SpaceTime =>
      (fun i : Fin 3 => fderiv ℝ (fun y : Contracts.V1.Space => z (q.1, y)) q.2
        (Contracts.V1.coordinateVector i))) p :=
    continuousAt_pi.2 fun i => h.clm_apply continuousAt_const
  exact ((PiLp.continuous_toLp 2 fun _ : Fin 3 => Contracts.V1.Space).continuousAt).comp hpi

/-- Joint continuity of the gradient three-vector for a globally smooth
field. -/
theorem continuous_spatialGradient_uncurry {z : Contracts.V1.VelocityField}
    (hz : ContDiff ℝ ∞ z) :
    Continuous (fun q : Contracts.V1.SpaceTime =>
      Contracts.V1.Data.spatialGradient z q.1 q.2) :=
  continuous_iff_continuousAt.2 fun _ =>
    continuousAt_spatialGradient_of_fderiv (contDiffAt_fderiv_slice hz.contDiffAt).continuousAt

/-- Joint continuity of the gradient three-vector on an open slab on which the
field is smooth. -/
theorem continuousOn_spatialGradient_uncurry {T : ℝ} {z : Contracts.V1.VelocityField}
    (hz : ContDiffOn ℝ ∞ z (Set.Iio T ×ˢ (Set.univ : Set Contracts.V1.Space))) :
    ContinuousOn (fun q : Contracts.V1.SpaceTime =>
        Contracts.V1.Data.spatialGradient z q.1 q.2)
      (Set.Iio T ×ˢ (Set.univ : Set Contracts.V1.Space)) := by
  have hopen : IsOpen (Set.Iio T ×ˢ (Set.univ : Set Contracts.V1.Space)) :=
    isOpen_Iio.prod isOpen_univ
  refine continuousOn_of_forall_continuousAt fun p hp => ?_
  exact continuousAt_spatialGradient_of_fderiv
    (contDiffAt_fderiv_slice (hz.contDiffAt (hopen.mem_nhds hp))).continuousAt

set_option linter.unusedVariables false in
/-- For a globally smooth compactly supported field.  Discharges the
`AEMeasurable` hypothesis of `energyGradient_add_le` for `w_ε`.  Compact support
is not used: joint continuity of the gradient already gives Tonelli
measurability of the time profile, and the hypothesis is kept only so that the
lemma applies verbatim to the correction as the paper produces it. -/
theorem aemeasurable_eLpNorm_spatialGradient_of_contDiff {z : Contracts.V1.VelocityField}
    (hz : ContDiff ℝ ∞ z) (hc : HasCompactSupport z) (μ : Measure ℝ) :
    AEMeasurable (fun t => eLpNorm
      (fun x : Contracts.V1.Space => Contracts.V1.Data.spatialGradient z t x) 2 volume) μ := by
  simp_rw [eLpNorm_spatialGradient_eq_lintegral]
  have hjoint : Measurable (fun q : Contracts.V1.SpaceTime =>
      ‖Contracts.V1.Data.spatialGradient z q.1 q.2‖ₑ ^ (2 : ℝ)) :=
    (ENNReal.continuous_rpow_const.comp
      (continuous_enorm.comp (continuous_spatialGradient_uncurry hz))).measurable
  have hinner : Measurable (fun t : ℝ => ∫⁻ x : Contracts.V1.Space,
      ‖Contracts.V1.Data.spatialGradient z t x‖ₑ ^ (2 : ℝ)) :=
    hjoint.lintegral_prod_right'
  exact (ENNReal.continuous_rpow_const.measurable.comp hinner).aemeasurable

/-- For a field smooth on the open slab below the singular time.  Discharges the
`AEMeasurable` hypothesis of `energyGradient_add_le` for
`U_ε = parabolicVelocity ε⁻¹ (T − ε²) x₀ (zeroPastField U)`, which is only
`ContDiffOn` there.  No support hypothesis is needed. -/
theorem aemeasurable_eLpNorm_spatialGradient_of_contDiffOn {T : ℝ}
    {z : Contracts.V1.VelocityField}
    (hz : ContDiffOn ℝ ∞ z (Set.Iio T ×ˢ (Set.univ : Set Contracts.V1.Space))) :
    AEMeasurable (fun t => eLpNorm
      (fun x : Contracts.V1.Space => Contracts.V1.Data.spatialGradient z t x) 2 volume)
      (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  simp_rw [eLpNorm_spatialGradient_eq_lintegral]
  have hsub : Ioo (0 : ℝ) T ×ˢ (univ : Set Contracts.V1.Space) ⊆
      Iio T ×ˢ (univ : Set Contracts.V1.Space) :=
    Set.prod_mono (fun _ ht => ht.2) (subset_refl _)
  have hprod : ((volume.restrict (Ioo (0 : ℝ) T)).prod (volume : Measure Contracts.V1.Space)) =
      (volume : Measure Contracts.V1.SpaceTime).restrict
        (Ioo (0 : ℝ) T ×ˢ (univ : Set Contracts.V1.Space)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hcont : ContinuousOn (fun q : Contracts.V1.SpaceTime =>
      ‖Contracts.V1.Data.spatialGradient z q.1 q.2‖ₑ ^ (2 : ℝ))
      (Ioo (0 : ℝ) T ×ˢ (univ : Set Contracts.V1.Space)) :=
    (ENNReal.continuous_rpow_const.comp continuous_enorm).comp_continuousOn
      ((continuousOn_spatialGradient_uncurry hz).mono hsub)
  have hjoint : AEMeasurable (fun q : Contracts.V1.SpaceTime =>
      ‖Contracts.V1.Data.spatialGradient z q.1 q.2‖ₑ ^ (2 : ℝ))
      ((volume.restrict (Ioo (0 : ℝ) T)).prod (volume : Measure Contracts.V1.Space)) := by
    rw [hprod]
    exact hcont.aemeasurable (measurableSet_Ioo.prod MeasurableSet.univ)
  exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hjoint.lintegral_prod_right'

/-! ## 6. Slice regularity of the two summands

The per-slice hypotheses of `energyENorm_add_le` follow from a single smoothness
assumption on each summand — global for `w_ε`, slab-local for `U_ε` — and these
lemmas take that step once so no caller repeats it. -/

/-- A field smooth on the open slab below `T` is smooth in every spatial slice
strictly before `T`.  This is
`NSFormalization.Section4.I03.slice_contDiff_of_slab`, named here in the
contract's vocabulary. -/
theorem contDiff_slice_of_contDiffOn {T : ℝ} {z : Contracts.V1.VelocityField}
    (hz : ContDiffOn ℝ ∞ z (Set.Iio T ×ˢ (Set.univ : Set Contracts.V1.Space)))
    {t : ℝ} (ht : t < T) :
    ContDiff ℝ ∞ (fun y : Contracts.V1.Space => z (t, y)) :=
  NSFormalization.Section4.I03.slice_contDiff_of_slab hz ht

/-- The gradient three-vector of a smooth spatial slice is continuous in space.
The slice form of `NSFormalization.Section4.I02.continuous_spatialGradient`,
which assumes global smoothness that `U_ε` does not have. -/
theorem continuous_spatialGradient_slice {z : Contracts.V1.VelocityField} {t : ℝ}
    (hs : ContDiff ℝ ∞ (fun y : Contracts.V1.Space => z (t, y))) :
    Continuous (fun x : Contracts.V1.Space => Contracts.V1.Data.spatialGradient z t x) := by
  have hd : Continuous (fun x : Contracts.V1.Space =>
      fderiv ℝ (fun y : Contracts.V1.Space => z (t, y)) x) :=
    (hs.fderiv_right (m := ∞) (by simp)).continuous
  have hpi : Continuous (fun x : Contracts.V1.Space =>
      (fun i : Fin 3 => fderiv ℝ (fun y : Contracts.V1.Space => z (t, y)) x
        (Contracts.V1.coordinateVector i))) :=
    continuous_pi fun i => hd.clm_apply continuous_const
  exact (PiLp.continuous_toLp 2 fun _ : Fin 3 => Contracts.V1.Space).comp hpi

/-- Slice differentiability of a globally smooth field: the `hdz`/`hdw` clause
of `energyGradient_add_le` for `w_ε`. -/
theorem differentiableAt_slice_of_contDiff {z : Contracts.V1.VelocityField}
    (hz : ContDiff ℝ ∞ z) (t : ℝ) (x : Contracts.V1.Space) :
    DifferentiableAt ℝ (fun y : Contracts.V1.Space => z (t, y)) x :=
  (((hz.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)) x)

/-- Slice measurability of a globally smooth field: the `hz`/`hw` clause of
`energyENorm_add_le` for `w_ε`. -/
theorem aestronglyMeasurable_slice_of_contDiff {z : Contracts.V1.VelocityField}
    (hz : ContDiff ℝ ∞ z) (t : ℝ) :
    AEStronglyMeasurable (fun x : Contracts.V1.Space => z (t, x)) volume :=
  ((hz.comp (contDiff_const.prodMk contDiff_id)).continuous).aestronglyMeasurable

/-- Slice measurability of the gradient of a globally smooth field: the
`hmz`/`hmw` clause of `energyGradient_add_le` for `w_ε`. -/
theorem aestronglyMeasurable_spatialGradient_slice_of_contDiff
    {z : Contracts.V1.VelocityField} (hz : ContDiff ℝ ∞ z) (t : ℝ) :
    AEStronglyMeasurable
      (fun x : Contracts.V1.Space => Contracts.V1.Data.spatialGradient z t x) volume :=
  (continuous_spatialGradient_slice
    (hz.comp (contDiff_const.prodMk contDiff_id))).aestronglyMeasurable

/-- Slice differentiability below the slab time: the `hdz`/`hdw` clause of
`energyGradient_add_le` for `U_ε`. -/
theorem differentiableAt_slice_of_contDiffOn {T : ℝ} {z : Contracts.V1.VelocityField}
    (hz : ContDiffOn ℝ ∞ z (Set.Iio T ×ˢ (Set.univ : Set Contracts.V1.Space)))
    {t : ℝ} (ht : t < T) (x : Contracts.V1.Space) :
    DifferentiableAt ℝ (fun y : Contracts.V1.Space => z (t, y)) x :=
  ((contDiff_slice_of_contDiffOn hz ht).differentiable (by simp)) x

/-- Slice measurability below the slab time: the `hz`/`hw` clause of
`energyENorm_add_le` for `U_ε`. -/
theorem aestronglyMeasurable_slice_of_contDiffOn {T : ℝ} {z : Contracts.V1.VelocityField}
    (hz : ContDiffOn ℝ ∞ z (Set.Iio T ×ˢ (Set.univ : Set Contracts.V1.Space)))
    {t : ℝ} (ht : t < T) :
    AEStronglyMeasurable (fun x : Contracts.V1.Space => z (t, x)) volume :=
  (contDiff_slice_of_contDiffOn hz ht).continuous.aestronglyMeasurable

/-- Slice measurability of the gradient below the slab time: the `hmz`/`hmw`
clause of `energyGradient_add_le` for `U_ε`. -/
theorem aestronglyMeasurable_spatialGradient_slice_of_contDiffOn {T : ℝ}
    {z : Contracts.V1.VelocityField}
    (hz : ContDiffOn ℝ ∞ z (Set.Iio T ×ˢ (Set.univ : Set Contracts.V1.Space)))
    {t : ℝ} (ht : t < T) :
    AEStronglyMeasurable
      (fun x : Contracts.V1.Space => Contracts.V1.Data.spatialGradient z t x) volume :=
  (continuous_spatialGradient_slice (contDiff_slice_of_contDiffOn hz ht)).aestronglyMeasurable

end BlowupDensity.Bindings
