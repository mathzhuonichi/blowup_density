import NSFormalization.Section3.T13.ConstantEndpoints
import NSFormalization.Section3.T13.TorusIdentity
import NSFormalization.Section4.I02.Energy

/-!
# T15 U-TB1: the energy Haar/Lebesgue single-copy bridges

This module proves the "single copy of the support" `L²` identities that move a
Haar norm on the unit three-torus to a whole-space Lebesgue norm, for the
periodization of a field supported inside the fundamental cube.  These are the
`missing T10` bridges flagged in `research/T15/T15_SPLIT.md` unit U-TB1.

The core is a *measure-free change of variables*
(`eLpNorm_torusLift_restrict`): for **any** `g : Space → F` (no regularity, no
measurability),
`eLpNorm (torusLift g) 2 periodicTorusMeasure = eLpNorm g 2 (volume.restrict fundamentalCube)`.
Its only inputs are Mathlib's proved `UnitAddTorus.lintegral_preimage` (Haar on
`T³` unfolds to Lebesgue on the `Ioc`-box), `torusLift_coe`
(`NSFormalization.Paper1.TorusCube`), and the volume-preserving chart
`toSpace` with `T13.TorusIdentity.toSpace_preimage_fundamentalCube`.

On top of it:

* `eLpNorm_torusLift_periodize` (Goal 1) composes the bridge with the single-copy
  identity `periodize f = f` on the closed cube.  It only needs
  `tsupport f ⊆ interior fundamentalCube` — smoothness is unused, kept as a
  hypothesis so the statement matches the T15 spec interface.
* `eLpNorm_torusLift_spatialGradient_periodize` (Goal 2) is the gradient
  companion, identifying the `energyGradientT`-style norm
  `eLpNorm (torusLift (fun x ↦ spatialGradient _ t x)) 2 periodicTorusMeasure`
  with `T13`'s `gradientENorm f volume`.  The regularity of `periodize f` is
  never used: the bridge is measure-free, and `periodize f`'s gradient is
  replaced a.e. on the cube by that of `f` (they differ only on the null
  frontier), whose norm reduces to `gradientENorm f`.
* `eLpNorm_torusLift_periodize_slice` (Goal 3) is the time-slice corollary of
  Goal 1 used by the `energyEssSupT` datum.

Everything reuses the T13 vocabulary (`fundamentalCube`, `periodize`,
`gradientENorm`, `interior_fundamentalCube`, `volume_frontier_fundamentalCube`,
`fderiv_eq_zero_of_notMem_tsupport`) and I02's `spatialGradient`; the two
interior-hypothesis single-copy helpers below generalise the ball-hypothesis
`T13.eq_zero_of_mem_cube` / `T13.periodize_eventuallyEq`.  No `sorry`, no named
input, no new mathematical alias.
-/

noncomputable section

namespace NSFormalization.Section3.T15

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section4.I02 (spatialGradient)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open NavierStokes.PeriodicIntegration (Coords toSpace cubeIntegral)
open scoped ContDiff ENNReal BigOperators Topology

/-! ## §1  The measure-free Haar/Lebesgue change of variables -/

/-- Haar integration on `T³` of the extended-real power of the enorm of a lift
equals Lebesgue integration of the same power over the fundamental cube.  This
holds for *every* field `g` (no measurability): it is Mathlib's proved torus
fundamental-domain change of variables `UnitAddTorus.lintegral_preimage`
followed by the volume-preserving chart `toSpace`. -/
theorem lintegral_enorm_torusLift {F : Type*} [NormedAddCommGroup F]
    (g : Space → F) (q : ℝ) :
    ∫⁻ z : PeriodicTorus, ‖torusLift g z‖ₑ ^ q ∂periodicTorusMeasure
      = ∫⁻ x in fundamentalCube, ‖g x‖ₑ ^ q ∂volume := by
  rw [UnitAddTorus.lintegral_preimage (fun z => ‖torusLift g z‖ₑ ^ q) (0 : Coords)]
  have hmp : MeasurePreserving (toSpace : Coords → Space) volume volume :=
    PiLp.volume_preserving_toLp (Fin 3)
  have hemb : MeasurableEmbedding (toSpace : Coords → Space) :=
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding
  rw [← hmp.setLIntegral_comp_preimage_emb hemb (fun x => ‖g x‖ₑ ^ q) fundamentalCube,
    toSpace_preimage_fundamentalCube]
  have hbox : {y : Coords | ∀ i, y i ∈ Ioc ((0 : Coords) i) ((0 : Coords) i + 1)}
      = Set.univ.pi (fun _ : Fin 3 => Ioc (0 : ℝ) 1) := by
    ext y; simp
  rw [hbox,
    setLIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)
      (fun y hy => congrArg (fun a => ‖a‖ₑ ^ q)
        (NSFormalization.Paper1.torusLift_coe g y (fun i => hy i (Set.mem_univ i))))]
  exact setLIntegral_congr Measure.univ_pi_Ioc_ae_eq_Icc

/-- The energy Haar/Lebesgue bridge in `eLpNorm` form, for an arbitrary field. -/
theorem eLpNorm_torusLift_restrict {F : Type*} [NormedAddCommGroup F] (g : Space → F) :
    eLpNorm (torusLift g) 2 periodicTorusMeasure
      = eLpNorm g 2 (volume.restrict fundamentalCube) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    lintegral_enorm_torusLift g ((2 : ℝ≥0∞).toReal)]

/-! ## §2  Interior-hypothesis single-copy helpers

These generalise `T13.eq_zero_of_mem_cube` / `T13.periodize_eq_of_mem_cube` /
`T13.periodize_eventuallyEq` from the ball hypothesis to the weaker
`tsupport f ⊆ interior fundamentalCube`. -/

/-- On the closed fundamental cube the periodization is the zero extension
itself, under the weaker hypothesis `tsupport f ⊆ interior fundamentalCube`. -/
theorem periodize_eq_of_mem_interior {f : SpatialField}
    (hsupp : tsupport f ⊆ interior fundamentalCube)
    {x : Space} (hx : x ∈ fundamentalCube) : periodize f x = f x := by
  have hzero : ∀ n : PeriodicFrequency, n ≠ 0 → f (x - latticeVector n) = 0 := by
    intro n hn
    by_contra hne
    have hmem : x - latticeVector n ∈ interior fundamentalCube :=
      hsupp (subset_tsupport f hne)
    have hI := interior_subset_fundamentalCubeInterior hmem
    obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := Function.ne_iff.mp hn
    have hxi := hx i
    have hIi := hI i
    have hcoord : (x - latticeVector n) i = x i - (n i : ℝ) := rfl
    rw [hcoord] at hIi
    rcases lt_or_gt_of_ne hi with hneg | hpos
    · have hz : (1 : ℤ) ≤ -n i := by omega
      have hz' : (1 : ℝ) ≤ -(n i : ℝ) := by exact_mod_cast hz
      linarith [hxi.2, hIi.2]
    · have hz : (1 : ℤ) ≤ n i := by omega
      have hz' : (1 : ℝ) ≤ (n i : ℝ) := by exact_mod_cast hz
      linarith [hxi.1, hIi.1]
  have h := tsum_eq_single (L := SummationFilter.unconditional PeriodicFrequency)
    (0 : PeriodicFrequency) (fun n hn => hzero n hn)
  simpa only [periodize, latticeVector_zero, sub_zero] using h

/-- The same agreement holds on a whole neighbourhood of every interior point. -/
theorem periodize_eventuallyEq_interior {f : SpatialField}
    (hsupp : tsupport f ⊆ interior fundamentalCube)
    {x : Space} (hx : x ∈ interior fundamentalCube) : periodize f =ᶠ[nhds x] f := by
  filter_upwards [isOpen_interior.mem_nhds hx] with y hy
  exact periodize_eq_of_mem_interior hsupp (interior_subset hy)

/-- Single-copy `L²` identity on the cube for `periodize`, interior hypothesis
version of `T13.endpoint_zero_eq`. -/
theorem eLpNorm_periodize_restrict_eq {f : SpatialField}
    (hsupp : tsupport f ⊆ interior fundamentalCube) :
    eLpNorm (periodize f) 2 (volume.restrict fundamentalCube) = eLpNorm f 2 volume := by
  have hae : periodize f =ᵐ[volume.restrict fundamentalCube] f :=
    ae_restrict_of_forall_mem measurableSet_fundamentalCube
      (fun x hx => periodize_eq_of_mem_interior hsupp hx)
  rw [eLpNorm_congr_ae hae,
    ← eLpNorm_indicator_eq_eLpNorm_restrict (p := 2) (μ := volume) measurableSet_fundamentalCube]
  congr 1
  exact Set.indicator_eq_self.mpr ((subset_tsupport f).trans (hsupp.trans interior_subset))

/-! ## §3  Goal 1: the energy identity for `periodize f` -/

/-- `03-torus.tex:29` (order zero, single copy on the torus): the Haar `L²` norm
of the lifted periodization equals the whole-space `L²` norm of the source.

The smoothness hypothesis `hf` is kept only for interface compatibility with the
T15 spec; the proof uses only `tsupport f ⊆ interior fundamentalCube`. -/
theorem eLpNorm_torusLift_periodize (f : SpatialField) (_hf : ContDiff ℝ ∞ f)
    (hsupp : tsupport f ⊆ interior fundamentalCube) :
    eLpNorm (torusLift (periodize f)) 2 periodicTorusMeasure = eLpNorm f 2 volume := by
  rw [eLpNorm_torusLift_restrict (periodize f)]
  exact eLpNorm_periodize_restrict_eq hsupp

/-! ## §4  Goal 2: the gradient companion

The `energyGradientT` per-slice quantity is
`eLpNorm (torusLift (fun x ↦ spatialGradient Z t x)) 2 periodicTorusMeasure`.
For the constant-in-time extension of `periodize f` it equals `T13`'s
`gradientENorm f volume`.  The two identified norms are exactly those. -/

/-- The `L²` norm of the assembled spatial gradient vector (`I02.spatialGradient`
spelling) equals `T13.gradientENorm`, on any measure, for a smooth field. -/
theorem eLpNorm_gradientVector_eq_gradientENorm {f : SpatialField} (hf : ContDiff ℝ ∞ f)
    (μ : Measure Space) :
    eLpNorm (fun x => (WithLp.toLp 2 (fun i => fderiv ℝ f x (coordinateVector i)) :
        WithLp 2 (Fin 3 → Space))) 2 μ = gradientENorm f μ := by
  have hcont : Continuous (fun x : Space => fderiv ℝ f x) :=
    (hf.fderiv_right (m := ∞) (by simp)).continuous
  have hmeas : ∀ i : Fin 3,
      Measurable (fun x : Space => ENNReal.ofReal (‖fderiv ℝ f x (coordinateVector i)‖ ^ 2)) :=
    fun i => (ENNReal.continuous_ofReal.comp
      (((hcont.clm_apply continuous_const).norm).pow 2)).measurable
  have hbase :
      ∫⁻ x, ‖(WithLp.toLp 2 (fun i => fderiv ℝ f x (coordinateVector i)) :
          WithLp 2 (Fin 3 → Space))‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ
        = ∑ i : Fin 3, ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ f x (coordinateVector i)‖ ^ 2) ∂μ := by
    have hpt : (fun x => ‖(WithLp.toLp 2 (fun i => fderiv ℝ f x (coordinateVector i)) :
          WithLp 2 (Fin 3 → Space))‖ₑ ^ (2 : ℝ≥0∞).toReal)
        = fun x => ∑ i : Fin 3, ENNReal.ofReal (‖fderiv ℝ f x (coordinateVector i)‖ ^ 2) := by
      funext x
      rw [show (2 : ℝ≥0∞).toReal = 2 by norm_num, ← ofReal_norm,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two,
        PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => Space),
        ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
    rw [hpt, lintegral_finsetSum Finset.univ (fun i _ => hmeas i)]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), hbase, gradientENorm]
  congr 1
  norm_num

/-- The `T13.gradientENorm` of a field supported inside the cube is unchanged by
restricting Lebesgue measure to the cube (interior hypothesis version of the
support half of `T13.endpoint_one_eq`). -/
theorem gradientENorm_restrict_eq {f : SpatialField}
    (hsupp : tsupport f ⊆ interior fundamentalCube) :
    gradientENorm f (volume.restrict fundamentalCube) = gradientENorm f volume := by
  rw [gradientENorm, gradientENorm]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hsub : Function.support
      (fun x => ENNReal.ofReal (‖fderiv ℝ f x (coordinateVector i)‖ ^ 2)) ⊆ fundamentalCube := by
    refine Function.support_subset_iff'.2 (fun x hx => ?_)
    have hnt : x ∉ tsupport f := fun hc => hx (hsupp.trans interior_subset hc)
    rw [fderiv_eq_zero_of_notMem_tsupport hnt]
    simp
  rw [← lintegral_indicator measurableSet_fundamentalCube, Set.indicator_eq_self.mpr hsub]

/-- The gradient companion of Goal 1, in the `energyGradientT`-compatible
`I02.spatialGradient` spelling (constant-in-time extension of `periodize f`),
identified with `T13.gradientENorm f volume`. -/
theorem eLpNorm_torusLift_spatialGradient_periodize
    (f : SpatialField) (hf : ContDiff ℝ ∞ f) (t : ℝ)
    (hsupp : tsupport f ⊆ interior fundamentalCube) :
    eLpNorm (torusLift
        (fun x => spatialGradient (fun p : SpaceTime => periodize f p.2) t x)) 2
        periodicTorusMeasure = gradientENorm f volume := by
  have hae :
      (fun x => (WithLp.toLp 2 (fun i => fderiv ℝ (periodize f) x (coordinateVector i)) :
          WithLp 2 (Fin 3 → Space)))
        =ᵐ[volume.restrict fundamentalCube]
      (fun x => (WithLp.toLp 2 (fun i => fderiv ℝ f x (coordinateVector i)) :
          WithLp 2 (Fin 3 → Space))) := by
    refine ae_iff.2 ?_
    rw [Measure.restrict_apply' measurableSet_fundamentalCube]
    refine measure_mono_null ?_ volume_frontier_fundamentalCube
    intro x hx
    obtain ⟨hne, hcube⟩ := hx
    refine ⟨subset_closure hcube, fun hint => hne ?_⟩
    show (WithLp.toLp 2 (fun i => fderiv ℝ (periodize f) x (coordinateVector i)) :
        WithLp 2 (Fin 3 → Space))
      = WithLp.toLp 2 (fun i => fderiv ℝ f x (coordinateVector i))
    rw [(periodize_eventuallyEq_interior hsupp hint).fderiv_eq]
  have hg : (fun x => spatialGradient (fun p : SpaceTime => periodize f p.2) t x)
      = (fun x => (WithLp.toLp 2 (fun i => fderiv ℝ (periodize f) x (coordinateVector i)) :
          WithLp 2 (Fin 3 → Space))) := rfl
  rw [hg, eLpNorm_torusLift_restrict, eLpNorm_congr_ae hae,
    eLpNorm_gradientVector_eq_gradientENorm hf (volume.restrict fundamentalCube),
    gradientENorm_restrict_eq hsupp]

/-! ## §5  Goal 3: the time-slice form -/

/-- `energyEssSupT` slice form: Goal 1 applied to each spatial slice of a
spacetime field, under the per-slice support hypothesis. -/
theorem eLpNorm_torusLift_periodize_slice (F : SpaceTimeField) (t : ℝ)
    (hf : ContDiff ℝ ∞ (fun x : Space => F (t, x)))
    (hsupp : tsupport (fun x : Space => F (t, x)) ⊆ interior fundamentalCube) :
    eLpNorm (torusLift (periodize (fun x => F (t, x)))) 2 periodicTorusMeasure
      = eLpNorm (fun x => F (t, x)) 2 volume :=
  eLpNorm_torusLift_periodize (fun x => F (t, x)) hf hsupp

end NSFormalization.Section3.T15
