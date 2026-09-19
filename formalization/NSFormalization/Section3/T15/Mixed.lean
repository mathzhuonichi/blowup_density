import NSFormalization.Section3.T15.Energy
import NSFormalization.Section4.I03.Mixed

/-!
# T15 U5 — the mixed-norm identity on the torus, with honest Bochner paths

`paper/sections/03-torus.tex:129-133,148-149` (`eq:packetFscale`) states, for
every `1 ≤ p, q ≤ ∞`,
`‖F_ε‖_{L^q(0,∞;L^p(T³))} = ε^{α(p,q)} ‖F‖_{L^q(0,∞;L^p(ℝ³))}`,
`α(p,q) = -3 + 3/p + 2/q`.

This module proves the two canonical `ScalingAPI` fields `mixed_memLp` and
`packetMixedScaling` (`Section3/T15/Scaling.lean:376,390`, Spec form
`research/T15/Spec.lean:828-845`) over the raw packet clauses and the canonical
`PlacementData`.

Route (`research/T15/T15_SPLIT.md` U5):

* §1 upgrades the `|Q| = 1` Haar/Lebesgue identification to **every** exponent,
  endpoints included, by identifying the pushforward of the Haar measure under
  the canonical chart `torusChart` with `volume.restrict fundamentalCube`
  (`map_torusChart`).  The `p = ∞` endpoint then needs no separate argument:
  `eLpNorm_map_measure` is exponent-generic.  `HaarBridge`'s exponent-2 bridge
  is the specialisation it was written for; this is the general form U5 needs.
* §2 shows the whole-space Bochner infimum defining `mixedLebesgueENorm` is
  *attained*, at `I03.positiveMixedNorm` — the formalization-side twin of
  `verification/Bindings/Scaling.lean:296 mixedLebesgueENorm_eq`, which cannot
  be imported from here.
* §3 builds the Haar `L^p(T³)` slice path and proves it continuous.  The torus
  is a probability space, so the uniform-continuity estimate of
  `I02.continuous_slicePath` loses its `volume B` factor entirely.
* §4 shows the torus infimum defining `mixedLebesgueENormT` is attained too,
  for any field whose slices have the same Haar lift as a continuous compactly
  supported one.  `U3.force_singleCopy` supplies exactly that: the chart always
  lands in the closed fundamental cube, so the periodized force and the
  rescaled force have literally equal lifts.
* §5 assembles: the torus norm collapses to `I03.positiveMixedNorm` of the
  rescaled force, `I03.positiveMixedNorm_parabolicForce` scales it by
  `ε^{-3+3/p+2/q} = ε^{alphaT p q}`, and §2 turns the whole-space side back into
  `mixedLebesgueENorm`.

No `sorry`, no named input, no new mathematical alias.
-/

noncomputable section

namespace NSFormalization.Section3.T15

open Set MeasureTheory Filter Topology
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField forceTimeMeasure)
open NSFormalization.Source
open NSFormalization.Source.PacketScaling
open NavierStokes.PeriodicIntegration (Coords toSpace)
open scoped ContDiff ENNReal Topology

/-! ## §1  The exponent-generic Haar/Lebesgue chart bridge -/

/-- The canonical representative map underlying `torusLift`: it sends a torus
point to its `(0,1]³` representative in `Space`. -/
def torusChart (z : PeriodicTorus) : Space :=
  toSpace ((UnitAddTorus.measurableEquivPiIoc (0 : Coords) z).val)

/-- `torusLift` is literally precomposition with the chart. -/
theorem torusLift_eq_comp {E : Type*} (g : Space → E) :
    torusLift g = g ∘ torusChart := rfl

theorem measurable_torusChart : Measurable torusChart :=
  toSpace.continuous.measurable.comp
    (measurable_subtype_coe.comp (UnitAddTorus.measurableEquivPiIoc (0 : Coords)).measurable)

/-- On a coordinate box representative the chart is the identity. -/
theorem torusChart_coe (y : Coords) (hy : ∀ i, y i ∈ Ioc (0 : ℝ) 1) :
    torusChart (fun i => (y i : AddCircle (1 : ℝ))) = toSpace y :=
  NSFormalization.Paper1.torusLift_coe (fun x : Space => x) y hy

/-- Haar integration of any extended-nonnegative function of the chart equals
Lebesgue integration over the fundamental cube.  No measurability hypothesis:
this is Mathlib's proved fundamental-domain change of variables
`UnitAddTorus.lintegral_preimage` composed with the volume-preserving chart
`toSpace`, exactly as in `HaarBridge.lintegral_enorm_torusLift`. -/
theorem lintegral_comp_torusChart (F : Space → ℝ≥0∞) :
    ∫⁻ z : PeriodicTorus, F (torusChart z) ∂periodicTorusMeasure
      = ∫⁻ x in fundamentalCube, F x ∂volume := by
  rw [UnitAddTorus.lintegral_preimage (fun z => F (torusChart z)) (0 : Coords)]
  have hmp : MeasurePreserving (toSpace : Coords → Space) volume volume :=
    PiLp.volume_preserving_toLp (Fin 3)
  have hemb : MeasurableEmbedding (toSpace : Coords → Space) :=
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding
  rw [← hmp.setLIntegral_comp_preimage_emb hemb F fundamentalCube,
    toSpace_preimage_fundamentalCube]
  have hbox : {y : Coords | ∀ i, y i ∈ Ioc ((0 : Coords) i) ((0 : Coords) i + 1)}
      = Set.univ.pi (fun _ : Fin 3 => Ioc (0 : ℝ) 1) := by
    ext y; simp
  rw [hbox,
    setLIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)
      (fun y hy => congrArg F (torusChart_coe y (fun i => hy i (Set.mem_univ i))))]
  exact setLIntegral_congr Measure.univ_pi_Ioc_ae_eq_Icc

/-- The Haar measure of the unit three-torus pushes forward, under the canonical
chart, to Lebesgue measure restricted to the fundamental cube. -/
theorem map_torusChart :
    Measure.map torusChart periodicTorusMeasure = volume.restrict fundamentalCube := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply measurable_torusChart hs,
    ← lintegral_indicator_one (measurable_torusChart hs),
    ← lintegral_indicator_one (μ := volume.restrict fundamentalCube) hs]
  exact lintegral_comp_torusChart (s.indicator (fun _ => (1 : ℝ≥0∞)))

/-- The Haar/Lebesgue bridge at **every** exponent, essential supremum
included. -/
theorem eLpNorm_torusLift_eq_restrict {E : Type*} [NormedAddCommGroup E]
    (g : Space → E) (hg : AEStronglyMeasurable g (volume.restrict fundamentalCube))
    (r : ℝ≥0∞) :
    eLpNorm (torusLift g) r periodicTorusMeasure
      = eLpNorm g r (volume.restrict fundamentalCube) := by
  have hg' : AEStronglyMeasurable g (Measure.map torusChart periodicTorusMeasure) := by
    rwa [map_torusChart]
  have h := eLpNorm_map_measure (p := r) (μ := periodicTorusMeasure)
    (g := g) (f := torusChart) hg' measurable_torusChart.aemeasurable
  rw [map_torusChart] at h
  exact h.symm

/-- For a continuous field supported in the closed fundamental cube the Haar
norm of the lift is the whole-space Lebesgue norm, at every exponent. -/
theorem eLpNorm_torusLift_eq_volume {E : Type*} [NormedAddCommGroup E]
    {g : Space → E} (hg : Continuous g) (hsupp : tsupport g ⊆ fundamentalCube)
    (r : ℝ≥0∞) :
    eLpNorm (torusLift g) r periodicTorusMeasure = eLpNorm g r volume := by
  rw [eLpNorm_torusLift_eq_restrict g hg.aestronglyMeasurable r,
    ← eLpNorm_indicator_eq_eLpNorm_restrict (p := r) (μ := volume)
      measurableSet_fundamentalCube]
  congr 1
  exact Set.indicator_eq_self.mpr ((subset_tsupport g).trans hsupp)

/-! ## §2  The whole-space Bochner infimum is attained -/

/-- `mixedLebesgueENorm` is *attained*: all admissible whole-space Bochner slice
paths of one continuous compactly supported field agree at every nonnegative
time, so the defining infimum is the single value `I03.positiveMixedNorm`.  This
is the formalization-side twin of `Bindings/Scaling.lean:296`. -/
theorem mixedLebesgueENorm_eq {r q : ℝ≥0∞} [Fact (1 ≤ r)] {F : VelocityField}
    (hF : Continuous F) (hc : HasCompactSupport F) :
    mixedLebesgueENorm q r F = NSFormalization.Section4.I03.positiveMixedNorm r q F := by
  refine le_antisymm ?_ ?_
  · refine le_trans (iInf_le _
      ⟨fun t => (NSFormalization.Section4.I02.slice_memLp hF hc r t).toLp
          (fun x : Space => F (t, x)),
        fun t _ => MemLp.coeFn_toLp _,
        (NSFormalization.Section4.I02.continuous_slicePath hF
          hc).stronglyMeasurable.aestronglyMeasurable⟩) ?_
    exact le_of_eq (NSFormalization.Section4.I03.eLpNorm_slicePath_eq r hF hc q)
  · refine le_iInf ?_
    rintro ⟨G, hslice, _hmeas⟩
    refine le_of_eq (eLpNorm_congr_enorm_ae ?_).symm
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hG : eLpNorm (G t : Space → Space) r volume =
        eLpNorm (fun x : Space => F (t, x)) r volume :=
      eLpNorm_congr_ae (hslice t (le_of_lt ht))
    rw [Lp.enorm_def, hG, Real.enorm_eq_ofReal ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal
        ((NSFormalization.Section4.I02.slice_memLp hF hc r t).eLpNorm_lt_top.ne)]

/-! ## §3  The Haar `L^p(T³)` slice path -/

/-- Spatial slices of a continuous spacetime field are continuous, in the
literal `fun x => H (t, x)` spelling the norms below are written in. -/
theorem continuous_slice {H : VelocityField} (hH : Continuous H) (t : ℝ) :
    Continuous (fun x : Space => H (t, x)) :=
  hH.comp (continuous_const.prodMk continuous_id)

/-- The Haar `L^p(T³)`-valued slice path of a continuous field. -/
def torusSlicePath (r : ℝ≥0∞) [Fact (1 ≤ r)] {H : VelocityField}
    (hH : Continuous H) (t : ℝ) : Lp Space r periodicTorusMeasure :=
  (memLp_torusLift_vector (continuous_slice hH t) r).toLp
    (torusLift (fun x : Space => H (t, x)))

/-- The `L^p(T³)` norm of a slice-path value is the Haar norm of the lift. -/
theorem enorm_torusSlicePath (r : ℝ≥0∞) [Fact (1 ≤ r)] {H : VelocityField}
    (hH : Continuous H) (t : ℝ) :
    ‖torusSlicePath r hH t‖ₑ
      = eLpNorm (torusLift (fun x : Space => H (t, x))) r periodicTorusMeasure := by
  rw [show torusSlicePath r hH t
      = (memLp_torusLift_vector (continuous_slice hH t) r).toLp
        (torusLift (fun x : Space => H (t, x))) from rfl, Lp.enorm_toLp]

/-- The Haar slice path of a continuous compactly supported field is continuous,
hence strongly measurable.  The torus is a probability space, so the `L^p` bound
of `I02.continuous_slicePath` collapses to the uniform bound itself. -/
theorem continuous_torusSlicePath (r : ℝ≥0∞) [Fact (1 ≤ r)] {H : VelocityField}
    (hH : Continuous H) (hc : HasCompactSupport H) :
    Continuous (torusSlicePath r hH) := by
  rw [Metric.continuous_iff]
  intro b δ hδ
  obtain ⟨η, hη, hd⟩ := Metric.uniformContinuous_iff.mp
    (hc.uniformContinuous_of_continuous hH) (δ / 2) (half_pos hδ)
  refine ⟨η, hη, fun a hab => ?_⟩
  have hpt : ∀ z : PeriodicTorus,
      ‖torusLift (fun x : Space => H (a, x)) z
        - torusLift (fun x : Space => H (b, x)) z‖ ≤ δ / 2 := by
    intro z
    have hdist : dist ((a, torusChart z) : SpaceTime) ((b, torusChart z) : SpaceTime) < η := by
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
      exact hab
    have hlt := hd hdist
    rw [dist_eq_norm] at hlt
    exact hlt.le
  have hbound : eLpNorm (fun z : PeriodicTorus =>
      torusLift (fun x : Space => H (a, x)) z
        - torusLift (fun x : Space => H (b, x)) z) r periodicTorusMeasure
      ≤ ENNReal.ofReal (δ / 2) := by
    refine (eLpNorm_le_of_ae_bound (Filter.Eventually.of_forall hpt)).trans_eq ?_
    rw [measure_univ, ENNReal.one_rpow, one_mul]
  have hnorm : dist (torusSlicePath r hH a) (torusSlicePath r hH b)
      = (eLpNorm (fun z : PeriodicTorus =>
          torusLift (fun x : Space => H (a, x)) z
            - torusLift (fun x : Space => H (b, x)) z) r periodicTorusMeasure).toReal := by
    rw [dist_eq_norm, torusSlicePath, torusSlicePath, ← MemLp.toLp_sub, Lp.norm_toLp]
    rfl
  rw [hnorm]
  calc (eLpNorm (fun z : PeriodicTorus =>
        torusLift (fun x : Space => H (a, x)) z
          - torusLift (fun x : Space => H (b, x)) z) r periodicTorusMeasure).toReal
      ≤ (ENNReal.ofReal (δ / 2)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    _ = δ / 2 := ENNReal.toReal_ofReal (by positivity)
    _ < δ := by linarith

/-! ## §4  The torus Bochner infimum is attained -/

/-- `mixedLebesgueENormT` is attained, for any field whose Haar slice lifts are
those of a continuous compactly supported field. -/
theorem mixedLebesgueENormT_eq {r q : ℝ≥0∞} [Fact (1 ≤ r)]
    {F : SpaceTimeField} {H : VelocityField}
    (hH : Continuous H) (hc : HasCompactSupport H)
    (hFH : ∀ t : ℝ, 0 ≤ t →
      torusLift (fun x : Space => F (t, x)) = torusLift (fun x : Space => H (t, x))) :
    mixedLebesgueENormT q r F
      = eLpNorm (fun t : ℝ => (eLpNorm (torusLift (fun x : Space => H (t, x))) r
          periodicTorusMeasure).toReal) q forceTimeMeasure := by
  have hmem : ∀ t : ℝ, MemLp (torusLift (fun x : Space => H (t, x))) r periodicTorusMeasure :=
    fun t => memLp_torusLift_vector (continuous_slice hH t) r
  have hpath : IsPeriodicLebesgueSlicePath r F (torusSlicePath r hH) := by
    intro t ht
    rw [hFH t ht]
    exact MemLp.coeFn_toLp _
  refine le_antisymm ?_ ?_
  · refine le_trans (iInf_le _ ⟨torusSlicePath r hH, hpath,
      (continuous_torusSlicePath r hH hc).stronglyMeasurable.aestronglyMeasurable⟩) ?_
    refine le_of_eq (eLpNorm_congr_enorm_ae (Filter.Eventually.of_forall (fun t => ?_)))
    rw [enorm_torusSlicePath, Real.enorm_eq_ofReal ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (hmem t).eLpNorm_lt_top.ne]
  · refine le_iInf ?_
    rintro ⟨G, hslice, _hmeas⟩
    refine le_of_eq (eLpNorm_congr_enorm_ae ?_).symm
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hG : eLpNorm (G t : PeriodicTorus → Space) r periodicTorusMeasure =
        eLpNorm (torusLift (fun x : Space => H (t, x))) r periodicTorusMeasure := by
      rw [eLpNorm_congr_ae (hslice t (le_of_lt ht)), hFH t (le_of_lt ht)]
    rw [Lp.enorm_def, hG, Real.enorm_eq_ofReal ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (hmem t).eLpNorm_lt_top.ne]

/-! ## §5  The two canonical fields -/

section Packet

variable {u f : VelocityField} {pfield : PressureField} {K : Set Space}

/-- The rescaled force is globally smooth. -/
theorem scaledForce_contDiff (hf : ContDiff ℝ ∞ f) (x₀ : Space) (T ε : ℝ) :
    ContDiff ℝ ∞ (scaledForce f x₀ T ε) :=
  parabolicForce_smooth hf ε⁻¹ (T - ε ^ 2) x₀

/-- The rescaled force has compact spacetime support. -/
theorem scaledForce_hasCompactSupport (hc : HasCompactSupport f) (x₀ : Space) (T ε : ℝ) :
    HasCompactSupport (scaledForce f x₀ T ε) :=
  parabolicForce_compact ε⁻¹ (T - ε ^ 2) x₀ hc

/-- Every rescaled force slice is supported in the closed fundamental cube. -/
theorem scaledForce_slice_tsupport_cube
    (hfc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u pfield f K) {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) place.ε₀) (t : ℝ) :
    tsupport (fun x : Space => scaledForce f place.x₀ place.T ε (t, x)) ⊆ fundamentalCube :=
  (scaledForce_slice_subset_cube hε place.Kstar_compact hfc place.force_projection_subset
    place.eps_space place.chartBall_in_cube t).trans interior_subset

/-- The single-copy identity gives literally equal Haar lifts: the chart always
produces a representative in the closed fundamental cube. -/
theorem torusLift_periodizedScaledForce
    (hfc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u pfield f K) {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) place.ε₀) (t : ℝ) :
    torusLift (fun x : Space => periodizedScaledForce f place.x₀ place.T ε (t, x))
      = torusLift (fun x : Space => scaledForce f place.x₀ place.T ε (t, x)) :=
  torusLift_congr_cube (fun x hx => force_singleCopy hfc place ε hε t x hx)

/-- The torus mixed norm of the periodized rescaled force is the whole-space
`(0,∞)` mixed norm of the rescaled force: `|Q| = 1` slice by slice. -/
theorem mixedLebesgueENormT_periodizedScaledForce {r q : ℝ≥0∞} [Fact (1 ≤ r)]
    (hf : ContDiff ℝ ∞ f)
    (hfc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u pfield f K) {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) place.ε₀) :
    mixedLebesgueENormT q r (periodizedScaledForce f place.x₀ place.T ε)
      = NSFormalization.Section4.I03.positiveMixedNorm r q
          (scaledForce f place.x₀ place.T ε) := by
  have hsm := scaledForce_contDiff hf place.x₀ place.T ε
  have hcs := scaledForce_hasCompactSupport hfc.1 place.x₀ place.T ε
  rw [mixedLebesgueENormT_eq hsm.continuous hcs
    (fun t _ => torusLift_periodizedScaledForce hfc place hε t)]
  refine eLpNorm_congr_enorm_ae (Filter.Eventually.of_forall (fun t => ?_))
  rw [eLpNorm_torusLift_eq_volume (continuous_slice hsm.continuous t)
    (scaledForce_slice_tsupport_cube hfc place hε t) r]

/-- `03-torus.tex:129-133,148-149`, the honesty guard of `eq:packetFscale`: both
sides of the mixed identity have genuine Bochner `MemLp` representatives, at
every exponent pair including the essential-supremum endpoints. -/
theorem mixed_memLp (hf : ContDiff ℝ ∞ f)
    (hfc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u pfield f K) :
    ∀ (r q : ℝ≥0∞) [Fact (1 ≤ r)], 1 ≤ q →
      MemMixedLebesgueR q r f ∧
        ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
          MemMixedLebesgueT q r (periodizedScaledForce f place.x₀ place.T ε) := by
  intro r q _ _
  constructor
  · refine ⟨fun t => (NSFormalization.Section4.I02.slice_memLp hf.continuous hfc.1 r t).toLp
      (fun x : Space => f (t, x)), fun t _ => MemLp.coeFn_toLp _,
      (NSFormalization.Section4.I02.continuous_slicePath hf.continuous
        hfc.1).stronglyMeasurable.aestronglyMeasurable, ?_⟩
    rw [NSFormalization.Section4.I03.eLpNorm_slicePath_eq r hf.continuous hfc.1 q]
    refine lt_of_le_of_lt (eLpNorm_mono_measure _ Measure.restrict_le_self) ?_
    exact (Source.compact_mixed_memLp hf hfc.1 r q).eLpNorm_lt_top
  · intro ε hε
    have hsm := scaledForce_contDiff hf place.x₀ place.T ε
    have hcs := scaledForce_hasCompactSupport hfc.1 place.x₀ place.T ε
    refine ⟨torusSlicePath r hsm.continuous, ?_,
      (continuous_torusSlicePath r hsm.continuous hcs).stronglyMeasurable.aestronglyMeasurable,
      ?_⟩
    · intro t _
      rw [torusLift_periodizedScaledForce hfc place hε t]
      exact MemLp.coeFn_toLp _
    · have hval : eLpNorm (torusSlicePath r hsm.continuous) q forceTimeMeasure
          = mixedLebesgueENormT q r (periodizedScaledForce f place.x₀ place.T ε) := by
        rw [mixedLebesgueENormT_eq hsm.continuous hcs
          (fun t _ => torusLift_periodizedScaledForce hfc place hε t)]
        refine eLpNorm_congr_enorm_ae (Filter.Eventually.of_forall (fun t => ?_))
        rw [enorm_torusSlicePath, Real.enorm_eq_ofReal ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal
            (memLp_torusLift_vector (continuous_slice hsm.continuous t)
              r).eLpNorm_lt_top.ne]
      rw [hval, mixedLebesgueENormT_periodizedScaledForce hf hfc place hε]
      refine lt_of_le_of_lt (eLpNorm_mono_measure _ Measure.restrict_le_self) ?_
      exact (Source.compact_mixed_memLp hsm hcs r q).eLpNorm_lt_top

/-- `03-torus.tex:129-133,148-149`, equation `eq:packetFscale`:
`‖F_ε‖_{L^q(0,∞;L^p(T³))} = ε^{α(p,q)} ‖F‖_{L^q(0,∞;L^p(ℝ³))}`, for every
`1 ≤ p, q ≤ ∞`. -/
theorem packetMixedScaling (hf : ContDiff ℝ ∞ f)
    (hfc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u pfield f K) :
    ∀ (r q : ℝ≥0∞) [Fact (1 ≤ r)], 1 ≤ q →
      ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
        mixedLebesgueENormT q r
            (periodizedScaledForce f place.x₀ place.T ε) =
          ENNReal.ofReal (ε ^ alphaT r q) * mixedLebesgueENorm q r f := by
  intro r q _ _ ε hε
  have hT : 0 ≤ place.T - ε ^ 2 := by
    have h := place.eps_time ε hε
    nlinarith [sq_nonneg ε]
  have hzero : ∀ t : ℝ, t ≤ 0 → ∀ x : Space, f (t, x) = 0 := by
    intro t ht x
    refine image_eq_zero_of_notMem_tsupport (f := f) (fun hmem => ?_)
    exact absurd (hfc.2 hmem).1 (not_lt.2 ht)
  rw [mixedLebesgueENormT_periodizedScaledForce hf hfc place hε,
    show scaledForce f place.x₀ place.T ε
        = Source.parabolicForce ε⁻¹ (place.T - ε ^ 2) place.x₀ f from rfl,
    NSFormalization.Section4.I03.positiveMixedNorm_parabolicForce hf hfc.1 hzero
      hε.1 hT place.x₀ r q,
    mixedLebesgueENorm_eq hf.continuous hfc.1, alphaT_formula]

end Packet

end NSFormalization.Section3.T15
