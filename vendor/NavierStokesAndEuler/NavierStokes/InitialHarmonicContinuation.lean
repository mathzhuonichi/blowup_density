import NavierStokes.ActualPrimaryBounds
import NavierStokes.ActualPrimaryCoherence
import NavierStokes.WaveStageContinuation
import NavierStokes.GenericEndpointExtension

/-!
# Continuation of the actual initial harmonic coefficients

The native amplitude and pressure are the fields attached to the existing
`ActualPrimary.choice`. Their full derivative bounds are used before the
same native copies, cutoff, and harmonic coefficients are assembled.
-/

noncomputable section

namespace NavierStokes.InitialHarmonicContinuation

open Set Filter Function CorrectionInitialization WeightedClasses
open scoped Topology ContDiff BigOperators


abbrev Native := ActualSignedGeometry.Native
abbrev Plane := TorusInverse.Plane
abbrev Point := LocalSignedRequest.Point
abbrev Spatial := ℝ × (ℝ × Plane)
abbrev Model := ℝ × Spatial

noncomputable def nativeMap (z : Model) : Native :=
  ((Real.sqrt (Real.exp z.2.1) * z.2.2.1,
    ((Real.exp z.2.1) ^ CoordinateAlgebra.D ActualPrimary.h * z.1,
      Real.exp z.2.1 * (1 - z.1 ^ 2))), z.2.2.2)

noncomputable def modelStrip : Set Model := Ioo (-1 : ℝ) 1 ×ˢ univ

theorem nativeMap_smooth : ContDiff ℝ ∞ nativeMap := by
  have hq : ContDiff ℝ ∞ (fun z : Model => Real.exp z.2.1) := contDiff_snd.fst.exp
  exact ((hq.sqrt (fun z => (Real.exp_pos _).ne')).mul contDiff_snd.snd.fst |>.prodMk
    ((hq.rpow_const_of_ne (fun z => (Real.exp_pos _).ne')).mul contDiff_fst |>.prodMk
      (hq.mul (contDiff_const.sub (contDiff_fst.pow 2))))).prodMk contDiff_snd.snd.snd

theorem nativeMap_time {z : Model} (hz : z ∈ modelStrip) : 0 < (nativeMap z).1.2.2 := by
  have hs : z.1 ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one z.1).mpr (abs_lt.mpr hz.1)
  exact mul_pos (Real.exp_pos _) (sub_pos.mpr hs)

theorem nativeMap_q {z : Model} (hz : z ∈ modelStrip) :
    NativeBandExtension.nativeQ ActualPrimary.h (nativeMap z) = Real.exp z.2.1 := by
  symm
  apply SimilarityCoordinates.eq_coordinateQ (a := 2 * ActualPrimary.h)
    (p := ((nativeMap z).1.2.2, (nativeMap z).1.2.1))
    (by linarith [ActualPrimary.outgoing.data.h_pos])
    (by linarith [ActualPrimary.outgoing.data.h_lt_half]) (nativeMap_time hz)
    (Real.exp_pos _)
  exact (CoordinateAlgebra.forward_coordinate_identity (Real.exp_pos _) ActualPrimary.h z.1).symm

theorem nativeMap_radius {z : Model} (hz : z ∈ modelStrip) :
    WaveEdgeExtension.nativeRadius ActualPrimary.h (nativeMap z) = z.2.2.1 := by
  have hq := nativeMap_q hz
  dsimp only [WaveEdgeExtension.nativeRadius, PrimaryTargetBounds.profileRadius]
  rw [BaseChartJets.normalizedCoordinates_eq]
  change (Real.sqrt (Real.exp z.2.1) * z.2.2.1) /
    Real.sqrt (NativeBandExtension.nativeQ ActualPrimary.h (nativeMap z)) = _
  rw [hq, mul_div_cancel_left₀ _ (Real.sqrt_pos.mpr (Real.exp_pos _)).ne']

section NativeBounds

variable {B N0 : ℕ}

theorem envelope_le_one (j : Fin 2) (L : ActualPrimary.Label B N0) {x : Native}
    (hx : x.2 ∈ (ActualPrimary.clockWindow L).core) :
    NativeBandExtension.envelope ActualPrimary.certificate ActualPrimary.modulation
      (ActualPrimary.choice B N0).prepared ActualPrimary.slots.radius_pos j L x ≤ 1 := by
  have he : (ActualSignedGeometry.pulseCoordinates ActualPrimary.certificate ActualPrimary.modulation
      (ActualPrimary.choice B N0).prepared L x).2 = x.2.2 / (ActualPrimary.phases B N0 0).L L := rfl
  have ht : (ActualPrimary.phases B N0 j).L L *
      (ActualSignedGeometry.pulseCoordinates ActualPrimary.certificate ActualPrimary.modulation
        (ActualPrimary.choice B N0).prepared L x).2 = x.2.2 := by
    rw [he, ActualPrimary.length_sign j L,
      mul_div_cancel₀ _ ((ActualPrimary.phases B N0 0).L_pos L).ne']
  change PrimaryPulseBounds.referenceP ((ActualPrimary.phases B N0 j).lam L)
    ((ActualPrimary.phases B N0 j).u L) ((ActualPrimary.phases B N0 j).L L)
    ((ActualPrimary.phases B N0 j).L L *
      (ActualSignedGeometry.pulseCoordinates ActualPrimary.certificate ActualPrimary.modulation
        (ActualPrimary.choice B N0).prepared L x).2) ≤ 1
  rw [ht]
  exact PrimaryPulseBounds.referenceP_le_one ((ActualPrimary.phases B N0 j).lam_pos L)
    ((ActualPrimary.phases B N0 j).u_pos L) ((ActualPrimary.phases B N0 j).L_pos L) hx.2

theorem flat_factor_bound (p : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ x : Native,
    WaveEdgeExtension.nativeRadius ActualPrimary.h x ∈
      Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) →
    Real.sqrt (PrimaryTargetBounds.movingWeight ActualPrimary.nominal x.1) *
      WaveEdgeExtension.edgeGrowth (WaveEdgeExtension.nativeRadius ActualPrimary.h)
        (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) x ^ p ≤ K := by
  obtain ⟨K, hK, hb⟩ := GaussianTailFlat.sqrt_zeta_inverse_power_bounded
    (cL := FinalSlowBase.edgeExponent ActualPrimary.nominal / 4) (cR := 1)
    (div_pos (FinalSlowBase.edgeExponent_pos ActualPrimary.nominal) (by norm_num))
    zero_lt_one
    (WeightedRadialPrimitive.logLength (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) p
  refine ⟨K, hK, fun x hx => ?_⟩
  exact hb _ (WeightedRadialPrimitive.logPosition_mem
    (PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal) hx)

theorem zero_jet_off_core {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ActualPrimary.Label B N0) {f : Native → E}
    (hs : ∀ x, f x ≠ 0 → x.2 ∈ (ActualPrimary.clockWindow L).core)
    {x : Native} (hx : x.2 ∉ (ActualPrimary.clockWindow L).core) (m : ℕ) :
    iteratedFDeriv ℝ m f x = 0 := by
  have hg : f =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [continuous_snd.continuousAt
      ((ActualPrimary.clockWindow L).core_compact.isClosed.isOpen_compl.mem_nhds hx)] with y hy
    by_contra hn
    exact hy (hs y hn)
  rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hg, iteratedFDeriv_fun_zero]
  rfl

theorem native_bounded_of_weighted
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : Fin 2) (A : ActualPrimary.Label B N0 → ℝ) (hA : ∀ L, 0 ≤ A L)
    (f : ActualPrimary.Label B N0 → Native → E)
    (hf : PrimaryCopyBounds.NativeJets
      (NativeBandExtension.radialDomain ActualPrimary.certificate ActualPrimary.modulation
        (ActualPrimary.choice B N0).prepared)
      (fun L x => A L * Real.sqrt (PrimaryTargetBounds.movingWeight ActualPrimary.nominal x.1) *
        NativeBandExtension.envelope ActualPrimary.certificate ActualPrimary.modulation
          (ActualPrimary.choice B N0).prepared ActualPrimary.slots.radius_pos j L x) f)
    (he : ∀ L m x, 0 < x.1.2.2 →
      WaveEdgeExtension.nativeRadius ActualPrimary.h x ∉
        Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) →
      iteratedFDeriv ℝ m (f L) x = 0)
    (hs : ∀ L x, f L x ≠ 0 → x.2 ∈ (ActualPrimary.clockWindow L).core)
    (L : ActualPrimary.Label B N0) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Native, 0 < x.1.2.2 → ∀ k ≤ m,
      ‖iteratedFDeriv ℝ k (f L) x‖ ≤ C := by
  obtain ⟨C, hC, p, hb⟩ := hf.bound m
  obtain ⟨K, hK, hKbound⟩ := flat_factor_bound p
  let D := C * BaseContextAssembly.slowScale (BaseChartJets.cellBand L) ^ p * A L
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg (zero_le_one.trans hC)
    (pow_nonneg (zero_le_one.trans (BaseContextAssembly.one_le_slowScale _)) _)) (hA L)
  refine ⟨D * K, mul_nonneg hD hK, ?_⟩
  intro x ht k hk
  by_cases hr : WaveEdgeExtension.nativeRadius ActualPrimary.h x ∈
      Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)
  · by_cases hcore : x.2 ∈ (ActualPrimary.clockWindow L).core
    · have h := hb L x ⟨ht, hr⟩ k hk
      rw [NativeBandExtension.radialDomain_growth, mul_pow] at h
      have he1 := envelope_le_one j L hcore
      have hw : 0 ≤ Real.sqrt (PrimaryTargetBounds.movingWeight ActualPrimary.nominal x.1) :=
        Real.sqrt_nonneg _
      have hg : 0 ≤ WaveEdgeExtension.edgeGrowth (WaveEdgeExtension.nativeRadius ActualPrimary.h)
          (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) x ^ p :=
        pow_nonneg (zero_le_one.trans (le_max_left _ _)) _
      calc
        ‖iteratedFDeriv ℝ k (f L) x‖ ≤ _ := h
        _ = D * (Real.sqrt (PrimaryTargetBounds.movingWeight ActualPrimary.nominal x.1) *
          WaveEdgeExtension.edgeGrowth (WaveEdgeExtension.nativeRadius ActualPrimary.h)
            (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
            (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) x ^ p) *
          NativeBandExtension.envelope ActualPrimary.certificate ActualPrimary.modulation
            (ActualPrimary.choice B N0).prepared ActualPrimary.slots.radius_pos j L x := by dsimp [D]; ring
        _ ≤ D * (Real.sqrt (PrimaryTargetBounds.movingWeight ActualPrimary.nominal x.1) *
          WaveEdgeExtension.edgeGrowth (WaveEdgeExtension.nativeRadius ActualPrimary.h)
            (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
            (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) x ^ p) :=
          mul_le_of_le_one_right (mul_nonneg hD (mul_nonneg hw hg)) he1
        _ ≤ D * K := mul_le_mul_of_nonneg_left (hKbound x hr) hD
    · rw [zero_jet_off_core L (hs L) hcore, norm_zero]
      exact mul_nonneg hD hK
  · rw [he L k x ht hr, norm_zero]
    exact mul_nonneg hD hK

theorem attached_velocity_bounded (j : Fin 2) (L : ActualPrimary.Label B N0) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Native, 0 < x.1.2.2 → ∀ k ≤ m,
      ‖iteratedFDeriv ℝ k (ActualPrimary.attachedRawVelocity j L) x‖ ≤ C := by
  apply native_bounded_of_weighted j
    (fun L => Real.sqrt (ChartScales.epsilon ActualPrimary.h (BaseChartJets.cellBand L)))
    (fun _ => Real.sqrt_nonneg _) (fun L => ActualPrimary.attachedRawVelocity j L)
    (ActualPrimaryBounds.attached_velocity_jets B N0 j)
  · intro L k x ht hr
    exact (ActualPrimary.attachedPair_regular B N0 j L).1.jet_outside k ht hr
  · exact ActualPrimary.attachedRawVelocity_core j

theorem attached_pressure_bounded (j : Fin 2) (L : ActualPrimary.Label B N0) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Native, 0 < x.1.2.2 → ∀ k ≤ m,
      ‖iteratedFDeriv ℝ k (ActualPrimary.attachedRawPressure j L) x‖ ≤ C := by
  apply native_bounded_of_weighted j
    (fun L => ChartScales.epsilon ActualPrimary.h (BaseChartJets.cellBand L))
    (fun L => (ChartScales.epsilon_pos ActualPrimary.h _).le) (fun L => ActualPrimary.attachedRawPressure j L)
    (ActualPrimaryBounds.attached_pressure_jets B N0 j)
  · intro L k x ht hr
    exact (ActualPrimary.attachedPair_regular B N0 j L).2.jet_outside k ht hr
  · exact ActualPrimary.attachedRawPressure_core j

end NativeBounds

section NormalizedSource

variable {B N0 : ℕ}

theorem attached_zero_outside_band (j : Fin 2) (L : ActualPrimary.Label B N0) {x : Native}
    (ht : 0 < x.1.2.2) (hq : NativeBandExtension.nativeQ ActualPrimary.h x ∉ Icc (1 / 2 : ℝ) 2) :
    ActualPrimary.attachedRawVelocity j L x = 0 ∧ ActualPrimary.attachedRawPressure j L x = 0 := by
  have hz := NativeBandExtension.band_pair_zero_germ_factor ActualPrimary.certificate ActualPrimary.modulation
    (ActualPrimary.choice B N0).prepared ActualPrimary.slots.radius_pos ActualPrimary.radialVector
    ActualPrimary.temporalVector j L
    (NativeBandExtension.factor_zero_germ_band ActualPrimary.certificate ActualPrimary.modulation
      (ActualPrimary.choice B N0).prepared L ht hq)
  have hv : ActualPrimary.outerRawVelocity j L x = 0 := by
    simpa only [ActualPrimary.bandVelocity_eq] using hz.1.eq_of_nhds
  have hp : ActualPrimary.outerRawPressure j L x = 0 := by
    simpa only [ActualPrimary.bandPressure_eq] using hz.2.eq_of_nhds
  constructor
  · simp only [ActualPrimary.attachedRawVelocity, WaveEdgeExtension.nativeExtension,
      WaveEdgeExtension.extension, hv, ite_self]
  · simp only [ActualPrimary.attachedRawPressure, WaveEdgeExtension.nativeExtension,
      WaveEdgeExtension.extension, hp, ite_self]

def NativeSupport {E : Type*} [Zero E] (L : ActualPrimary.Label B N0) (f : Native → E) : Prop :=
  ∀ x, 0 < x.1.2.2 → f x ≠ 0 →
    NativeBandExtension.nativeQ ActualPrimary.h x ∈ Icc (1 / 2 : ℝ) 2 ∧
    WaveEdgeExtension.nativeRadius ActualPrimary.h x ∈
      Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) ∧
    x.2 ∈ (ActualPrimary.clockWindow L).core

theorem attached_velocity_support (j : Fin 2) (L : ActualPrimary.Label B N0) :
    NativeSupport L (ActualPrimary.attachedRawVelocity j L) := by
  intro x ht hn
  refine ⟨?_, ?_, ActualPrimary.attachedRawVelocity_core j L x hn⟩
  · by_contra hq
    exact hn (attached_zero_outside_band j L ht hq).1
  · have hr : WaveEdgeExtension.nativeRadius ActualPrimary.h x ∈
        Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) := by
      by_contra hr
      exact hn (WaveEdgeExtension.nativeExtension_outside ActualPrimary.nominal _ hr)
    exact ⟨hr.1.le, hr.2.le⟩

theorem attached_pressure_support (j : Fin 2) (L : ActualPrimary.Label B N0) :
    NativeSupport L (ActualPrimary.attachedRawPressure j L) := by
  intro x ht hn
  refine ⟨?_, ?_, ActualPrimary.attachedRawPressure_core j L x hn⟩
  · by_contra hq
    exact hn (attached_zero_outside_band j L ht hq).2
  · have hr : WaveEdgeExtension.nativeRadius ActualPrimary.h x ∈
        Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) := by
      by_contra hr
      exact hn (WaveEdgeExtension.nativeExtension_outside ActualPrimary.nominal _ hr)
    exact ⟨hr.1.le, hr.2.le⟩

noncomputable def spatialSupport (L : ActualPrimary.Label B N0) : Set Spatial :=
  Icc (Real.log (1 / 2 : ℝ)) (Real.log 2) ×ˢ
    (Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) ×ˢ (ActualPrimary.clockWindow L).core)

theorem spatialSupport_compact (L : ActualPrimary.Label B N0) : IsCompact (spatialSupport L) :=
  isCompact_Icc.prod (isCompact_Icc.prod (ActualPrimary.clockWindow L).core_compact)

theorem modelStrip_open : IsOpen modelStrip := isOpen_Ioo.prod isOpen_univ

noncomputable def modelSource {E : Type*} (f : Native → E) : Model → E := f ∘ nativeMap

theorem modelSource_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Native → E} (hf : ContDiffOn ℝ ∞ f WaveEdgeExtension.nativeSlowDomain) :
    ContDiffOn ℝ ∞ (modelSource f) modelStrip :=
  hf.comp nativeMap_smooth.contDiffOn (fun _ hx => nativeMap_time hx)

theorem modelSource_support {E : Type*} [Zero E] (L : ActualPrimary.Label B N0)
    {f : Native → E} (hf : NativeSupport L f) {z : Model} (hz : z ∈ modelStrip)
    (hn : modelSource f z ≠ 0) : z.2 ∈ spatialSupport L := by
  obtain ⟨hq, hr, hc⟩ := hf (nativeMap z) (nativeMap_time hz) hn
  rw [nativeMap_q hz] at hq
  rw [nativeMap_radius hz] at hr
  refine ⟨⟨?_, ?_⟩, hr, hc⟩
  · simpa only [Real.log_exp] using Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hq.1
  · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hq.2

theorem modelSource_zero_jet_off_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ActualPrimary.Label B N0) {f : Native → E} (hf : NativeSupport L f)
    {z : Model} (hz : z ∈ modelStrip) (hs : z.2 ∉ spatialSupport L) (m : ℕ) :
    iteratedFDeriv ℝ m (modelSource f) z = 0 := by
  have hg : modelSource f =ᶠ[𝓝 z] fun _ => 0 := by
    filter_upwards [modelStrip_open.mem_nhds hz,
      continuous_snd.continuousAt ((spatialSupport_compact L).isClosed.isOpen_compl.mem_nhds hs)]
      with y hy hys
    by_contra hn
    exact hys (modelSource_support L hf hy hn)
  rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hg, iteratedFDeriv_fun_zero]
  rfl

theorem modelSource_bounded {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ActualPrimary.Label B N0) {f : Native → E}
    (hf : ContDiffOn ℝ ∞ f WaveEdgeExtension.nativeSlowDomain)
    (hs : NativeSupport L f)
    (hb : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Native, 0 < x.1.2.2 → ∀ k ≤ m,
      ‖iteratedFDeriv ℝ k f x‖ ≤ C) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Model, z ∈ modelStrip →
      ‖iteratedFDeriv ℝ m (modelSource f) z‖ ≤ C := by
  obtain ⟨A, hA, ha⟩ := hb m
  obtain ⟨D, hD, hd⟩ := PhysicalGraphBounds.compact_jet_bound isOpen_univ nativeMap_smooth.contDiffOn
    (isCompact_Icc.prod (spatialSupport_compact L)) (subset_univ _) m
  refine ⟨(m.factorial : ℝ) * A * D ^ m, by positivity, ?_⟩
  intro z hz
  by_cases hsx : z.2 ∈ spatialSupport L
  · have h := norm_iteratedFDerivWithin_comp_le hf nativeMap_smooth.contDiffOn
      (show (m : WithTop ℕ∞) ≤ ∞ from ENat.natCast_le_of_coe_top_le_withTop le_rfl m)
      WaveEdgeExtension.nativeSlowDomain_open.uniqueDiffOn modelStrip_open.uniqueDiffOn
      (fun y hy => nativeMap_time hy) hz
      (C := A) (D := D)
      (by
        intro i hi
        rw [iteratedFDerivWithin_of_isOpen i WaveEdgeExtension.nativeSlowDomain_open (nativeMap_time hz)]
        exact ha (nativeMap z) (nativeMap_time hz) i hi)
      (by
        intro i hi him
        rw [iteratedFDerivWithin_of_isOpen i modelStrip_open hz]
        exact (hd i him z ⟨⟨hz.1.1.le, hz.1.2.le⟩, hsx⟩).trans
          (by simpa only [pow_one] using pow_le_pow_right₀ hD hi))
    simpa only [modelSource, iteratedFDerivWithin_of_isOpen m modelStrip_open hz] using h
  · rw [modelSource_zero_jet_off_support L hs hz hsx, norm_zero]
    positivity

theorem velocity_model_bounded (j : Fin 2) (L : ActualPrimary.Label B N0) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Model, z ∈ modelStrip →
      ‖iteratedFDeriv ℝ m (modelSource (ActualPrimary.attachedRawVelocity j L)) z‖ ≤ C :=
  modelSource_bounded L (ActualPrimary.attachedRawVelocity_smooth B N0 j L)
    (attached_velocity_support j L) (attached_velocity_bounded j L) m

theorem pressure_model_bounded (j : Fin 2) (L : ActualPrimary.Label B N0) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Model, z ∈ modelStrip →
      ‖iteratedFDeriv ℝ m (modelSource (ActualPrimary.attachedRawPressure j L)) z‖ ≤ C :=
  modelSource_bounded L (ActualPrimary.attachedRawPressure_smooth B N0 j L)
    (attached_pressure_support j L) (attached_pressure_bounded j L) m

end NormalizedSource

section StableCoordinates

noncomputable def stableDomain : Set Native :=
  {x | (x.1.2.2, x.1.2.1) ∈ PositiveRepresentatives.stableTarget (2 * ActualPrimary.h)}

noncomputable def nativeQ (x : Native) : ℝ :=
  OffplaneCorrectionExtensions.stableQ (2 * ActualPrimary.h) (x.1.2.2, x.1.2.1)

noncomputable def nativeCoordinates (x : Native) : Model :=
  (x.1.2.1 / nativeQ x ^ CoordinateAlgebra.D ActualPrimary.h,
    (Real.log (nativeQ x), (x.1.1 / Real.sqrt (nativeQ x), x.2)))

theorem stableDomain_open : IsOpen stableDomain :=
  (PositiveRepresentatives.stableTarget_open _).preimage
    (continuous_fst.snd.snd.prodMk continuous_fst.snd.fst)

theorem nativeQ_pos {x : Native} (hx : x ∈ stableDomain) : 0 < nativeQ x :=
  OffplaneCorrectionExtensions.stableQ_pos hx

theorem nativeQ_smoothAt {x : Native} (hx : x ∈ stableDomain) : ContDiffAt ℝ ∞ nativeQ x :=
  (OffplaneCorrectionExtensions.stableQ_contDiffAt
    (by linarith [ActualPrimary.outgoing.data.h_pos])
    (by linarith [ActualPrimary.outgoing.data.h_lt_half]) hx).comp x
      (contDiffAt_fst.snd.snd.prodMk contDiffAt_fst.snd.fst)

theorem nativeCoordinates_smooth : ContDiffOn ℝ ∞ nativeCoordinates stableDomain := by
  intro x hx
  have hq := nativeQ_smoothAt hx
  have hp := nativeQ_pos hx
  exact ((contDiffAt_fst.snd.fst.div (hq.rpow_const_of_ne hp.ne')
      (Real.rpow_pos_of_pos hp _).ne').prodMk
    ((hq.log hp.ne').prodMk
      ((contDiffAt_fst.fst.div (hq.sqrt hp.ne') (Real.sqrt_pos.mpr hp).ne').prodMk
        contDiffAt_snd))).contDiffWithinAt

theorem nativeQ_forward {x : Native} (hx : x ∈ stableDomain) :
    SimilarityCoordinates.forwardScalar (2 * ActualPrimary.h) x.1.2.1 (nativeQ x) = x.1.2.2 := by
  have hs := (PositiveRepresentatives.stableInverse_spec hx).2
  have hz := congrArg Prod.snd hs
  have ht := congrArg Prod.fst hs
  change (PositiveRepresentatives.stableInverse (2 * ActualPrimary.h) (x.1.2.2, x.1.2.1)).2 = x.1.2.1 at hz
  change SimilarityCoordinates.forwardScalar (2 * ActualPrimary.h)
    (PositiveRepresentatives.stableInverse (2 * ActualPrimary.h) (x.1.2.2, x.1.2.1)).2 (nativeQ x) = x.1.2.2 at ht
  rwa [hz] at ht

theorem nativeMap_coordinates {x : Native} (hx : x ∈ stableDomain) :
    nativeMap (nativeCoordinates x) = x := by
  have hq := nativeQ_pos hx
  have ht := CoordinateAlgebra.forward_coordinate_identity hq ActualPrimary.h
    (x.1.2.1 / nativeQ x ^ CoordinateAlgebra.D ActualPrimary.h)
  rw [mul_div_cancel₀ _ (Real.rpow_pos_of_pos hq _).ne'] at ht
  have htime : nativeQ x * (1 - (x.1.2.1 / nativeQ x ^ CoordinateAlgebra.D ActualPrimary.h) ^ 2) = x.1.2.2 :=
    ht.trans (nativeQ_forward hx)
  ext <;> simp only [nativeMap, nativeCoordinates, Real.exp_log hq,
    mul_div_cancel₀ _ (Real.sqrt_pos.mpr hq).ne', mul_div_cancel₀ _ (Real.rpow_pos_of_pos hq _).ne', htime]

theorem positive_mem_stable {x : Native} (ht : 0 < x.1.2.2) : x ∈ stableDomain :=
  PositiveRepresentatives.positiveTime_mem_stableTarget
    (by linarith [ActualPrimary.outgoing.data.h_pos])
    (by linarith [ActualPrimary.outgoing.data.h_lt_half]) ht

theorem nativeCoordinates_mem {x : Native} (ht : 0 < x.1.2.2) : nativeCoordinates x ∈ modelStrip := by
  have hq : nativeQ x = SimilarityCoordinates.coordinateQ (2 * ActualPrimary.h) (x.1.2.2, x.1.2.1) :=
    OffplaneCorrectionExtensions.stableQ_eq_coordinateQ
      (by linarith [ActualPrimary.outgoing.data.h_pos])
      (by linarith [ActualPrimary.outgoing.data.h_lt_half]) ht
  refine ⟨?_, mem_univ _⟩
  change x.1.2.1 / nativeQ x ^ CoordinateAlgebra.D ActualPrimary.h ∈ Ioo (-1 : ℝ) 1
  rw [hq]
  have he := SimilarityCoordinates.coordinateEta_abs_lt_one
    (p := (x.1.2.2, x.1.2.1))
    (by linarith [ActualPrimary.outgoing.data.h_pos] : 0 < 2 * ActualPrimary.h)
    (by linarith [ActualPrimary.outgoing.data.h_lt_half] : 2 * ActualPrimary.h < 1) ht
  have hpow : CoordinateAlgebra.D ActualPrimary.h = (1 - 2 * ActualPrimary.h) / 2 := by
    unfold CoordinateAlgebra.D
    ring
  simpa only [SimilarityCoordinates.coordinateEta, hpow, mem_Ioo, abs_lt] using he

variable {B N0 : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Data constructed from the actual normalized source and its bounded jets.
The constructor from the endpoint theorem is given below. -/
structure ModelContinuation (L : ActualPrimary.Label B N0) (f : Native → E) where
  value : Model → E
  smooth : ContDiff ℝ ∞ value
  agrees : EqOn value (modelSource f) modelStrip
  supported : ∀ z, value z ≠ 0 → z.2 ∈ spatialSupport L

namespace ModelContinuation

variable {L : ActualPrimary.Label B N0} {f : Native → E} (e : ModelContinuation L f)

noncomputable def native : Native → E := e.value ∘ nativeCoordinates

theorem native_smooth : ContDiffOn ℝ ∞ e.native stableDomain :=
  e.smooth.comp_contDiffOn nativeCoordinates_smooth

theorem native_agrees {x : Native} (ht : 0 < x.1.2.2) : e.native x = f x := by
  rw [native, comp_apply, e.agrees (nativeCoordinates_mem ht)]
  simp only [modelSource, comp_apply, nativeMap_coordinates (positive_mem_stable ht)]

theorem native_core {x : Native} (hn : e.native x ≠ 0) : x.2 ∈ (ActualPrimary.clockWindow L).core :=
  (e.supported (nativeCoordinates x) hn).2.2

theorem native_radial {x : Native} (hx : x ∈ stableDomain) (hn : e.native x ≠ 0) :
    x.1.1 ∈ Icc (Real.sqrt (nativeQ x) * PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (Real.sqrt (nativeQ x) * PrimaryTargetBounds.rightRadius ActualPrimary.nominal) := by
  have hr := (e.supported (nativeCoordinates x) hn).2.1
  have hp := Real.sqrt_pos.mpr (nativeQ_pos hx)
  exact ⟨by simpa only [mul_comm] using (le_div_iff₀ hp).mp hr.1,
    by simpa only [mul_comm] using (div_le_iff₀ hp).mp hr.2⟩

end ModelContinuation

end StableCoordinates

section StableScaling

theorem scalarSlope_scale {Q q : ℝ} (hQ : 0 < Q) (hq : 0 < q) (a z : ℝ) :
    SimilarityCoordinates.scalarSlope a (Q ^ ((1 - a) / 2) * z) (Q * q) =
      SimilarityCoordinates.scalarSlope a z q := by
  have hp : (Q ^ ((1 - a) / 2)) ^ 2 * Q ^ (a - 1) = 1 := by
    rw [← Real.rpow_mul_natCast hQ.le, ← Real.rpow_add hQ]
    rw [show (1 - a) / 2 * (2 : ℕ) + (a - 1) = (0 : ℝ) by ring, Real.rpow_zero]
  unfold SimilarityCoordinates.scalarSlope
  rw [Real.mul_rpow hQ.le hq.le, mul_pow]
  calc
    _ = 1 - ((Q ^ ((1 - a) / 2)) ^ 2 * Q ^ (a - 1)) * (z ^ 2 * a * q ^ (a - 1)) := by ring
    _ = _ := by rw [hp, one_mul]

theorem stableTarget_scale {a Q : ℝ} (hQ : 0 < Q) {p : Plane}
    (hp : p ∈ PositiveRepresentatives.stableTarget a) :
    (Q * p.1, Q ^ ((1 - a) / 2) * p.2) ∈ PositiveRepresentatives.stableTarget a := by
  rcases hp with ⟨r, hr, he⟩
  refine ⟨(Q * r.1, Q ^ ((1 - a) / 2) * r.2), ⟨mul_pos hQ hr.1, ?_⟩, ?_⟩
  · simpa only [scalarSlope_scale hQ hr.1] using hr.2
  · change (SimilarityCoordinates.forwardScalar a (Q ^ ((1 - a) / 2) * r.2) (Q * r.1), _) = _
    rw [SimilarityHomogeneity.forwardScalar_scale hQ hr.1]
    exact congrArg (fun y : Plane => (Q * y.1, Q ^ ((1 - a) / 2) * y.2)) he

theorem stableQ_scale {a Q : ℝ} (ha : 0 < a) (ha1 : a < 1) (hQ : 0 < Q) {p : Plane}
    (hp : p ∈ PositiveRepresentatives.stableTarget a) :
    OffplaneCorrectionExtensions.stableQ a (Q * p.1, Q ^ ((1 - a) / 2) * p.2) =
      Q * OffplaneCorrectionExtensions.stableQ a p := by
  let r := PositiveRepresentatives.stableInverse a p
  have hs := PositiveRepresentatives.stableInverse_spec hp
  have hsrc : (Q * r.1, Q ^ ((1 - a) / 2) * r.2) ∈ PositiveRepresentatives.stableSource a := by
    refine ⟨mul_pos hQ hs.1.1, ?_⟩
    rw [scalarSlope_scale hQ (show 0 < r.1 from hs.1.1)]
    exact hs.1.2
  have hforward : SimilarityCoordinates.forwardMap a (Q * r.1, Q ^ ((1 - a) / 2) * r.2) =
      (Q * p.1, Q ^ ((1 - a) / 2) * p.2) := by
    change (SimilarityCoordinates.forwardScalar a (Q ^ ((1 - a) / 2) * r.2) (Q * r.1), _) = _
    rw [SimilarityHomogeneity.forwardScalar_scale hQ hs.1.1]
    exact congrArg (fun y : Plane => (Q * y.1, Q ^ ((1 - a) / 2) * y.2)) hs.2
  unfold OffplaneCorrectionExtensions.stableQ
  rw [← hforward, PositiveRepresentatives.stableInverse_forwardMap ha.le ha1.le hsrc]

end StableScaling

section Periodization

variable {B N0 : ℕ} {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {L : ActualPrimary.Label B N0} {f : Native → E}

namespace ModelContinuation

noncomputable def map (e : ModelContinuation L f) (A : E →L[ℝ] F) :
    ModelContinuation L (fun x => A (f x)) where
  value z := A (e.value z)
  smooth := A.contDiff.comp e.smooth
  agrees := fun z hz => congrArg A (e.agrees hz)
  supported := fun z hz => e.supported z (fun he => hz (by rw [he, map_zero]))

noncomputable def periodized (e : ModelContinuation L f) (j : Fin 2) (x : Native) : E :=
  ∑' k : TorusInverse.Frequency, e.native (x.1, (ActualPrimary.geometry j L).coordinates k x.2)

theorem periodized_smooth (e : ModelContinuation L f) (j : Fin 2) :
    ContDiffOn ℝ ∞ (e.periodized j) stableDomain := by
  classical
  let H : TorusInverse.Frequency → Native → E :=
    fun k x => e.native (x.1, (ActualPrimary.geometry j L).coordinates k x.2)
  have hs : ∀ k, support (H k) ⊆ (ActualPrimary.copyCells j L).carrier 0 k := by
    intro k x hx
    exact e.native_core hx
  intro x hx
  obtain ⟨J, hJ⟩ := PeriodizedWaveBounds.copySum_eventually_finite (ActualPrimary.copyCells j L) 0 H hs x
  have hsm : ContDiffAt ℝ ∞ (fun y => ∑ k ∈ J, H k y) x := by
    apply ContDiffAt.sum
    intro k hk
    have hmem : (x.1, (ActualPrimary.geometry j L).coordinates k x.2) ∈ stableDomain := hx
    exact ContDiffAt.comp (g := e.native) (f := fun y : Native =>
      (y.1, (ActualPrimary.geometry j L).coordinates k y.2)) x
      (e.native_smooth.contDiffAt (stableDomain_open.mem_nhds hmem))
      (contDiff_fst.prodMk ((ActualPrimary.geometry j L).coordinates_contDiff k |>.comp contDiff_snd)).contDiffAt
  exact (hsm.congr_of_eventuallyEq hJ).contDiffWithinAt

theorem periodized_agrees (e : ModelContinuation L f) (j : Fin 2) {x : Native}
    (ht : 0 < x.1.2.2) :
    e.periodized j x = ∑' k : TorusInverse.Frequency, f (x.1, (ActualPrimary.geometry j L).coordinates k x.2) := by
  apply tsum_congr
  intro k
  exact e.native_agrees ht

theorem periodized_radial (e : ModelContinuation L f) (j : Fin 2) {x : Native}
    (hx : x ∈ stableDomain) (hn : e.periodized j x ≠ 0) :
    x.1.1 ∈ Icc (Real.sqrt (nativeQ x) * PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (Real.sqrt (nativeQ x) * PrimaryTargetBounds.rightRadius ActualPrimary.nominal) := by
  by_contra hr
  have hzero (k : TorusInverse.Frequency) :
      e.native (x.1, (ActualPrimary.geometry j L).coordinates k x.2) = 0 := by
    by_contra hk
    exact hr (e.native_radial (x := (x.1, (ActualPrimary.geometry j L).coordinates k x.2)) hx hk)
  exact hn (by simp only [periodized, hzero, tsum_zero])

theorem periodized_periodic (e : ModelContinuation L f) (j : Fin 2)
    (p : PhaseCalculus.Slow) (Y : Plane) (k : TorusInverse.Frequency) :
    e.periodized j (p, Y + TorusAverages.latticePoint k) = e.periodized j (p, Y) := by
  change PeriodizedWaveBounds.copySum
    (fun l (Z : Plane) => e.native (p, (ActualPrimary.geometry j L).coordinates l Z))
    (Y + TorusAverages.latticePoint k) = _
  apply PeriodizedWaveBounds.copySum_translate _ (fun Z => Z + TorusAverages.latticePoint k)
    (Equiv.addRight (CommonCoverSolve.coverIndex (ActualPrimary.geometry j L).gap k))
  intro l Z
  exact congrArg (fun q => e.native (p, q)) ((ActualPrimary.geometry j L).coordinates_deck l k Z)

end ModelContinuation

end Periodization

section ActualExtensions

variable {B N0 : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

noncomputable def ModelContinuation.ofBounded (L : ActualPrimary.Label B N0) (f : Native → E)
    (hf : ContDiffOn ℝ ∞ f WaveEdgeExtension.nativeSlowDomain)
    (hs : NativeSupport L f)
    (hb : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Native, 0 < x.1.2.2 → ∀ k ≤ m,
      ‖iteratedFDeriv ℝ k f x‖ ≤ C) : ModelContinuation L f := by
  have hsm := modelSource_smooth hf
  have hbd : ∀ m : ℕ, ∃ C : ℝ, ∀ z ∈ modelStrip,
      ‖iteratedFDeriv ℝ m (modelSource f) z‖ ≤ C := by
    intro m
    obtain ⟨C, _, hC⟩ := modelSource_bounded L hf hs hb m
    exact ⟨C, hC⟩
  refine ⟨GenericEndpointExtension.extension (modelSource f) hsm hbd,
    GenericEndpointExtension.extension_contDiff hsm hbd,
    fun z hz => GenericEndpointExtension.extension_eq hsm hbd hz, ?_⟩
  intro z hn
  by_contra hz
  apply hn
  apply GenericEndpointExtension.extension_zero_of_fiber hsm hbd (x := z.2)
  intro t ht
  by_contra he
  exact hz (modelSource_support L hs (z := (t, z.2)) ⟨ht, mem_univ _⟩ he)

noncomputable def velocityContinuation (j : Fin 2) (L : ActualPrimary.Label B N0) :
    ModelContinuation L (ActualPrimary.attachedRawVelocity j L) :=
  ModelContinuation.ofBounded L _ (ActualPrimary.attachedRawVelocity_smooth B N0 j L)
    (attached_velocity_support j L) (attached_velocity_bounded j L)

noncomputable def pressureContinuation (j : Fin 2) (L : ActualPrimary.Label B N0) :
    ModelContinuation L (ActualPrimary.attachedRawPressure j L) :=
  ModelContinuation.ofBounded L _ (ActualPrimary.attachedRawPressure_smooth B N0 j L)
    (attached_pressure_support j L) (attached_pressure_bounded j L)

end ActualExtensions

section AbsoluteCoordinates

abbrev Absolute := ActualPrimaryCoherence.Absolute

noncomputable def absoluteDomain : Set Absolute :=
  {x | (x.1.1.2.2, x.1.1.2.1) ∈ PositiveRepresentatives.stableTarget (2 * ActualPrimary.h)}

noncomputable def positiveAbsoluteDomain : Set Absolute :=
  {x | 0 < x.1.1.1 ∧ x ∈ absoluteDomain}

theorem absoluteDomain_open : IsOpen absoluteDomain :=
  (PositiveRepresentatives.stableTarget_open _).preimage
    (continuous_fst.fst.snd.snd.prodMk continuous_fst.fst.snd.fst)

theorem positiveAbsoluteDomain_open : IsOpen positiveAbsoluteDomain :=
  (isOpen_lt continuous_const continuous_fst.fst.fst).inter absoluteDomain_open

noncomputable def absoluteQ (x : Absolute) : ℝ :=
  OffplaneCorrectionExtensions.stableQ (2 * ActualPrimary.h) (x.1.1.2.2, x.1.1.2.1)

noncomputable def absoluteLength (x : Absolute) : ℝ := Real.sqrt (absoluteQ x)

theorem absoluteLength_pos {x : Absolute} (hx : x ∈ absoluteDomain) : 0 < absoluteLength x :=
  Real.sqrt_pos.mpr (OffplaneCorrectionExtensions.stableQ_pos hx)

theorem absoluteLength_smooth : ContDiffOn ℝ ∞ absoluteLength absoluteDomain := by
  intro x hx
  have hq : ContDiffAt ℝ ∞ (OffplaneCorrectionExtensions.stableQ (2 * ActualPrimary.h))
      (x.1.1.2.2, x.1.1.2.1) := OffplaneCorrectionExtensions.stableQ_contDiffAt
    (by exact mul_pos (by norm_num) ActualPrimary.outgoing.data.h_pos)
    (by nlinarith [ActualPrimary.outgoing.data.h_lt_half]) hx
  have hcomp : ContDiffAt ℝ ∞ absoluteQ x := ContDiffAt.comp
    (g := OffplaneCorrectionExtensions.stableQ (2 * ActualPrimary.h))
    (f := fun y : Absolute => (y.1.1.2.2, y.1.1.2.1)) x hq
    ((contDiff_fst.fst.snd.snd.prodMk contDiff_fst.fst.snd.fst).contDiffAt)
  exact (hcomp.sqrt (show absoluteQ x ≠ 0 from
    (OffplaneCorrectionExtensions.stableQ_pos hx).ne')).contDiffWithinAt

variable {B N0 : ℕ}

noncomputable def nativeArgument (L : ActualPrimary.Label B N0) (x : Absolute) : Native :=
  (ActualPrimary.nativeSlow L x.1, x.1.2)

theorem nativeArgument_smooth (L : ActualPrimary.Label B N0) : ContDiff ℝ ∞ (nativeArgument L) :=
  ((ActualPrimary.nativeSlow_smooth L).comp contDiff_fst).prodMk contDiff_fst.snd

theorem nativeArgument_mem (L : ActualPrimary.Label B N0) {x : Absolute}
    (hx : x ∈ absoluteDomain) : nativeArgument L x ∈ stableDomain := by
  have hh : CoordinateAlgebra.D ActualPrimary.h = (1 - 2 * ActualPrimary.h) / 2 := by
    unfold CoordinateAlgebra.D
    ring
  have hm := stableTarget_scale (inv_pos.mpr (ChartScales.Q_pos (BaseChartJets.cellBand L))) hx
  change (x.1.1.2.2 / ChartScales.Q (BaseChartJets.cellBand L),
    x.1.1.2.1 / ChartScales.Q (BaseChartJets.cellBand L) ^ CoordinateAlgebra.D ActualPrimary.h) ∈
      PositiveRepresentatives.stableTarget (2 * ActualPrimary.h)
  simpa only [Real.inv_rpow (ChartScales.Q_pos _).le, hh, div_eq_mul_inv, mul_comm] using hm

theorem nativeArgument_q (L : ActualPrimary.Label B N0) {x : Absolute}
    (hx : x ∈ absoluteDomain) :
    nativeQ (nativeArgument L x) = absoluteQ x / ChartScales.Q (BaseChartJets.cellBand L) := by
  have hh : CoordinateAlgebra.D ActualPrimary.h = (1 - 2 * ActualPrimary.h) / 2 := by
    unfold CoordinateAlgebra.D
    ring
  have he := stableQ_scale
    (a := 2 * ActualPrimary.h) (mul_pos (by norm_num) ActualPrimary.outgoing.data.h_pos)
    (by nlinarith [ActualPrimary.outgoing.data.h_lt_half])
    (inv_pos.mpr (ChartScales.Q_pos (BaseChartJets.cellBand L))) hx
  change OffplaneCorrectionExtensions.stableQ (2 * ActualPrimary.h)
    (x.1.1.2.2 / ChartScales.Q (BaseChartJets.cellBand L),
      x.1.1.2.1 / ChartScales.Q (BaseChartJets.cellBand L) ^ CoordinateAlgebra.D ActualPrimary.h) = _
  simpa only [Real.inv_rpow (ChartScales.Q_pos _).le, hh, div_eq_mul_inv, mul_comm, absoluteQ] using he

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {L : ActualPrimary.Label B N0} {f : Native → E}

noncomputable def ModelContinuation.absolute (e : ModelContinuation L f) (j : Fin 2) (c : ℝ)
    (x : Absolute) : E := c • e.periodized j (nativeArgument L x)

theorem ModelContinuation.absolute_smooth (e : ModelContinuation L f) (j : Fin 2) (c : ℝ) :
    ContDiffOn ℝ ∞ (e.absolute j c) absoluteDomain :=
  ((e.periodized_smooth j).comp (nativeArgument_smooth L).contDiffOn
    (fun _ hx => nativeArgument_mem L hx)).const_smul c

theorem ModelContinuation.absolute_supported (e : ModelContinuation L f) (j : Fin 2) (c : ℝ)
    {x : Absolute} (hx : x ∈ absoluteDomain) (hn : e.absolute j c x ≠ 0) :
    x.1.1.1 ∈ Icc (absoluteLength x * PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (absoluteLength x * PrimaryTargetBounds.rightRadius ActualPrimary.nominal) := by
  have hp : e.periodized j (nativeArgument L x) ≠ 0 := by
    intro hz
    exact hn (by simp only [ModelContinuation.absolute, hz, smul_zero])
  have hr := e.periodized_radial j (nativeArgument_mem L hx) hp
  rw [nativeArgument_q L hx,
    Real.sqrt_div (show 0 ≤ absoluteQ x from (OffplaneCorrectionExtensions.stableQ_pos hx).le)] at hr
  change x.1.1.1 / Real.sqrt (ChartScales.Q (BaseChartJets.cellBand L)) ∈ _ at hr
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div] at hr
  exact ⟨(div_le_div_iff_of_pos_right (Real.sqrt_pos.mpr (ChartScales.Q_pos _))).mp hr.1,
    (div_le_div_iff_of_pos_right (Real.sqrt_pos.mpr (ChartScales.Q_pos _))).mp hr.2⟩

end AbsoluteCoordinates

section AbsoluteFields

variable {B N0 : ℕ}

noncomputable def absoluteAmplitude (j : Fin 2) (L : ActualPrimary.Label B N0) :
    Absolute → HarmonicCalculus.ComplexVector :=
  ((velocityContinuation j L).map CurlClassBounds.complexify).absolute j
    (ChartScales.Q (BaseChartJets.cellBand L) ^ (-CoordinateAlgebra.A ActualPrimary.h))

noncomputable def absolutePressure (j : Fin 2) (L : ActualPrimary.Label B N0) : Absolute → ℂ :=
  (pressureContinuation j L).absolute j
    (ChartScales.Q (BaseChartJets.cellBand L) ^ (-(2 * CoordinateAlgebra.A ActualPrimary.h)))

theorem absoluteAmplitude_smooth (j : Fin 2) (L : ActualPrimary.Label B N0) :
    ContDiffOn ℝ ∞ (absoluteAmplitude j L) absoluteDomain :=
  ModelContinuation.absolute_smooth _ _ _

theorem absolutePressure_smooth (j : Fin 2) (L : ActualPrimary.Label B N0) :
    ContDiffOn ℝ ∞ (absolutePressure j L) absoluteDomain :=
  ModelContinuation.absolute_smooth _ _ _

theorem absoluteAmplitude_agrees (j : Fin 2) (L : ActualPrimary.Label B N0) {x : Absolute}
    (ht : 0 < x.1.1.2.2) : absoluteAmplitude j L x = ActualPrimary.absoluteAmplitude j L x.1 := by
  unfold absoluteAmplitude ModelContinuation.absolute
  rw [ModelContinuation.periodized_agrees _ _ (div_pos ht (ChartScales.Q_pos _))]
  rfl

theorem absolutePressure_agrees (j : Fin 2) (L : ActualPrimary.Label B N0) {x : Absolute}
    (ht : 0 < x.1.1.2.2) : absolutePressure j L x = ActualPrimary.absolutePressure j L x.1 := by
  unfold absolutePressure ModelContinuation.absolute
  rw [ModelContinuation.periodized_agrees _ _ (div_pos ht (ChartScales.Q_pos _))]
  rfl

theorem absoluteAmplitude_supported (j : Fin 2) (L : ActualPrimary.Label B N0) {x : Absolute}
    (hx : x ∈ absoluteDomain) (hn : absoluteAmplitude j L x ≠ 0) :
    x.1.1.1 ∈ Icc (absoluteLength x * PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (absoluteLength x * PrimaryTargetBounds.rightRadius ActualPrimary.nominal) :=
  ModelContinuation.absolute_supported _ _ _ hx hn

theorem absolutePressure_supported (j : Fin 2) (L : ActualPrimary.Label B N0) {x : Absolute}
    (hx : x ∈ absoluteDomain) (hn : absolutePressure j L x ≠ 0) :
    x.1.1.1 ∈ Icc (absoluteLength x * PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (absoluteLength x * PrimaryTargetBounds.rightRadius ActualPrimary.nominal) :=
  ModelContinuation.absolute_supported _ _ _ hx hn

end AbsoluteFields

section AbsoluteCurl

open HarmonicCalculus

variable {B N0 : ℕ}

noncomputable def absolutePhase (j : Fin 2) (L : ActualPrimary.Label B N0) (x : Absolute) : ℝ :=
  (PrimaryGeometryAssembly.angularMode ActualPrimary.certificate ActualPrimary.modulation
    (ActualPrimary.choice B N0).prepared j L : ℝ) * x.2 +
  ChartScales.carrier ActualPrimary.h (BaseChartJets.cellBand L) *
    ActualCorrectionModels.periodicPhase ActualPrimary.certificate ActualPrimary.modulation
      (ActualPrimary.choice B N0).prepared ActualPrimary.slots.radius_pos j L
      (ActualPrimary.geometry j L) (ActualPrimary.clockWindow L) (nativeArgument L x)

theorem absolutePhase_smooth (j : Fin 2) (L : ActualPrimary.Label B N0) :
    ContDiffOn ℝ ∞ (absolutePhase j L) positiveAbsoluteDomain := by
  have hm : MapsTo (nativeArgument L) positiveAbsoluteDomain
      (ActualCorrectionModels.positiveStableDomain ActualPrimary.h ×ˢ (univ : Set Plane)) := by
    intro x hx
    exact ⟨⟨nativeArgument_mem L hx.2, div_pos hx.1 (Real.sqrt_pos.mpr (ChartScales.Q_pos _))⟩, mem_univ _⟩
  exact (contDiffOn_const.mul contDiffOn_snd).add (contDiffOn_const.mul
    ((ActualCorrectionModels.periodicPhase_smooth ActualPrimary.certificate ActualPrimary.modulation
      (ActualPrimary.choice B N0).prepared ActualPrimary.slots.radius_pos j L
      (ActualPrimary.geometry j L) (ActualPrimary.clockWindow L)).comp
        (nativeArgument_smooth L).contDiffOn hm))

theorem absolutePhase_agrees (j : Fin 2) (L : ActualPrimary.Label B N0) {x : Absolute}
    (ht : 0 < x.1.1.2.2) : absolutePhase j L x = ActualPrimary.absolutePhase j L x := by
  unfold absolutePhase
  rw [ActualCorrectionModels.periodicPhase_eq _ _ _ _ _ _ _ _
    (div_pos ht (ChartScales.Q_pos _))]
  rfl

theorem absolutePhase_angular (j : Fin 2) (L : ActualPrimary.Label B N0) :
    CopyAngularInvariance.AffinePhase ((0 : ActualPrimary.AbsolutePoint), 1)
      (PrimaryGeometryAssembly.angularMode ActualPrimary.certificate ActualPrimary.modulation
        (ActualPrimary.choice B N0).prepared j L : ℝ) (absolutePhase j L) := by
  intro x t
  simp only [absolutePhase, nativeArgument, Prod.fst_add, Prod.smul_fst,
    smul_zero, add_zero, Prod.snd_add, Prod.smul_snd, smul_eq_mul, mul_one]
  ring

noncomputable def absoluteCutAmplitude (j : Fin 2) (L : ActualPrimary.Label B N0) (x : Absolute) :
    ComplexVector := ActualPrimary.periodicGaussian j L x.1.2 • absoluteAmplitude j L x

noncomputable def absoluteCutPressure (j : Fin 2) (L : ActualPrimary.Label B N0) (x : Absolute) : ℂ :=
  ActualPrimary.periodicGaussian j L x.1.2 • absolutePressure j L x

noncomputable def absoluteNormal (j : Fin 2) (L : ActualPrimary.Label B N0) :
    Absolute → ProblemStatement.Space :=
  phaseNormal ActualPrimaryCoherence.absoluteRadius ActualPrimaryCoherence.absoluteRadial
    ActualPrimaryCoherence.absoluteAngular ActualPrimaryCoherence.absoluteAxial (absolutePhase j L)

noncomputable def absoluteExactAmplitude (j : Fin 2) (L : ActualPrimary.Label B N0) :
    Absolute → ComplexVector :=
  CurlClassBounds.realizedCoefficient 1 ActualPrimaryCoherence.absoluteRadius
    ActualPrimaryCoherence.absoluteRadial ActualPrimaryCoherence.absoluteAngular
    ActualPrimaryCoherence.absoluteAxial (absolutePhase j L) (absoluteCutAmplitude j L)

noncomputable def absoluteGaussian (j : Fin 2) (L : ActualPrimary.Label B N0) (x : Absolute) :
    ComplexVector :=
  along ActualPrimaryCoherence.absoluteFast (fun y => ActualPrimary.periodicGaussian j L y.1.2) x •
    absoluteAmplitude j L x

theorem absoluteCutAmplitude_smooth (j : Fin 2) (L : ActualPrimary.Label B N0) :
    ContDiffOn ℝ ∞ (absoluteCutAmplitude j L) absoluteDomain :=
  (ActualPrimaryCoherence.absoluteCutoff_smooth j L).contDiffOn.smul (absoluteAmplitude_smooth j L)

theorem absoluteCutPressure_smooth (j : Fin 2) (L : ActualPrimary.Label B N0) :
    ContDiffOn ℝ ∞ (absoluteCutPressure j L) absoluteDomain :=
  (ActualPrimaryCoherence.absoluteCutoff_smooth j L).contDiffOn.smul (absolutePressure_smooth j L)

theorem absoluteRadial_smooth :
    ContDiffOn ℝ ∞ ActualPrimaryCoherence.absoluteRadial positiveAbsoluteDomain := by
  intro x hx
  have hr : ContDiffAt ℝ ∞ (fun y : Absolute =>
      RadialPullback.radialJacobian (ChartScales.radialExponent ActualPrimary.h) y.1.1.1) x :=
    contDiffAt_const.mul (contDiffAt_fst.fst.fst.rpow_const_of_ne hx.1.ne')
  exact ((contDiffAt_const.prodMk (hr.smul contDiffAt_const)).prodMk contDiffAt_const).contDiffWithinAt

theorem absoluteNormal_smooth (j : Fin 2) (L : ActualPrimary.Label B N0) :
    ContDiffOn ℝ ∞ (absoluteNormal j L) positiveAbsoluteDomain := by
  apply (contDiffOn_piLp 2).mpr
  intro i
  fin_cases i
  · exact contDiffOn_along positiveAbsoluteDomain_open absoluteRadial_smooth (absolutePhase_smooth j L)
  · exact (contDiffOn_along positiveAbsoluteDomain_open contDiffOn_const (absolutePhase_smooth j L)).div
      contDiffOn_fst.fst.fst (fun x hx => hx.1.ne')
  · exact contDiffOn_along positiveAbsoluteDomain_open contDiffOn_const (absolutePhase_smooth j L)

theorem absoluteNormal_ne (j : Fin 2) (L : ActualPrimary.Label B N0) {x : Absolute}
    (hx : x ∈ positiveAbsoluteDomain) : absoluteNormal j L x ≠ 0 := by
  have hd := (absolutePhase_angular j L).directional_eq
    (((absolutePhase_smooth j L).contDiffAt (positiveAbsoluteDomain_open.mem_nhds hx)).differentiableAt (by simp))
  have hc : absoluteNormal j L x 1 =
      (PrimaryGeometryAssembly.angularMode ActualPrimary.certificate ActualPrimary.modulation
        (ActualPrimary.choice B N0).prepared j L : ℝ) / x.1.1.1 := by
    simpa only [absoluteNormal, phaseNormal, ActualPrimaryCoherence.absoluteAngular,
      ActualPrimaryCoherence.absoluteRadius, along, PiLp.single_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
      using congrArg (fun a : ℝ => a / x.1.1.1) hd
  have hp : (PrimaryGeometryAssembly.angularMode ActualPrimary.certificate ActualPrimary.modulation
      (ActualPrimary.choice B N0).prepared j L : ℝ) ≠ 0 :=
    Int.cast_ne_zero.mpr (PrimaryGeometryAssembly.angularMode_ne_zero ActualPrimary.certificate
      ActualPrimary.modulation (ActualPrimary.choice B N0).prepared j L)
  intro hz
  have he := congrArg (fun v : ProblemStatement.Space => v 1) hz
  change absoluteNormal j L x 1 = 0 at he
  rw [hc] at he
  exact div_ne_zero hp hx.1.ne' he

theorem absoluteExactAmplitude_smooth_positive (j : Fin 2) (L : ActualPrimary.Label B N0) :
    ContDiffOn ℝ ∞ (absoluteExactAmplitude j L) positiveAbsoluteDomain := by
  have ha : ContDiffOn ℝ ∞ (absoluteCutAmplitude j L) positiveAbsoluteDomain :=
    (absoluteCutAmplitude_smooth j L).mono (fun _ hx => hx.2)
  have hb := CurlClassBounds.normalCoefficient_contDiffOn (absoluteNormal_smooth j L) ha
    (fun _ hx => absoluteNormal_ne j L hx)
  have hc := CurlClassBounds.cylindricalCurl_contDiffOn positiveAbsoluteDomain_open
    (R := ActualPrimaryCoherence.absoluteRadius) (Vθ := ActualPrimaryCoherence.absoluteAngular)
    (Vz := ActualPrimaryCoherence.absoluteAxial)
    (contDiffOn_fst.fst.fst.inv (fun x hx => hx.1.ne')) absoluteRadial_smooth
    contDiffOn_const contDiffOn_const hb
  exact ha.add ((hc.const_smul Complex.I).const_smul (1 / (1 : ℝ)))

theorem absoluteGaussian_smooth (j : Fin 2) (L : ActualPrimary.Label B N0) :
    ContDiffOn ℝ ∞ (absoluteGaussian j L) absoluteDomain :=
  (contDiffOn_along absoluteDomain_open contDiffOn_const
    (ActualPrimaryCoherence.absoluteCutoff_smooth j L).contDiffOn).smul (absoluteAmplitude_smooth j L)

end AbsoluteCurl

section AbsoluteSupport

open HarmonicCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def AbsoluteSupported (f : Absolute → E) : Prop :=
  ∀ x, x ∈ absoluteDomain → f x ≠ 0 →
    x.1.1.1 ∈ Icc (absoluteLength x * PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (absoluteLength x * PrimaryTargetBounds.rightRadius ActualPrimary.nominal)

omit [NormedSpace ℝ E] in
theorem zero_germ_of_absoluteSupported {f : Absolute → E} (hf : AbsoluteSupported f)
    {x : Absolute} (hx : x ∈ absoluteDomain)
    (hr : x.1.1.1 ∉ Icc (absoluteLength x * PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (absoluteLength x * PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) :
    f =ᶠ[𝓝 x] fun _ => 0 := by
  have hl := (absoluteLength_smooth.contDiffAt (absoluteDomain_open.mem_nhds hx)).continuousAt
  have hR : ContinuousAt (fun y : Absolute => y.1.1.1) x := continuous_fst.fst.fst.continuousAt
  have hout : x.1.1.1 < absoluteLength x * PrimaryTargetBounds.leftRadius ActualPrimary.nominal ∨
      absoluteLength x * PrimaryTargetBounds.rightRadius ActualPrimary.nominal < x.1.1.1 := by
    by_cases hl : absoluteLength x * PrimaryTargetBounds.leftRadius ActualPrimary.nominal ≤ x.1.1.1
    · exact Or.inr (lt_of_not_ge (fun hh => hr ⟨hl, hh⟩))
    · exact Or.inl (lt_of_not_ge hl)
  rcases hout with hr | hr
  · have he := hR.eventually_lt (hl.mul_const _) hr
    filter_upwards [he, absoluteDomain_open.mem_nhds hx] with y hy hyD
    by_contra hn
    exact (not_lt_of_ge (hf y hyD hn).1) hy
  · have he := (hl.mul_const _).eventually_lt hR hr
    filter_upwards [he, absoluteDomain_open.mem_nhds hx] with y hy hyD
    by_contra hn
    exact (not_lt_of_ge (hf y hyD hn).2) hy

theorem outside_absolute_shell_of_nonpositive {x : Absolute} (hx : x ∈ absoluteDomain)
    (hr : x.1.1.1 ≤ 0) :
    x.1.1.1 ∉ Icc (absoluteLength x * PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (absoluteLength x * PrimaryTargetBounds.rightRadius ActualPrimary.nominal) := by
  intro hi
  exact (not_lt_of_ge hr) ((mul_pos (absoluteLength_pos hx)
    (PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal)).trans_le hi.1)

variable {B N0 : ℕ}

theorem absoluteCutAmplitude_supported (j : Fin 2) (L : ActualPrimary.Label B N0) :
    AbsoluteSupported (absoluteCutAmplitude j L) := by
  intro x hx hn
  apply absoluteAmplitude_supported j L hx
  intro hz
  exact hn (by simp only [absoluteCutAmplitude, hz, smul_zero])

theorem absoluteCutPressure_supported (j : Fin 2) (L : ActualPrimary.Label B N0) :
    AbsoluteSupported (absoluteCutPressure j L) := by
  intro x hx hn
  apply absolutePressure_supported j L hx
  intro hz
  exact hn (by simp only [absoluteCutPressure, hz, smul_zero])

theorem absoluteGaussian_supported (j : Fin 2) (L : ActualPrimary.Label B N0) :
    AbsoluteSupported (absoluteGaussian j L) := by
  intro x hx hn
  apply absoluteAmplitude_supported j L hx
  intro hz
  exact hn (by simp only [absoluteGaussian, hz, smul_zero])

theorem absoluteExactAmplitude_tsupport (j : Fin 2) (L : ActualPrimary.Label B N0) :
    tsupport (absoluteExactAmplitude j L) ⊆ tsupport (absoluteCutAmplitude j L) := by
  unfold absoluteExactAmplitude CurlClassBounds.realizedCoefficient CurlClassBounds.curlRemainder
  exact (tsupport_add _ _).trans (union_subset subset_rfl
    ((tsupport_smul_subset_right _ _).trans ((tsupport_smul_subset_right _ _).trans
      ((CurlClassBounds.cylindricalCurl_tsupport_subset _ _ _ _ _).trans
        (CurlClassBounds.coefficient_tsupport_subset _ _ _ _ _ _)))))

theorem absoluteExactAmplitude_supported (j : Fin 2) (L : ActualPrimary.Label B N0) :
    AbsoluteSupported (absoluteExactAmplitude j L) := by
  intro x hx hn
  by_contra hr
  have hg := zero_germ_of_absoluteSupported (absoluteCutAmplitude_supported j L) hx hr
  have hzero : absoluteExactAmplitude j L =ᶠ[𝓝 x] fun _ => 0 :=
    notMem_tsupport_iff_eventuallyEq.mp
      (fun hm => (notMem_tsupport_iff_eventuallyEq.mpr hg) (absoluteExactAmplitude_tsupport j L hm))
  exact hn hzero.eq_of_nhds

theorem absoluteExactAmplitude_smooth (j : Fin 2) (L : ActualPrimary.Label B N0) :
    ContDiffOn ℝ ∞ (absoluteExactAmplitude j L) absoluteDomain := by
  intro x hx
  by_cases hr : 0 < x.1.1.1
  · exact ((absoluteExactAmplitude_smooth_positive j L).contDiffAt
      (positiveAbsoluteDomain_open.mem_nhds ⟨hr, hx⟩)).contDiffWithinAt
  · exact (contDiffAt_const.congr_of_eventuallyEq
      (zero_germ_of_absoluteSupported (absoluteExactAmplitude_supported j L) hx
        (outside_absolute_shell_of_nonpositive hx (le_of_not_gt hr)))).contDiffWithinAt

end AbsoluteSupport

section ExactAgreement

open HarmonicCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem realizedCoefficient_eqOn {U : Set E} (hU : IsOpen U) (K : ℝ)
    (R : E → ℝ) (Vr Vθ Vz : E → E) {Φ Ψ : E → ℝ} {a b : E → ComplexVector}
    (hp : EqOn Φ Ψ U) (ha : EqOn a b U) :
    EqOn (CurlClassBounds.realizedCoefficient K R Vr Vθ Vz Φ a)
      (CurlClassBounds.realizedCoefficient K R Vr Vθ Vz Ψ b) U := by
  have hn : EqOn (phaseNormal R Vr Vθ Vz Φ) (phaseNormal R Vr Vθ Vz Ψ) U := by
    intro x hx
    ext i
    fin_cases i <;> simp only [phaseNormal, along_congr hU hp hx]
  have hb : EqOn (CurlClassBounds.coefficient R Vr Vθ Vz Φ a)
      (CurlClassBounds.coefficient R Vr Vθ Vz Ψ b) U := by
    intro x hx
    simp only [CurlClassBounds.coefficient, hn hx, ha hx]
  intro x hx
  have he := PhysicalCurlCovariance.cylindricalCurl_congr
    (R := R) (Vr := Vr) (Vθ := Vθ) (Vz := Vz)
    (eventually_of_mem (hU.mem_nhds hx) hb)
  simp only [CurlClassBounds.realizedCoefficient, CurlClassBounds.curlRemainder, ha hx, he]

variable {B N0 : ℕ}

theorem absoluteExactAmplitude_agrees (j : Fin 2) (L : ActualPrimary.Label B N0) {x : Absolute}
    (ht : 0 < x.1.1.2.2) :
    absoluteExactAmplitude j L x = ActualPrimaryCoherence.absoluteExactAmplitude j L x := by
  apply realizedCoefficient_eqOn ActualPrimaryCoherence.positiveAbsolute_open
    1 _ _ _ _ (fun y hy => absolutePhase_agrees j L hy) _ ht
  intro y hy
  exact congrArg (fun a => ActualPrimary.periodicGaussian j L y.1.2 • a)
    (absoluteAmplitude_agrees j L hy)

theorem absoluteCutPressure_agrees (j : Fin 2) (L : ActualPrimary.Label B N0) {x : Absolute}
    (ht : 0 < x.1.1.2.2) : absoluteCutPressure j L x =
      ActualPrimary.periodicGaussian j L x.1.2 • ActualPrimary.absolutePressure j L x.1 := by
  exact congrArg (fun p => ActualPrimary.periodicGaussian j L x.1.2 • p) (absolutePressure_agrees j L ht)

theorem absoluteGaussian_agrees (j : Fin 2) (L : ActualPrimary.Label B N0) {x : Absolute}
    (ht : 0 < x.1.1.2.2) : absoluteGaussian j L x =
      ActualPrimaryCoherence.absoluteGaussianCoefficient j L x := by
  exact congrArg (fun a => along ActualPrimaryCoherence.absoluteFast
    (fun y : Absolute => ActualPrimary.periodicGaussian j L y.1.2) x • a)
    (absoluteAmplitude_agrees j L ht)

end ExactAgreement

section ChartFields

open HarmonicCalculus

noncomputable def absoluteLift (n : ℕ) (x : Point) : Absolute :=
  ActualPrimaryCoherence.absoluteChart n (x, 0)

theorem absoluteLift_smooth (n : ℕ) : ContDiff ℝ ∞ (absoluteLift n) :=
  (ActualPrimaryCoherence.absoluteChart n).contDiff.comp (contDiff_id.prodMk contDiff_const)

theorem absoluteLift_mem (n : ℕ) {x : Point}
    (hx : x.2.1 ∈ PositiveRepresentatives.stableTarget (2 * ActualPrimary.h)) :
    absoluteLift n x ∈ absoluteDomain := by
  have he : CoordinateAlgebra.D ActualPrimary.h = (1 - 2 * ActualPrimary.h) / 2 := by
    unfold CoordinateAlgebra.D
    ring
  simpa only [absoluteLift, ActualPrimaryCoherence.absoluteChart_apply, ActualPrimary.toAbsolute,
    absoluteDomain, Set.mem_ofPred_eq, he] using stableTarget_scale (ChartScales.Q_pos n) hx

theorem absoluteLift_length (n : ℕ) {x : Point}
    (hx : x.2.1 ∈ PositiveRepresentatives.stableTarget (2 * ActualPrimary.h)) :
    absoluteLength (absoluteLift n x) = Real.sqrt (ChartScales.Q n) *
      OffplaneCorrectionExtensions.stableLength (2 * ActualPrimary.h) x.2.1 := by
  have he : CoordinateAlgebra.D ActualPrimary.h = (1 - 2 * ActualPrimary.h) / 2 := by
    unfold CoordinateAlgebra.D
    ring
  change Real.sqrt (OffplaneCorrectionExtensions.stableQ (2 * ActualPrimary.h)
    (ChartScales.Q n * x.2.1.1, ChartScales.Q n ^ CoordinateAlgebra.D ActualPrimary.h * x.2.1.2)) = _
  rw [he, stableQ_scale (mul_pos (by norm_num) ActualPrimary.outgoing.data.h_pos)
    (by nlinarith [ActualPrimary.outgoing.data.h_lt_half]) (ChartScales.Q_pos n) hx,
    Real.sqrt_mul (ChartScales.Q_pos n).le]
  rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def chartValue (a : ℝ) (f : Absolute → E) (n : ℕ) (x : Point) : E :=
  ChartScales.Q n ^ a • f (absoluteLift n x)

variable (W : OffplaneCorrectionExtensions.Window (2 * ActualPrimary.h)
  (PrimaryTargetBounds.leftRadius ActualPrimary.nominal) (PrimaryTargetBounds.rightRadius ActualPrimary.nominal))

theorem chartValue_smooth (a : ℝ) {f : Absolute → E} (hf : ContDiffOn ℝ ∞ f absoluteDomain) (n : ℕ) :
    ContDiffOn ℝ ∞ (chartValue a f n) (PhysicalMeanDomain.slowDomain W.carrier) :=
  (hf.comp (absoluteLift_smooth n).contDiffOn (fun _ hx => absoluteLift_mem n (W.stable hx))).const_smul _

theorem chartValue_supported (a : ℝ) {f : Absolute → E} (hf : AbsoluteSupported f) (n : ℕ) :
    WaveStageContinuation.RadialSupport (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)
      (OffplaneCorrectionExtensions.stableLength (2 * ActualPrimary.h)) W.carrier (chartValue a f n) := by
  intro x hx hn
  have hn' : f (absoluteLift n x) ≠ 0 := by
    intro hz
    exact hn (by simp only [chartValue, hz, smul_zero])
  have hr := hf (absoluteLift n x) (absoluteLift_mem n (W.stable hx)) hn'
  rw [absoluteLift_length n (W.stable hx)] at hr
  change Real.sqrt (ChartScales.Q n) * x.1 ∈ _ at hr
  simp only [mul_assoc] at hr
  exact ⟨(mul_le_mul_iff_right₀ (Real.sqrt_pos.mpr (ChartScales.Q_pos n))).mp hr.1,
    (mul_le_mul_iff_right₀ (Real.sqrt_pos.mpr (ChartScales.Q_pos n))).mp hr.2⟩

variable {B N0 : ℕ}

noncomputable def velocityField (j : Fin 2) (L : ActualPrimary.Label B N0) (n : ℕ) :
    WaveStageContinuation.FieldContinuation W
      (fun x => (ActualPrimary.piece ActualPrimary.standardRegion j L).exactCoefficients.amplitude n (x, 0)) where
  value := chartValue (CoordinateAlgebra.A ActualPrimary.h) (absoluteExactAmplitude j L) n
  smooth := chartValue_smooth W _ (absoluteExactAmplitude_smooth j L) n
  supported := chartValue_supported W _ (absoluteExactAmplitude_supported j L) n
  agrees := by
    intro x hx
    unfold chartValue
    rw [absoluteExactAmplitude_agrees j L (mul_pos (ChartScales.Q_pos n) hx.2)]
    exact (ActualPrimaryCoherence.exactAmplitude_representation ActualPrimary.standardRegion j L n (x, 0)).symm

noncomputable def pressureField (j : Fin 2) (L : ActualPrimary.Label B N0) (n : ℕ) :
    WaveStageContinuation.FieldContinuation W
      (fun x => (ActualPrimary.piece ActualPrimary.standardRegion j L).exactCoefficients.pressure n (x, 0)) where
  value := chartValue (2 * CoordinateAlgebra.A ActualPrimary.h) (absoluteCutPressure j L) n
  smooth := chartValue_smooth W _ (absoluteCutPressure_smooth j L) n
  supported := chartValue_supported W _ (absoluteCutPressure_supported j L) n
  agrees := by
    intro x hx
    unfold chartValue
    rw [absoluteCutPressure_agrees j L (mul_pos (ChartScales.Q_pos n) hx.2)]
    let q := ChartScales.Q n ^ (2 * CoordinateAlgebra.A ActualPrimary.h)
    let t := ActualPrimary.periodicGaussian j L (ActualPrimary.toAbsolute n x).2
    let p := ActualPrimary.absolutePressure j L (ActualPrimary.toAbsolute n x)
    change q • (t • p) = (t : ℂ) * (q • p)
    simp only [Complex.real_smul]
    ring

noncomputable def gaussianField (j : Fin 2) (L : ActualPrimary.Label B N0) (n : ℕ) :
    WaveStageContinuation.FieldContinuation W
      (fun x => LinearWaveBounds.excludedSlotError (ActualPrimary.piece ActualPrimary.standardRegion j L).directions
        (ActualPrimary.chartCutoff j L) (ActualPrimary.chartCoefficients j L).amplitude 0 n (x, 0)) where
  value := chartValue (2 * CoordinateAlgebra.A ActualPrimary.h + 1 / 2) (absoluteGaussian j L) n
  smooth := chartValue_smooth W _ (absoluteGaussian_smooth j L) n
  supported := chartValue_supported W _ (absoluteGaussian_supported j L) n
  agrees := by
    intro x hx
    unfold chartValue
    rw [absoluteGaussian_agrees j L (mul_pos (ChartScales.Q_pos n) hx.2)]
    exact (ActualPrimaryCoherence.gaussianCoefficient_representation ActualPrimary.standardRegion j L n (x, 0)).symm

noncomputable def chartPhase (j : Fin 2) (L : ActualPrimary.Label B N0) (n : ℕ) (x : Point) : ℝ :=
  absolutePhase j L (absoluteLift n x) / ChartScales.carrier ActualPrimary.h n

theorem chartPhase_smooth (j : Fin 2) (L : ActualPrimary.Label B N0) (n : ℕ) :
    ContDiffOn ℝ ∞ (chartPhase j L n) (LocalRankDefect.positiveDomain W.carrier) := by
  apply ((absolutePhase_smooth j L).comp (absoluteLift_smooth n).contDiffOn ?_).div_const
  intro x hx
  exact ⟨mul_pos (Real.sqrt_pos.mpr (ChartScales.Q_pos n)) hx.1,
    absoluteLift_mem n (W.stable hx.2)⟩

theorem chartPhase_agrees (j : Fin 2) (L : ActualPrimary.Label B N0) (n : ℕ) :
    OffplaneCorrectionExtensions.FiberAgreement W.carrier (chartPhase j L n)
      (fun x => (ActualPrimary.chartCoefficients j L).phase n (x, 0)) := by
  intro x hx
  unfold chartPhase
  rw [absolutePhase_agrees j L (mul_pos (ChartScales.Q_pos n) hx.2)]
  rfl

end ChartFields

section HarmonicPackaging

open HarmonicFields
open scoped ComplexConjugate

variable {coord a b : ℝ} {W : OffplaneCorrectionExtensions.Window coord a b}

noncomputable def zeroField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    WaveStageContinuation.FieldContinuation W (fun _ : Point => (0 : E)) where
  value := fun _ => 0
  smooth := contDiffOn_const
  supported := fun _ _ hn => (hn rfl).elim
  agrees := fun _ _ => rfl

noncomputable def pairField {f : Point → ℂ} (e : WaveStageContinuation.FieldContinuation W f)
    (k : ℤ) : WaveStageContinuation.FieldContinuation W (ErrorHarmonics.conjugatePair 1 f k) where
  value x := ErrorHarmonics.conjugatePair 1 e.value k x
  smooth := by
    classical
    have hs (m : ℤ) : ContDiffOn ℝ ∞ (fun x =>
        (AddMonoidAlgebra.single 1 (fun y => e.value y / 2) : Coefficients Point) m x)
        (PhysicalMeanDomain.slowDomain W.carrier) := by
      change ContDiffOn ℝ ∞ (fun x => Finsupp.single (1 : ℤ) (fun y => e.value y / 2) m x) _
      by_cases hm : (1 : ℤ) = m
      · simpa only [Finsupp.single_apply, ite_eq_left hm] using e.smooth.div_const (2 : ℂ)
      · simpa only [Finsupp.single_apply, ite_eq_right hm, Pi.zero_apply] using
          (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : Point => (0 : ℂ)) _)
    exact (hs k).add ((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp_contDiffOn (hs (-k)))
  supported := by
    intro x hx hn
    apply e.supported x hx
    intro hz
    apply hn
    classical
    change Finsupp.single (1 : ℤ) (fun y => e.value y / 2) k x +
      (starRingEnd ℂ) (Finsupp.single (1 : ℤ) (fun y => e.value y / 2) (-k) x) = 0
    simp [Finsupp.single_apply, ite_apply, hz]
  agrees := by
    intro x hx
    classical
    change Finsupp.single (1 : ℤ) (fun y => e.value y / 2) k x +
      (starRingEnd ℂ) (Finsupp.single (1 : ℤ) (fun y => e.value y / 2) (-k) x) =
      Finsupp.single (1 : ℤ) (fun y => f y / 2) k x +
      (starRingEnd ℂ) (Finsupp.single (1 : ℤ) (fun y => f y / 2) (-k) x)
    simp [Finsupp.single_apply, ite_apply, e.agrees hx]

variable {B N0 : ℕ}

abbrev Index (B N0 : ℕ) := ActualPrimary.Label B N0 × Fin 2

noncomputable def primaryPiece (l : Index B N0) :=
  ActualPrimary.piece ActualPrimary.standardRegion l.2 l.1

noncomputable def primaryPhase (l : Index B N0) (n : ℕ) (x : Point) : ℝ :=
  (primaryPiece l).coefficients.phase n (x, 0)

noncomputable def angularMode (l : Index B N0) (_n : ℕ) : ℤ :=
  PrimaryGeometryAssembly.angularMode ActualPrimary.certificate ActualPrimary.modulation
    (ActualPrimary.choice B N0).prepared l.2 l.1

noncomputable def primaryBlock (l : Index B N0) : CorrectionState.HarmonicBlock Point :=
  (primaryPiece l).harmonicBlock (primaryPhase l) (angularMode l)

noncomputable def gaussianBlock (l : Index B N0) : CorrectionState.HarmonicBlock Point :=
  (primaryPiece l).excludedBlock (primaryPhase l) (angularMode l)

variable (W : OffplaneCorrectionExtensions.Window (2 * ActualPrimary.h)
  (PrimaryTargetBounds.leftRadius ActualPrimary.nominal) (PrimaryTargetBounds.rightRadius ActualPrimary.nominal))

/-- The harmonic primitives of the literal initial family, from the same
chosen native data.  No continuation of an output field is assumed. -/
noncomputable def harmonicPrimitives (l : Index B N0) :
    WaveStageContinuation.HarmonicPrimitives W (primaryBlock l) (gaussianBlock l).velocity 0 where
  velocity n i k := pairField ((velocityField W l.2 l.1 n).map (ContinuousLinearMap.proj i)) k
  pressure n k := pairField (pressureField W l.2 l.1 n) k
  gaussian n i k := pairField ((gaussianField W l.2 l.1 n).map (ContinuousLinearMap.proj i)) k
  aliasError _ _ _ := zeroField
  phase := chartPhase l.2 l.1
  phase_smooth := chartPhase_smooth W l.2 l.1
  phase_agrees := chartPhase_agrees W l.2 l.1

end HarmonicPackaging

section Periodicity

open HarmonicCalculus

variable {B N0 : ℕ}

noncomputable def absoluteDeck (n : ℕ) (k : TorusInverse.Frequency) : Absolute :=
  ActualPrimaryCoherence.absoluteChart n (ActualPrimaryCoherence.chartDeck k)

noncomputable def pointDeck (k : TorusInverse.Frequency) : Point :=
  (ActualPrimaryCoherence.chartDeck k).1

theorem absoluteDeck_slow (n : ℕ) (k : TorusInverse.Frequency) : (absoluteDeck n k).1.1 = 0 := by
  simp [absoluteDeck, ActualPrimaryCoherence.absoluteChart_apply, ActualPrimaryCoherence.chartDeck,
    ActualPrimary.toAbsolute]

theorem absolute_periodic_of_chart {E : Type*} {f : Absolute → E} (n : ℕ) (k : TorusInverse.Frequency)
    (h : ∀ x : ActualPrimary.FullPoint,
      f (ActualPrimaryCoherence.absoluteChart n (x + ActualPrimaryCoherence.chartDeck k)) =
        f (ActualPrimaryCoherence.absoluteChart n x)) (x : Absolute) :
    f (x + absoluteDeck n k) = f x := by
  simpa only [map_add, ContinuousLinearEquiv.apply_symm_apply, absoluteDeck] using
    h ((ActualPrimaryCoherence.absoluteChart n).symm x)

theorem ModelContinuation.absolute_chart_periodic {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : ActualPrimary.Label B N0} {f : Native → E} (e : ModelContinuation L f)
    (j : Fin 2) (c : ℝ) (n : ℕ)
    (hi : CommonWindow.index ActualPrimary.h n ≤ ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand L))
    (k : TorusInverse.Frequency) (x : ActualPrimary.FullPoint) :
    e.absolute j c (ActualPrimaryCoherence.absoluteChart n (x + ActualPrimaryCoherence.chartDeck k)) =
      e.absolute j c (ActualPrimaryCoherence.absoluteChart n x) := by
  simp only [ModelContinuation.absolute, ModelContinuation.periodized, nativeArgument,
    ActualPrimaryCoherence.absoluteChart_apply, ActualPrimary.toAbsolute, ActualPrimaryCoherence.chartDeck,
    Prod.fst_add, Prod.snd_add, add_zero]
  exact congrArg (fun a : E => c • a) (ActualPrimaryCoherence.native_copy_sum_periodic j L n hi
    (fun Z => e.native (ActualPrimary.nativeSlow L (ActualPrimary.toAbsolute n x.1), Z)) x.1.2.2 k)

theorem absoluteAmplitude_periodic (j : Fin 2) (L : ActualPrimary.Label B N0) (n : ℕ)
    (hi : CommonWindow.index ActualPrimary.h n ≤ ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand L))
    (k : TorusInverse.Frequency) (x : Absolute) :
    absoluteAmplitude j L (x + absoluteDeck n k) = absoluteAmplitude j L x :=
  absolute_periodic_of_chart n k
    (ModelContinuation.absolute_chart_periodic _ j _ n hi k) x

theorem absolutePressure_periodic (j : Fin 2) (L : ActualPrimary.Label B N0) (n : ℕ)
    (hi : CommonWindow.index ActualPrimary.h n ≤ ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand L))
    (k : TorusInverse.Frequency) (x : Absolute) :
    absolutePressure j L (x + absoluteDeck n k) = absolutePressure j L x :=
  absolute_periodic_of_chart n k
    (ModelContinuation.absolute_chart_periodic _ j _ n hi k) x

theorem absoluteCutoff_periodic (j : Fin 2) (L : ActualPrimary.Label B N0) (n : ℕ)
    (hi : CommonWindow.index ActualPrimary.h n ≤ ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand L))
    (k : TorusInverse.Frequency) (x : Absolute) :
    ActualPrimary.periodicGaussian j L (x + absoluteDeck n k).1.2 =
      ActualPrimary.periodicGaussian j L x.1.2 :=
  absolute_periodic_of_chart (f := fun y : Absolute => ActualPrimary.periodicGaussian j L y.1.2)
    n k (ActualPrimaryCoherence.chart_cutoff_periodic j L n hi k) x

theorem absolutePhase_periodic (j : Fin 2) (L : ActualPrimary.Label B N0) (n : ℕ)
    (hi : CommonWindow.index ActualPrimary.h n ≤ ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand L))
    (k : TorusInverse.Frequency) (x : Absolute) :
    absolutePhase j L (x + absoluteDeck n k) = absolutePhase j L x := by
  apply absolute_periodic_of_chart n k _ x
  intro y
  simp only [absolutePhase, ActualCorrectionModels.periodicPhase, PeriodicPhaseAssembly.phase,
    nativeArgument, ActualPrimaryCoherence.absoluteChart_apply, ActualPrimary.toAbsolute, ActualPrimary.nativeSlow,
    ActualPrimaryCoherence.chartDeck, Prod.fst_add, Prod.snd_add, add_zero,
    ActualPrimaryCoherence.native_clock_periodic j L n hi]

theorem absoluteExactAmplitude_periodic (j : Fin 2) (L : ActualPrimary.Label B N0) (n : ℕ)
    (hi : CommonWindow.index ActualPrimary.h n ≤ ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand L))
    (k : TorusInverse.Frequency) (x : Absolute) :
    absoluteExactAmplitude j L (x + absoluteDeck n k) = absoluteExactAmplitude j L x := by
  apply ActualPrimaryCoherence.realizedCoefficient_translate (absoluteDeck n k) 1
  · intro y
    change (y.1.1 + (absoluteDeck n k).1.1).1 = y.1.1.1
    rw [absoluteDeck_slow, add_zero]
  · exact absolutePhase_periodic j L n hi k
  · intro y
    simp only [absoluteCutAmplitude, absoluteCutoff_periodic j L n hi k,
      absoluteAmplitude_periodic j L n hi k]
  · intro y
    simp only [ActualPrimaryCoherence.absoluteRadial, Prod.fst_add, absoluteDeck_slow,
      add_zero]
  · intro y
    rfl
  · intro y
    rfl

theorem absoluteGaussian_periodic (j : Fin 2) (L : ActualPrimary.Label B N0) (n : ℕ)
    (hi : CommonWindow.index ActualPrimary.h n ≤ ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand L))
    (k : TorusInverse.Frequency) (x : Absolute) :
    absoluteGaussian j L (x + absoluteDeck n k) = absoluteGaussian j L x := by
  have hd := ActualPrimaryCoherence.along_translate (absoluteDeck n k)
    (f := fun y : Absolute => ActualPrimary.periodicGaussian j L y.1.2)
    (V := ActualPrimaryCoherence.absoluteFast)
    (absoluteCutoff_periodic j L n hi k) (fun _ => rfl) x
  simp only [absoluteGaussian, absoluteAmplitude_periodic j L n hi k, hd]

theorem absoluteCutPressure_periodic (j : Fin 2) (L : ActualPrimary.Label B N0) (n : ℕ)
    (hi : CommonWindow.index ActualPrimary.h n ≤ ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand L))
    (k : TorusInverse.Frequency) (x : Absolute) :
    absoluteCutPressure j L (x + absoluteDeck n k) = absoluteCutPressure j L x := by
  simp only [absoluteCutPressure, absoluteCutoff_periodic j L n hi k, absolutePressure_periodic j L n hi k]

theorem absoluteLift_add_deck (n : ℕ) (k : TorusInverse.Frequency) (x : Point) :
    absoluteLift n (x + pointDeck k) = absoluteLift n x + absoluteDeck n k := by
  simpa only [absoluteLift, absoluteDeck, pointDeck, ActualPrimaryCoherence.chartDeck,
    Prod.mk_add_mk, add_zero] using
    (ActualPrimaryCoherence.absoluteChart n).map_add (x, 0) (ActualPrimaryCoherence.chartDeck k)

theorem chartValue_periodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) {f : Absolute → E} (n : ℕ) (k : TorusInverse.Frequency)
    (hf : ∀ x, f (x + absoluteDeck n k) = f x) (x : Point) :
    chartValue a f n (x + pointDeck k) = chartValue a f n x := by
  simp only [chartValue, absoluteLift_add_deck, hf]

variable (W : OffplaneCorrectionExtensions.Window (2 * ActualPrimary.h)
  (PrimaryTargetBounds.leftRadius ActualPrimary.nominal) (PrimaryTargetBounds.rightRadius ActualPrimary.nominal))

theorem velocityField_periodic (j : Fin 2) (L : ActualPrimary.Label B N0) (n : ℕ)
    (hi : CommonWindow.index ActualPrimary.h n ≤ ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand L))
    (k : TorusInverse.Frequency) (x : Point) :
    (velocityField W j L n).value (x + pointDeck k) = (velocityField W j L n).value x :=
  chartValue_periodic _ n k (absoluteExactAmplitude_periodic j L n hi k) x

theorem pressureField_periodic (j : Fin 2) (L : ActualPrimary.Label B N0) (n : ℕ)
    (hi : CommonWindow.index ActualPrimary.h n ≤ ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand L))
    (k : TorusInverse.Frequency) (x : Point) :
    (pressureField W j L n).value (x + pointDeck k) = (pressureField W j L n).value x :=
  chartValue_periodic _ n k (absoluteCutPressure_periodic j L n hi k) x

theorem gaussianField_periodic (j : Fin 2) (L : ActualPrimary.Label B N0) (n : ℕ)
    (hi : CommonWindow.index ActualPrimary.h n ≤ ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand L))
    (k : TorusInverse.Frequency) (x : Point) :
    (gaussianField W j L n).value (x + pointDeck k) = (gaussianField W j L n).value x :=
  chartValue_periodic _ n k (absoluteGaussian_periodic j L n hi k) x

theorem chartPhase_periodic (j : Fin 2) (L : ActualPrimary.Label B N0) (n : ℕ)
    (hi : CommonWindow.index ActualPrimary.h n ≤ ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand L))
    (k : TorusInverse.Frequency) (x : Point) :
    chartPhase j L n (x + pointDeck k) = chartPhase j L n x := by
  simp only [chartPhase, absoluteLift_add_deck, absolutePhase_periodic j L n hi k]

end Periodicity

section FinalBindings

variable {B N0 : ℕ}

theorem chartValue_band {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (f : Absolute → E) (n m k : ℕ)
    (hi : CommonWindow.index ActualPrimary.h n + k = CommonWindow.index ActualPrimary.h m) (x : Point) :
    chartValue a f n x = (ChartScales.Q n / ChartScales.Q m) ^ a •
      chartValue a f m (GaugeStateCoherence.bandChartEquiv ActualPrimary.h n m k x) := by
  have he : absoluteLift m (GaugeStateCoherence.bandChartEquiv ActualPrimary.h n m k x) =
      absoluteLift n x := by
    change (ActualPrimary.toAbsolute m _, (0 : ℝ)) = (ActualPrimary.toAbsolute n x, 0)
    rw [ActualPrimaryCoherence.toAbsolute_bandChart n m k hi]
  simp only [chartValue, he, smul_smul]
  rw [mul_comm, ActualPrimaryCoherence.band_power_cancel]

theorem pairField_periodic {coord a b : ℝ} {W : OffplaneCorrectionExtensions.Window coord a b}
    {f : Point → ℂ} (e : WaveStageContinuation.FieldContinuation W f) (m : ℤ) (w : Point)
    (he : ∀ x, e.value (x + w) = e.value x) (x : Point) :
    (pairField e m).value (x + w) = (pairField e m).value x := by
  classical
  change Finsupp.single (1 : ℤ) (fun y => e.value y / 2) m (x + w) +
    (starRingEnd ℂ) (Finsupp.single (1 : ℤ) (fun y => e.value y / 2) (-m) (x + w)) =
    Finsupp.single (1 : ℤ) (fun y => e.value y / 2) m x +
    (starRingEnd ℂ) (Finsupp.single (1 : ℤ) (fun y => e.value y / 2) (-m) x)
  simp [Finsupp.single_apply, ite_apply, he x]

structure HarmonicPeriodicAt {coord a b : ℝ} {W : OffplaneCorrectionExtensions.Window coord a b}
    {block : CorrectionState.HarmonicBlock Point} {G A : HarmonicResidual.BlockCoefficients Point}
    (p : WaveStageContinuation.HarmonicPrimitives W block G A) (n : ℕ) : Prop where
  velocity : ∀ i m k x, (p.velocity n i m).value (x + pointDeck k) = (p.velocity n i m).value x
  pressure : ∀ m k x, (p.pressure n m).value (x + pointDeck k) = (p.pressure n m).value x
  gaussian : ∀ i m k x, (p.gaussian n i m).value (x + pointDeck k) = (p.gaussian n i m).value x
  aliasError : ∀ i m k x, (p.aliasError n i m).value (x + pointDeck k) = (p.aliasError n i m).value x
  phase : ∀ k x, p.phase n (x + pointDeck k) = p.phase n x

variable (W : OffplaneCorrectionExtensions.Window (2 * ActualPrimary.h)
  (PrimaryTargetBounds.leftRadius ActualPrimary.nominal) (PrimaryTargetBounds.rightRadius ActualPrimary.nominal))

theorem harmonicPrimitives_periodic (l : Index B N0) (n : ℕ)
    (hi : CommonWindow.index ActualPrimary.h n ≤ ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand l.1)) :
    HarmonicPeriodicAt (harmonicPrimitives W l) n where
  velocity i m k x := pairField_periodic _ m (pointDeck k)
    (fun y => congrArg (fun a : HarmonicCalculus.ComplexVector => a i) (velocityField_periodic W l.2 l.1 n hi k y)) x
  pressure m k x := pairField_periodic _ m (pointDeck k) (pressureField_periodic W l.2 l.1 n hi k) x
  gaussian i m k x := pairField_periodic _ m (pointDeck k)
    (fun y => congrArg (fun a : HarmonicCalculus.ComplexVector => a i) (gaussianField_periodic W l.2 l.1 n hi k y)) x
  aliasError _ _ _ _ := rfl
  phase := chartPhase_periodic l.2 l.1 n hi

theorem active_index_le {n : ℕ} {l : Index B N0}
    (hl : l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n) :
    CommonWindow.index ActualPrimary.h n ≤ ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand l.1) := by
  have hm := (ActualPrimary.mem_activeLabels ActualPrimary.standardRegion n l.1 l.2).mp hl
  obtain ⟨m, hm, hgrid⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨g, hg, he⟩ := Finset.mem_image.mp hgrid
  apply CommonWindow.index_le
  have he' := congrArg Prod.fst he
  change m = BaseChartJets.cellBand l.1 at he'
  exact he' ▸ hm

/-- Every label actually present in the initial band sum has the required
periods, including after continuation across the time-zero plane. -/
theorem active_harmonicPrimitives_periodic (n : ℕ) (l : Index B N0)
    (hl : l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n) :
    HarmonicPeriodicAt (harmonicPrimitives W l) n :=
  harmonicPrimitives_periodic W l n (active_index_le hl)

end FinalBindings

end NavierStokes.InitialHarmonicContinuation
