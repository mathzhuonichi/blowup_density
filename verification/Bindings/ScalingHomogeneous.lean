import Bindings.Scaling
import NSFormalization.Section4.I03.HomogeneousScaling

/-!
# Homogeneous scaling in the registered vocabulary

The single open analytic input is `CompactHomogeneousRealization`: a measurable
homogeneous datum path for each compact smooth force. This is a realization statement independent of scaling,
not either of the desired estimates. D01 already constructs its slice data;
its negative-order time measurability is not discharged here. The angular
component comparison is proved in HomogeneousScaling. All results below that consume it are conditional.

This file lives in Bindings because Contracts is downstream of NSFormalization.
-/
noncomputable section
namespace NSFormalization.Section4.I03
open Set MeasureTheory
open NSFormalization.Source
open NSFormalization.Paper3 (RealVectorSobolev)
open BlowupDensity.Contracts.V1
open BlowupDensity.Bindings
open scoped ContDiff ENNReal

/-- The single outstanding analytic fact: time strong measurability of D01's
explicit compact homogeneous datum path. All slice pairing and norm statements
are proved, including the negative-order angular norm comparison. -/
def CompactHomogeneousRealization : Prop :=
  ∀ (s : ℝ) (hs : -3 / 2 < s), s < 0 → ∀ (F : VelocityField)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F),
    AEStronglyMeasurable (D01.Homogeneous.compactHomogeneousPath hs hF hc)
      Data.forceTimeMeasure

/-- Exhibit the datum path before taking the registered infimum. -/
theorem forceHomogeneousENorm_le_components (hreal : CompactHomogeneousRealization)
    {s : ℝ} (hs : -3 / 2 < s) (hs0 : s < 0) {F : VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (q : ℝ≥0∞) (hq : 1 ≤ q) :
    Data.forceHomogeneousENorm q s F ≤
      ENNReal.ofReal (frequencyUnit ^ s) * componentTimeNorm q s F := by
  let G := D01.Homogeneous.compactHomogeneousPath hs hF hc
  have hG : Data.IsHomogeneousPath s F G := D01.Homogeneous.isHomogeneousPath_compact hs hF hc
  have hm := hreal s hs hs0 F hF hc
  have hb := compactHomogeneousPath_norm_le hs hF hc
  refine (iInf_le_of_le ⟨G, hG, hm⟩ le_rfl).trans ?_
  change eLpNorm G q Data.forceTimeMeasure ≤ _
  refine (eLpNorm_mono_real hb).trans ?_
  have he : (fun t => frequencyUnit ^ s * ∑ i : Fin 3,
      homogeneousFourierNorm s (fun x => coordinateForce F i (t, x))) =
      frequencyUnit ^ s • (∑ i : Fin 3, fun t =>
        homogeneousFourierNorm s (fun x => coordinateForce F i (t, x))) := by
    ext t
    simp
  rw [he, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs,
    abs_of_pos (Real.rpow_pos_of_pos frequencyUnit_pos s)]
  apply mul_le_mul_right
  refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
  exact eLpNorm_sum_le (fun i _ =>
    (Paper3.stronglyMeasurable_homogeneousFourier_time s
      (coordinateForce_smooth hF i).continuous).aestronglyMeasurable) hq

/-- With the one measurable witness, uniqueness identifies the registered
infimum with the norm of the concrete D01 path. -/
theorem forceHomogeneousENorm_eq_path (hreal : CompactHomogeneousRealization)
    {s : ℝ} (hs : -3 / 2 < s) (hs0 : s < 0) {F : VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (q : ℝ≥0∞) :
    Data.forceHomogeneousENorm q s F =
      eLpNorm (D01.Homogeneous.compactHomogeneousPath hs hF hc) q Data.forceTimeMeasure := by
  change D01.Homogeneous.forceHomogeneousENorm q s F = _
  rw [D01.Homogeneous.forceHomogeneousENorm_eq_of_aestronglyMeasurable hs hF hc
    (hreal s hs hs0 F hF hc)]
  exact (D01.Homogeneous.bochnerDatumENorm_eq_eLpNorm_slice hs hF hc _
    (D01.Homogeneous.isHomogeneousPath_compact hs hF hc)).symm

/-- Exact parabolic scaling for the registered positive-time homogeneous norm.
The support and nonnegative delay hypotheses ensure the whole transformed
support is included. The source amplitude is `k³`, `k = ε⁻¹`. -/
theorem forceHomogeneousENorm_scaling (hreal : CompactHomogeneousRealization)
    {s : ℝ} (hs : -3 / 2 < s) (hs0 : s < 0) {F : VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hzero : ∀ t : ℝ, t ≤ 0 → ∀ x : Space, F (t, x) = 0)
    {k : ℝ} (hk : 0 < k) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (x₀ : Space) (q : ℝ≥0∞) :
    Data.forceHomogeneousENorm q s (parabolicForce k t₀ x₀ F) =
      ENNReal.ofReal (k ^ (3 / 2 + s - 2 / q.toReal)) * Data.forceHomogeneousENorm q s F := by
  have hFs := Source.parabolicForce_smooth k t₀ x₀ hF
  have hcs := Source.parabolicForce_compact k t₀ x₀ hc
  have hzs : ∀ t : ℝ, t ≤ 0 → ∀ x : Space, parabolicForce k t₀ x₀ F (t, x) = 0 := by
    intro t ht x
    change k ^ 3 • F (k ^ 2 * (t - t₀), k • (x - x₀)) = 0
    rw [hzero _ (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg k)
      (sub_nonpos.mpr (ht.trans ht₀)))]
    simp
  rw [forceHomogeneousENorm_eq_path hreal hs hs0 hFs hcs q,
    forceHomogeneousENorm_eq_path hreal hs hs0 hF hc q,
    homogeneous_datum_positive_eq_volume hs hFs hcs hzs q,
    homogeneous_datum_positive_eq_volume hs hF hc hzero q]
  exact homogeneous_datum_time_scaling hs hF hc hk t₀ x₀ q

/-- The exact registered identity with the paper's beta and the packet's delay. -/
theorem packetHomogeneousIdentity (hreal : CompactHomogeneousRealization)
    {ν : ℝ} (P : PacketAPI ν) (th : ThresholdAPI) {s : ℝ}
    (hs : -3 / 2 < s) (hs0 : s < 0) {ε T : ℝ} (hε : 0 < ε)
    (hT : 0 ≤ T - ε ^ 2) (x₀ : Space) (q : ℝ≥0∞) :
    Data.forceHomogeneousENorm q s (scaledForce P.force x₀ T ε) =
      ENNReal.ofReal (ε ^ th.exponent q.toReal s) * Data.forceHomogeneousENorm q s P.force := by
  change Data.forceHomogeneousENorm q s (parabolicForce ε⁻¹ (T - ε ^ 2) x₀ P.force) = _
  rw [forceHomogeneousENorm_scaling hreal hs hs0 P.force_smooth P.force_support.1
    P.force_zero_nonpos (inv_pos.mpr hε) hT x₀ q, th.formula]
  congr 2
  rw [Real.inv_rpow hε.le, ← Real.rpow_neg hε.le]
  congr 1
  ring

/-- The finite profile constant, explicit and independent of epsilon. It is a
sum of component homogeneous time norms, converted to the angular convention. -/
def packetHomogeneousConst (F : VelocityField) (q : ℝ≥0∞) (s : ℝ) : ℝ :=
  frequencyUnit ^ s * (componentTimeNorm q s F).toReal

/-- Convert a finite component bound to the registered homogeneous norm. -/
theorem homogeneous_bound_of_components (hreal : CompactHomogeneousRealization)
    {s : ℝ} (hs : -3 / 2 < s) (hs0 : s < 0) {F : VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (q : ℝ≥0∞) (hq : 1 ≤ q)
    {K : ℝ≥0∞} (hK : K ≠ ⊤) {b : ℝ} (_hb : 0 ≤ b)
    (hbound : componentTimeNorm q s F ≤ ENNReal.ofReal b * K) :
    Data.forceHomogeneousENorm q s F ≤
      ENNReal.ofReal ((frequencyUnit ^ s * K.toReal) * b) := by
  refine (forceHomogeneousENorm_le_components hreal hs hs0 hF hc q hq).trans
    ((mul_le_mul_right hbound _).trans_eq ?_)
  rw [ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg frequencyUnit_pos.le s)
    ENNReal.toReal_nonneg), ENNReal.ofReal_mul (Real.rpow_nonneg frequencyUnit_pos.le s),
    ENNReal.ofReal_toReal hK]
  ac_rfl

/-- The packet clause, with exactly the draft's quantifier range and exponent.
The constant is the explicit finite component profile norm above. -/
theorem packetNegativeHomogeneous (hreal : CompactHomogeneousRealization)
    {ν : ℝ} (packet : PacketAPI ν) (x₀ : Space) (T ε₀ : ℝ) (thresholds : ThresholdAPI) :
    ∀ (q : ℝ≥0∞), 1 ≤ q → ∀ s : ℝ, -3 / 2 < s → s < 0 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      Data.forceHomogeneousENorm q s (scaledForce packet.force x₀ T ε) ≤
        ENNReal.ofReal (packetHomogeneousConst packet.force q s * ε ^ thresholds.exponent q.toReal s) := by
  intro q hq s hs hs0 ε hε
  have hF := packet.force_smooth
  have hc := packet.force_support.1
  rw [thresholds.formula]
  apply homogeneous_bound_of_components hreal hs hs0
    (Source.parabolicForce_smooth _ _ _ hF)
    (Source.parabolicForce_compact _ _ _ hc) q hq
    (componentTimeNorm_finite q hs hs0.le hF hc) (Real.rpow_nonneg hε.1.le _)
  exact (componentTimeNorm_packet q s hF hε.1 (T - ε ^ 2) x₀).le

/-- Compact smooth forces have finite registered homogeneous time norm once
the measurable-path obligation is supplied. -/
theorem forceHomogeneousENorm_finite (hreal : CompactHomogeneousRealization)
    {s : ℝ} (hs : -3 / 2 < s) (hs0 : s < 0) {F : VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (q : ℝ≥0∞) (hq : 1 ≤ q) :
    Data.forceHomogeneousENorm q s F ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (componentTimeNorm_finite q hs hs0.le hF hc))
    (forceHomogeneousENorm_le_components hreal hs hs0 hF hc q hq)

/-- The draft packet bound with the actual finite vector homogeneous profile
norm as its constant (sharper than the component-sum bound). -/
theorem packetNegativeHomogeneous_profile (hreal : CompactHomogeneousRealization)
    {ν : ℝ} (packet : PacketAPI ν) (x₀ : Space) (T ε₀ : ℝ) (thresholds : ThresholdAPI)
    (hdelay : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 0 ≤ T - ε ^ 2) :
    ∀ (q : ℝ≥0∞), 1 ≤ q → ∀ s : ℝ, -3 / 2 < s → s < 0 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      Data.forceHomogeneousENorm q s (scaledForce packet.force x₀ T ε) ≤
        ENNReal.ofReal ((Data.forceHomogeneousENorm q s packet.force).toReal *
          ε ^ thresholds.exponent q.toReal s) := by
  intro q hq s hs hs0 ε hε
  rw [packetHomogeneousIdentity hreal packet thresholds hs hs0 hε.1 (hdelay ε hε) x₀ q,
    ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (forceHomogeneousENorm_finite hreal hs hs0
      packet.force_smooth packet.force_support.1 q hq), mul_comm]

/-- The abstract correction family has the same component bound as its actual
profile; the existing window extension keeps precisely the registered family. -/
theorem correction_components {ν : ℝ} {P : PacketAPI ν} (C : CorrectionAPI ν P)
    (q : ℝ≥0∞) {s : ℝ} (hs : -3 / 2 < s) (hs0 : s ≤ 0) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ ε ∈ Ioc (0 : ℝ) (scalingThreshold C),
      componentTimeNorm q s (C.forceCorrection ε) ≤
        ENNReal.ofReal (ε ^ (2 / q.toReal - 1 / 2 - s)) * K := by
  obtain ⟨V, hVs, hV⟩ := exists_window_extension C
  obtain ⟨K, hK, hb⟩ := correction_componentTimeNorm ν hVs C.x₀ C.T
    C.theta_smooth C.eta_smooth C.theta_compactSupport C.eta_compactSupport hs hs0 q
  refine ⟨K, hK, fun ε hε => ?_⟩
  rw [forceCorrection_eq_extension C hV hε.1 (window_bound C hε)]
  exact hb ε (mem_unit_range C hε)

/-- Correction clause, with a real finite constant uniform on the same shrunken
scale range as the existing inhomogeneous scaling package. -/
theorem correctionNegativeHomogeneous (hreal : CompactHomogeneousRealization)
    {ν : ℝ} {P : PacketAPI ν} (C : CorrectionAPI ν P) (thresholds : ThresholdAPI)
    (q : ℝ≥0∞) (hq : 1 ≤ q) (s : ℝ) (hs : -3 / 2 < s) (hs0 : s < 0) :
    ∃ correctionNegativeConst : ℝ, ∀ ε ∈ Ioc (0 : ℝ) (scalingThreshold C),
      Data.forceHomogeneousENorm q s (C.forceCorrection ε) ≤
        ENNReal.ofReal (correctionNegativeConst *
          ε ^ (thresholds.exponent q.toReal s + 1)) := by
  obtain ⟨K, hK, hb⟩ := correction_components C q hs hs0.le
  refine ⟨frequencyUnit ^ s * K.toReal, fun ε hε => ?_⟩
  rw [thresholds.formula]
  have he : 2 / q.toReal - 3 / 2 - s + 1 = 2 / q.toReal - 1 / 2 - s := by ring
  rw [he]
  exact homogeneous_bound_of_components hreal hs hs0
    (C.force_smooth ε (mem_correction_range C hε))
    (C.force_compactSupport ε (mem_correction_range C hε)) q hq hK
    (Real.rpow_nonneg hε.1.le _) (hb ε hε)

/-- Total choice of the correction constant family, with no obligation outside
its specified range. -/
theorem exists_correction_homogeneous_const (hreal : CompactHomogeneousRealization)
    {ν : ℝ} {P : PacketAPI ν} (C : CorrectionAPI ν P) (th : ThresholdAPI)
    (q : ℝ≥0∞) (s : ℝ) :
    ∃ K : ℝ, 1 ≤ q → -3 / 2 < s → s < 0 →
      ∀ ε ∈ Ioc (0 : ℝ) (scalingThreshold C),
        Data.forceHomogeneousENorm q s (C.forceCorrection ε) ≤
          ENNReal.ofReal (K * ε ^ (th.exponent q.toReal s + 1)) := by
  by_cases hq : 1 ≤ q
  · by_cases hs : -3 / 2 < s
    · by_cases hs0 : s < 0
      · obtain ⟨K, hK⟩ := correctionNegativeHomogeneous hreal C th q hq s hs hs0
        exact ⟨K, fun _ _ _ => hK⟩
      · exact ⟨0, fun _ _ h => (hs0 h).elim⟩
    · exact ⟨0, fun _ h => (hs h).elim⟩
  · exact ⟨0, fun h => (hq h).elim⟩

/-- Both fields of the existing, unregistered homogeneous API, on the very same
family as the registered inhomogeneous package. Conditional only on the one
compact-path measurability input; this does not register an unconditional API. -/
def homogeneousScaling (hreal : CompactHomogeneousRealization)
    {ν : ℝ} {P : PacketAPI ν} (C : CorrectionAPI ν P) (th : ThresholdAPI) :
    HomogeneousScalingAPI ν P := by
  classical
  choose K hK using exists_correction_homogeneous_const hreal C th
  refine { scaling := scaling C th
           packetHomogeneousConst := fun q s => (Data.forceHomogeneousENorm q s P.force).toReal
           correctionHomogeneousConst := K
           packetNegativeHomogeneous := ?_
           correctionNegativeHomogeneous := ?_ }
  · exact packetNegativeHomogeneous_profile hreal P C.x₀ C.T (scalingThreshold C) th
      (fun ε hε => sub_nonneg.mpr (eps_sq_lt_time C hε).le)
  · intro q hq s
    exact hK q s hq

/-- Zero is an admissible measurable path at every order, independently of the
open realization input. -/
theorem zero_homogeneous_path (s : ℝ) :
    Data.IsHomogeneousPath s (0 : VelocityField) (fun _ => 0) := by
  intro t _
  refine ⟨0, ?_, ?_⟩
  · simp [Data.IsSliceDistribution]
  · simp [Data.IsHomogeneousVectorDatum, Data.IsHomogeneousDatum]

/-- The registered infimum is nonempty and exactly zero for zero force. -/
theorem forceHomogeneousENorm_zero (q : ℝ≥0∞) (s : ℝ) :
    Data.forceHomogeneousENorm q s (0 : VelocityField) = 0 := by
  apply le_antisymm _ bot_le
  refine iInf_le_of_le ⟨fun _ => 0, zero_homogeneous_path s, aestronglyMeasurable_const⟩ ?_
  simp [Data.bochnerDatumENorm]

/-- The open measurability obligation is satisfied by the zero compact force,
using the very same D01 constructor as in its statement. -/
theorem compact_realization_zero {s : ℝ} (hs : -3 / 2 < s)
    (hF : ContDiff ℝ ∞ (0 : VelocityField)) (hc : HasCompactSupport (0 : VelocityField)) :
    AEStronglyMeasurable (D01.Homogeneous.compactHomogeneousPath hs hF hc)
      Data.forceTimeMeasure := by
  have he : D01.Homogeneous.compactHomogeneousPath hs hF hc = fun _ => 0 := by
    funext t
    apply norm_eq_zero.mp
    have h := compactHomogeneousPath_norm_le hs hF hc t
    simpa [coordinateForce, homogeneousFourierNorm, Real.fourier_eq] using h
  rw [he]
  exact aestronglyMeasurable_const

example (q : ℝ≥0∞) (s : ℝ) : Data.forceHomogeneousENorm q s (0 : VelocityField) = 0 :=
  forceHomogeneousENorm_zero q s

example {ν : ℝ} (P : PacketAPI ν) (q : ℝ≥0∞) : componentTimeNorm q (-1) P.force ≠ ⊤ :=
  componentTimeNorm_finite q (by norm_num) (by norm_num) P.force_smooth P.force_support.1

end NSFormalization.Section4.I03
