import NSFormalization.Section4.I02.Energy
import NSFormalization.Source.PacketScaling

/-!
# I03: `eq:packetEscale` in the canonical `ENNReal` energy norms

`paper/sections/03-torus.tex:122-146` (Proposition 3.3, display `eq:packetEscale`)
asserts, for the parabolically rescaled packet `U_ε` of `eq:scaling`
(`paper/sections/03-torus.tex:112-120`),
`‖U_ε‖_{L^∞(0,T;L²)} = ε^{1/2} M` and `‖∇U_ε‖_{L²(0,T;L²)} = ε^{1/2} D`,
where `M = sup_{0≤t<1}‖U(t)‖₂` and `D² = ∫₀¹‖∇U(t)‖₂²`.  Section 4 reuses the
identity verbatim on `R³`, `paper/sections/04-whole-space.tex:21-23`.

The source tree provides the two exact scaling identities
(`Source.PacketScaling.l2Norm_parabolic`,
`Source.PacketScaling.total_dissipation_parabolic`) in the real-valued
`NavierStokesR3.CompactEnergy.l2Sq` / `dissipation` language.  Section 4's
registered norms are instead the two `ENNReal` summands of
`Contracts.V1.Data.energyENorm`, namely
`essSup (fun t => eLpNorm (z t ·) 2 volume)` on `Ioo 0 T` and
`(∫⁻ t in Ioo 0 T, (eLpNorm (∇z t ·) 2 volume)^2)^{1/2}`.

This module does the transport for the rescaled packet
`U_ε = Source.parabolicVelocity ε⁻¹ (T - ε²) x₀ (zeroPastField U)`, with the
inverse length `k = ε⁻¹` and the activation time `t₀ = T - ε²`, so that
`t₀ + (k²)⁻¹ = T`.  Nothing below mentions the contract; the expressions are
written exactly as `Contracts.V1.Data.energyEssSup` and
`Contracts.V1.Data.energyGradient` unfold, so the binding is by `rfl`.
-/

noncomputable section

namespace NSFormalization.Section4.I03

open NavierStokes NavierStokes.ProblemStatement NavierStokesR3.CompactEnergy
open NSFormalization.Source.PacketScaling
open Set MeasureTheory Filter
open scoped ContDiff ENNReal Topology

/-! ## 1. Generic auxiliaries -/

/-- A field smooth on an open time slab is smooth in each of its spatial slices.
Both `Source.PacketScaling.zeroPastField_smoothOn` (slab `Iio 1`) and
`Source.PacketScaling.dilate_smoothOn` (slab `Iio T`) deliver exactly this
hypothesis, and the slice form is what the spatial `L²` lemmas need. -/
theorem slice_contDiff_of_slab {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : SpaceTime → V} {b : ℝ} (hf : ContDiffOn ℝ ∞ f (Iio b ×ˢ (univ : Set Space)))
    {t : ℝ} (ht : t < b) : ContDiff ℝ ∞ (fun y : Space => f (t, y)) := by
  have hopen : IsOpen (Iio b ×ˢ (univ : Set Space)) := isOpen_Iio.prod isOpen_univ
  rw [contDiff_iff_contDiffAt]
  intro y
  have hz : ContDiffAt ℝ ∞ f (t, y) :=
    hf.contDiffAt (hopen.mem_nhds ⟨ht, mem_univ y⟩)
  exact hz.comp y (contDiffAt_const.prodMk contDiffAt_id)

/-- Per-slice restatement of `I02.eLpNorm_spatialGradient_sq`: the squared
spatial gradient `eLpNorm` is the dissipation rate, assuming only that the
single slice `y ↦ w (t, y)` is smooth and compactly supported.  The rescaled
packet is *not* globally smooth (its reference field is smooth only on
`Ico 0 1 ×ˢ univ`), so the global form of the lemma is unusable here. -/
theorem eLpNorm_spatialGradient_sq_slice {w : VelocityField} {t : ℝ}
    (hs : ContDiff ℝ ∞ (fun y : Space => w (t, y)))
    (hcs : HasCompactSupport (fun y : Space => w (t, y))) :
    (eLpNorm (fun x : Space => I02.spatialGradient w t x) 2 volume) ^ (2 : ℝ) =
      ENNReal.ofReal (dissipation w t) := by
  have hcomp : ∀ i : Fin 3,
      Integrable (fun x : Space => ‖spatialDerivative w t x (coordinateVector i)‖ ^ 2) volume :=
    fun i => Paper1.InsertionEnergy.spatial_gradient_square_integrable hs hcs (coordinateVector i)
  have hsum : Integrable (fun x : Space => ‖I02.spatialGradient w t x‖ ^ 2) volume := by
    simp_rw [I02.norm_spatialGradient_sq]
    exact integrable_finsetSum _ (fun i _ => hcomp i)
  have hval : (∫ x : Space, ‖I02.spatialGradient w t x‖ ^ 2) = dissipation w t := by
    simp_rw [I02.norm_spatialGradient_sq]
    rw [integral_finsetSum _ (fun i _ => hcomp i)]
    simp only [dissipation, NavierStokes.PeriodicIntegration.spatialPartial, spatialDerivative]
  rw [I02.eLpNorm_two_eq_ofReal_sqrt hsum, hval,
    ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num : (0:ℝ) ≤ 2),
    Real.rpow_two, Real.sq_sqrt (dissipation_nonneg w t)]

/-- A lower bound holding on a set of positive measure forces the essential
supremum up.  This is the only direction of `essSup` not already in Mathlib in
the shape needed for the `≥` half of `eq:packetEscale`. -/
theorem le_essSup_of_le_on_pos_measure {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} {a : ℝ≥0∞} {s : Set α} (hs : μ s ≠ 0) (hle : ∀ x ∈ s, a ≤ f x) :
    a ≤ essSup f μ := by
  by_contra hcon
  rw [not_le] at hcon
  have h := ae_lt_of_essSup_lt hcon
  rw [Filter.eventually_iff, mem_ae_iff] at h
  exact hs (measure_mono_null (fun x hx => by simpa using not_lt.2 (hle x hx)) h)

/-! ## 2. The packet hypotheses -/

/-- The packet hypotheses that `eq:packetEscale` consumes, bundled so the
statements below stay readable.  Every field is a genuine field of
`Contracts.V1.Packet.PacketAPI`: `extension_smooth` is
`velocity_extension_smooth`, `energy_isLUB` is the *least* upper bound clause
that makes `eq:packetEscale` an equality, and `dissipation_eq` is `D = √∫₀¹`.
Note what is *not* assumed: `U` is smooth only on `Ico 0 1 ×ˢ univ`, its zero
extension only on `Iio 1 ×ˢ univ`, and `U` has compact support only slicewise. -/
structure PacketData (U : VelocityField) (K : Set Space) (M D : ℝ) : Prop where
  /-- `U`'s zero extension into nonpositive time is smooth on `(-∞,1) × R³`. -/
  extension_smooth :
    ContDiffOn ℝ ∞ (zeroPastField U) (Iio (1 : ℝ) ×ˢ (univ : Set Space))
  /-- The single spatial carrier is compact. -/
  carrier_compact : IsCompact K
  /-- Every presingular slice of `U` is supported in `K`. -/
  support : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => U (t, x)) ⊆ K
  /-- Every presingular slice of `U` is square integrable. -/
  square_int : ∀ t ∈ Ico (0 : ℝ) 1, Integrable (fun x : Space => ‖U (t, x)‖ ^ 2) volume
  /-- `U(·,0) = 0`. -/
  zero_initial : ∀ x : Space, U (0, x) = 0
  /-- `M = sup_{0≤t<1}‖U(t)‖₂`, a least upper bound. -/
  energy_isLUB : IsLUB ((fun t : ℝ => Real.sqrt (l2Sq U t)) '' Ico (0 : ℝ) 1) M
  /-- The dissipation rate is time integrable on `(0,1)`. -/
  dissipation_int : IntegrableOn (dissipation U) (Ioo (0 : ℝ) 1)
  /-- `D = (∫₀¹‖∇U(t)‖₂²)^{1/2}`. -/
  dissipation_eq : D = Real.sqrt (∫ t in Ioo (0 : ℝ) 1, dissipation U t)

variable {U : VelocityField} {K : Set Space} {M D ε T : ℝ}

/-- `M ≥ 0`, because `‖U(0)‖₂ = 0` is one of the numbers `M` dominates. -/
theorem energyBound_nonneg (hP : PacketData U K M D) : 0 ≤ M := by
  have h0 : l2Sq U 0 = 0 := by simp [l2Sq, hP.zero_initial]
  have hmem : Real.sqrt (l2Sq U 0) ∈
      (fun t : ℝ => Real.sqrt (l2Sq U t)) '' Ico (0 : ℝ) 1 :=
    ⟨0, ⟨le_rfl, zero_lt_one⟩, rfl⟩
  simpa [h0] using hP.energy_isLUB.1 hmem

/-- On strictly positive times the zero extension does not change the spatial
squared `L²` energy. -/
theorem l2Sq_zeroPastField (U : VelocityField) {σ : ℝ} (hσ : 0 < σ) :
    l2Sq (zeroPastField U) σ = l2Sq U σ := by
  simp only [l2Sq, zeroPastField_of_pos U hσ]

/-- Every slice of the extended packet strictly before the singular time is
square integrable: past times contribute the zero field. -/
theorem square_int_zeroPastField (hP : PacketData U K M D) {σ : ℝ} (hσ : σ < 1) :
    Integrable (fun x : Space => ‖zeroPastField U (σ, x)‖ ^ 2) volume := by
  rcases le_or_gt σ 0 with h | h
  · have hz : (fun x : Space => ‖zeroPastField U (σ, x)‖ ^ 2) = fun _ : Space => (0 : ℝ) := by
      funext x; simp [zeroPastField_of_nonpos U h]
    rw [hz]
    exact integrable_zero Space ℝ volume
  · simpa only [zeroPastField_of_pos U h] using hP.square_int σ ⟨h.le, hσ⟩

/-- `M` dominates the extended packet's spatial `L²` norm at every time before
the singular time, the past times contributing `0 ≤ M`. -/
theorem l2Norm_zeroPastField_le (hP : PacketData U K M D) {σ : ℝ} (hσ : σ < 1) :
    Real.sqrt (l2Sq (zeroPastField U) σ) ≤ M := by
  rcases le_or_gt σ 0 with h | h
  · have : l2Sq (zeroPastField U) σ = 0 := by
      simp [l2Sq, zeroPastField_of_nonpos U h]
    simpa [this] using energyBound_nonneg hP
  · rw [l2Sq_zeroPastField U h]
    exact hP.energy_isLUB.1 ⟨σ, ⟨h.le, hσ⟩, rfl⟩

/-! ## 3. The parabolic window -/

/-- The concentration parameters of `eq:scaling`: with inverse length `k = ε⁻¹`
and activation time `t₀ = T - ε²`, the active window `t₀ + (k²)⁻¹` is exactly
the target singular time `T`. -/
theorem parabolic_window (e t : ℝ) : (t - e ^ 2) + ((e⁻¹) ^ 2)⁻¹ = t := by
  rw [inv_pow, inv_inv]; ring

/-- Reference times of the active window lie strictly below the reference
singular time `1`. -/
theorem reference_time_lt_one (hε : 0 < ε) {t : ℝ} (ht : t < T) :
    (ε⁻¹) ^ 2 * (t - (T - ε ^ 2)) < 1 := by
  have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
  have hlt : (ε ^ 2)⁻¹ * (t - (T - ε ^ 2)) < (ε ^ 2)⁻¹ * ε ^ 2 :=
    mul_lt_mul_of_pos_left (by linarith) (inv_pos.2 hε2)
  rw [inv_mul_cancel₀ hε2.ne'] at hlt
  rwa [inv_pow]

/-! ## 4. Slice regularity of the rescaled packet -/

/-- The rescaled packet is smooth on the whole open slab `(-∞,T) × R³`;
`Source.PacketScaling.dilate_smoothOn` transported through
`parabolic_window`. -/
theorem scaled_smoothOn (hP : PacketData U K M D) (x₀ : Space) (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (Source.parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField U))
      (Iio T ×ˢ (univ : Set Space)) := by
  have h := dilate_smoothOn (f := zeroPastField U) ε⁻¹ (inv_pos.2 hε) (T - ε ^ 2) x₀
    hP.extension_smooth
  rwa [parabolic_window ε T] at h

/-- Each spatial slice of the rescaled packet before `T` is smooth. -/
theorem scaled_slice_contDiff (hP : PacketData U K M D) (x₀ : Space) (hε : 0 < ε)
    {t : ℝ} (ht : t < T) :
    ContDiff ℝ ∞
      (fun y : Space => Source.parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField U) (t, y)) :=
  slice_contDiff_of_slab (scaled_smoothOn hP x₀ hε) ht

/-- Each spatial slice of the rescaled packet before `T` has compact support,
inside the concentrated carrier `Source.PacketScaling.scaledSupport`. -/
theorem scaled_slice_hasCompactSupport (hP : PacketData U K M D) (x₀ : Space) (hε : 0 < ε)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    HasCompactSupport
      (fun y : Space => Source.parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField U) (t, y)) := by
  have hsupp := delayed_full_support (u := U) hP.carrier_compact (inv_pos.2 hε) x₀ hP.support t
    (by rwa [parabolic_window ε T])
  exact IsCompact.of_isClosed_subset (scaledSupport_compact hP.carrier_compact _ _)
    (isClosed_tsupport _) hsupp

/-! ## 5. The `L^∞_t L²_x` half of `eq:packetEscale` -/

/-- The spatial `L²` seminorm of each slice of the rescaled packet: exactly
`ε^{1/2}` times the reference norm at the transported time.  This is
`Source.PacketScaling.l2Norm_parabolic` moved into `ENNReal`. -/
theorem eLpNorm_scaled_slice (hP : PacketData U K M D) (x₀ : Space) (hε : 0 < ε)
    {t : ℝ} (ht : t < T) :
    eLpNorm (fun x : Space =>
        Source.parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField U) (t, x)) 2 volume =
      ENNReal.ofReal (Real.sqrt ε *
        Real.sqrt (l2Sq (zeroPastField U) ((ε⁻¹) ^ 2 * (t - (T - ε ^ 2))))) := by
  have hk : (0 : ℝ) < ε⁻¹ := inv_pos.2 hε
  have hint : Integrable (fun x : Space =>
      ‖Source.parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField U) (t, x)‖ ^ 2) volume :=
    square_integrable_parabolic hk x₀ (square_int_zeroPastField hP (reference_time_lt_one hε ht))
  rw [I02.eLpNorm_two_eq_ofReal_sqrt hint]
  have hval : (∫ x : Space,
      ‖Source.parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField U) (t, x)‖ ^ 2) =
      l2Sq (Source.parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField U)) t := rfl
  rw [hval, l2Norm_parabolic (zeroPastField U) ε⁻¹ (T - ε ^ 2) hk x₀ t, inv_inv]

set_option linter.unusedVariables false in
/-- `eq:packetEscale`, first display, `≤` half: the `L^∞_tL²_x` summand of the
canonical `E_T` norm of the rescaled packet is at most `ε^{1/2}M`.  The
hypothesis `2ε² < T` is not needed for this half; it is carried so that all
four `eq:packetEscale` statements share one signature. -/
theorem energyEssSup_scaled_le (hP : PacketData U K M D) (x₀ : Space) (hε : 0 < ε)
    (hT : 2 * ε ^ 2 < T) :
    essSup (fun t => eLpNorm (fun x : Space =>
          Source.parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField U) (t, x)) 2 volume)
        (volume.restrict (Ioo (0 : ℝ) T)) ≤ ENNReal.ofReal (Real.sqrt ε * M) := by
  refine essSup_le_of_ae_le _ ?_
  filter_upwards [self_mem_ae_restrict (measurableSet_Ioo (a := (0 : ℝ)) (b := T))] with t ht
  show eLpNorm (fun x : Space =>
      Source.parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField U) (t, x)) 2 volume ≤ _
  rw [eLpNorm_scaled_slice hP x₀ hε ht.2]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (l2Norm_zeroPastField_le hP (reference_time_lt_one hε ht.2)) (Real.sqrt_nonneg _))

/-! ## 6. The `L²_t Ḣ¹_x` half of `eq:packetEscale` -/

/-- The rescaled dissipation rate is time integrable on the whole physical
window, the delayed segment `(0, T-ε²]` contributing zero. -/
theorem scaled_dissipation_integrableOn (hP : PacketData U K M D) (x₀ : Space)
    (hε : 0 < ε) (hT : 2 * ε ^ 2 < T) :
    IntegrableOn
      (dissipation (Source.parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField U)))
      (Ioo (0 : ℝ) T) := by
  have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
  have h := delayed_full_dissipation_integrable (u := U) (inv_pos.2 hε)
    (by linarith [hT, hε2] : (0 : ℝ) ≤ T - ε ^ 2) x₀ hP.dissipation_int
  rwa [parabolic_window ε T] at h

/-- The total rescaled dissipation is exactly `ε` times the reference total:
`Source.PacketScaling.total_dissipation_parabolic` plus vanishing on the
delayed segment. -/
theorem scaled_total_dissipation (hP : PacketData U K M D) (x₀ : Space)
    (hε : 0 < ε) (hT : 2 * ε ^ 2 < T) :
    (∫ t in Ioo (0 : ℝ) T,
        dissipation (Source.parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField U)) t) =
      ε * ∫ t in Ioo (0 : ℝ) 1, dissipation U t := by
  have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
  have hk : (0 : ℝ) < ε⁻¹ := inv_pos.2 hε
  have ht₀ : (0 : ℝ) ≤ T - ε ^ 2 := by linarith
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hearly : IntervalIntegrable
      (dissipation (Source.parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField U)))
      volume 0 (T - ε ^ 2) := by
    apply (intervalIntegrable_const (c := (0 : ℝ))).congr
    intro t ht
    rw [uIoc_of_le ht₀] at ht
    exact (zeroPast_parabolic_dissipation_early U hk x₀ ht.2).symm
  have hlate : IntervalIntegrable
      (dissipation (Source.parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField U)))
      volume (T - ε ^ 2) T := by
    have h := dissipation_intervalIntegrable (u := zeroPastField U) hk (T - ε ^ 2) x₀
      (zeroPastField_dissipation_integrable hP.dissipation_int)
    rwa [parabolic_window ε T] at h
  have hzero : (∫ t in (0 : ℝ)..(T - ε ^ 2),
      dissipation (Source.parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField U)) t) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro t ht
      rw [uIcc_of_le ht₀] at ht
      exact zeroPast_parabolic_dissipation_early U hk x₀ ht.2
  have hlateval : (∫ t in (T - ε ^ 2)..T,
      dissipation (Source.parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField U)) t) =
      ε * ∫ t in Ioo (0 : ℝ) 1, dissipation U t := by
    have h := total_dissipation_parabolic (zeroPastField U) ε⁻¹ (T - ε ^ 2) hk x₀
    rw [parabolic_window ε T] at h
    rw [h, inv_inv, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    congr 1
    exact setIntegral_congr_fun measurableSet_Ioo (fun s hs => dissipation_zeroPastField hs.1)
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hT0,
    ← intervalIntegral.integral_add_adjacent_intervals hearly hlate, hzero, hlateval, zero_add]

/-- `eq:packetEscale`, second display: the `L²_tḢ¹_x` summand of the canonical
`E_T` norm of the rescaled packet is *exactly* `ε^{1/2}D`. -/
theorem energyGradient_scaled_eq (hP : PacketData U K M D) (x₀ : Space) (hε : 0 < ε)
    (hT : 2 * ε ^ 2 < T) :
    (∫⁻ t in Ioo (0 : ℝ) T,
        (eLpNorm (fun x : Space => I02.spatialGradient
          (Source.parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField U)) t x) 2 volume)
            ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) = ENNReal.ofReal (Real.sqrt ε * D) := by
  have hnn : (0 : ℝ) ≤ ∫ t in Ioo (0 : ℝ) 1, dissipation U t :=
    setIntegral_nonneg measurableSet_Ioo (fun t _ => dissipation_nonneg U t)
  have hA : (∫⁻ t in Ioo (0 : ℝ) T,
        (eLpNorm (fun x : Space => I02.spatialGradient
          (Source.parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField U)) t x) 2 volume)
            ^ (2 : ℝ)) =
      ∫⁻ t in Ioo (0 : ℝ) T, ENNReal.ofReal
        (dissipation (Source.parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField U)) t) := by
    refine setLIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
    exact eLpNorm_spatialGradient_sq_slice (scaled_slice_contDiff hP x₀ hε ht.2)
      (scaled_slice_hasCompactSupport hP x₀ hε ⟨ht.1.le, ht.2⟩)
  have hB := (ofReal_integral_eq_lintegral_ofReal
    (scaled_dissipation_integrableOn hP x₀ hε hT)
    (Filter.Eventually.of_forall (fun t =>
      dissipation_nonneg (Source.parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField U)) t))).symm
  rw [hA, hB, scaled_total_dissipation hP x₀ hε hT,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)]
  congr 1
  rw [show ((2 : ℝ)⁻¹) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow, Real.sqrt_mul hε.le,
    hP.dissipation_eq]

/-! ## 7. The arithmetic of the exponent -/

set_option linter.unusedVariables false in
/-- `√ε · M = ε^{1/2} · M`: the conversion between the square root written by
the source lemmas and the real power `ε^{1/2}` written in `eq:packetEscale`.
`Real.sqrt_eq_rpow` needs no sign hypothesis, but `0 ≤ ε` is kept in the
signature because that is the shape every call site has available. -/
theorem sqrt_mul_eq_rpow_half (hε : 0 ≤ ε) (M : ℝ) :
    Real.sqrt ε * M = ε ^ ((1 : ℝ) / 2) * M := by
  rw [Real.sqrt_eq_rpow]

/-! ## 8. Continuity of the reference spatial energy -/

/-- The extended packet's spatial squared `L²` energy is continuous at every
interior reference time.  Dominated convergence on the compact carrier `K`:
`extension_smooth` makes `(σ,x) ↦ U(σ,x)` jointly continuous on the *open* slab
`Iio 1 ×ˢ univ`, and `support` confines every presingular slice to `K`, so the
integrand is uniformly dominated by a constant multiple of `K.indicator 1` on a
compact time window around `σ₀`. -/
theorem continuousAt_l2Sq_zeroPastField (hP : PacketData U K M D)
    {σ₀ : ℝ} (hσ₀ : σ₀ ∈ Ioo (0 : ℝ) 1) :
    ContinuousAt (fun σ : ℝ => l2Sq (zeroPastField U) σ) σ₀ := by
  obtain ⟨hσ0, hσ1⟩ := hσ₀
  obtain ⟨a, ha0, haσ⟩ : ∃ a : ℝ, 0 < a ∧ a < σ₀ := ⟨σ₀ / 2, by linarith, by linarith⟩
  obtain ⟨b, hσb, hb1⟩ : ∃ b : ℝ, σ₀ < b ∧ b < 1 := ⟨(σ₀ + 1) / 2, by linarith, by linarith⟩
  have hslice : ∀ σ : ℝ, σ < 1 → Continuous (fun x : Space => zeroPastField U (σ, x)) :=
    fun σ hσ => (slice_contDiff_of_slab hP.extension_smooth hσ).continuous
  have hvanish : ∀ σ : ℝ, 0 < σ → σ < 1 → ∀ x : Space, x ∉ K → zeroPastField U (σ, x) = 0 := by
    intro σ h0 h1 x hx
    rw [zeroPastField_of_pos U h0]
    exact image_eq_zero_of_notMem_tsupport (f := fun y : Space => U (σ, y))
      (fun hmem => hx (hP.support σ ⟨h0.le, h1⟩ hmem))
  have hcontOn : ContinuousOn (zeroPastField U) (Icc a b ×ˢ K) := by
    refine hP.extension_smooth.continuousOn.mono ?_
    rintro ⟨σ, x⟩ ⟨hσ, -⟩
    exact ⟨lt_of_le_of_lt hσ.2 hb1, mem_univ x⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hP.carrier_compact).exists_bound_of_continuousOn hcontOn
  have hC0 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  show ContinuousAt (fun σ : ℝ => ∫ x : Space, ‖zeroPastField U (σ, x)‖ ^ 2) σ₀
  refine continuousAt_of_dominated (bound := K.indicator (fun _ => (max C 0) ^ 2)) ?_ ?_ ?_ ?_
  · filter_upwards [isOpen_Iio.mem_nhds (show σ₀ ∈ Iio (1 : ℝ) from hσ1)] with σ hσ
    exact (((hslice σ hσ).norm).pow 2).aestronglyMeasurable
  · filter_upwards [Icc_mem_nhds haσ hσb] with σ hσ
    refine Filter.Eventually.of_forall (fun x => ?_)
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _)
        ((hC (σ, x) ⟨hσ, hx⟩).trans (le_max_left _ _)) 2
    · rw [Set.indicator_of_notMem hx,
        hvanish σ (lt_of_lt_of_le ha0 hσ.1) (lt_of_le_of_lt hσ.2 hb1) x hx]
      simp
  · exact (integrable_indicator_iff hP.carrier_compact.measurableSet).2
      (integrableOn_const hP.carrier_compact.measure_lt_top.ne)
  · refine Filter.Eventually.of_forall (fun x => ?_)
    have hVA : ContinuousAt (zeroPastField U) ((σ₀, x) : SpaceTime) :=
      ContinuousOn.continuousAt hP.extension_smooth.continuousOn
        ((isOpen_Iio.prod isOpen_univ).mem_nhds ⟨hσ1, mem_univ x⟩)
    exact ((hVA.comp (f := fun σ : ℝ => ((σ, x) : SpaceTime))
      (by fun_prop)).norm).pow 2

/-! ## 9. The `L^∞_t L²_x` equality -/

/-- `eq:packetEscale`, first display, `≥` half.  Because `M` is a *least* upper
bound, every `c < M` is beaten at some reference time `σ₀ ∈ Ioo 0 1` (the value
at `σ₀ = 0` is `0 ≤ c`, so `σ₀` is interior).  Continuity of the reference
energy turns that single time into an interval of positive measure of physical
times, which is what an essential supremum sees. -/
theorem le_energyEssSup_scaled (hP : PacketData U K M D) (x₀ : Space) (hε : 0 < ε)
    (hT : 2 * ε ^ 2 < T) :
    ENNReal.ofReal (Real.sqrt ε * M) ≤
      essSup (fun t => eLpNorm (fun x : Space =>
          Source.parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField U) (t, x)) 2 volume)
        (volume.restrict (Ioo (0 : ℝ) T)) := by
  have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
  have ht₀ : (0 : ℝ) < T - ε ^ 2 := by linarith
  have hsq : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have key : ∀ c : ℝ, 0 ≤ c → c < M →
      ENNReal.ofReal (Real.sqrt ε * c) ≤
        essSup (fun t => eLpNorm (fun x : Space =>
            Source.parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField U) (t, x)) 2 volume)
          (volume.restrict (Ioo (0 : ℝ) T)) := by
    intro c hc0 hcM
    have hnub : c ∉ upperBounds ((fun t : ℝ => Real.sqrt (l2Sq U t)) '' Ico (0 : ℝ) 1) :=
      fun hub => absurd (hP.energy_isLUB.2 hub) (not_le.2 hcM)
    rw [mem_upperBounds] at hnub
    push Not at hnub
    obtain ⟨y, ⟨σ₀, hσ₀mem, rfl⟩, hy⟩ := hnub
    have hy' : c < Real.sqrt (l2Sq U σ₀) := hy
    have hσ₀pos : 0 < σ₀ := by
      rcases eq_or_lt_of_le hσ₀mem.1 with h | h
      · exfalso
        have h0 : l2Sq U σ₀ = 0 := by rw [← h]; simp [l2Sq, hP.zero_initial]
        rw [h0, Real.sqrt_zero] at hy'
        linarith
      · exact h
    have hcont : ContinuousAt (fun σ : ℝ => Real.sqrt (l2Sq (zeroPastField U) σ)) σ₀ :=
      Real.continuous_sqrt.continuousAt.comp
        (continuousAt_l2Sq_zeroPastField hP ⟨hσ₀pos, hσ₀mem.2⟩)
    have hgt : c < Real.sqrt (l2Sq (zeroPastField U) σ₀) := by
      rwa [l2Sq_zeroPastField U hσ₀pos]
    have h1 : (fun σ : ℝ => Real.sqrt (l2Sq (zeroPastField U) σ)) ⁻¹' Ioi c ∈ 𝓝 σ₀ :=
      hcont (Ioi_mem_nhds hgt)
    obtain ⟨p, q, hmem, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1
      (Filter.inter_mem h1 (Ioo_mem_nhds hσ₀pos hσ₀mem.2))
    have hp'0 : (0 : ℝ) ≤ max p 0 := le_max_right _ _
    have hq'1 : min q 1 ≤ (1 : ℝ) := min_le_right _ _
    have hp'lt : max p 0 < σ₀ := max_lt hmem.1 hσ₀pos
    have hltq' : σ₀ < min q 1 := lt_min hmem.2 hσ₀mem.2
    have hp'q' : max p 0 < min q 1 := hp'lt.trans hltq'
    have hSsub : Ioo (T - ε ^ 2 + max p 0 * ε ^ 2) (T - ε ^ 2 + min q 1 * ε ^ 2) ⊆
        Ioo (0 : ℝ) T := by
      intro t ht
      have hlow : (0 : ℝ) ≤ max p 0 * ε ^ 2 := mul_nonneg hp'0 hε2.le
      have hhigh : min q 1 * ε ^ 2 ≤ 1 * ε ^ 2 := mul_le_mul_of_nonneg_right hq'1 hε2.le
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    refine le_essSup_of_le_on_pos_measure
      (s := Ioo (T - ε ^ 2 + max p 0 * ε ^ 2) (T - ε ^ 2 + min q 1 * ε ^ 2)) ?_ ?_
    · rw [Measure.restrict_apply' measurableSet_Ioo,
        inter_eq_self_of_subset_left hSsub, Real.volume_Ioo]
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      nlinarith [hp'q', hε2]
    · intro t htS
      have htT : t ∈ Ioo (0 : ℝ) T := hSsub htS
      show ENNReal.ofReal (Real.sqrt ε * c) ≤ eLpNorm (fun x : Space =>
        Source.parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField U) (t, x)) 2 volume
      rw [eLpNorm_scaled_slice hP x₀ hε htT.2]
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
      have hσlow : max p 0 < (ε⁻¹) ^ 2 * (t - (T - ε ^ 2)) := by
        rw [inv_pow, ← div_eq_inv_mul, lt_div_iff₀ hε2]; linarith [htS.1]
      have hσhigh : (ε⁻¹) ^ 2 * (t - (T - ε ^ 2)) < min q 1 := by
        rw [inv_pow, ← div_eq_inv_mul, div_lt_iff₀ hε2]; linarith [htS.2]
      have hin := (hsub ⟨(le_max_left p 0).trans_lt hσlow,
        hσhigh.trans_le (min_le_left q 1)⟩).1
      simp only [Set.mem_preimage, Set.mem_Ioi] at hin
      exact hin.le
  have hle := energyEssSup_scaled_le hP x₀ hε hT
  have hEtop : essSup (fun t => eLpNorm (fun x : Space =>
      Source.parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField U) (t, x)) 2 volume)
      (volume.restrict (Ioo (0 : ℝ) T)) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  rw [ENNReal.ofReal_le_iff_le_toReal hEtop]
  refine le_of_forall_lt (fun c' hc' => ?_)
  obtain ⟨c'', hc''1, hc''2⟩ := exists_between hc'
  rcases le_or_gt c'' 0 with h | h
  · have hnn : (0 : ℝ) ≤ (essSup (fun t => eLpNorm (fun x : Space =>
        Source.parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField U) (t, x)) 2 volume)
        (volume.restrict (Ioo (0 : ℝ) T))).toReal := ENNReal.toReal_nonneg
    linarith
  · have hcM : c'' / Real.sqrt ε < M := by
      rw [div_lt_iff₀ hsq, mul_comm]; exact hc''2
    have hk := key (c'' / Real.sqrt ε) (le_of_lt (div_pos h hsq)) hcM
    have heq : Real.sqrt ε * (c'' / Real.sqrt ε) = c'' := by field_simp
    rw [heq, ENNReal.ofReal_le_iff_le_toReal hEtop] at hk
    linarith

/-- `eq:packetEscale`, first display: the `L^∞_tL²_x` summand of the canonical
`E_T` norm of the rescaled packet is *exactly* `ε^{1/2}M`. -/
theorem energyEssSup_scaled_eq (hP : PacketData U K M D) (x₀ : Space) (hε : 0 < ε)
    (hT : 2 * ε ^ 2 < T) :
    essSup (fun t => eLpNorm (fun x : Space =>
          Source.parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField U) (t, x)) 2 volume)
        (volume.restrict (Ioo (0 : ℝ) T)) = ENNReal.ofReal (Real.sqrt ε * M) :=
  le_antisymm (energyEssSup_scaled_le hP x₀ hε hT) (le_energyEssSup_scaled hP x₀ hε hT)

end NSFormalization.Section4.I03
