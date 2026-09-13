import NSFormalization.Source.ParabolicScaling
import NSFormalization.Source.PacketEnergy
import Mathlib.MeasureTheory.Group.Integral
import NavierStokes.ResidualRegularity

/-!
# Parabolic concentration of the actual packet

The inverse length k preserves viscosity. Spatial squared L2 energy and total
spacetime dissipation both scale by k^{-1}; the blow-up time and support are
transported by the same actual field map.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace NSFormalization.Source.PacketScaling
open NavierStokes.ProblemStatement
open NavierStokesR3.CompactEnergy
open NavierStokes.PeriodicIntegration (spatialPartial)

/-- Pointwise speed becomes unbounded approaching any specified positive time. -/
def SpeedUnboundedAt (T : ℝ) (u : VelocityField) : Prop :=
  ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
    ∃ t : ℝ, ∃ x : Space, t ∈ Ioo 0 T ∧ T - δ < t ∧ M < ‖u (t, x)‖

@[simp] theorem speedUnboundedAt_one (u : VelocityField) :
    SpeedUnboundedAt 1 u ↔ SpeedUnboundedAtOne u := Iff.rfl

/-- Translation introduces no factor into the actual spatial energy formula. -/
theorem spatial_energy_affine (u : Space → Space) (a k : ℝ) (hk : 0 < k) (x₀ : Space) :
    (∫ x : Space, ‖a • u (k • (x - x₀))‖ ^ 2) =
      a ^ 2 * (k ^ 3)⁻¹ * (∫ x : Space, ‖u x‖ ^ 2) := by
  rw [integral_sub_right_eq_self (fun x : Space => ‖a • u (k • x)‖ ^ 2) x₀]
  exact spatial_energy_dilate u a k hk

/-- Exact physical spatial squared-L2 scaling at each transformed time. -/
theorem l2Sq_parabolic (u : VelocityField) (k t₀ : ℝ) (hk : 0 < k) (x₀ : Space) (t : ℝ) :
    l2Sq (parabolicVelocity k t₀ x₀ u) t =
      k⁻¹ * l2Sq u (k ^ 2 * (t - t₀)) := by
  unfold l2Sq parabolicVelocity dilateField
  dsimp only
  rw [spatial_energy_affine (fun y => u (k ^ 2 * (t - t₀), y)) k k hk x₀]
  field_simp

/-- Every spatial gradient component gains k^2; volume contributes k^{-3}. -/
theorem dissipation_parabolic (u : VelocityField) (k t₀ : ℝ) (hk : 0 < k)
    (x₀ : Space) (t : ℝ) :
    dissipation (parabolicVelocity k t₀ x₀ u) t =
      k * dissipation u (k ^ 2 * (t - t₀)) := by
  unfold dissipation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (∫ x : Space, ‖spatialDerivative (parabolicVelocity k t₀ x₀ u) t x
      (coordinateVector i)‖ ^ 2) = _
  simp only [parabolicVelocity, dilate_spatialDerivative, smul_apply]
  rw [spatial_energy_affine
    (fun y => spatialDerivative u (k ^ 2 * (t - t₀)) y (coordinateVector i))
    (k * k) k hk x₀]
  simp only [spatialPartial, spatialDerivative]
  field_simp

/-- Finite full-interval dissipation transports to the shifted short interval. -/
theorem dissipation_intervalIntegrable {u : VelocityField} {k : ℝ} (hk : 0 < k)
    (t₀ : ℝ) (x₀ : Space)
    (hd : IntegrableOn (dissipation u) (Ioo (0 : ℝ) 1)) :
    IntervalIntegrable (dissipation (parabolicVelocity k t₀ x₀ u)) volume t₀
      (t₀ + (k ^ 2)⁻¹) := by
  have hi : IntervalIntegrable (dissipation u) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hd
  have hh := (hi.comp_mul_left (c := k ^ 2)).comp_sub_right t₀
  have he : IntervalIntegrable (fun s => k * dissipation u (k ^ 2 * (s - t₀)))
      volume t₀ (t₀ + (k ^ 2)⁻¹) := by
    simpa [zero_div, one_div, add_comm] using hh.const_mul k
  exact he.congr (fun s _ => (dissipation_parabolic u k t₀ hk x₀ s).symm)

/-- Exact total physical dissipation scaling, including the actual time Jacobian. -/
theorem total_dissipation_parabolic (u : VelocityField) (k t₀ : ℝ) (hk : 0 < k)
    (x₀ : Space) :
    (∫ s in t₀..t₀ + (k ^ 2)⁻¹, dissipation (parabolicVelocity k t₀ x₀ u) s) =
      k⁻¹ * (∫ s in (0 : ℝ)..1, dissipation u s) := by
  simp_rw [dissipation_parabolic u k t₀ hk x₀]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_right (fun s => dissipation u (k ^ 2 * s)) t₀]
  simp only [sub_self, add_sub_cancel_left]
  rw [intervalIntegral.integral_comp_mul_left _ (pow_ne_zero 2 hk.ne')]
  simp only [mul_zero, mul_inv_cancel₀ (pow_ne_zero 2 hk.ne'), smul_eq_mul]
  field_simp

/-- Integrability of the spatial square is preserved by the actual affine map. -/
theorem square_integrable_parabolic {u : VelocityField} {k t₀ t : ℝ}
    (hk : 0 < k) (x₀ : Space)
    (hi : Integrable (fun x : Space => ‖u (k ^ 2 * (t - t₀), x)‖ ^ 2)) :
    Integrable (fun x : Space => ‖parabolicVelocity k t₀ x₀ u (t, x)‖ ^ 2) := by
  have hh := ((hi.comp_smul hk.ne').comp_sub_right x₀).const_mul (k ^ 2)
  simpa only [parabolicVelocity, dilateField, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs] using hh

/-- The actual spatial L2 norm scales by the inverse square root of k. -/
theorem l2Norm_parabolic (u : VelocityField) (k t₀ : ℝ) (hk : 0 < k)
    (x₀ : Space) (t : ℝ) :
    Real.sqrt (l2Sq (parabolicVelocity k t₀ x₀ u) t) =
      Real.sqrt k⁻¹ * Real.sqrt (l2Sq u (k ^ 2 * (t - t₀))) := by
  rw [l2Sq_parabolic u k t₀ hk x₀ t, Real.sqrt_mul (inv_nonneg.mpr hk.le)]

/-- The short physical interval is mapped precisely into the reference interval. -/
theorem reference_time_mem {k t₀ t : ℝ} (hk : 0 < k)
    (ht : t ∈ Ico t₀ (t₀ + (k ^ 2)⁻¹)) :
    k ^ 2 * (t - t₀) ∈ Ico (0 : ℝ) 1 := by
  have hk2 : 0 < k ^ 2 := sq_pos_of_pos hk
  have hc : k ^ 2 * (k ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hk2.ne'
  refine ⟨mul_nonneg hk2.le (sub_nonneg.mpr ht.1), ?_⟩
  have hh := mul_lt_mul_of_pos_left ht.2 hk2
  nlinarith

/-- A uniform reference L2 norm bound gives the scaled L-infinity-in-time,
L2-in-space bound throughout the short interval. -/
theorem uniform_l2Norm_parabolic {u : VelocityField} {k t₀ N : ℝ}
    (hk : 0 < k) (x₀ : Space)
    (hN : ∀ s ∈ Ico (0 : ℝ) 1, Real.sqrt (l2Sq u s) ≤ N) :
    ∀ t ∈ Ico t₀ (t₀ + (k ^ 2)⁻¹),
      Real.sqrt (l2Sq (parabolicVelocity k t₀ x₀ u) t) ≤ Real.sqrt k⁻¹ * N := by
  intro t ht
  rw [l2Norm_parabolic u k t₀ hk x₀ t]
  exact mul_le_mul_of_nonneg_left (hN _ (reference_time_mem hk ht)) (Real.sqrt_nonneg _)

/-- Uniform physical energy, including actual slice square-integrability,
transports to the short interval with the same inverse-length factor. -/
theorem uniform_energy_parabolic {u : VelocityField} {k : ℝ} (hk : 0 < k)
    (t₀ : ℝ) (x₀ : Space)
    (hE : NavierStokesR3.ProblemStatement.UniformFiniteEnergy (Ico (0 : ℝ) 1) u) :
    NavierStokesR3.ProblemStatement.UniformFiniteEnergy (Ico t₀ (t₀ + (k ^ 2)⁻¹))
      (parabolicVelocity k t₀ x₀ u) := by
  obtain ⟨E, hE0, hE⟩ := hE
  refine ⟨k⁻¹ * E, mul_nonneg (inv_nonneg.mpr hk.le) hE0, ?_⟩
  intro t ht
  have hs := hE _ (reference_time_mem hk ht)
  refine ⟨square_integrable_parabolic hk x₀ hs.1, ?_⟩
  change (1 / 2 : ℝ) * l2Sq (parabolicVelocity k t₀ x₀ u) t ≤ k⁻¹ * E
  rw [l2Sq_parabolic u k t₀ hk x₀ t]
  have hh := mul_le_mul_of_nonneg_left hs.2 (inv_nonneg.mpr hk.le)
  change k⁻¹ * ((1 / 2 : ℝ) * l2Sq u (k ^ 2 * (t - t₀))) ≤ k⁻¹ * E at hh
  nlinarith

/-- The reference singular time one is transported to t0+k^{-2}; the witness
points are transported by the inverse spatial affine map. -/
theorem speed_unbounded_parabolic {u : VelocityField} {k t₀ : ℝ}
    (hk : 0 < k) (ht₀ : 0 ≤ t₀) (x₀ : Space) (hu : SpeedUnboundedAtOne u) :
    SpeedUnboundedAt (t₀ + (k ^ 2)⁻¹) (parabolicVelocity k t₀ x₀ u) := by
  intro M hM δ hδ
  have hk2 : 0 < k ^ 2 := sq_pos_of_pos hk
  obtain ⟨s, y, hs, hnear, hlarge⟩ := hu (M / k) (div_pos hM hk)
    (k ^ 2 * δ) (mul_pos hk2 hδ)
  let t := t₀ + s / k ^ 2
  let x := x₀ + k⁻¹ • y
  have ht : t ∈ Ioo 0 (t₀ + (k ^ 2)⁻¹) := by
    dsimp [t]
    refine ⟨lt_of_le_of_lt ht₀ (lt_add_of_pos_right _ (div_pos hs.1 hk2)), ?_⟩
    have hdiv : s / k ^ 2 < (k ^ 2)⁻¹ := by
      simpa only [one_div] using (div_lt_div_of_pos_right hs.2 hk2)
    linarith
  have htnear : t₀ + (k ^ 2)⁻¹ - δ < t := by
    have hh := (div_lt_div_of_pos_right hnear hk2)
    dsimp [t]
    have hc : (k ^ 2 * δ) / k ^ 2 = δ := by field_simp
    rw [sub_div, one_div, hc] at hh
    linarith
  have htime : k ^ 2 * (t - t₀) = s := by dsimp [t]; field_simp; ring
  have hspace : k • (x - x₀) = y := by
    dsimp [x]
    simp [smul_smul, hk.ne']
  refine ⟨t, x, ht, htnear, ?_⟩
  simp only [parabolicVelocity, dilateField, htime, hspace, norm_smul,
    Real.norm_eq_abs, abs_of_pos hk]
  simpa only [mul_comm] using (div_lt_iff₀ hk).mp hlarge

/-- Place the same speed singularity at any prescribed positive target time,
provided the concentration leaves a nonnegative initial delay. -/
theorem speed_unbounded_at_target {u : VelocityField} {k T : ℝ}
    (hk : 0 < k) (hdelay : (k ^ 2)⁻¹ ≤ T) (x₀ : Space)
    (hu : SpeedUnboundedAtOne u) :
    SpeedUnboundedAt T (parabolicVelocity k (T - (k ^ 2)⁻¹) x₀ u) := by
  simpa only [sub_add_cancel] using
    speed_unbounded_parabolic hk (sub_nonneg.mpr hdelay) x₀ hu

/-- The transported spatial compact set. -/
def scaledSupport (k : ℝ) (x₀ : Space) (K : Set Space) : Set Space :=
  (fun y : Space => x₀ + k⁻¹ • y) '' K

theorem scaledSupport_compact {K : Set Space} (hK : IsCompact K)
    (k : ℝ) (x₀ : Space) : IsCompact (scaledSupport k x₀ K) :=
  hK.image (by fun_prop)

/-- Topological spatial support is transported into the same scaled compact
set at each strictly presingular transformed time. -/
theorem parabolic_support {u : VelocityField} {K : Set Space}
    (hK : IsCompact K) {k t₀ t : ℝ} (hk : 0 < k) (x₀ : Space)
    (hs : tsupport (fun y => u (k ^ 2 * (t - t₀), y)) ⊆ K) :
    tsupport (fun x => parabolicVelocity k t₀ x₀ u (t, x)) ⊆ scaledSupport k x₀ K := by
  apply closure_minimal _ (scaledSupport_compact hK k x₀).isClosed
  intro x hx
  have hu : u (k ^ 2 * (t - t₀), k • (x - x₀)) ≠ 0 := by
    intro hz
    exact hx (by simp [parabolicVelocity, dilateField, hz])
  refine ⟨k • (x - x₀), hs (subset_tsupport _ hu), ?_⟩
  simp [smul_smul, hk.ne']

/-- An explicit inverse-length choice simultaneously fits the compact support
inside any prescribed open ball and delays the active packet past any τ<T. -/
theorem exists_concentration_parameters {K : Set Space} (hK : IsCompact K)
    (x₀ : Space) {r T τ : ℝ} (hr : 0 < r) (hτ : τ < T) :
    ∃ k : ℝ, 0 < k ∧ τ < T - (k ^ 2)⁻¹ ∧
      scaledSupport k x₀ K ⊆ Metric.ball x₀ r := by
  obtain ⟨R, hR, hb⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨k, hkbig⟩ := exists_gt (max (1 : ℝ) (max (R / r) (1 / (T - τ))))
  have hk1 : 1 < k := (le_max_left _ _).trans_lt hkbig
  have hk : 0 < k := zero_lt_one.trans hk1
  have hkr : R / r < k :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hkbig
  have hkt : 1 / (T - τ) < k :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hkbig
  have hlength : (k ^ 2)⁻¹ < T - τ := by
    rw [← one_div]
    apply (div_lt_iff₀ (sq_pos_of_pos hk)).mpr
    have hh := (div_lt_iff₀ (sub_pos.mpr hτ)).mp hkt
    have hh2 : k < k ^ 2 := by nlinarith
    have hh3 := mul_lt_mul_of_pos_left hh2 (sub_pos.mpr hτ)
    nlinarith
  refine ⟨k, hk, by linarith, ?_⟩
  rintro z ⟨y, hy, rfl⟩
  rw [Metric.mem_ball, dist_eq_norm]
  have hn : ‖x₀ + k⁻¹ • y - x₀‖ = k⁻¹ * ‖y‖ := by
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos hk]
  rw [hn]
  have hnorm := mul_le_mul_of_nonneg_left (hb y hy) (inv_nonneg.mpr hk.le)
  have hratio : k⁻¹ * R < r := by
    have hh := (div_lt_iff₀ hr).mp hkr
    have hh' : R / k < r := (div_lt_iff₀ hk).mpr (by nlinarith)
    simpa [div_eq_mul_inv, mul_comm] using hh'
  exact hnorm.trans_lt hratio

/-- Canonical zero extension of a spacetime field into nonpositive time. -/
def zeroPastField {V : Type*} [Zero V] (f : SpaceTime → V) : SpaceTime → V :=
  fun z => if 0 < z.1 then f z else 0

@[simp] theorem zeroPastField_of_pos {V : Type*} [Zero V] (f : SpaceTime → V)
    {t : ℝ} (ht : 0 < t) (x : Space) : zeroPastField f (t, x) = f (t, x) := by
  simp [zeroPastField, ht]

@[simp] theorem zeroPastField_of_nonpos {V : Type*} [Zero V] (f : SpaceTime → V)
    {t : ℝ} (ht : t ≤ 0) (x : Space) : zeroPastField f (t, x) = 0 := by
  simp [zeroPastField, not_lt.mpr ht]

/-- All actual spatial derivatives are unchanged at strictly positive times. -/
theorem dissipation_zeroPastField {u : VelocityField} {t : ℝ} (ht : 0 < t) :
    dissipation (zeroPastField u) t = dissipation u t := by
  simp only [dissipation, zeroPastField_of_pos u ht]

/-- The zero extension preserves the full physical dissipation integral. -/
theorem zeroPastField_dissipation_integrable {u : VelocityField}
    (hd : IntegrableOn (dissipation u) (Ioo (0 : ℝ) 1)) :
    IntegrableOn (dissipation (zeroPastField u)) (Ioo (0 : ℝ) 1) := by
  apply (integrableOn_congr_fun (fun t ht => dissipation_zeroPastField ht.1)
    measurableSet_Ioo).mpr hd

/-- Parabolic scaling of the zero-extended reference field leaves every earlier
time unchanged when added to any background, without assumptions on the raw
reference field at far negative times. -/
theorem zeroPast_parabolic_earlier_history (u v : VelocityField) (k t₀ : ℝ)
    (x₀ : Space) {t : ℝ} (ht : t ≤ t₀) (x : Space) :
    v (t, x) + parabolicVelocity k t₀ x₀ (zeroPastField u) (t, x) = v (t, x) := by
  have htime : k ^ 2 * (t - t₀) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg k) (sub_nonpos.mpr ht)
  simp [parabolicVelocity, dilateField, zeroPastField_of_nonpos u htime]

/-- The speed witnesses lie at positive reference times, so extending into the
past does not alter their divergence at time one. -/
theorem zeroPastField_speed {u : VelocityField} (hu : SpeedUnboundedAtOne u) :
    SpeedUnboundedAtOne (zeroPastField u) := by
  intro M hM δ hδ
  obtain ⟨t, x, ht, hnear, hb⟩ := hu M hM δ hδ
  exact ⟨t, x, ht, hnear, by simpa only [zeroPastField_of_pos u ht.1 x] using hb⟩

/-- Positive-time slices and the zero initial slice retain their uniform
physical finite-energy bound under extension into the past. -/
theorem zeroPastField_uniform_energy {u : VelocityField}
    (hE : NavierStokesR3.ProblemStatement.UniformFiniteEnergy (Ico (0 : ℝ) 1) u) :
    NavierStokesR3.ProblemStatement.UniformFiniteEnergy (Ico (0 : ℝ) 1) (zeroPastField u) := by
  obtain ⟨E, hE0, hE⟩ := hE
  refine ⟨E, hE0, ?_⟩
  intro t ht
  by_cases hp : 0 < t
  · simpa only [NavierStokesR3.ProblemStatement.SquareIntegrableAtTime,
      NavierStokesR3.ProblemStatement.kineticEnergy, zeroPastField_of_pos u hp] using hE t ht
  · have hz : t ≤ 0 := le_of_not_gt hp
    simp [NavierStokesR3.ProblemStatement.SquareIntegrableAtTime,
      NavierStokesR3.ProblemStatement.kineticEnergy, zeroPastField_of_nonpos u hz, hE0]

/-- Generic early vanishing includes both velocity and pressure dilations. -/
theorem zeroPast_dilate_early {V : Type*} [Zero V] [SMulZeroClass ℝ V]
    (f : SpaceTime → V) (a c d t₀ : ℝ) (hc : 0 ≤ c) (x₀ : Space)
    {t : ℝ} (ht : t ≤ t₀) (x : Space) :
    dilateField a c d t₀ x₀ (zeroPastField f) (t, x) = 0 := by
  have hs : c * (t - t₀) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc (sub_nonpos.mpr ht)
  simp [dilateField, zeroPastField_of_nonpos f hs]

/-- Actual spatial dissipation vanishes on the entire delayed initial interval. -/
theorem zeroPast_parabolic_dissipation_early (u : VelocityField) {k t₀ t : ℝ}
    (hk : 0 < k) (x₀ : Space) (ht : t ≤ t₀) :
    dissipation (parabolicVelocity k t₀ x₀ (zeroPastField u)) t = 0 := by
  rw [dissipation_parabolic _ k t₀ hk x₀ t]
  have hs : k ^ 2 * (t - t₀) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg k) (sub_nonpos.mpr ht)
  simp [dissipation, spatialPartial, zeroPastField_of_nonpos u hs]

/-- Full physical time integrability includes the delayed zero segment, so no
uncontrolled piece is omitted before the short active interval. -/
theorem delayed_full_dissipation_integrable {u : VelocityField} {k t₀ : ℝ}
    (hk : 0 < k) (ht₀ : 0 ≤ t₀) (x₀ : Space)
    (hd : IntegrableOn (dissipation u) (Ioo (0 : ℝ) 1)) :
    IntegrableOn (dissipation (parabolicVelocity k t₀ x₀ (zeroPastField u)))
      (Ioo (0 : ℝ) (t₀ + (k ^ 2)⁻¹)) := by
  have hearly : IntervalIntegrable
      (dissipation (parabolicVelocity k t₀ x₀ (zeroPastField u))) volume 0 t₀ := by
    apply (intervalIntegrable_const (c := (0 : ℝ))).congr
    intro t ht
    rw [uIoc_of_le ht₀] at ht
    exact (zeroPast_parabolic_dissipation_early u hk x₀ ht.2).symm
  have hlate := dissipation_intervalIntegrable hk t₀ x₀ (zeroPastField_dissipation_integrable hd)
  have hT : 0 ≤ t₀ + (k ^ 2)⁻¹ := add_nonneg ht₀ (inv_nonneg.mpr (sq_nonneg k))
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hT).mp (hearly.trans hlate)

/-- The global physical support remains inside the concentrated compact set,
including the entire interval before activation. -/
theorem delayed_full_support {u : VelocityField} {K : Set Space}
    (hK : IsCompact K) {k t₀ : ℝ} (hk : 0 < k) (x₀ : Space)
    (hs : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x => u (t, x)) ⊆ K) :
    ∀ t ∈ Ico (0 : ℝ) (t₀ + (k ^ 2)⁻¹),
      tsupport (fun x => parabolicVelocity k t₀ x₀ (zeroPastField u) (t, x)) ⊆
        scaledSupport k x₀ K := by
  intro t ht
  by_cases hbefore : t ≤ t₀
  · have hz : (fun x => parabolicVelocity k t₀ x₀ (zeroPastField u) (t, x)) =
        fun _ => 0 := by
      funext x
      exact zeroPast_dilate_early u k (k ^ 2) k t₀ (sq_nonneg k) x₀ hbefore x
    simp [hz]
  · have hafter : t₀ < t := lt_of_not_ge hbefore
    apply parabolic_support hK hk x₀
    have htime := reference_time_mem hk ⟨hafter.le, ht.2⟩
    have htimepos : 0 < k ^ 2 * (t - t₀) := mul_pos (sq_pos_of_pos hk) (sub_pos.mpr hafter)
    simpa only [zeroPastField_of_pos u htimepos] using hs _ htime

/-- The delayed zero segment preserves the transported uniform physical energy
bound over all physical times before the target singularity. -/
theorem delayed_full_uniform_energy {u : VelocityField} {k t₀ : ℝ}
    (hk : 0 < k) (x₀ : Space)
    (hE : NavierStokesR3.ProblemStatement.UniformFiniteEnergy (Ico (0 : ℝ) 1) u) :
    NavierStokesR3.ProblemStatement.UniformFiniteEnergy
      (Ico (0 : ℝ) (t₀ + (k ^ 2)⁻¹)) (parabolicVelocity k t₀ x₀ (zeroPastField u)) := by
  obtain ⟨E, hE0, hbound⟩ := uniform_energy_parabolic hk t₀ x₀ (zeroPastField_uniform_energy hE)
  refine ⟨E, hE0, ?_⟩
  intro t ht
  by_cases hbefore : t ≤ t₀
  · have hz : ∀ x, parabolicVelocity k t₀ x₀ (zeroPastField u) (t, x) = 0 :=
      fun x => zeroPast_dilate_early u k (k ^ 2) k t₀ (sq_nonneg k) x₀ hbefore x
    simp [NavierStokesR3.ProblemStatement.SquareIntegrableAtTime,
      NavierStokesR3.ProblemStatement.kineticEnergy, hz, hE0]
  · exact hbound t ⟨(lt_of_not_ge hbefore).le, ht.2⟩

/-- Smoothness of a field on the physical presingular half-domain extends
smoothly through initial time after past-zero extension, using its quiet germ. -/
theorem zeroPastField_smoothOn {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : SpaceTime → V} {ε : ℝ} (hε : 0 < ε)
    (hf : ContDiffOn ℝ ∞ f preSingularDomain)
    (hq : ∀ t ∈ Ioo (0 : ℝ) ε, ∀ x, f (t, x) = 0) :
    ContDiffOn ℝ ∞ (zeroPastField f) (Iio (1 : ℝ) ×ˢ univ) := by
  intro z hz
  by_cases ht : 0 < z.1
  · have heq : zeroPastField f =ᶠ[𝓝 z] f := by
      filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds ht] with y hy
      simp [zeroPastField, hy]
    exact ((hf.contDiffAt (prod_mem_nhds (Ico_mem_nhds ht hz.1) univ_mem)).congr_of_eventuallyEq
      heq).contDiffWithinAt
  · have heq : zeroPastField f =ᶠ[𝓝 z] (fun _ => 0) := by
      have hzε : z.1 < ε := (le_of_not_gt ht).trans_lt hε
      filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hzε] with y hy
      by_cases hp : 0 < y.1
      · simp [zeroPastField, hp, hq y.1 ⟨hp, hy⟩ y.2]
      · simp [zeroPastField, hp]
    exact (contDiffAt_const.congr_of_eventuallyEq heq).contDiffWithinAt

/-- The support transport works for scalar pressure as well as vector velocity. -/
theorem dilate_support {V : Type*} [Zero V] [SMulZeroClass ℝ V]
    {f : SpaceTime → V} {K : Set Space} (hK : IsCompact K)
    (a c : ℝ) {k t₀ t : ℝ} (hk : 0 < k) (x₀ : Space)
    (hs : tsupport (fun y => f (c * (t - t₀), y)) ⊆ K) :
    tsupport (fun x => dilateField a c k t₀ x₀ f (t, x)) ⊆ scaledSupport k x₀ K := by
  apply closure_minimal _ (scaledSupport_compact hK k x₀).isClosed
  intro x hx
  have hu : f (c * (t - t₀), k • (x - x₀)) ≠ 0 := by
    intro hz
    exact hx (by simp [dilateField, hz])
  refine ⟨k • (x - x₀), hs (subset_tsupport _ hu), ?_⟩
  simp [smul_smul, hk.ne']

/-- The common compact spatial support survives pressure scaling and all
initial delayed times, exactly as it does for velocity. -/
theorem delayed_pressure_support {p : PressureField} {K : Set Space}
    (hK : IsCompact K) {k t₀ : ℝ} (hk : 0 < k) (x₀ : Space)
    (hs : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x => p (t, x)) ⊆ K) :
    ∀ t ∈ Ico (0 : ℝ) (t₀ + (k ^ 2)⁻¹),
      tsupport (fun x => parabolicPressure k t₀ x₀ (zeroPastField p) (t, x)) ⊆
        scaledSupport k x₀ K := by
  intro t ht
  by_cases hbefore : t ≤ t₀
  · have hz : (fun x => parabolicPressure k t₀ x₀ (zeroPastField p) (t, x)) =
        fun _ => 0 := by
      funext x
      exact zeroPast_dilate_early p (k ^ 2) (k ^ 2) k t₀ (sq_nonneg k) x₀ hbefore x
    simp [hz]
  · have hafter : t₀ < t := lt_of_not_ge hbefore
    apply dilate_support hK (k ^ 2) (k ^ 2) hk x₀
    have htime := reference_time_mem hk ⟨hafter.le, ht.2⟩
    have htimepos : 0 < k ^ 2 * (t - t₀) := mul_pos (sq_pos_of_pos hk) (sub_pos.mpr hafter)
    simpa only [zeroPastField_of_pos p htimepos] using hs _ htime

/-- The same affine map transports joint smoothness on the extended open
presingular domain to all physical times before the new singular time. -/
theorem dilate_smoothOn {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : SpaceTime → V} (a : ℝ) {k : ℝ} (hk : 0 < k) (t₀ : ℝ) (x₀ : Space)
    (hf : ContDiffOn ℝ ∞ f (Iio (1 : ℝ) ×ˢ univ)) :
    ContDiffOn ℝ ∞ (dilateField a (k ^ 2) k t₀ x₀ f)
      (Iio (t₀ + (k ^ 2)⁻¹) ×ˢ univ) := by
  have hg : ContDiff ℝ ∞ (fun z : SpaceTime =>
      (k ^ 2 * (z.1 - t₀), k • (z.2 - x₀))) := by fun_prop
  apply contDiffOn_const.smul (hf.comp hg.contDiffOn _)
  intro z hz
  refine ⟨?_, mem_univ _⟩
  change k ^ 2 * (z.1 - t₀) < 1
  have hk2 : 0 < k ^ 2 := sq_pos_of_pos hk
  have hc : k ^ 2 * (k ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hk2.ne'
  have hh := mul_lt_mul_of_pos_left hz.1 hk2
  nlinarith

/-- Local equality transports the physical residual at arbitrary viscosity. -/
theorem residual_congr_local (ν : ℝ) {u v : VelocityField} {p q : PressureField}
    {z : SpaceTime} (hu : u =ᶠ[𝓝 z] v) (hp : p =ᶠ[𝓝 z] q) :
    residual ν u p z.1 z.2 = residual ν v q z.1 z.2 := by
  unfold residual
  rw [NavierStokes.ResidualRegularity.temporalDerivative_congr hu,
    NavierStokes.ResidualRegularity.advection_congr hu,
    NavierStokes.ResidualRegularity.spatialLaplacian_congr hu,
    NavierStokes.ResidualRegularity.pressureGradient_congr hp]

theorem zeroPastField_eventually_pos {V : Type*} [Zero V] (f : SpaceTime → V)
    {z : SpaceTime} (hz : 0 < z.1) : zeroPastField f =ᶠ[𝓝 z] f := by
  filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hz] with y hy
  simp [zeroPastField, hy]

theorem zeroPastField_eventually_zero {V : Type*} [Zero V] {f : SpaceTime → V}
    {ε : ℝ} (hε : 0 < ε) (hq : ∀ t ∈ Ioo (0 : ℝ) ε, ∀ x, f (t, x) = 0)
    {z : SpaceTime} (hz : z.1 ≤ 0) : zeroPastField f =ᶠ[𝓝 z] (fun _ => 0) := by
  filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds (hz.trans_lt hε)] with y hy
  by_cases hp : 0 < y.1
  · simp [zeroPastField, hp, hq y.1 ⟨hp, hy⟩ y.2]
  · simp [zeroPastField, hp]

/-- Past extension satisfies the exact physical PDE even at the activation
seam, using the quiet velocity/pressure germ to justify time differentiation. -/
theorem zeroPastField_equation {u f : VelocityField} {p : PressureField} {ν ε : ℝ}
    (hε : 0 < ε)
    (hu : ∀ t ∈ Ioo (0 : ℝ) ε, ∀ x, u (t, x) = 0)
    (hp : ∀ t ∈ Ioo (0 : ℝ) ε, ∀ x, p (t, x) = 0)
    (hNS : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, residual ν u p t x = f (t, x))
    {t : ℝ} (ht : t < 1) (x : Space) :
    residual ν (zeroPastField u) (zeroPastField p) t x = zeroPastField f (t, x) := by
  by_cases hpos : 0 < t
  · rw [residual_congr_local ν (zeroPastField_eventually_pos u (z := (t, x)) hpos)
      (zeroPastField_eventually_pos p (z := (t, x)) hpos), hNS t ⟨hpos, ht⟩ x,
      zeroPastField_of_pos f hpos]
  · have hz : t ≤ 0 := le_of_not_gt hpos
    rw [residual_congr_local ν (zeroPastField_eventually_zero hε hu (z := (t, x)) hz)
      (zeroPastField_eventually_zero hε hp (z := (t, x)) hz), zeroPastField_of_nonpos f hz]
    simp [residual, temporalDerivative, advection, spatialDerivative, spatialLaplacian, pressureGradient]

/-- The delayed, concentrated fields solve the original viscosity equation at
every time before the new singularity, including the entire inactive past. -/
theorem delayed_parabolic_equation {u f : VelocityField} {p : PressureField} {ν ε k : ℝ}
    (hε : 0 < ε) (hk : 0 < k) (t₀ : ℝ) (x₀ : Space)
    (hu : ∀ t ∈ Ioo (0 : ℝ) ε, ∀ x, u (t, x) = 0)
    (hp : ∀ t ∈ Ioo (0 : ℝ) ε, ∀ x, p (t, x) = 0)
    (hNS : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, residual ν u p t x = f (t, x))
    {t : ℝ} (ht : t < t₀ + (k ^ 2)⁻¹) (x : Space) :
    residual ν (parabolicVelocity k t₀ x₀ (zeroPastField u))
      (parabolicPressure k t₀ x₀ (zeroPastField p)) t x =
      parabolicForce k t₀ x₀ (zeroPastField f) (t, x) := by
  apply parabolic_equation
  apply zeroPastField_equation hε hu hp hNS
  have hk2 : 0 < k ^ 2 := sq_pos_of_pos hk
  have hc : k ^ 2 * (k ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hk2.ne'
  have hh := mul_lt_mul_of_pos_left ht hk2
  nlinarith

/-- Incompressibility is transported across the delayed seam as well. -/
theorem delayed_parabolic_divergence {u : VelocityField} {k : ℝ}
    (hk : 0 < k) (t₀ : ℝ) (x₀ : Space)
    (hd : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, spatialDivergence u t x = 0)
    {t : ℝ} (ht : t < t₀ + (k ^ 2)⁻¹) (x : Space) :
    spatialDivergence (parabolicVelocity k t₀ x₀ (zeroPastField u)) t x = 0 := by
  rw [parabolicVelocity, dilate_divergence]
  by_cases hs : 0 < k ^ 2 * (t - t₀)
  · have hs1 : k ^ 2 * (t - t₀) < 1 := by
      have hk2 : 0 < k ^ 2 := sq_pos_of_pos hk
      have hc : k ^ 2 * (k ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hk2.ne'
      have hh := mul_lt_mul_of_pos_left ht hk2
      nlinarith
    have he : spatialDivergence (zeroPastField u) (k ^ 2 * (t - t₀)) (k • (x - x₀)) =
        spatialDivergence u (k ^ 2 * (t - t₀)) (k • (x - x₀)) := by
      simp only [spatialDivergence, spatialDerivative, zeroPastField_of_pos u hs]
    rw [he, hd _ ⟨hs, hs1⟩, mul_zero]
  · have hn := le_of_not_gt hs
    simp [spatialDivergence, spatialDerivative, zeroPastField_of_nonpos u hn]

/-- The inverse affine map on physical spacetime. -/
def scaledSpaceTimeSupport (k t₀ : ℝ) (x₀ : Space) (K : Set SpaceTime) : Set SpaceTime :=
  (fun z : SpaceTime => (t₀ + z.1 / k ^ 2, x₀ + k⁻¹ • z.2)) '' K

theorem scaledSpaceTimeSupport_compact {K : Set SpaceTime} (hK : IsCompact K)
    (k t₀ : ℝ) (x₀ : Space) : IsCompact (scaledSpaceTimeSupport k t₀ x₀ K) :=
  hK.image (by fun_prop)

/-- True compact spacetime support transforms by the inverse affine map. -/
theorem parabolicForce_support {f : VelocityField} (hf : HasCompactSupport f)
    {k : ℝ} (hk : 0 < k) (t₀ : ℝ) (x₀ : Space) :
    tsupport (parabolicForce k t₀ x₀ f) ⊆ scaledSpaceTimeSupport k t₀ x₀ (tsupport f) := by
  apply closure_minimal _ (scaledSpaceTimeSupport_compact hf.isCompact k t₀ x₀).isClosed
  intro z hz
  have hfn : f (k ^ 2 * (z.1 - t₀), k • (z.2 - x₀)) ≠ 0 := by
    intro hzero
    exact hz (by simp [parabolicForce, dilateField, hzero])
  refine ⟨(k ^ 2 * (z.1 - t₀), k • (z.2 - x₀)), subset_tsupport _ hfn, ?_⟩
  apply Prod.ext
  · dsimp only
    field_simp
    ring
  · dsimp only
    simp [smul_smul, hk.ne']

/-- Concentration after a nonnegative delay preserves the required globally
compact force support strictly inside positive physical time. -/
theorem parabolicForce_positive_support {f : VelocityField}
    (hf : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    {k t₀ : ℝ} (hk : 0 < k) (ht₀ : 0 ≤ t₀) (x₀ : Space) :
    NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport (parabolicForce k t₀ x₀ f) := by
  have hs := parabolicForce_support hf.1 hk t₀ x₀
  refine ⟨(scaledSpaceTimeSupport_compact hf.1.isCompact k t₀ x₀).of_isClosed_subset
    (isClosed_tsupport _) hs, ?_⟩
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hs hz
  refine ⟨?_, mem_univ _⟩
  exact lt_of_le_of_lt ht₀ (lt_add_of_pos_right _ (div_pos (hf.2 hy).1 (sq_pos_of_pos hk)))

/-- The globally smooth force remains globally smooth after concentration. -/
theorem parabolicForce_smooth {f : VelocityField} (hf : ContDiff ℝ ∞ f)
    (k t₀ : ℝ) (x₀ : Space) : ContDiff ℝ ∞ (parabolicForce k t₀ x₀ f) := by
  have hg : ContDiff ℝ ∞ (fun z : SpaceTime =>
      (k ^ 2 * (z.1 - t₀), k • (z.2 - x₀))) := by fun_prop
  have ha : ContDiff ℝ ∞ (fun _ : SpaceTime => (k ^ 3 : ℝ)) := contDiff_const
  have hh : ContDiff ℝ ∞ (fun z : SpaceTime => f (k ^ 2 * (z.1 - t₀), k • (z.2 - x₀))) := hf.comp hg
  exact ha.smul hh

/-- A force supported strictly in positive time already equals its past-zero
extension, so the physical prescribed force is unchanged by that convention. -/
theorem zeroPastField_eq_of_positive_support {f : VelocityField}
    (hf : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f) : zeroPastField f = f := by
  funext z
  by_cases hp : 0 < z.1
  · simp [zeroPastField, hp]
  · have hz := hf.eq_zero_of_nonpos (le_of_not_gt hp) z.2
    simpa [zeroPastField, hp] using hz.symm

/-- A single concentration choice delivers the physical packet in any open
ball, singular at any T>τ≥0, with full finite dissipation, uniform energy and
exact preservation of the earlier history. Pressure uses the same compact set. -/
theorem concentrate_packet {u : VelocityField} {p : PressureField} {K : Set Space}
    (hK : IsCompact K) (x₀ : Space) {r T τ : ℝ} (hr : 0 < r)
    (hτ0 : 0 ≤ τ) (hτT : τ < T)
    (huSupport : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x => u (t, x)) ⊆ K)
    (hpSupport : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x => p (t, x)) ⊆ K)
    (hE : NavierStokesR3.ProblemStatement.UniformFiniteEnergy (Ico (0 : ℝ) 1) u)
    (hD : IntegrableOn (dissipation u) (Ioo (0 : ℝ) 1))
    (hSpeed : SpeedUnboundedAtOne u) :
    ∃ k : ℝ, 0 < k ∧ τ < T - (k ^ 2)⁻¹ ∧
      scaledSupport k x₀ K ⊆ Metric.ball x₀ r ∧
      let U := parabolicVelocity k (T - (k ^ 2)⁻¹) x₀ (zeroPastField u)
      let P := parabolicPressure k (T - (k ^ 2)⁻¹) x₀ (zeroPastField p)
      (∀ t ∈ Ico (0 : ℝ) T,
        tsupport (fun x => U (t, x)) ⊆ Metric.ball x₀ r ∧
        tsupport (fun x => P (t, x)) ⊆ Metric.ball x₀ r) ∧
      SpeedUnboundedAt T U ∧
      NavierStokesR3.ProblemStatement.UniformFiniteEnergy (Ico (0 : ℝ) T) U ∧
      IntegrableOn (dissipation U) (Ioo (0 : ℝ) T) ∧
      (∀ t : ℝ, t ≤ τ → ∀ x, U (t, x) = 0 ∧ P (t, x) = 0) := by
  obtain ⟨k, hk, hdelay, hball⟩ := exists_concentration_parameters hK x₀ hr hτT
  have ht₀ : 0 ≤ T - (k ^ 2)⁻¹ := hτ0.trans hdelay.le
  refine ⟨k, hk, hdelay, hball, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have hU := delayed_full_support hK hk x₀ huSupport (t₀ := T - (k ^ 2)⁻¹) t
      (by simpa only [sub_add_cancel] using ht)
    have hP := delayed_pressure_support hK hk x₀ hpSupport (t₀ := T - (k ^ 2)⁻¹) t
      (by simpa only [sub_add_cancel] using ht)
    exact ⟨hU.trans hball, hP.trans hball⟩
  · simpa only [sub_add_cancel] using speed_unbounded_parabolic hk ht₀ x₀ (zeroPastField_speed hSpeed)
  · have hh := delayed_full_uniform_energy hk x₀ hE (t₀ := T - (k ^ 2)⁻¹)
    rw [sub_add_cancel] at hh
    exact hh
  · simpa only [sub_add_cancel] using delayed_full_dissipation_integrable hk ht₀ x₀ hD
  · intro t ht x
    exact ⟨zeroPast_dilate_early u k (k ^ 2) k _ (sq_nonneg k) x₀ (ht.trans hdelay.le) x,
      zeroPast_dilate_early p (k ^ 2) (k ^ 2) k _ (sq_nonneg k) x₀ (ht.trans hdelay.le) x⟩

/-- The exact dissipation factor holds on the entire physical interval,
including the zero segment before activation and excluding no earlier times. -/
theorem total_delayed_dissipation {u : VelocityField} {k t₀ : ℝ}
    (hk : 0 < k) (ht₀ : 0 ≤ t₀) (x₀ : Space)
    (hd : IntegrableOn (dissipation u) (Ioo (0 : ℝ) 1)) :
    (∫ t in (0 : ℝ)..t₀ + (k ^ 2)⁻¹,
      dissipation (parabolicVelocity k t₀ x₀ (zeroPastField u)) t) =
      k⁻¹ * (∫ t in (0 : ℝ)..1, dissipation u t) := by
  have hearly : IntervalIntegrable
      (dissipation (parabolicVelocity k t₀ x₀ (zeroPastField u))) volume 0 t₀ := by
    apply (intervalIntegrable_const (c := (0 : ℝ))).congr
    intro t ht
    rw [uIoc_of_le ht₀] at ht
    exact (zeroPast_parabolic_dissipation_early u hk x₀ ht.2).symm
  have hlate := dissipation_intervalIntegrable hk t₀ x₀ (zeroPastField_dissipation_integrable hd)
  have hzero : (∫ t in (0 : ℝ)..t₀,
      dissipation (parabolicVelocity k t₀ x₀ (zeroPastField u)) t) = 0 := by
    calc
      _ = ∫ t in (0 : ℝ)..t₀, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le ht₀
        intro t ht
        exact zeroPast_parabolic_dissipation_early u hk x₀ ht.2.le
      _ = 0 := by simp
  have hsource : (∫ t in (0 : ℝ)..1, dissipation (zeroPastField u) t) =
      ∫ t in (0 : ℝ)..1, dissipation u t := by
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro t ht
    exact dissipation_zeroPastField ht.1
  have hh := intervalIntegral.integral_add_adjacent_intervals hearly hlate
  rw [hzero, total_dissipation_parabolic (zeroPastField u) k t₀ hk x₀, hsource, zero_add] at hh
  exact hh.symm

/-- Full classical concentration bridge for an existing physical candidate:
all fields, PDE, incompressibility, compact force, common spatial support,
energy, dissipation, speed divergence and earlier history use the same k. -/
theorem concentrate_classical_packet {ν : ℝ} {u f : VelocityField} {p : PressureField}
    {K : Set Space} (h : NavierStokesR3.ProblemStatement.CandidateProperties ν u p f K)
    (hD : IntegrableOn (dissipation u) (Ioo (0 : ℝ) 1))
    {ε : ℝ} (hε : 0 < ε)
    (huQuiet : ∀ t ∈ Ioo (0 : ℝ) ε, ∀ x, u (t, x) = 0)
    (hpQuiet : ∀ t ∈ Ioo (0 : ℝ) ε, ∀ x, p (t, x) = 0)
    (x₀ : Space) {r T τ : ℝ} (hr : 0 < r) (hτ0 : 0 ≤ τ) (hτT : τ < T) :
    ∃ k : ℝ, 0 < k ∧ τ < T - (k ^ 2)⁻¹ ∧
      scaledSupport k x₀ K ⊆ Metric.ball x₀ r ∧
      let U := parabolicVelocity k (T - (k ^ 2)⁻¹) x₀ (zeroPastField u)
      let P := parabolicPressure k (T - (k ^ 2)⁻¹) x₀ (zeroPastField p)
      let F := parabolicForce k (T - (k ^ 2)⁻¹) x₀ f
      ContDiffOn ℝ ∞ U (Ico (0 : ℝ) T ×ˢ univ) ∧
      ContDiffOn ℝ ∞ P (Ico (0 : ℝ) T ×ˢ univ) ∧
      ContDiff ℝ ∞ F ∧ NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport F ∧
      (∀ z ∈ tsupport F, z.2 ∈ Metric.ball x₀ r) ∧
      (∀ t ∈ Ico (0 : ℝ) T,
        tsupport (fun x => U (t, x)) ⊆ Metric.ball x₀ r ∧
        tsupport (fun x => P (t, x)) ⊆ Metric.ball x₀ r) ∧
      (∀ t ∈ Ico (0 : ℝ) T, ∀ x, spatialDivergence U t x = 0) ∧
      (∀ t ∈ Ioo (0 : ℝ) T, ∀ x, residual ν U P t x = F (t, x)) ∧
      SpeedUnboundedAt T U ∧
      NavierStokesR3.ProblemStatement.UniformFiniteEnergy (Ico (0 : ℝ) T) U ∧
      IntegrableOn (dissipation U) (Ioo (0 : ℝ) T) ∧
      (∀ t : ℝ, t ≤ τ → ∀ x, U (t, x) = 0 ∧ P (t, x) = 0) := by
  let Kf : Set Space := Prod.snd '' tsupport f
  have hKf : IsCompact Kf := h.force_support.1.isCompact.image continuous_snd
  have hK : IsCompact (K ∪ Kf) := h.support_compact.union hKf
  obtain ⟨k, hk, hdelay, hball, hs, hspeed, he, hd, hearly⟩ :=
    concentrate_packet hK x₀ hr hτ0 hτT
      (fun t ht => (h.velocity_support t ht).trans subset_union_left)
      (fun t ht => (h.pressure_support t ht).trans subset_union_left)
      h.energy_bounded hD h.speed_unbounded
  have ht₀ : 0 ≤ T - (k ^ 2)⁻¹ := hτ0.trans hdelay.le
  have hballK : scaledSupport k x₀ K ⊆ Metric.ball x₀ r := by
    rintro z ⟨y, hy, rfl⟩
    exact hball ⟨y, Or.inl hy, rfl⟩
  refine ⟨k, hk, hdelay, hballK, ?_, ?_, parabolicForce_smooth h.force_smooth _ _ _,
    parabolicForce_positive_support h.force_support hk ht₀ x₀, ?_, hs, ?_, ?_,
    hspeed, he, hd, hearly⟩
  · have hh := dilate_smoothOn k hk (T - (k ^ 2)⁻¹) x₀
      (zeroPastField_smoothOn hε h.velocity_smooth huQuiet)
    rw [sub_add_cancel] at hh
    exact hh.mono (fun z hz => ⟨hz.1.2, hz.2⟩)
  · have hh := dilate_smoothOn (k ^ 2) hk (T - (k ^ 2)⁻¹) x₀
      (zeroPastField_smoothOn hε h.pressure_smooth hpQuiet)
    rw [sub_add_cancel] at hh
    exact hh.mono (fun z hz => ⟨hz.1.2, hz.2⟩)
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := parabolicForce_support h.force_support.1 hk _ x₀ hz
    exact hball ⟨y.2, Or.inr ⟨y, hy, rfl⟩, rfl⟩
  · intro t ht x
    exact delayed_parabolic_divergence hk _ x₀
      (fun s hs => h.divergence_free s ⟨hs.1.le, hs.2⟩)
      (by simpa only [sub_add_cancel] using ht.2) x
  · intro t ht x
    have hh := delayed_parabolic_equation hε hk (T - (k ^ 2)⁻¹) x₀ huQuiet hpQuiet
      h.navier_stokes (t := t) (by simpa only [sub_add_cancel] using ht.2) x
    rw [zeroPastField_eq_of_positive_support h.force_support] at hh
    exact hh

end NSFormalization.Source.PacketScaling
