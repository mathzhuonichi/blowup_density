import NSFormalization.Source.LocalizedInsertion
import NSFormalization.Source.PhysicalRemoval
import NSFormalization.Source.LocalizedBlowup

/-! One physical packet and fixed rescaled cutoffs generate an insertion family. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace NSFormalization.Source.InsertionFamily
open NavierStokes.ProblemStatement NavierStokesR3.CompactEnergy
open PacketScaling LocalizedInsertion PhysicalRemoval LocalizedBlowup
open NSFormalization.Paper1 NSFormalization.Paper1.CorrectionProfile

/-- All assertions concern one total velocity, pressure and perturbation force. -/
def InsertionProperties (ν : ℝ) (v : VelocityField) (q : PressureField) (g : VelocityField)
    (x₀ : Space) (r T τ : ℝ) (V : VelocityField) (Q : PressureField) (G : VelocityField) : Prop :=
  ContDiffOn ℝ ∞ V (Ico (0 : ℝ) T ×ˢ univ) ∧
  ContDiffOn ℝ ∞ Q (Ico (0 : ℝ) T ×ˢ univ) ∧
  ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
  tsupport G ⊆ Ioi τ ×ˢ Metric.ball x₀ r ∧
  (∃ L : Set Space, IsCompact L ∧ L ⊆ Metric.ball x₀ r ∧
    ∀ t ∈ Ico (0 : ℝ) T,
      tsupport (fun x => V (t, x) - v (t, x)) ⊆ L ∧
      tsupport (fun x => Q (t, x) - q (t, x)) ⊆ L) ∧
  (∀ t ∈ Ico (0 : ℝ) T, ∀ x, spatialDivergence V t x = 0) ∧
  (∀ t ∈ Ioo (0 : ℝ) T, ∀ x, residual ν V Q t x = g (t, x) + G (t, x)) ∧
  SpeedUnboundedAt T V ∧
  LocalSpeedUnboundedAt T (Metric.closedBall x₀ r) V ∧
  (∀ t : ℝ, t ≤ τ → ∀ x, V (t, x) = v (t, x) ∧ Q (t, x) = q (t, x))

/-- The correction is exactly the field estimated by the profile norm lemmas. -/
def velocity (u v : VelocityField) (x₀ : Space) (T : ℝ)
    (θ : Space → ℝ) (η : ℝ → ℝ) (ε : ℝ) : VelocityField := fun z =>
  v z + physicalCorrection v x₀ T θ η ε z +
    parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField u) z

def pressure (p q : PressureField) (x₀ : Space) (T ε : ℝ) : PressureField := fun z =>
  q z + parabolicPressure ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField p) z

def force (ν : ℝ) (f v : VelocityField) (x₀ : Space) (T : ℝ)
    (θ : Space → ℝ) (η : ℝ → ℝ) (ε : ℝ) : VelocityField := fun z =>
  correctionForce ν v (physicalCorrection v x₀ T θ η ε) z +
    parabolicForce ε⁻¹ (T - ε ^ 2) x₀ f z

/-- The actual family solves the insertion problem at every admissible scale,
with fixed spatial and temporal cutoffs. -/
theorem insertion_at_scale {ν : ℝ} {u f v g : VelocityField} {p q : PressureField}
    {K : Set Space} (hc : NavierStokesR3.ProblemStatement.CandidateProperties ν u p f K)
    {a : ℝ} (ha : 0 < a)
    (huQuiet : ∀ t ∈ Ioo (0 : ℝ) a, ∀ x, u (t, x) = 0)
    (hpQuiet : ∀ t ∈ Ioo (0 : ℝ) a, ∀ x, p (t, x) = 0)
    (hv : ContDiff ℝ ∞ v) (hq : ContDiff ℝ ∞ q)
    (hvdiv : ∀ t x, spatialDivergence v t x = 0)
    (x₀ : Space) {r R T τ ε : ℝ} (hτ0 : 0 ≤ τ) (hε : 0 < ε)
    (hspace : ε * R < r) (htime : 2 * ε ^ 2 < T - τ)
    (hKR : K ⊆ Metric.ball 0 R)
    (hfR : ∀ z ∈ tsupport f, z.2 ∈ Metric.ball 0 R)
    {θ : Space → ℝ} {η : ℝ → ℝ} {O : Set Space}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθR : tsupport θ ⊆ Metric.ball 0 R) (hηI : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hO : IsOpen O) (hKO : K ⊆ O) (hθone : EqOn θ (fun _ => 1) O)
    (hηone : EqOn η (fun _ => 1) (Icc (-1 : ℝ) 1))
    (hvNS : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, residual ν v q t x = g (t, x)) :
    InsertionProperties ν v q g x₀ r T τ
      (velocity u v x₀ T θ η ε) (pressure p q x₀ T ε) (force ν f v x₀ T θ η ε) := by
  let k := ε⁻¹
  let t₀ := T - ε ^ 2
  let U := parabolicVelocity k t₀ x₀ (zeroPastField u)
  let P := parabolicPressure k t₀ x₀ (zeroPastField p)
  let F := parabolicForce k t₀ x₀ f
  let w := physicalCorrection v x₀ T θ η ε
  have hk : 0 < k := inv_pos.mpr hε
  have hinv : (k ^ 2)⁻¹ = ε ^ 2 := by simp [k, inv_pow]
  have hend : t₀ + (k ^ 2)⁻¹ = T := by rw [hinv]; dsimp [t₀]; ring
  have hstart : τ < t₀ := by dsimp [t₀]; nlinarith [sq_pos_of_pos hε]
  have ht₀ : 0 ≤ t₀ := hτ0.trans hstart.le
  have hUs : ContDiffOn ℝ ∞ U (Ico (0 : ℝ) T ×ˢ univ) := by
    have hh := dilate_smoothOn k hk t₀ x₀ (zeroPastField_smoothOn ha hc.velocity_smooth huQuiet)
    rw [hend] at hh
    exact hh.mono (fun z hz => ⟨hz.1.2, hz.2⟩)
  have hPs : ContDiffOn ℝ ∞ P (Ico (0 : ℝ) T ×ˢ univ) := by
    have hh := dilate_smoothOn (k ^ 2) hk t₀ x₀ (zeroPastField_smoothOn ha hc.pressure_smooth hpQuiet)
    rw [hend] at hh
    exact hh.mono (fun z hz => ⟨hz.1.2, hz.2⟩)
  have hFs : ContDiff ℝ ∞ F := parabolicForce_smooth hc.force_smooth k t₀ x₀
  have hFc := parabolicForce_positive_support hc.force_support hk ht₀ x₀
  have hws := physical_smooth hv x₀ T ε hθ hη
  have hwc := physical_compact hε.ne' v x₀ T hθc hηc
  have hwdiv := physical_divergence hv x₀ T ε η hθ
  have hwSupp := physical_support hε v x₀ T hθc hηc hθR hηI
  have hball : scaledSupport k x₀ K ⊆ Metric.ball x₀ r := by
    rintro x ⟨y, hy, rfl⟩
    have hyN : ‖y‖ < R := by simpa using hKR hy
    have hh := (mul_lt_mul_of_pos_left hyN hε).trans hspace
    simpa [k, dist_eq_norm, norm_smul, abs_of_pos hε] using hh
  have hscaledO : scaledSupport k x₀ K ⊆ spaceMap ε x₀ '' O := by
    rintro x ⟨y, hy, rfl⟩
    exact ⟨y, hKO hy, by simp [spaceMap, k]⟩
  have hremove := physical_removes hv hvdiv x₀ T hε θ η hO hθone hηone
  have hcancel : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ tsupport (fun y => U (t, y)),
      ∀ᶠ y in 𝓝 x, v (t, y) + w (t, y) = 0 := by
    have hh := background_removed_on_packet hk x₀ hc.velocity_support hc.support_compact hscaledO
      (by simpa only [hinv] using hremove)
    simpa only [hinv] using hh
  have hUdiv : ∀ t ∈ Ico (0 : ℝ) T, ∀ x, spatialDivergence U t x = 0 := by
    intro t ht x
    exact delayed_parabolic_divergence hk t₀ x₀
      (fun s hs => hc.divergence_free s ⟨hs.1.le, hs.2⟩) (by simpa only [hend] using ht.2) x
  have hUNS : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, residual ν U P t x = F (t, x) := by
    intro t ht x
    have hh := delayed_parabolic_equation ha hk t₀ x₀ huQuiet hpQuiet hc.navier_stokes
      (t := t) (by simpa only [hend] using ht.2) x
    rw [zeroPastField_eq_of_positive_support hc.force_support] at hh
    exact hh
  have hSpeed : SpeedUnboundedAt T U := by
    simpa only [hend] using speed_unbounded_parabolic hk ht₀ x₀ (zeroPastField_speed hc.speed_unbounded)
  have hFloc : tsupport F ⊆ Ioi τ ×ˢ Metric.ball x₀ r := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := parabolicForce_support hc.force_support.1 hk t₀ x₀ hz
    constructor
    · have hh := div_pos (hc.force_support.2 hy).1 (sq_pos_of_pos hk)
      change τ < t₀ + y.1 / k ^ 2
      linarith
    · have hyN : ‖y.2‖ < R := by simpa using hfR y hy
      have hh := (mul_lt_mul_of_pos_left hyN hε).trans hspace
      simpa [k, dist_eq_norm, norm_smul, abs_of_pos hε] using hh
  have hwloc : tsupport w ⊆ Ioi τ ×ˢ Metric.ball x₀ r := by
    intro z hz
    have hh := hwSupp hz
    exact ⟨(show τ < z.1 by have := hh.1.1; linarith), Metric.ball_subset_ball hspace.le hh.2⟩
  refine ⟨(hv.contDiffOn.add hws.contDiffOn).add hUs, hq.contDiffOn.add hPs,
    (correctionForce_smooth ν hv hws).add hFs,
    (correctionForce_compact ν v hwc).add hFc.1, ?_, ?_,
    inserted_divergence hv hws hUs hvdiv hwdiv hUdiv, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hh := tsupport_binop_subset (fun a b : Space => a + b) (by simp)
      (correctionForce ν v w) F hz
    exact hh.elim (fun hh => hwloc (correctionForce_support ν v w hh)) (fun hh => hFloc hh)
  · let Lw := Prod.snd '' tsupport w
    refine ⟨Lw ∪ scaledSupport k x₀ K,
      (hwc.isCompact.image continuous_snd).union (scaledSupport_compact hc.support_compact k x₀), ?_, ?_⟩
    · rintro x (hx | hx)
      · obtain ⟨z, hz, rfl⟩ := hx
        exact (hwloc hz).2
      · exact hball hx
    · intro t ht
      have heq (a b c : Space) : a + b + c - a = b + c := by abel
      simp only [velocity, pressure, heq, add_sub_cancel_left]
      constructor
      · intro x hx
        have hh := tsupport_binop_subset (fun a b : Space => a + b) (by simp)
          (fun x => w (t, x)) (fun x => U (t, x)) hx
        rcases hh with hh | hh
        · exact Or.inl (slice_support_projection hwc t hh)
        · exact Or.inr (delayed_full_support hc.support_compact hk x₀ hc.velocity_support
            t (by rwa [hend]) hh)
      · intro x hx
        exact Or.inr (delayed_pressure_support hc.support_compact hk x₀ hc.pressure_support
          t (by rwa [hend]) hx)
  · intro t ht x
    change residual ν (fun z => v z + w z + U z) (fun z => q z + P z) t x =
      g (t, x) + (correctionForce ν v w (t, x) + F (t, x))
    simpa only [add_assoc] using inserted_equation hv hws hq hUs hPs hvNS hUNS hcancel t ht x
  · exact inserted_speed hSpeed (fun t ht x hx => (hcancel t ht x hx).self_of_nhds)
  · apply inserted_local_speed hSpeed _
      (fun t ht x hx => (hcancel t ht x hx).self_of_nhds)
    intro t ht
    exact (delayed_full_support hc.support_compact hk x₀ hc.velocity_support
      t (by simpa only [hend] using ⟨ht.1.le, ht.2⟩)).trans
      (hball.trans Metric.ball_subset_closedBall)
  · intro t ht x
    have hw0 : w (t, x) = 0 := image_eq_zero_of_notMem_tsupport
      (fun hz => (not_lt_of_ge ht) (hwloc hz).1)
    have hU0 := zeroPast_dilate_early u k (k ^ 2) k t₀ (sq_nonneg k) x₀ (ht.trans hstart.le) x
    have hP0 := zeroPast_dilate_early p (k ^ 2) (k ^ 2) k t₀ (sq_nonneg k) x₀ (ht.trans hstart.le) x
    change U (t, x) = 0 at hU0
    change P (t, x) = 0 at hP0
    change v (t, x) + w (t, x) + U (t, x) = _ ∧ q (t, x) + P (t, x) = _
    simp only [hw0, hU0, hP0, add_zero, and_self]

/-- No continuous continuation of the constructed trajectory can cross T.
The compact spatial localization is essential when the reference is unbounded. -/
theorem InsertionProperties.no_continuous_continuation
    {ν r T τ : ℝ} {v g V G : VelocityField} {q Q : PressureField} {x₀ : Space}
    (h : InsertionProperties ν v q g x₀ r T τ V Q G) :
    ¬ ∃ δ : ℝ, 0 < δ ∧ ∃ W : VelocityField,
      ContinuousOn W (Icc (T - δ) (T + δ) ×ˢ Metric.closedBall x₀ r) ∧
      (∀ t ∈ Ioo (0 : ℝ) T, T - δ < t → ∀ x ∈ Metric.closedBall x₀ r,
        W (t, x) = V (t, x)) := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, hlocal, _⟩
  exact LocalizedBlowup.no_continuous_continuation (isCompact_closedBall x₀ r) hlocal

/-- One source packet and one pair of cutoffs work at every sufficiently small
positive scale. This quantifier order permits simultaneous norm limits. -/
theorem exists_insertion_family {ν : ℝ} (hν : 0 < ν)
    {v g : VelocityField} {q : PressureField}
    (hv : ContDiff ℝ ∞ v) (hq : ContDiff ℝ ∞ q)
    (hvdiv : ∀ t x, spatialDivergence v t x = 0)
    (x₀ : Space) {r T τ : ℝ} (hr : 0 < r) (hτ0 : 0 ≤ τ) (hτT : τ < T)
    (hvNS : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, residual ν v q t x = g (t, x)) :
    ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField, ∃ K : Set Space,
    ∃ θ : Space → ℝ, ∃ η : ℝ → ℝ, ∃ ε₀ : ℝ,
      NavierStokesR3.ProblemStatement.CandidateProperties ν u p f K ∧
      IntegrableOn (dissipation u) (Ioo (0 : ℝ) 1) ∧
      ContDiff ℝ ∞ θ ∧ ContDiff ℝ ∞ η ∧
      HasCompactSupport θ ∧ HasCompactSupport η ∧ 0 < ε₀ ∧
      ∀ ε ∈ Ioo (0 : ℝ) ε₀,
        InsertionProperties ν v q g x₀ r T τ
          (velocity u v x₀ T θ η ε) (pressure p q x₀ T ε) (force ν f v x₀ T θ η ε) := by
  obtain ⟨u, p, f, K, hc, hD, hquiet⟩ := selected_packet_every_viscosity hν
  have huQuiet : ∀ t ∈ Ioo (0 : ℝ) (3 / 8), ∀ x, u (t, x) = 0 := by
    intro t ht x
    exact (hquiet t (by rw [abs_of_pos ht.1]; exact ht.2.le) x).1
  have hpQuiet : ∀ t ∈ Ioo (0 : ℝ) (3 / 8), ∀ x, p (t, x) = 0 := by
    intro t ht x
    exact (hquiet t (by rw [abs_of_pos ht.1]; exact ht.2.le) x).2
  let Kall := K ∪ Prod.snd '' tsupport f
  have hKall : IsCompact Kall := hc.support_compact.union
    (hc.force_support.1.isCompact.image continuous_snd)
  obtain ⟨B, hB, hb⟩ := hKall.isBounded.exists_pos_norm_le
  let R := B + 1
  have hR : 0 < R := by dsimp [R]; linarith
  have hKallR : Kall ⊆ Metric.ball 0 R := by
    intro y hy
    have hh := hb y hy
    change dist y 0 < R
    rw [dist_zero_right]
    dsimp [R]
    linarith
  have hKR : K ⊆ Metric.ball 0 R := fun _ hy => hKallR (Or.inl hy)
  have hfR : ∀ z ∈ tsupport f, z.2 ∈ Metric.ball 0 R :=
    fun z hz => hKallR (Or.inr ⟨z, hz, rfl⟩)
  obtain ⟨θ, O, hθ, hθc, hθR, hO, hKO, hθone⟩ :=
    exists_spatial_cutoff hc.support_compact hR hKR
  obtain ⟨η, hη, hηc, hηone, hηI⟩ := exists_temporal_cutoff 0 1 (by norm_num)
  have hηone' : EqOn η (fun _ => 1) (Icc (-1 : ℝ) 1) := by simpa using hηone
  have hηI' : tsupport η ⊆ Ioo (-2 : ℝ) 2 := by simpa using hηI
  let ε₀ := min 1 (min (r / R) ((T - τ) / 2))
  have hε₀ : 0 < ε₀ := lt_min zero_lt_one (lt_min (div_pos hr hR) (by linarith))
  refine ⟨u, p, f, K, θ, η, ε₀, hc, hD, hθ, hη, hθc, hηc, hε₀, ?_⟩
  intro ε hε
  have he1 : ε < 1 := hε.2.trans_le (min_le_left _ _)
  have heR : ε < r / R := hε.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heT : ε < (T - τ) / 2 := hε.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hspace : ε * R < r := (lt_div_iff₀ hR).mp heR
  have htime : 2 * ε ^ 2 < T - τ := by nlinarith [hε.1]
  exact insertion_at_scale hc (by norm_num : (0 : ℝ) < 3 / 8) huQuiet hpQuiet hv hq hvdiv
    x₀ hτ0 hε.1 hspace htime hKR hfR hθ hη hθc hηc hθR hηI' hO hKO hθone hηone' hvNS

end NSFormalization.Source.InsertionFamily
