import NSFormalization.Section3.T15.Energy
import NSFormalization.Section3.T15.Mixed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# T15 U4/U5 conformance and concrete active-scale probe

Part 1 copies the five canonical `ScalingAPI` field types
(`formalization/NSFormalization/Section3/T15/Scaling.lean:341,352,363,376,390`,
Spec form `research/T15/Spec.lean:793-845`) verbatim and closes each by a bare
`exact` of the corresponding U4/U5 theorem.  Part 1b checks that the Section 4
hypothesis bundle `I03.PacketData` used by the two energy identities is built
*only* from clauses that `scalingStatement`
(`Section3/T15/Scaling.lean:462-503`) already carries, so no hypothesis is
smuggled in.

Part 2 instantiates the same geometry as `research/T15/probes/placement_closes.lean`
and `single_copy_closes.lean` — cube centre `(1/2,1/2,1/2)`, spatial bump of
radius `1/4`, chart ball of radius `3/8`, `ε₀ = 1/2`, `T = 1` — with a
**genuinely nonzero** velocity/force, obtained by multiplying the spatial bump
by a time bump supported in `[1/4,3/4] ⊆ (0,∞)`.  At `ε = 1/2` all five fields
whose hypotheses are the cheap packet clauses fire on that data.

Run from `verification/` with
`lake env lean ../research/T15/probes/energy_mixed_closes.lean`.
-/

noncomputable section

namespace NSFormalization.Section3.T15

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NavierStokesR3.CompactEnergy (l2Sq dissipation)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open NSFormalization.Source
open NSFormalization.Source.PacketScaling
open scoped ContDiff ENNReal Topology

/-! ## Part 1 — five literal `ScalingAPI` field-type checks -/

section FieldChecks

variable {u f : VelocityField} {pf : PressureField} {K : Set Space} {M D : ℝ}
variable (hext : ContDiffOn ℝ ∞ (zeroPastField u) (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
variable (hK : IsCompact K)
variable (hu : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => u (t, x)) ⊆ K)
variable (hP : NSFormalization.Section4.I03.PacketData u K M D)
variable (hf : ContDiff ℝ ∞ f)
variable (hfc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
variable (place : PlacementData u pf f K)

example : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    EnergySlicesMemLpT place.T
      (periodizedScaledVelocity u place.x₀ place.T ε) := by
  exact energySlices_memLp hext hK hu place

example : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    energyEssSupT place.T
        (periodizedScaledVelocity u place.x₀ place.T ε) =
      ENNReal.ofReal (ε ^ ((1 : ℝ) / 2) * M) := by
  exact packetEnergyIdentity hP hu place

example : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    energyGradientT place.T
        (periodizedScaledVelocity u place.x₀ place.T ε) =
      ENNReal.ofReal (ε ^ ((1 : ℝ) / 2) * D) := by
  exact packetDissipationIdentity hP hu place

example : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    MemMixedLebesgueR q p f ∧
      ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
        MemMixedLebesgueT q p
          (periodizedScaledForce f place.x₀ place.T ε) := by
  exact mixed_memLp hf hfc place

example : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      mixedLebesgueENormT q p
          (periodizedScaledForce f place.x₀ place.T ε) =
        ENNReal.ofReal (ε ^ alphaT p q) * mixedLebesgueENorm q p f := by
  exact packetMixedScaling hf hfc place

end FieldChecks

/-! ## Part 1b — `I03.PacketData` carries no hypothesis beyond `scalingStatement` -/

/-- The eight fields of the Section 4 bundle used by `packetEnergyIdentity` and
`packetDissipationIdentity` are literally eight clauses of `scalingStatement`
(`Section3/T15/Scaling.lean:466-489`). -/
example {u : VelocityField} {K : Set Space} {M D : ℝ}
    (hext : ContDiffOn ℝ ∞ (zeroPastField u) (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
    (hK : IsCompact K)
    (hu : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => u (t, x)) ⊆ K)
    (hsq : ∀ t ∈ Ico (0 : ℝ) 1,
      NavierStokesR3.ProblemStatement.SquareIntegrableAtTime u t)
    (hz : ∀ x : Space, u (0, x) = 0)
    (hM : IsLUB ((fun t : ℝ => Real.sqrt (l2Sq u t)) '' Ico (0 : ℝ) 1) M)
    (hdi : IntegrableOn (dissipation u) (Ioo (0 : ℝ) 1))
    (hD : D = Real.sqrt (∫ t in Ioo (0 : ℝ) 1, dissipation u t)) :
    NSFormalization.Section4.I03.PacketData u K M D :=
  { extension_smooth := hext
    carrier_compact := hK
    support := hu
    square_int := hsq
    zero_initial := hz
    energy_isLUB := hM
    dissipation_int := hdi
    dissipation_eq := hD }

/-! ## Part 2 — the explicit geometry, with a nonzero time-localized packet -/

/-- Centre of the fundamental cube. -/
def emCenter : Space := (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun _ => (1 / 2 : ℝ))

/-- Spatial bump, support `closedBall 0 (1/4)`. -/
def emSpaceBump : ContDiffBump (0 : Space) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- Time bump, support `closedBall (1/2) (1/4) = [1/4,3/4] ⊆ (0,∞)`. -/
def emTimeBump : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- A genuinely nonzero smooth spatial profile. -/
def emField : Space → Space := fun x => emSpaceBump x • coordinateVector 0

/-- The velocity packet: nonzero, smooth, vanishing at every nonpositive time. -/
def emVel : VelocityField := fun z => emTimeBump z.1 • emField z.2

/-- The force: the same time-localized bump field. -/
def emForce : VelocityField := fun z => emTimeBump z.1 • emField z.2

/-- The pressure packet. -/
def emPres : PressureField := fun z => emTimeBump z.1 * emSpaceBump z.2

def emCarrier : Set Space := Metric.closedBall (0 : Space) (1 / 4)

theorem emTimeBump_eq_zero {t : ℝ} (ht : t ≤ 0) : emTimeBump t = 0 := by
  refine emTimeBump.zero_of_le_dist ?_
  rw [Real.dist_eq, abs_of_nonpos (by linarith : t - 1 / 2 ≤ 0)]
  change (1 / 4 : ℝ) ≤ _
  linarith

theorem emField_tsupport : tsupport emField ⊆ emCarrier := by
  have hsub : Function.support emField ⊆ Function.support (⇑emSpaceBump) := by
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro hzero
    exact hx (by simp [emField, hzero])
  have h : tsupport emField ⊆ tsupport (⇑emSpaceBump) := closure_mono hsub
  change tsupport emField ⊆ Metric.closedBall (0 : Space) (1 / 4)
  rwa [emSpaceBump.tsupport_eq] at h

theorem emField_contDiff : ContDiff ℝ ∞ emField :=
  emSpaceBump.contDiff.smul contDiff_const

theorem emVel_contDiff : ContDiff ℝ ∞ emVel :=
  (emTimeBump.contDiff.comp contDiff_fst).smul (emField_contDiff.comp contDiff_snd)

theorem emVel_zeroPast : zeroPastField emVel = emVel := by
  funext z
  by_cases h : 0 < z.1
  · exact zeroPastField_of_pos emVel h z.2
  · rw [zeroPastField_of_nonpos emVel (not_lt.1 h)]
    show (0 : Space) = emTimeBump z.1 • emField z.2
    rw [emTimeBump_eq_zero (not_lt.1 h), zero_smul]

theorem emVel_extension_smooth :
    ContDiffOn ℝ ∞ (zeroPastField emVel) (Iio (1 : ℝ) ×ˢ (univ : Set Space)) := by
  rw [emVel_zeroPast]
  exact emVel_contDiff.contDiffOn

theorem emVel_support : ∀ t ∈ Ico (0 : ℝ) 1,
    tsupport (fun x : Space => emVel (t, x)) ⊆ emCarrier := by
  intro t _
  refine Subset.trans (closure_mono ?_) emField_tsupport
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro hzero
  exact hx (by simp [emVel, hzero])

/-- The time-localized bump field has compact spacetime support inside strictly
positive times, and its spatial projection stays in the carrier. -/
theorem emForce_tsupport :
    tsupport emForce ⊆ tsupport (⇑emTimeBump) ×ˢ tsupport emField := by
  have hsub : Function.support emForce ⊆
      Function.support (⇑emTimeBump) ×ˢ Function.support emField := by
    intro z hz
    simp only [Function.mem_support] at hz
    constructor
    · simp only [Function.mem_support]
      intro hzero
      exact hz (by simp [emForce, hzero])
    · simp only [Function.mem_support]
      intro hzero
      exact hz (by simp [emForce, hzero])
  refine Subset.trans (closure_mono hsub) ?_
  rw [closure_prod_eq]
  exact Subset.rfl

theorem emForce_contDiff : ContDiff ℝ ∞ emForce := emVel_contDiff

theorem emForce_compactSupport :
    NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport emForce := by
  have hts := emForce_tsupport
  have htime : tsupport (⇑emTimeBump) = Metric.closedBall (1 / 2 : ℝ) (1 / 4) :=
    emTimeBump.tsupport_eq
  constructor
  · refine IsCompact.of_isClosed_subset ?_ (isClosed_tsupport _) hts
    exact (htime ▸ (isCompact_closedBall (1 / 2 : ℝ) (1 / 4))).prod
      ((isCompact_closedBall (0 : Space) (1 / 4)).of_isClosed_subset
        (isClosed_tsupport _) emField_tsupport)
  · intro z hz
    obtain ⟨hz1, _⟩ := hts hz
    rw [htime, Metric.mem_closedBall, Real.dist_eq] at hz1
    refine ⟨?_, mem_univ _⟩
    have := abs_le.1 hz1
    simp only [mem_Ioi]
    linarith [this.1]

theorem em_chartBall_in_cube :
    closure (Metric.ball emCenter (3 / 8 : ℝ)) ⊆ interior fundamentalCube := by
  refine (Metric.closure_ball_subset_closedBall).trans ?_
  rw [interior_fundamentalCube]
  intro x hx i
  have hd : ‖x - emCenter‖ ≤ 3 / 8 := by
    rw [← dist_eq_norm]; exact hx
  have h1 : |x i - emCenter i| ≤ 3 / 8 := by
    have h := abs_spaceCoord_le_norm (x - emCenter) i
    have h2 : (x - emCenter) i = x i - emCenter i := rfl
    rw [h2] at h
    linarith
  have hc : emCenter i = 1 / 2 := rfl
  rw [hc, abs_le] at h1
  exact ⟨by linarith [h1.1], by linarith [h1.2]⟩

theorem em_eps_space : ∀ ε ∈ Ioc (0 : ℝ) (1 / 2), ∀ y ∈ emCarrier,
    emCenter + ε • y ∈ Metric.ball emCenter (3 / 8) := by
  intro ε hε y hy
  rw [Metric.mem_ball, dist_eq_norm]
  have hsub : emCenter + ε • y - emCenter = ε • y := by abel
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hε.1]
  have hyn : ‖y‖ ≤ 1 / 4 := by
    simpa only [emCarrier, Metric.mem_closedBall, dist_zero_right] using hy
  have h1 : ε * ‖y‖ ≤ (1 / 2 : ℝ) * (1 / 4) :=
    mul_le_mul hε.2 hyn (norm_nonneg _) (by norm_num)
  linarith

/-- The canonical placement datum on this geometry. -/
def emPlacement : PlacementData emVel emPres emForce emCarrier where
  T := 1
  time_pos := by norm_num
  chartCenter := emCenter
  chartRadius := 3 / 8
  chartRadius_pos := by norm_num
  chartBall_in_cube := em_chartBall_in_cube
  x₀ := emCenter
  x₀_mem := by simp
  Kstar := emCarrier
  Kstar_compact := isCompact_closedBall _ _
  carrier_subset := Subset.rfl
  force_projection_subset := by
    intro t x h
    exact emField_tsupport (emForce_tsupport h).2
  ε₀ := 1 / 2
  eps_pos := by norm_num
  eps_le_one := by norm_num
  eps_time := by
    intro ε hε
    have hsquare : ε ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith [hε.1, hε.2]
    nlinarith
  eps_space := em_eps_space

/-! ### The full packet datum on the same geometry -/

/-- The reference spatial `L²` energy of the profile. -/
def emA : ℝ := ∫ x : Space, ‖emField x‖ ^ 2

/-- The reference spatial dissipation of the profile. -/
def emB : ℝ := ∑ i : Fin 3, ∫ x : Space, ‖fderiv ℝ emField x (coordinateVector i)‖ ^ 2

theorem emA_nonneg : 0 ≤ emA := integral_nonneg (fun _ => sq_nonneg _)

theorem l2Sq_emVel (t : ℝ) : l2Sq emVel t = emTimeBump t ^ 2 * emA := by
  show (∫ x : Space, ‖emVel (t, x)‖ ^ 2) = emTimeBump t ^ 2 * emA
  rw [show emA = ∫ x : Space, ‖emField x‖ ^ 2 from rfl, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  show ‖emTimeBump t • emField x‖ ^ 2 = emTimeBump t ^ 2 * ‖emField x‖ ^ 2
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

theorem dissipation_emVel (t : ℝ) : dissipation emVel t = emTimeBump t ^ 2 * emB := by
  have hd : ∀ x : Space, fderiv ℝ (fun y : Space => emVel (t, y)) x
      = emTimeBump t • fderiv ℝ emField x := by
    intro x
    rw [show (fun y : Space => emVel (t, y))
        = fun y : Space => emTimeBump t • emField y from rfl]
    exact fderiv_const_smul (𝕜 := ℝ) (emField_contDiff.differentiable (by simp) x)
      (emTimeBump t : ℝ)
  show (∑ i : Fin 3, ∫ x : Space,
      ‖NavierStokes.PeriodicIntegration.spatialPartial i
        (fun y : Space => emVel (t, y)) x‖ ^ 2) = emTimeBump t ^ 2 * emB
  rw [show emB = ∑ i : Fin 3, ∫ x : Space,
      ‖fderiv ℝ emField x (coordinateVector i)‖ ^ 2 from rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  show ‖fderiv ℝ (fun y : Space => emVel (t, y)) x (coordinateVector i)‖ ^ 2 = _
  rw [hd x, smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

/-- `M = sup_{0≤t<1}‖U(t)‖₂`: the time bump attains its maximum `1` at the
interior time `t = 1/2`, so the supremum is `√emA` and it is a genuine `IsLUB`. -/
def emM : ℝ := Real.sqrt emA

/-- `D = (∫₀¹‖∇U(t)‖₂²)^{1/2}`, in the exact shape the packet clause demands. -/
def emD : ℝ := Real.sqrt (∫ t in Ioo (0 : ℝ) 1, dissipation emVel t)

theorem emVel_isLUB :
    IsLUB ((fun t : ℝ => Real.sqrt (l2Sq emVel t)) '' Ico (0 : ℝ) 1) emM := by
  have hval : ∀ t : ℝ, Real.sqrt (l2Sq emVel t) = emTimeBump t * Real.sqrt emA := by
    intro t
    rw [l2Sq_emVel, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq emTimeBump.nonneg]
  have hone : emTimeBump (1 / 2 : ℝ) = 1 :=
    emTimeBump.one_of_mem_closedBall (by norm_num [emTimeBump])
  refine IsGreatest.isLUB ⟨⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩, ?_⟩
  · show Real.sqrt (l2Sq emVel (1 / 2)) = emM
    rw [hval, hone, one_mul]
    rfl
  · rintro y ⟨t, _, rfl⟩
    show Real.sqrt (l2Sq emVel t) ≤ emM
    rw [hval]
    exact mul_le_of_le_one_left (Real.sqrt_nonneg _) emTimeBump.le_one

theorem emVel_square_int : ∀ t ∈ Ico (0 : ℝ) 1,
    NavierStokesR3.ProblemStatement.SquareIntegrableAtTime emVel t := by
  intro t _
  have hcont : Continuous (fun x : Space => ‖emVel (t, x)‖ ^ 2) := by
    exact ((emVel_contDiff.continuous.comp
      (continuous_const.prodMk continuous_id)).norm).pow 2
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) (1 / 4)) (fun x hx => ?_)
  have hz : emVel (t, x) = 0 := by
    have hnot : x ∉ tsupport emField := fun hmem => hx (emField_tsupport hmem)
    show emTimeBump t • emField x = 0
    rw [image_eq_zero_of_notMem_tsupport hnot, smul_zero]
  rw [hz, norm_zero]
  norm_num

theorem emVel_dissipation_int : IntegrableOn (dissipation emVel) (Ioo (0 : ℝ) 1) := by
  have heq : dissipation emVel = fun t : ℝ => emTimeBump t ^ 2 * emB :=
    funext dissipation_emVel
  rw [heq]
  exact ((emTimeBump.continuous.pow 2).mul continuous_const).integrableOn_Icc.mono_set
    Ioo_subset_Icc_self

/-- The eight packet clauses of `scalingStatement` on this concrete data. -/
theorem emPacketData : NSFormalization.Section4.I03.PacketData emVel emCarrier emM emD where
  extension_smooth := emVel_extension_smooth
  carrier_compact := isCompact_closedBall _ _
  support := emVel_support
  square_int := emVel_square_int
  zero_initial := by
    intro x
    show emTimeBump (0 : ℝ) • emField x = 0
    rw [emTimeBump_eq_zero le_rfl, zero_smul]
  energy_isLUB := emVel_isLUB
  dissipation_int := emVel_dissipation_int
  dissipation_eq := rfl

/-! ### The three fields whose hypotheses are the cheap packet clauses -/

/-- `energySlices_memLp`, `mixed_memLp` and `packetMixedScaling` on the explicit
geometry, at the admissible scale `ε = 1/2`. -/
theorem energy_mixed_closes :
    EnergySlicesMemLpT emPlacement.T
        (periodizedScaledVelocity emVel emPlacement.x₀ emPlacement.T (1 / 2)) ∧
    energyEssSupT emPlacement.T
        (periodizedScaledVelocity emVel emPlacement.x₀ emPlacement.T (1 / 2)) =
      ENNReal.ofReal ((1 / 2 : ℝ) ^ ((1 : ℝ) / 2) * emM) ∧
    energyGradientT emPlacement.T
        (periodizedScaledVelocity emVel emPlacement.x₀ emPlacement.T (1 / 2)) =
      ENNReal.ofReal ((1 / 2 : ℝ) ^ ((1 : ℝ) / 2) * emD) ∧
    MemMixedLebesgueR 1 2 emForce ∧
    MemMixedLebesgueT 1 2
      (periodizedScaledForce emForce emPlacement.x₀ emPlacement.T (1 / 2)) ∧
    mixedLebesgueENormT 1 2
        (periodizedScaledForce emForce emPlacement.x₀ emPlacement.T (1 / 2)) =
      ENNReal.ofReal ((1 / 2 : ℝ) ^ alphaT 2 1) * mixedLebesgueENorm 1 2 emForce := by
  have hε : (1 / 2 : ℝ) ∈ Ioc (0 : ℝ) emPlacement.ε₀ := by
    change (1 / 2 : ℝ) ∈ Ioc (0 : ℝ) (1 / 2)
    norm_num
  have hmix := mixed_memLp emForce_contDiff emForce_compactSupport emPlacement 2 1 le_rfl
  exact ⟨energySlices_memLp emVel_extension_smooth (isCompact_closedBall _ _)
      emVel_support emPlacement (1 / 2) hε,
    packetEnergyIdentity emPacketData emVel_support emPlacement (1 / 2) hε,
    packetDissipationIdentity emPacketData emVel_support emPlacement (1 / 2) hε,
    hmix.1, hmix.2 (1 / 2) hε,
    packetMixedScaling emForce_contDiff emForce_compactSupport emPlacement 2 1 le_rfl
      (1 / 2) hε⟩

/-- Non-vacuity of the energy side: the packet constant `M` is strictly
positive, so `packetEnergyIdentity` above is not the identity `0 = 0`. -/
example : 0 < emM := by
  have hcont : Continuous (fun x : Space => ‖emField x‖ ^ 2) :=
    (emField_contDiff.continuous.norm).pow 2
  have hint : Integrable (fun x : Space => ‖emField x‖ ^ 2) volume := by
    refine hcont.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) (1 / 4)) (fun x hx => ?_)
    have hnot : x ∉ tsupport emField := fun hmem => hx (emField_tsupport hmem)
    rw [image_eq_zero_of_notMem_tsupport hnot, norm_zero]
    norm_num
  have hne : emField (0 : Space) ≠ 0 := by
    have hb : emSpaceBump (0 : Space) = 1 :=
      emSpaceBump.one_of_mem_closedBall (by norm_num [emSpaceBump])
    simp [emField, hb, coordinateVector]
  refine Real.sqrt_pos.2 ?_
  exact integral_pos_of_integrable_nonneg_nonzero (x := (0 : Space)) hcont hint
    (fun _ => sq_nonneg _) (pow_ne_zero 2 (norm_ne_zero_iff.2 hne))

/-- Non-vacuity of the concrete data: the force is genuinely nonzero at an
interior time, so the mixed identity above is not a zero-field artefact. -/
example : emForce (1 / 2, (0 : Space)) ≠ 0 := by
  have hb : emSpaceBump (0 : Space) = 1 :=
    emSpaceBump.one_of_mem_closedBall (by norm_num [emSpaceBump])
  have ht : emTimeBump (1 / 2 : ℝ) = 1 :=
    emTimeBump.one_of_mem_closedBall (by norm_num [emTimeBump])
  show emTimeBump (1 / 2 : ℝ) • emField (0 : Space) ≠ 0
  rw [ht, one_smul]
  simp [emField, hb, coordinateVector]

end NSFormalization.Section3.T15
