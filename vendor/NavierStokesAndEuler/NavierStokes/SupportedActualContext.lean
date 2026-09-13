import NavierStokes.SupportedParameterExtension
import NavierStokes.SignedRequestContinuation

/-!
# The actual continued context with exact radial support

Only the auxiliary continuation of the virtual stress is replaced.  The
base, graph operators, coefficients, Borel scales, and every positive-time
fiber are the original ones.  The supported parameter extension retains
the exact active annulus without a radial buffer.
-/

noncomputable section

namespace NavierStokes.SupportedActualContext

open Set Function Filter
open scoped Topology ContDiff

abbrev Slow := ActualCorrectionModels.Slow
abbrev Model := ActualCorrectionModels.Model
abbrev Point := LocalSignedRequest.Point
abbrev Parameter := TorusInverse.Plane

section Stress

variable {F : OutgoingProfile.Profile} {W₀ : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W₀) {ld : ModulatedProfileAssembly.LoopData W₀}
  (v : ModulatedProfileAssembly.Witness ld) (upper : ℝ) (B : ℕ)

noncomputable def stressModel (n : ℕ) (y : Model) : ℝ × ℝ :=
  (ChartScales.epsilon F.data.h n * y.1 ^ (-CoordinateAlgebra.A F.data.h - 1 / 2)) •
    SupportedParameterExtension.normalizedStress H v upper B
      (SlowBorelBase.scaleMap (ChartScales.Q n) (ActualCorrectionModels.modelCoordinates F.data.h y))

noncomputable def stress (n : ℕ) : Slow → ℝ × ℝ :=
  stressModel H v upper B n ∘ ActualCorrectionModels.stablePoint F.data.h

noncomputable def virtualStress (n : ℕ) (p : Slow) : ℝ × ℝ :=
  if 0 < p.1 then stress H v upper B n p else 0

theorem stressModel_smoothAt (n : ℕ) {y : Model} (hy : 0 < y.1) :
    ContDiffAt ℝ ∞ (stressModel H v upper B n) y := by
  have hc := (SlowBorelBase.scaleMap (ChartScales.Q n)).contDiff.contDiffAt.comp y
    (ActualCorrectionModels.modelCoordinates_smoothAt F.data.h hy)
  have hs := SupportedParameterExtension.normalizedStress_contDiffAt H v upper B
    (y := SlowBorelBase.scaleMap (ChartScales.Q n) (ActualCorrectionModels.modelCoordinates F.data.h y))
    (mul_pos (ChartScales.Q_pos n) hy)
  exact (contDiffAt_const.mul (contDiffAt_fst.rpow_const_of_ne hy.ne')).smul
    (ContDiffAt.comp (g := SupportedParameterExtension.normalizedStress H v upper B) y hs hc)

theorem stress_smoothAt (n : ℕ) {p : Slow} (hp : p ∈ ActualCorrectionModels.stableDomain F.data.h) :
    ContDiffAt ℝ ∞ (stress H v upper B n) p :=
  (stressModel_smoothAt H v upper B n (ActualCorrectionModels.stablePoint_pos hp)).comp p
    (ActualCorrectionModels.stablePoint_smoothAt F.data.h_pos F.data.h_lt_half hp)

theorem stress_zero_of_inner (n : ℕ) {p : Slow}
    (hp : (ActualCorrectionModels.modelCoordinates F.data.h
      (ActualCorrectionModels.stablePoint F.data.h p)).2.1 ≤ NominalConeAssembly.activeLeft W₀) :
    stress H v upper B n p = 0 := by
  change (_ : ℝ) • SupportedParameterExtension.normalizedStress H v upper B
    (SlowBorelBase.scaleMap (ChartScales.Q n) (ActualCorrectionModels.modelCoordinates F.data.h
      (ActualCorrectionModels.stablePoint F.data.h p))) = 0
  rw [SupportedParameterExtension.normalizedStress_zero_left H v upper B
    (y := SlowBorelBase.scaleMap (ChartScales.Q n) (ActualCorrectionModels.modelCoordinates F.data.h
      (ActualCorrectionModels.stablePoint F.data.h p))) hp, smul_zero]

theorem stress_zero_outside (n : ℕ) {p : Slow}
    (hp : (ActualCorrectionModels.modelCoordinates F.data.h
      (ActualCorrectionModels.stablePoint F.data.h p)).2.1 ∉
        Icc (NominalConeAssembly.activeLeft W₀) (NominalConeAssembly.activeRight W₀)) :
    stress H v upper B n p = 0 := by
  change (_ : ℝ) • SupportedParameterExtension.normalizedStress H v upper B
    (SlowBorelBase.scaleMap (ChartScales.Q n) (ActualCorrectionModels.modelCoordinates F.data.h
      (ActualCorrectionModels.stablePoint F.data.h p))) = 0
  rw [SupportedParameterExtension.normalizedStress_supported H v upper B
    (y := SlowBorelBase.scaleMap (ChartScales.Q n) (ActualCorrectionModels.modelCoordinates F.data.h
      (ActualCorrectionModels.stablePoint F.data.h p))) hp, smul_zero]

theorem virtualStress_smoothAt (n : ℕ) {p : Slow}
    (hp : p ∈ ActualCorrectionModels.stableDomain F.data.h) :
    ContDiffAt ℝ ∞ (virtualStress H v upper B n) p := by
  rcases lt_trichotomy p.1 0 with hneg | hzero | hpos
  · have he : virtualStress H v upper B n =ᶠ[𝓝 p] (fun _ => 0) := by
      filter_upwards [continuousAt_fst (gt_mem_nhds hneg)] with y hy
      change y.1 < 0 at hy
      simp only [virtualStress, ite_eq_right (not_lt.mpr hy.le)]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hc := (ActualCorrectionModels.modelCoordinates_smoothAt F.data.h
      (ActualCorrectionModels.stablePoint_pos hp)).comp p
        (ActualCorrectionModels.stablePoint_smoothAt F.data.h_pos F.data.h_lt_half hp)
    have hx : (ActualCorrectionModels.modelCoordinates F.data.h
        (ActualCorrectionModels.stablePoint F.data.h p)).2.1 < NominalConeAssembly.activeLeft W₀ := by
      simpa only [ActualCorrectionModels.modelCoordinates, ActualCorrectionModels.stablePoint, hzero,
        zero_pow (by decide : 2 ≠ 0), zero_div] using NominalConeAssembly.activeLeft_pos W₀
    have he : virtualStress H v upper B n =ᶠ[𝓝 p] (fun _ => 0) := by
      filter_upwards [hc.snd.fst.continuousAt (gt_mem_nhds hx)] with y hy
      change (ActualCorrectionModels.modelCoordinates F.data.h
        (ActualCorrectionModels.stablePoint F.data.h y)).2.1 < NominalConeAssembly.activeLeft W₀ at hy
      simp only [virtualStress, stress_zero_of_inner H v upper B n hy.le, ite_self]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have he : virtualStress H v upper B n =ᶠ[𝓝 p] stress H v upper B n := by
      filter_upwards [continuousAt_fst (lt_mem_nhds hpos)] with y hy
      exact ite_eq_left hy
    exact (stress_smoothAt H v upper B n hp).congr_of_eventuallyEq he

theorem stress_eq (n : ℕ) {p : Slow} (ht : 0 < p.2.2) :
    stress H v upper B n p = ActualCorrectionModels.stress H v upper B n p := by
  have hq : 0 < (ActualCorrectionModels.stablePoint F.data.h p).1 := ActualCorrectionModels.stablePoint_pos
    (ActualCorrectionModels.positiveTime_mem_stable F.data.h_pos F.data.h_lt_half (p := p) ht)
  have he : ActualCorrectionModels.modelCoordinates F.data.h (ActualCorrectionModels.stablePoint F.data.h p) =
      BaseChartJets.normalizedCoordinates F.data.h p := by
    rw [ActualCorrectionModels.stablePoint_eq F.data.h_pos F.data.h_lt_half ht,
      ActualCorrectionModels.modelCoordinates_original]
  have heta : (SlowBorelBase.scaleMap (ChartScales.Q n) (ActualCorrectionModels.modelCoordinates F.data.h
      (ActualCorrectionModels.stablePoint F.data.h p))).2.2 ∈ Icc (-1 : ℝ) 1 := by
    rw [he]
    have h := abs_lt.mp (BaseChartJets.normalizedCoordinates_eta F.data.h_pos F.data.h_lt_half (p := p) ht)
    exact ⟨h.1.le, h.2.le⟩
  change (_ : ℝ) • SupportedParameterExtension.normalizedStress H v upper B _ =
    (_ : ℝ) • FinalSlowBase.normalizedStress H v upper B _
  rw [SupportedParameterExtension.normalizedStress_eq H v upper B
    (mul_pos (ChartScales.Q_pos n) hq) heta]

theorem virtualStress_eq (n : ℕ) {p : Slow} (ht : 0 < p.2.2) :
    virtualStress H v upper B n p = ActualCorrectionModels.virtualStress H v upper B n p := by
  simp only [virtualStress, ActualCorrectionModels.virtualStress, stress_eq H v upper B n ht]

/-- Equality of the full ambient jets extends to the terminal face by
smoothness and density of positive time, including at zero radial coordinate. -/
theorem virtualStress_jets (n m : ℕ) {p : Slow}
    (hp : p ∈ ActualCorrectionModels.stableDomain F.data.h) (ht : 0 ≤ p.2.2) :
    iteratedFDeriv ℝ m (virtualStress H v upper B n) p =
      iteratedFDeriv ℝ m (ActualCorrectionModels.virtualStress H v upper B n) p := by
  apply FinalSlowBase.iteratedFDeriv_eq_on_dense
    (s := ActualCorrectionModels.stableDomain F.data.h ∩ {x : Slow | 0 < x.2.2})
    (t := ActualCorrectionModels.stableDomain F.data.h ∩ {x : Slow | 0 ≤ x.2.2})
    ((ActualCorrectionModels.stableDomain_open F.data.h).inter
      (isOpen_lt continuous_const continuous_snd.snd))
    (fun x hx => ⟨hx.1, (show 0 < x.2.2 from hx.2).le⟩) ?_ ?_ ?_ ?_ m ⟨hp, ht⟩
  · intro x hx
    apply (ActualCorrectionModels.stableDomain_open F.data.h).inter_closure
    refine ⟨hx.1, ?_⟩
    rw [show {x : Slow | 0 < x.2.2} = ((univ : Set ℝ) ×ˢ (univ ×ˢ Ioi (0 : ℝ))) by ext; simp]
    simp only [closure_prod_eq, closure_univ, closure_Ioi, mem_prod, mem_univ, true_and, mem_Ici]
    exact hx.2
  · exact fun x hx => virtualStress_smoothAt H v upper B n hx.1
  · exact fun x hx => ActualCorrectionModels.virtualStress_smoothAt H v upper B n hx.1
  · exact fun x hx => virtualStress_eq H v upper B n hx.2

/-- Radial bounds are exactly the active radii, with no future-parameter
restriction and no enlargement of the annulus. -/
theorem virtualStress_support (n : ℕ) {p : Slow}
    (hp : p ∈ ActualCorrectionModels.stableDomain F.data.h)
    (hn : virtualStress H v upper B n p ≠ 0) :
    p.1 / OffplaneCorrectionExtensions.stableLength (2 * F.data.h) (p.2.2, p.2.1) ∈
      Icc (PrimaryTargetBounds.leftRadius W₀) (PrimaryTargetBounds.rightRadius W₀) := by
  have hR : 0 < p.1 := by
    by_contra h
    exact hn (by simp [virtualStress, h])
  have hX : (ActualCorrectionModels.modelCoordinates F.data.h
      (ActualCorrectionModels.stablePoint F.data.h p)).2.1 ∈
        Icc (NominalConeAssembly.activeLeft W₀) (NominalConeAssembly.activeRight W₀) := by
    by_contra h
    exact hn (by simp only [virtualStress, ite_eq_left hR, stress_zero_outside H v upper B n h])
  let q := OffplaneCorrectionExtensions.stableQ (2 * F.data.h) (p.2.2, p.2.1)
  have hq : 0 < q := ActualCorrectionModels.stablePoint_pos hp
  have hell : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hs : (p.1 / Real.sqrt q) ^ 2 = 2 * (p.1 ^ 2 / 2 / q) := by
    rw [div_pow, Real.sq_sqrt hq.le]
    ring
  have ha : (PrimaryTargetBounds.leftRadius W₀) ^ 2 = 2 * NominalConeAssembly.activeLeft W₀ :=
    Real.sq_sqrt (mul_nonneg (by norm_num) (NominalConeAssembly.activeLeft_pos W₀).le)
  have hb : (PrimaryTargetBounds.rightRadius W₀) ^ 2 = 2 * NominalConeAssembly.activeRight W₀ :=
    Real.sq_sqrt (mul_nonneg (by norm_num) (LeadingStressWeights.activeRight_pos W₀).le)
  change p.1 ^ 2 / 2 / q ∈ Icc _ _ at hX
  change p.1 / Real.sqrt q ∈ Icc _ _
  have hrat := div_pos hR hell
  constructor
  · nlinarith [PrimaryTargetBounds.leftRadius_pos W₀, hX.1]
  · nlinarith [PrimaryTargetBounds.rightRadius_pos W₀, hX.2]

end Stress

section Context

variable {F : OutgoingProfile.Profile} {W₀ : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W₀) {ld : ModulatedProfileAssembly.LoopData W₀}
  (v : ModulatedProfileAssembly.Witness ld) (upper : ℝ) (B : ℕ) (index : ℕ → ℕ)

noncomputable def context : CorrectionState.Context Point :=
  {ActualCorrectionModels.context H v upper B index with
    virtualTheta := fun n x => (virtualStress H v upper B n (BaseContextAssembly.slowCoordinates x)).1
    virtualAxial := fun n x => (virtualStress H v upper B n (BaseContextAssembly.slowCoordinates x)).2}

@[simp] theorem context_base : (context H v upper B index).base =
    (ActualCorrectionModels.context H v upper B index).base := rfl

@[simp] theorem context_operators : (context H v upper B index).operators =
    (ActualCorrectionModels.context H v upper B index).operators := rfl

theorem context_base_agrees (U : Set Parameter) :
    SignedRequestContinuation.TripleAgrees U (context H v upper B index).base
      (CommonBaseContext.context H v upper B index).base :=
  ⟨fun n => (ActualCorrectionModels.context_base_fiberAgreement H v upper B index n U).1,
   fun n => (ActualCorrectionModels.context_base_fiberAgreement H v upper B index n U).2.1,
   fun n => (ActualCorrectionModels.context_base_fiberAgreement H v upper B index n U).2.2⟩

theorem context_stress_agrees (U : Set Parameter) :
    SignedRequestContinuation.Agrees U (context H v upper B index).virtualTheta
      (CommonBaseContext.context H v upper B index).virtualTheta ∧
    SignedRequestContinuation.Agrees U (context H v upper B index).virtualAxial
      (CommonBaseContext.context H v upper B index).virtualAxial := by
  constructor <;> intro n x hx
  · change (virtualStress H v upper B n (BaseContextAssembly.slowCoordinates x)).1 = _
    rw [virtualStress_eq H v upper B n (p := BaseContextAssembly.slowCoordinates x) hx.2]
    exact (ActualCorrectionModels.context_stress_eq H v upper B index n hx.2).1
  · change (virtualStress H v upper B n (BaseContextAssembly.slowCoordinates x)).2 = _
    rw [virtualStress_eq H v upper B n (p := BaseContextAssembly.slowCoordinates x) hx.2]
    exact (ActualCorrectionModels.context_stress_eq H v upper B index n hx.2).2

variable {P : SignedStressPrimitive.Patch}
  (W : OffplaneCorrectionExtensions.Window (2 * F.data.h) P.a P.b)

theorem context_stress_smooth (n : ℕ) :
    ContDiffOn ℝ ∞ ((context H v upper B index).virtualTheta n) (PhysicalMeanDomain.slowDomain W.carrier) ∧
    ContDiffOn ℝ ∞ ((context H v upper B index).virtualAxial n) (PhysicalMeanDomain.slowDomain W.carrier) := by
  constructor <;> intro x hx
  · exact (((virtualStress_smoothAt H v upper B n (p := BaseContextAssembly.slowCoordinates x)
      (W.stable hx)).comp x BaseContextAssembly.slowCoordinates.contDiff.contDiffAt).fst).contDiffWithinAt
  · exact (((virtualStress_smoothAt H v upper B n (p := BaseContextAssembly.slowCoordinates x)
      (W.stable hx)).comp x BaseContextAssembly.slowCoordinates.contDiff.contDiffAt).snd).contDiffWithinAt

variable (hleft : P.a ≤ PrimaryTargetBounds.leftRadius W₀)
  (hright : PrimaryTargetBounds.rightRadius W₀ ≤ P.b)

include hleft hright in
/-- This is the support conclusion needed by the residual calculus,
proved for the supported context rather than assumed for the raw future. -/
theorem context_support :
    SignedRequestContinuation.Supported P.a P.b (OffplaneCorrectionExtensions.stableLength (2 * F.data.h))
      W.carrier (context H v upper B index).virtualTheta ∧
    SignedRequestContinuation.Supported P.a P.b (OffplaneCorrectionExtensions.stableLength (2 * F.data.h))
      W.carrier (context H v upper B index).virtualAxial := by
  have hs (n : ℕ) (x : Point) (hx : x.2.1 ∈ W.carrier)
      (hn : virtualStress H v upper B n (BaseContextAssembly.slowCoordinates x) ≠ 0) :
      x.1 ∈ Icc (OffplaneCorrectionExtensions.stableLength (2 * F.data.h) x.2.1 * P.a)
        (OffplaneCorrectionExtensions.stableLength (2 * F.data.h) x.2.1 * P.b) := by
    have hh := virtualStress_support H v upper B n
      (p := BaseContextAssembly.slowCoordinates x) (W.stable hx) hn
    have hp := W.length_pos hx
    change x.1 / OffplaneCorrectionExtensions.stableLength (2 * F.data.h) x.2.1 ∈
      Icc (PrimaryTargetBounds.leftRadius W₀) (PrimaryTargetBounds.rightRadius W₀) at hh
    have hlo : OffplaneCorrectionExtensions.stableLength (2 * F.data.h) x.2.1 *
        PrimaryTargetBounds.leftRadius W₀ ≤ x.1 := by
      simpa only [mul_comm] using (le_div_iff₀ hp).mp hh.1
    have hhi : x.1 ≤ OffplaneCorrectionExtensions.stableLength (2 * F.data.h) x.2.1 *
        PrimaryTargetBounds.rightRadius W₀ := by
      simpa only [mul_comm] using (div_le_iff₀ hp).mp hh.2
    constructor
    · exact (mul_le_mul_of_nonneg_left hleft hp.le).trans hlo
    · exact hhi.trans (mul_le_mul_of_nonneg_left hright hp.le)
  constructor <;> intro n x hx hn
  · exact hs n x hx (fun hz => hn (congrArg Prod.fst hz))
  · exact hs n x hx (fun hz => hn (congrArg Prod.snd hz))

end Context

/-! ## The signed request with its context support obligation discharged -/

section Request

variable {F : OutgoingProfile.Profile} {W₀ : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W₀) {ld : ModulatedProfileAssembly.LoopData W₀}
  (v : ModulatedProfileAssembly.Witness ld) (upper : ℝ) (B : ℕ) (index : ℕ → ℕ)
  {P : SignedStressPrimitive.Patch} (W : OffplaneCorrectionExtensions.Window (2 * F.data.h) P.a P.b)
  (hleft : P.a ≤ PrimaryTargetBounds.leftRadius W₀)
  (hright : PrimaryTargetBounds.rightRadius W₀ ≤ P.b)
  {u : CorrectionState.State Point} (d : SignedRequestContinuation.Primitives P W u)

/-- The radial source is unchanged by the replacement of virtual stress. -/
noncomputable def radialSource (n : ℕ) :
    OffplaneCorrectionExtensions.SupportedContinuation W (u.gr (CommonBaseContext.context H v upper B index) n) :=
  SignedRequestContinuation.radialSource H v upper B index W d n

theorem radialSource_value (n : ℕ) : (radialSource H v upper B index W d n).value =
    d.state.gr (context H v upper B index) n := rfl

noncomputable def thetaSource (n : ℕ) :
    OffplaneCorrectionExtensions.SupportedContinuation W (u.thetaResidual (CommonBaseContext.context H v upper B index) n) where
  value := d.state.thetaResidual (context H v upper B index) n
  smooth := (SignedRequestContinuation.thetaResidual_localShell W.lower_pos W.isOpen
    (SignedRequestContinuation.actual_operators_local H v upper B index W) (SignedRequestContinuation.actual_base_smooth H v upper B index W)
    d.mean_localShell d.state.covariance d.covariance_localShell
    ⟨fun k => (context_stress_smooth H v upper B index W k).1,
      fun k => W.fixed_support ((context_support H v upper B index W hleft hright).1 k)⟩).smooth n
  supported := SignedRequestContinuation.thetaResidual_supported W.isOpen
    (W.length_smooth (by linarith [F.data.h_pos]) (by linarith [F.data.h_lt_half])).continuousOn
    (context H v upper B index).operators (context H v upper B index).base
    d.mean_supported d.state.covariance d.covariance_supported
    (context_support H v upper B index W hleft hright).1 n
  agrees := SignedRequestContinuation.thetaResidual_agrees W.isOpen (context H v upper B index).operators
    (SignedRequestContinuation.actual_base_agrees H v upper B index W) d.mean_agrees d.covariance_agrees
    (context_stress_agrees H v upper B index W.carrier).1 n

noncomputable def axialSource (n : ℕ) :
    OffplaneCorrectionExtensions.SupportedContinuation W (u.axialResidual (CommonBaseContext.context H v upper B index) n) where
  value := d.state.axialResidual (context H v upper B index) n
  smooth := (SignedRequestContinuation.axialResidual_localShell W.lower_pos W.isOpen
    (SignedRequestContinuation.actual_operators_local H v upper B index W) (SignedRequestContinuation.actual_base_smooth H v upper B index W)
    d.mean_localShell d.state.covariance d.covariance_localShell d.pressure_localShell
    ⟨fun k => (context_stress_smooth H v upper B index W k).2,
      fun k => W.fixed_support ((context_support H v upper B index W hleft hright).2 k)⟩).smooth n
  supported := SignedRequestContinuation.axialResidual_supported W.isOpen
    (W.length_smooth (by linarith [F.data.h_pos]) (by linarith [F.data.h_lt_half])).continuousOn
    (context H v upper B index).operators (context H v upper B index).base
    d.mean_supported d.state.covariance d.covariance_supported d.pressure_supported
    (context_support H v upper B index W hleft hright).2 n
  agrees := SignedRequestContinuation.axialResidual_agrees W.isOpen (context H v upper B index).operators
    (SignedRequestContinuation.actual_base_agrees H v upper B index W) d.mean_agrees d.covariance_agrees d.pressure_agrees
    (context_stress_agrees H v upper B index W.carrier).2 n

/-- This is the actual pair of moving radial integrals at stable positive
scale, with the original normalization. -/
noncomputable def fullRequest (s : WeightedClasses.StripData Point) :
    ℕ → Point × ℝ → SignedWaveUpdate.Vec2 :=
  fun n x => (s.epsilon n)⁻¹ •
    ![SignedStressPrimitive.physicalBarSigma P 2 (OffplaneCorrectionExtensions.stableQ (2 * F.data.h))
        (d.state.thetaResidual (context H v upper B index) n) (x.1.1, x.1.2.1),
      SignedStressPrimitive.physicalBarSigma P 1 (OffplaneCorrectionExtensions.stableQ (2 * F.data.h))
        (d.state.axialResidual (context H v upper B index) n) (x.1.1, x.1.2.1)]

include hleft hright in
theorem fullRequest_smooth (s : WeightedClasses.StripData Point) (n : ℕ) :
    ContDiffOn ℝ ∞ (fullRequest H v upper B index W d s n)
      (PhysicalMeanDomain.slowDomain W.carrier ×ˢ univ) := by
  let θ := SignedRequestContinuation.signedPrimitive (by linarith [F.data.h_pos]) (by linarith [F.data.h_lt_half])
    (thetaSource H v upper B index W hleft hright d n) 2
  let z := SignedRequestContinuation.signedPrimitive (by linarith [F.data.h_pos]) (by linarith [F.data.h_lt_half])
    (axialSource H v upper B index W hleft hright d n) 1
  have hθ : ContDiffOn ℝ ∞ (fun x : Point × ℝ => θ.value x.1) (PhysicalMeanDomain.slowDomain W.carrier ×ˢ univ) :=
    θ.smooth.comp contDiffOn_fst (fun _ hx => hx.1)
  have hz : ContDiffOn ℝ ∞ (fun x : Point × ℝ => z.value x.1) (PhysicalMeanDomain.slowDomain W.carrier ×ˢ univ) :=
    z.smooth.comp contDiffOn_fst (fun _ hx => hx.1)
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact contDiffOn_const.mul hθ
  · exact contDiffOn_const.mul hz

include hleft hright in
theorem fullRequest_supported (s : WeightedClasses.StripData Point) (n : ℕ) (i : Fin 2) (θ : ℝ) :
    VariableGaugeMean.SupportedGauge P.a P.b (OffplaneCorrectionExtensions.stableLength (2 * F.data.h)) W.carrier
      (fun x => fullRequest H v upper B index W d s n (x, θ) i) := by
  let th := SignedRequestContinuation.signedPrimitive (by linarith [F.data.h_pos]) (by linarith [F.data.h_lt_half])
    (thetaSource H v upper B index W hleft hright d n) 2
  let z := SignedRequestContinuation.signedPrimitive (by linarith [F.data.h_pos]) (by linarith [F.data.h_lt_half])
    (axialSource H v upper B index W hleft hright d n) 1
  intro x hx hn
  fin_cases i
  · exact th.supported x hx (right_ne_zero_of_mul hn)
  · exact z.supported x hx (right_ne_zero_of_mul hn)

include hleft hright in
theorem fullRequest_agrees (s : WeightedClasses.StripData Point) (n : ℕ) (θ : ℝ) :
    OffplaneCorrectionExtensions.FiberAgreement W.carrier
      (fun x => fullRequest H v upper B index W d s n (x, θ))
      (fun x => LocalSignedRequest.fullRequest s P (2 * F.data.h)
        (CommonBaseContext.context H v upper B index) u n (x, θ)) := by
  let th := SignedRequestContinuation.signedPrimitive (by linarith [F.data.h_pos]) (by linarith [F.data.h_lt_half])
    (thetaSource H v upper B index W hleft hright d n) 2
  let z := SignedRequestContinuation.signedPrimitive (by linarith [F.data.h_pos]) (by linarith [F.data.h_lt_half])
    (axialSource H v upper B index W hleft hright d n) 1
  intro x hx
  funext i
  fin_cases i
  · exact congrArg ((s.epsilon n)⁻¹ * ·) (th.agrees hx)
  · exact congrArg ((s.epsilon n)⁻¹ * ·) (z.agrees hx)

noncomputable def fullRequestComponent (s : WeightedClasses.StripData Point) (n : ℕ) (i : Fin 2) (θ : ℝ) :
    OffplaneCorrectionExtensions.SupportedContinuation W (fun x => LocalSignedRequest.fullRequest s P (2 * F.data.h)
      (CommonBaseContext.context H v upper B index) u n (x, θ) i) where
  value x := fullRequest H v upper B index W d s n (x, θ) i
  smooth := (contDiffOn_pi.mp ((fullRequest_smooth H v upper B index W hleft hright d s n).comp
    (contDiffOn_id.prodMk contDiffOn_const) (fun _ hx => ⟨hx, mem_univ _⟩))) i
  supported := fullRequest_supported H v upper B index W hleft hright d s n i θ
  agrees := fun _ hx => congrFun (fullRequest_agrees H v upper B index W hleft hright d s n θ hx) i

end Request

end NavierStokes.SupportedActualContext
