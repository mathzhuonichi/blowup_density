import NavierStokes.SupportedActualContext
import NavierStokes.MeanStateRegularity
import NavierStokes.RankStateBounds

/-!
# Supported continuation through the literal mean stages

All continuations retain whole radial and torus fibers.  Temporal inverses,
stream derivatives, measured debts, and the rank kernels are constructed
before the outgoing primitive continuation is assembled.
-/

noncomputable section

open Set Filter Function
open scoped Topology ContDiff BigOperators

namespace NavierStokes.MeanStageContinuation

abbrev Slow := TorusInverse.Plane
abbrev Point := PressureStream.Lift Slow
abbrev Scalar := MeanIncrementBounds.Field Point

namespace Continuation

variable {coord a b : ℝ} {W : OffplaneCorrectionExtensions.Window coord a b}
  {f g : Point → ℝ}

noncomputable def retarget (e : OffplaneCorrectionExtensions.SupportedContinuation W f)
    (h : ∀ x, f x = g x) : OffplaneCorrectionExtensions.SupportedContinuation W g where
  value := e.value
  smooth := e.smooth
  supported := e.supported
  agrees := fun x hx => (e.agrees hx).trans (h x)

noncomputable def zero : OffplaneCorrectionExtensions.SupportedContinuation W (fun _ => 0) where
  value := fun _ => 0
  smooth := contDiffOn_const
  supported := fun _ _ hn => (hn rfl).elim
  agrees := fun _ _ => rfl

noncomputable def add (e : OffplaneCorrectionExtensions.SupportedContinuation W f)
    (d : OffplaneCorrectionExtensions.SupportedContinuation W g) :
    OffplaneCorrectionExtensions.SupportedContinuation W (fun x => f x + g x) where
  value := fun x => e.value x + d.value x
  smooth := e.smooth.add d.smooth
  supported := by
    intro x hx hn
    by_contra hr
    have he : e.value x = 0 := by by_contra h; exact hr (e.supported x hx h)
    have hd : d.value x = 0 := by by_contra h; exact hr (d.supported x hx h)
    exact hn (by simp only [he, hd, add_zero])
  agrees := fun x hx => congrArg₂ (· + ·) (e.agrees hx) (d.agrees hx)

noncomputable def neg (e : OffplaneCorrectionExtensions.SupportedContinuation W f) :
    OffplaneCorrectionExtensions.SupportedContinuation W (fun x => -f x) where
  value := fun x => -e.value x
  smooth := e.smooth.neg
  supported := fun x hx hn => e.supported x hx (neg_ne_zero.mp hn)
  agrees := fun _ hx => congrArg Neg.neg (e.agrees hx)

noncomputable def directional (hc : 0 < coord) (hc1 : coord < 1)
    (e : OffplaneCorrectionExtensions.SupportedContinuation W f) (v : Point) :
    OffplaneCorrectionExtensions.SupportedContinuation W (fun x => fderiv ℝ f x v) where
  value := fun x => fderiv ℝ e.value x v
  smooth := ((contDiffOn_infty_iff_fderiv_of_isOpen
    (PhysicalMeanDomain.slowDomain_open W.isOpen)).mp e.smooth).2.clm_apply contDiffOn_const
  supported := VariableGaugeMean.fderiv_apply_supportedGauge W.isOpen
    (W.length_smooth hc hc1).continuousOn e.supported (fun _ => v)
  agrees := fun _ hx => congrArg (fun L : Point →L[ℝ] ℝ => L v)
    (e.agrees.eventuallyEq W.isOpen hx.1 hx.2).fderiv_eq

/-- A coefficient need only be smooth at positive radii.  The fixed lower
support bound gives a genuine zero germ through the axis. -/
noncomputable def coefficientMul
    (e : OffplaneCorrectionExtensions.SupportedContinuation W f) (c : Point → ℝ)
    (hc : ContDiffOn ℝ ∞ c (LocalRankDefect.positiveDomain W.carrier)) :
    OffplaneCorrectionExtensions.SupportedContinuation W (fun x => c x * f x) where
  value := fun x => c x * e.value x
  smooth := by
    have he : LocalRankDefect.LocalShell W.lower W.upper W.carrier (fun _ => e.value) :=
      ⟨fun _ => e.smooth, fun _ => W.fixed_support e.supported⟩
    exact (he.coefficient_mul W.lower_pos W.isOpen (fun _ => hc)).smooth 0
  supported := fun x hx hn => e.supported x hx (right_ne_zero_of_mul hn)
  agrees := fun x hx => congrArg (c x * ·) (e.agrees hx)

noncomputable def radialPower (e : OffplaneCorrectionExtensions.SupportedContinuation W f)
    (k : ℕ) : OffplaneCorrectionExtensions.SupportedContinuation W (fun x => x.1 ^ k * f x) :=
  coefficientMul e (fun x => x.1 ^ k) (contDiffOn_fst.pow k)

noncomputable def divideRadius (e : OffplaneCorrectionExtensions.SupportedContinuation W f) :
    OffplaneCorrectionExtensions.SupportedContinuation W (PressureStream.divideRadius f) where
  value := PressureStream.divideRadius e.value
  smooth := VariableGaugeMean.divideRadius_contDiffOn W.lower_pos W.isOpen e.smooth
    (W.fixed_support e.supported)
  supported := VariableGaugeMean.divideRadius_supportedGauge e.supported
  agrees := fun x hx => congrArg (· / x.1) (e.agrees hx)

noncomputable def streamBeta (hc : 0 < coord) (hc1 : coord < 1)
    (e : OffplaneCorrectionExtensions.SupportedContinuation W f) (w : Slow × Slow) :
    OffplaneCorrectionExtensions.SupportedContinuation W (PressureStream.streamBeta w f) :=
  neg (directional hc hc1 e (0, w))

theorem graphDr_split (d M : ℝ) (v : Slow) (f : Point → ℝ) (x : Point) :
    PressureStream.graphDr (PressureStream.physicalSpeed d M) ((0 : Slow), v) f x =
      fderiv ℝ f x (1, 0) + PressureStream.physicalSpeed d M x.1 *
        fderiv ℝ f x (0, (0, v)) := by
  change fderiv ℝ f x (1, _ • ((0 : Slow), v)) = _
  rw [show (((1 : ℝ), PressureStream.physicalSpeed d M x.1 • ((0 : Slow), v)) : Point) =
    (1, (0, (0 : Slow))) + PressureStream.physicalSpeed d M x.1 • (0, (0, v)) by simp]
  simp only [map_add, map_smul, smul_eq_mul]
  rfl

noncomputable def streamGamma (hc : 0 < coord) (hc1 : coord < 1)
    (e : OffplaneCorrectionExtensions.SupportedContinuation W f) (d M : ℝ) (v : Slow) :
    OffplaneCorrectionExtensions.SupportedContinuation W
      (PressureStream.streamGamma (PressureStream.physicalSpeed d M) ((0 : Slow), v) f) :=
  retarget (add (add (directional hc hc1 e (1, 0))
    (coefficientMul (directional hc hc1 e (0, (0, v)))
      (fun x => PressureStream.physicalSpeed d M x.1)
      (fun x hx => ((PressureStream.physicalSpeed_smooth d M hx.1.ne').comp x
        contDiffAt_fst).contDiffWithinAt))) (divideRadius e))
    (fun x => by rw [PressureStream.streamGamma, graphDr_split])

theorem streamGamma_value (hc : 0 < coord) (hc1 : coord < 1)
    (e : OffplaneCorrectionExtensions.SupportedContinuation W f) (d M : ℝ) (v : Slow) :
    (streamGamma hc hc1 e d M v).value =
      PressureStream.streamGamma (PressureStream.physicalSpeed d M) ((0 : Slow), v) e.value := by
  funext x
  change _ + PressureStream.divideRadius e.value x = _
  rw [PressureStream.streamGamma, graphDr_split]
  rfl

end Continuation

/-! ## Torus periodicity is propagated from primitive fields -/

open MeanStateRegularity

namespace PeriodicAlgebra

variable {U : Set Slow} {f : Scalar} {o : MeanIncrementBounds.Operators Point}

theorem dr (hf : Periodic U f) (hU : IsOpen U)
    (hp : Periodic U (fun _ => o.radialProfile)) : Periodic U (o.dr f) :=
  (hf.directional hU o.eR).add ((hp.mul (hf.directional hU o.vR)).band_mul o.radialFrequency)

theorem dz (hf : Periodic U f) (hU : IsOpen U) (o : MeanIncrementBounds.Operators Point) :
    Periodic U (o.dz f) := (hf.directional hU o.eZ).band_mul o.epsilon

theorem time (hf : Periodic U f) (hU : IsOpen U) (o : MeanIncrementBounds.Operators Point) :
    Periodic U (o.time f) :=
  ((hf.directional hU o.eT).band_mul o.epsilon).neg.add
    ((hf.directional hU o.vT).band_mul o.fastCoefficient)

theorem radialDiv (hf : Periodic U f) (hU : IsOpen U)
    (hp : Periodic U (fun _ => o.radialProfile)) (hr : Periodic U o.invRadius) (c : ℝ) :
    Periodic U (o.radialDiv c f) := (dr hf hU hp).add ((hr.mul hf).smul c)

theorem viscosity (hf : Periodic U f) (hU : IsOpen U)
    (hp : Periodic U (fun _ => o.radialProfile)) (hr : Periodic U o.invRadius) (c : ℝ) :
    Periodic U (o.viscosity c f) :=
  ((((dr (dr hf hU hp) hU hp).add (hr.mul (dr hf hU hp))).add
    (dz (dz hf hU o) hU o)).sub ((hr.mul (hr.mul hf)).smul c)).band_mul o.epsilon

theorem thetaResidual {base m : MeanIncrementBounds.Triple Point}
    (hb : PeriodicTriple U base) (hm : PeriodicTriple U m)
    {A : Fin 3 → Fin 3 → Scalar} (hA : ∀ i j, Periodic U (A i j))
    {T : Scalar} (hT : Periodic U T) (hU : IsOpen U)
    (hp : Periodic U (fun _ => o.radialProfile)) (hr : Periodic U o.invRadius) :
    Periodic U (MeanIncrementBounds.thetaResidual o base m A T) :=
  (((time hm.angular hU o).add
    (radialDiv ((((hb.radial.mul hm.angular).add (hm.radial.mul hb.angular)).add
      (hm.radial.mul hm.angular)).add (hA 0 1)) hU hp hr 2)).add
    (dz ((((hb.axial.mul hm.angular).add (hb.angular.mul hm.axial)).add
      (hm.axial.mul hm.angular)).add (hA 2 1)) hU o)).sub
    (viscosity hm.angular hU hp hr 1) |>.sub (radialDiv hT hU hp hr 2)

theorem axialResidual {base m : MeanIncrementBounds.Triple Point}
    (hb : PeriodicTriple U base) (hm : PeriodicTriple U m)
    {A : Fin 3 → Fin 3 → Scalar} (hA : ∀ i j, Periodic U (A i j))
    {p T : Scalar} (hP : Periodic U p) (hT : Periodic U T) (hU : IsOpen U)
    (hp : Periodic U (fun _ => o.radialProfile)) (hr : Periodic U o.invRadius) :
    Periodic U (MeanIncrementBounds.axialResidual o base m A p T) :=
  (((time hm.axial hU o).add
    (radialDiv ((((hb.radial.mul hm.axial).add (hm.radial.mul hb.axial)).add
      (hm.radial.mul hm.axial)).add (hA 0 2)) hU hp hr 1)).add
    (dz (((((hb.axial.mul hm.axial).smul 2).add (hm.axial.mul hm.axial)).add
      (hA 2 2)).add hP) hU o)).sub
    (viscosity hm.axial hU hp hr 0) |>.sub (radialDiv hT hU hp hr 1)

theorem gr {base m : MeanIncrementBounds.Triple Point}
    (hb : PeriodicTriple U base) (hm : PeriodicTriple U m)
    {A : Fin 3 → Fin 3 → Scalar} (hA : ∀ i j, Periodic U (A i j)) (hU : IsOpen U)
    (hp : Periodic U (fun _ => o.radialProfile)) (hr : Periodic U o.invRadius) :
    Periodic U (MeanIncrementBounds.gr o base m A) :=
  (((((time hm.radial hU o).add
    (radialDiv ((((hb.radial.mul hm.radial).smul 2).add (hm.radial.mul hm.radial)).add
      (hA 0 0)) hU hp hr 1)).add
    (dz ((((hb.radial.mul hm.axial).add (hm.radial.mul hb.axial)).add
      (hm.radial.mul hm.axial)).add (hA 2 0)) hU o)).sub
    (hr.mul ((((hb.angular.mul hm.angular).smul 2).add (hm.angular.mul hm.angular)).add
      (hA 1 1)))).sub (viscosity hm.radial hU hp hr 1)).neg

end PeriodicAlgebra

/-- The required torus symmetry belongs to the incoming primitive
continuations.  Residual symmetry is a consequence below. -/
structure PeriodicPrimitives {coord : ℝ} {P : SignedStressPrimitive.Patch}
    {W : OffplaneCorrectionExtensions.Window coord P.a P.b} {u : CorrectionState.State Point}
    (d : SignedRequestContinuation.Primitives P W u) : Prop where
  mean : PeriodicTriple W.carrier d.state.mean
  pressure : Periodic W.carrier d.state.pressure
  oscillation : ∀ n i θ, PhysicalMeanDomain.PeriodicOn W.carrier
    (fun x => d.oscillation n (x, θ) i)

theorem PeriodicPrimitives.covariance {coord : ℝ} {P : SignedStressPrimitive.Patch}
    {W : OffplaneCorrectionExtensions.Window coord P.a P.b} {u : CorrectionState.State Point}
    {d : SignedRequestContinuation.Primitives P W u} (hp : PeriodicPrimitives d) (i j : Fin 3) :
    Periodic W.carrier (d.state.covariance i j) := by
  intro n R s hs Y k
  apply congrArg (· / (2 * Real.pi))
  apply intervalIntegral.integral_congr
  intro θ _
  exact congrArg₂ (· * ·) (hp.oscillation n i θ R s hs Y k)
    (hp.oscillation n j θ R s hs Y k)

theorem streamBeta_periodic {U : Set Slow} (hU : IsOpen U) {f : Point → ℝ}
    (hf : PhysicalMeanDomain.PeriodicOn U f) (w : Slow × Slow) :
    PhysicalMeanDomain.PeriodicOn U (PressureStream.streamBeta w f) :=
  (Periodic.neg (Periodic.directional (f := fun _ => f) (fun _ => hf) hU (0, w))) 0

theorem streamGamma_periodic {U : Set Slow} (hU : IsOpen U) {f : Point → ℝ}
    (hf : PhysicalMeanDomain.PeriodicOn U f) (d M : ℝ) (v : Slow) :
    PhysicalMeanDomain.PeriodicOn U
      (PressureStream.streamGamma (PressureStream.physicalSpeed d M) ((0 : Slow), v) f) := by
  have h0 := Periodic.directional (f := fun _ => f) (fun _ => hf) hU (1, (0 : Slow × Slow))
  have h1 := Periodic.directional (f := fun _ => f) (fun _ => hf) hU (0, ((0 : Slow), v))
  intro R s hs Y k
  simp only [PressureStream.streamGamma, Continuation.graphDr_split, PressureStream.divideRadius]
  have e0 := h0 0 R s hs Y k
  have e1 := h1 0 R s hs Y k
  have ef := hf R s hs Y k
  dsimp only at e0 e1 ef
  rw [e0, e1, ef]

structure IncrementContinuations {coord : ℝ} (P : SignedStressPrimitive.Patch)
    (W : OffplaneCorrectionExtensions.Window coord P.a P.b) (m : MeanIncrementBounds.Triple Point) where
  radial : ∀ n, OffplaneCorrectionExtensions.SupportedContinuation W (m.radial n)
  angular : ∀ n, OffplaneCorrectionExtensions.SupportedContinuation W (m.angular n)
  axial : ∀ n, OffplaneCorrectionExtensions.SupportedContinuation W (m.axial n)

noncomputable def IncrementContinuations.value {coord : ℝ} {P : SignedStressPrimitive.Patch}
    {W : OffplaneCorrectionExtensions.Window coord P.a P.b} {m : MeanIncrementBounds.Triple Point}
    (e : IncrementContinuations P W m) : MeanIncrementBounds.Triple Point :=
  ⟨fun n => (e.radial n).value, fun n => (e.angular n).value, fun n => (e.axial n).value⟩

/-- Literal addition of the continued mean increments; the oscillation and
the previous pressure are retained until pressure reconstruction. -/
noncomputable def addPrimitives {coord : ℝ} {P : SignedStressPrimitive.Patch}
    {W : OffplaneCorrectionExtensions.Window coord P.a P.b} {u : CorrectionState.State Point}
    (d : SignedRequestContinuation.Primitives P W u) {m : MeanIncrementBounds.Triple Point}
    (e : IncrementContinuations P W m) (err : CorrectionState.ExcludedErrors Point) :
    SignedRequestContinuation.Primitives P W (u.addIncrement m 0 0 0 err) where
  radial := fun n => Continuation.add (d.radial n) (e.radial n)
  angular := fun n => Continuation.add (d.angular n) (e.angular n)
  axial := fun n => Continuation.add (d.axial n) (e.axial n)
  pressure := fun n => Continuation.retarget (d.pressure n) (fun _ => by
    simp only [CorrectionState.State.addIncrement, add_zero])
  oscillation := d.oscillation
  oscillation_smooth := d.oscillation_smooth
  oscillation_supported := d.oscillation_supported
  oscillation_agrees := fun n i θ x hx => by
    simpa only [CorrectionState.State.addIncrement, Pi.add_apply, Pi.zero_apply, add_zero]
      using d.oscillation_agrees n i θ hx

theorem addPrimitives_periodic {coord : ℝ} {P : SignedStressPrimitive.Patch}
    {W : OffplaneCorrectionExtensions.Window coord P.a P.b} {u : CorrectionState.State Point}
    {d : SignedRequestContinuation.Primitives P W u} (hd : PeriodicPrimitives d)
    {m : MeanIncrementBounds.Triple Point} (e : IncrementContinuations P W m)
    (he : PeriodicTriple W.carrier e.value) (err : CorrectionState.ExcludedErrors Point) :
    PeriodicPrimitives (addPrimitives d e err) :=
  ⟨⟨hd.mean.radial.add he.radial, hd.mean.angular.add he.angular, hd.mean.axial.add he.axial⟩,
    hd.pressure, hd.oscillation⟩

section Actual

variable {F : OutgoingProfile.Profile} {W₀ : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W₀) {ld : ModulatedProfileAssembly.LoopData W₀}
  (v : ModulatedProfileAssembly.Witness ld) (upper : ℝ) (B : ℕ) (index : ℕ → ℕ)
  {P : SignedStressPrimitive.Patch}
  (W : OffplaneCorrectionExtensions.Window (2 * F.data.h) P.a P.b)

theorem actual_base_periodic : PeriodicTriple W.carrier
    (SupportedActualContext.context H v upper B index).base :=
  ⟨fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

theorem actual_profile_periodic : Periodic W.carrier
    (fun _ => (SupportedActualContext.context H v upper B index).operators.radialProfile) :=
  fun _ _ _ _ _ _ => rfl

theorem actual_invRadius_periodic : Periodic W.carrier
    (SupportedActualContext.context H v upper B index).operators.invRadius :=
  fun _ _ _ _ _ _ => rfl

theorem actual_virtual_periodic :
    Periodic W.carrier (SupportedActualContext.context H v upper B index).virtualTheta ∧
    Periodic W.carrier (SupportedActualContext.context H v upper B index).virtualAxial :=
  ⟨fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

variable {u : CorrectionState.State Point} (d : SignedRequestContinuation.Primitives P W u)

theorem radialSource_periodic (hp : PeriodicPrimitives d) :
    Periodic W.carrier (fun n => (SignedRequestContinuation.radialSource H v upper B index W d n).value) :=
  PeriodicAlgebra.gr (actual_base_periodic H v upper B index W) hp.mean hp.covariance W.isOpen
    (actual_profile_periodic H v upper B index W) (actual_invRadius_periodic H v upper B index W)

theorem reconstructPrimitives_periodic (hp : PeriodicPrimitives d)
    (g : VariableGaugeMean.GaugeData Slow)
    (ha : g.radial.inner = P.a) (hb : g.radial.outer = P.b)
    (hell : ∀ n, g.length n = VariableGaugeMean.qLength (2 * F.data.h)) (he : 0 < g.radial.exponent) :
    PeriodicPrimitives (SignedRequestContinuation.reconstructPrimitives H v upper B index W d g ha hb hell he) := by
  refine ⟨hp.mean, ?_, hp.oscillation⟩
  intro n
  exact VariableGaugeMean.meanPressure_periodicOn P.a_lt_b g.radial.exponent
    (g.radial.frequency n) (OffplaneCorrectionExtensions.stableLength (2 * F.data.h))
    g.radial.radialDirection (radialSource_periodic H v upper B index W d hp n)

variable (hleft : P.a ≤ PrimaryTargetBounds.leftRadius W₀)
  (hright : PrimaryTargetBounds.rightRadius W₀ ≤ P.b)

theorem thetaSource_periodic (hp : PeriodicPrimitives d) :
    Periodic W.carrier (fun n =>
      (SupportedActualContext.thetaSource H v upper B index W hleft hright d n).value) :=
  PeriodicAlgebra.thetaResidual (actual_base_periodic H v upper B index W) hp.mean hp.covariance
    (actual_virtual_periodic H v upper B index W).1 W.isOpen
    (actual_profile_periodic H v upper B index W) (actual_invRadius_periodic H v upper B index W)

theorem axialSource_periodic (hp : PeriodicPrimitives d) :
    Periodic W.carrier (fun n =>
      (SupportedActualContext.axialSource H v upper B index W hleft hright d n).value) :=
  PeriodicAlgebra.axialResidual (actual_base_periodic H v upper B index W) hp.mean hp.covariance
    hp.pressure (actual_virtual_periodic H v upper B index W).2 W.isOpen
    (actual_profile_periodic H v upper B index W) (actual_invRadius_periodic H v upper B index W)

noncomputable def temporalAngular (hp : PeriodicPrimitives d) (n : ℕ) :
    OffplaneCorrectionExtensions.SupportedContinuation W
      (MeanChartCompatibility.temporalAtIndex F.data.h n (index n)
        (u.thetaResidual (CommonBaseContext.context H v upper B index) n)) :=
  (SupportedActualContext.thetaSource H v upper B index W hleft hright d n).temporal
    F.data.h n (index n) (thetaSource_periodic H v upper B index W d hleft hright hp n)

noncomputable def temporalDesiredAxial (hp : PeriodicPrimitives d) (n : ℕ) :
    OffplaneCorrectionExtensions.SupportedContinuation W
      (MeanChartCompatibility.temporalAtIndex F.data.h n (index n)
        (u.axialResidual (CommonBaseContext.context H v upper B index) n)) :=
  (SupportedActualContext.axialSource H v upper B index W hleft hright d n).temporal
    F.data.h n (index n) (axialSource_periodic H v upper B index W d hleft hright hp n)

variable (g : VariableGaugeMean.GaugeData Slow)
  (ha : g.radial.inner = P.a) (hb : g.radial.outer = P.b)
  (hell : ∀ n, g.length n = VariableGaugeMean.qLength (2 * F.data.h))
  (he : 0 < g.radial.exponent)

noncomputable def temporalPotential (hp : PeriodicPrimitives d) (n : ℕ) :
    OffplaneCorrectionExtensions.SupportedContinuation W
      (VariableGaugeMean.temporalPotential g F.data.h index
        (CommonBaseContext.context H v upper B index) u n) :=
  Continuation.retarget
    ((temporalDesiredAxial H v upper B index W d hleft hright hp n).stream
      (by linarith [F.data.h_pos]) (by linarith [F.data.h_lt_half]) P.a_pos P.a_lt_b he
      (g.radial.frequency n) g.radial.radialDirection)
    (fun _ => by simp only [VariableGaugeMean.temporalPotential, ha, hb, hell])

noncomputable def temporalIncrement (hp : PeriodicPrimitives d) (axial : Slow × Slow) :
    IncrementContinuations P W (VariableGaugeMean.temporalIncrementState g F.data.h index axial
      (CommonBaseContext.context H v upper B index) u) where
  radial := fun n => Continuation.streamBeta
    (by linarith [F.data.h_pos]) (by linarith [F.data.h_lt_half])
    (temporalPotential H v upper B index W d hleft hright g ha hb hell he hp n)
    ((CommonBaseContext.context H v upper B index).operators.epsilon n • axial)
  angular := temporalAngular H v upper B index W d hleft hright hp
  axial := fun n => Continuation.streamGamma
    (by linarith [F.data.h_pos]) (by linarith [F.data.h_lt_half])
    (temporalPotential H v upper B index W d hleft hright g ha hb hell he hp n)
    g.radial.exponent (g.radial.frequency n) g.radial.radialDirection

/-- The actual temporal stage, including its retained exact alias and
new reconstructed pressure, has a derived primitive continuation. -/
noncomputable def temporalPrimitives (hp : PeriodicPrimitives d) (axial : Slow × Slow) :
    SignedRequestContinuation.Primitives P W
      (VariableGaugeMean.temporalStageState g F.data.h index axial
        (CommonBaseContext.context H v upper B index) u) :=
  SignedRequestContinuation.reconstructPrimitives H v upper B index W
    (addPrimitives d (temporalIncrement H v upper B index W d hleft hright g ha hb hell he hp axial)
      ⟨0, 0, VariableGaugeMean.temporalAliasState g F.data.h index
        (CommonBaseContext.context H v upper B index) u⟩) g ha hb hell he

theorem temporalPotential_periodic (hp : PeriodicPrimitives d) (n : ℕ) :
    PhysicalMeanDomain.PeriodicOn W.carrier
      (temporalPotential H v upper B index W d hleft hright g ha hb hell he hp n).value :=
  VariableGaugeMean.streamPotential_periodicOn g.radial.exponent P.a P.b (g.radial.frequency n)
    (OffplaneCorrectionExtensions.stableLength (2 * F.data.h)) g.radial.radialDirection
    (fun R s _ => MeanChartCompatibility.temporalAtIndex_periodic F.data.h n (index n) _ R s)

theorem temporalIncrement_periodic (hp : PeriodicPrimitives d) (axial : Slow × Slow) :
    PeriodicTriple W.carrier
      (temporalIncrement H v upper B index W d hleft hright g ha hb hell he hp axial).value := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact streamBeta_periodic W.isOpen
      (temporalPotential_periodic H v upper B index W d hleft hright g ha hb hell he hp n) _
  · intro n R s _
    exact MeanChartCompatibility.temporalAtIndex_periodic F.data.h n (index n) _ R s
  · intro n
    change PhysicalMeanDomain.PeriodicOn W.carrier
      (Continuation.streamGamma _ _
        (temporalPotential H v upper B index W d hleft hright g ha hb hell he hp n)
        g.radial.exponent (g.radial.frequency n) g.radial.radialDirection).value
    rw [Continuation.streamGamma_value]
    exact streamGamma_periodic W.isOpen
      (temporalPotential_periodic H v upper B index W d hleft hright g ha hb hell he hp n) _ _ _

theorem temporalPrimitives_periodic (hp : PeriodicPrimitives d) (axial : Slow × Slow) :
    PeriodicPrimitives
      (temporalPrimitives H v upper B index W d hleft hright g ha hb hell he hp axial) :=
  reconstructPrimitives_periodic H v upper B index W _
    (addPrimitives_periodic hp _
      (temporalIncrement_periodic H v upper B index W d hleft hright g ha hb hell he hp axial) _)
    g ha hb hell he

/-! ## The continued debts are measured from the continued primitives -/

noncomputable def thetaFlux (n : ℕ) : OffplaneCorrectionExtensions.SupportedContinuation W
    (fun x => MeanIncrementBounds.thetaAxial (CommonBaseContext.context H v upper B index).base u.mean n x +
      u.covariance 2 1 n x) where
  value := fun x => MeanIncrementBounds.thetaAxial (SupportedActualContext.context H v upper B index).base
    d.state.mean n x + d.state.covariance 2 1 n x
  smooth := ((LocalRankDefect.thetaAxial_localShell W.lower_pos W.isOpen
    (SignedRequestContinuation.actual_base_smooth H v upper B index W) d.mean_localShell).add
      (d.covariance_localShell 2 1)).smooth n
  supported := ((d.mean_supported.thetaAxial (SupportedActualContext.context H v upper B index).base).add
    (d.covariance_supported 2 1)) n
  agrees := ((SupportedActualContext.context_base_agrees H v upper B index W.carrier).thetaAxial
    d.mean_agrees |>.add (d.covariance_agrees 2 1)) n

noncomputable def axialFlux (n : ℕ) : OffplaneCorrectionExtensions.SupportedContinuation W
    (fun x => MeanIncrementBounds.axialAxial (CommonBaseContext.context H v upper B index).base u.mean n x +
      u.covariance 2 2 n x) where
  value := fun x => MeanIncrementBounds.axialAxial (SupportedActualContext.context H v upper B index).base
    d.state.mean n x + d.state.covariance 2 2 n x
  smooth := ((LocalRankDefect.axialAxial_localShell W.lower_pos W.isOpen
    (SignedRequestContinuation.actual_base_smooth H v upper B index W) d.mean_localShell).add
      (d.covariance_localShell 2 2)).smooth n
  supported := ((d.mean_supported.axialAxial (SupportedActualContext.context H v upper B index).base).add
    (d.covariance_supported 2 2)) n
  agrees := ((SupportedActualContext.context_base_agrees H v upper B index W.carrier).axialAxial
    d.mean_agrees |>.add (d.covariance_agrees 2 2)) n

/-- No debt continuation is supplied: all three debts are actual radial
and torus integrals of the continued source and nonlinear fluxes. -/
noncomputable def continuedDebt (n : ℕ) : Slow → MeanRankUpdate.Debt :=
  CorrectionState.debt (SupportedActualContext.context H v upper B index) d.state n

theorem continuedDebt_smooth (n : ℕ) : ContDiffOn ℝ ∞
    (continuedDebt H v upper B index W d n) W.carrier := by
  let p0 := Continuation.radialPower (SignedRequestContinuation.radialSource H v upper B index W d n) 0
  let p2 := Continuation.radialPower (SignedRequestContinuation.radialSource H v upper B index W d n) 2
  let t2 := Continuation.radialPower (thetaFlux H v upper B index W d n) 2
  let z1 := Continuation.radialPower (axialFlux H v upper B index W d n) 1
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact p0.pressureMass_smooth
  · exact t2.pressureMass_smooth
  · exact z1.pressureMass_smooth.sub (contDiffOn_const.mul p2.pressureMass_smooth)

theorem continuedDebt_agrees (n : ℕ) : EqOn (continuedDebt H v upper B index W d n)
    (CorrectionState.debt (CommonBaseContext.context H v upper B index) u n)
    (W.carrier ∩ OffplaneCorrectionExtensions.positiveSlow) := by
  let p0 := Continuation.radialPower (SignedRequestContinuation.radialSource H v upper B index W d n) 0
  let p2 := Continuation.radialPower (SignedRequestContinuation.radialSource H v upper B index W d n) 2
  let t2 := Continuation.radialPower (thetaFlux H v upper B index W d n) 2
  let z1 := Continuation.radialPower (axialFlux H v upper B index W d n) 1
  intro s hs
  funext i
  fin_cases i
  · exact p0.pressureMass_agreement hs
  · exact t2.pressureMass_agreement hs
  · exact congrArg₂ (fun a b : ℝ => a - 1 / 2 * b)
      (z1.pressureMass_agreement hs) (p2.pressureMass_agreement hs)

/-! ## The same normalized five-row rank kernels, with measured debts -/

variable (A C lam ra rb : ℝ) (hC : C ≠ 0) (hrab : ra < rb)
  (hra : P.a ≤ ra) (hrb : rb ≤ P.b)

noncomputable def rankAngularKernel (i : Fin 3) :
    OffplaneCorrectionExtensions.SupportedContinuation W
      (MeanRankUpdate.chartKernel (2 * F.data.h)
        (MeanRankUpdate.angularModel (2 * F.data.h) A C lam ra rb (Pi.single i 1))) := by
  apply OffplaneCorrectionExtensions.SupportedContinuation.ofModel
    (by linarith [F.data.h_pos]) (by linarith [F.data.h_lt_half])
    (fun y => MeanRankUpdate.angularModel (2 * F.data.h) A C lam ra rb (Pi.single i 1) y.1)
  · exact (MeanRankUpdate.angularModel_contDiffOn (2 * F.data.h) A C lam ra rb hC _).comp
      contDiffOn_fst (fun _ hy => hy)
  · intro y hy hn
    have hs := OffplaneCorrectionExtensions.rankAngular_model_supported
      (2 * F.data.h) A C lam ra rb hrab (Pi.single i 1) y hy hn
    exact ⟨(mul_le_mul_of_nonneg_left hra (Real.sqrt_nonneg _)).trans hs.1,
      hs.2.trans (mul_le_mul_of_nonneg_left hrb (Real.sqrt_nonneg _))⟩

noncomputable def rankAxialKernel (i : Fin 3) :
    OffplaneCorrectionExtensions.SupportedContinuation W
      (MeanRankUpdate.chartKernel (2 * F.data.h)
        (MeanRankUpdate.axialModel (2 * F.data.h) A C lam ra rb (Pi.single i 1))) := by
  apply OffplaneCorrectionExtensions.SupportedContinuation.ofModel
    (by linarith [F.data.h_pos]) (by linarith [F.data.h_lt_half])
    (fun y => MeanRankUpdate.axialModel (2 * F.data.h) A C lam ra rb (Pi.single i 1) y.1)
  · exact (MeanRankUpdate.axialModel_contDiffOn (2 * F.data.h) A C lam ra rb hC _).comp
      contDiffOn_fst (fun _ hy => hy)
  · intro y hy hn
    have hs := OffplaneCorrectionExtensions.rankAxial_model_supported
      (2 * F.data.h) A C lam ra rb hrab (Pi.single i 1) y hy hn
    exact ⟨(mul_le_mul_of_nonneg_left hra (Real.sqrt_nonneg _)).trans hs.1,
      hs.2.trans (mul_le_mul_of_nonneg_left hrb (Real.sqrt_nonneg _))⟩

noncomputable def rankAngular (n : ℕ) :
    OffplaneCorrectionExtensions.SupportedContinuation W
      (MeanRankUpdate.slowLift (CorrectionState.rankAngular
        (RankStateBounds.normalizedData (2 * F.data.h) A C lam ra rb)
        (CommonBaseContext.context H v upper B index) u n)) :=
  Continuation.retarget
    (OffplaneCorrectionExtensions.SupportedContinuation.finiteSum Finset.univ
      (fun i x => CorrectionState.debt (CommonBaseContext.context H v upper B index) u n x.2.1 i *
        MeanRankUpdate.chartKernel (2 * F.data.h)
          (MeanRankUpdate.angularModel (2 * F.data.h) A C lam ra rb (Pi.single i 1)) x)
      (fun i => (rankAngularKernel W A C lam ra rb hC hrab hra hrb i).scaleSlow
        (fun s => continuedDebt H v upper B index W d n s i)
        (contDiffOn_pi.mp (continuedDebt_smooth H v upper B index W d n) i)
        (fun _ hs => congrFun (continuedDebt_agrees H v upper B index W d n hs) i)))
    (fun x => (MeanRankUpdate.chartAngular_eq_sum (2 * F.data.h) A C lam ra rb
      (fun z => CorrectionState.debt (CommonBaseContext.context H v upper B index) u n z.2.1) x).symm)

noncomputable def rankDesiredAxial (n : ℕ) :
    OffplaneCorrectionExtensions.SupportedContinuation W
      (MeanRankUpdate.slowLift (CorrectionState.rankDesiredAxial
        (RankStateBounds.normalizedData (2 * F.data.h) A C lam ra rb)
        (CommonBaseContext.context H v upper B index) u n)) :=
  Continuation.retarget
    (OffplaneCorrectionExtensions.SupportedContinuation.finiteSum Finset.univ
      (fun i x => CorrectionState.debt (CommonBaseContext.context H v upper B index) u n x.2.1 i *
        MeanRankUpdate.chartKernel (2 * F.data.h)
          (MeanRankUpdate.axialModel (2 * F.data.h) A C lam ra rb (Pi.single i 1)) x)
      (fun i => (rankAxialKernel W A C lam ra rb hC hrab hra hrb i).scaleSlow
        (fun s => continuedDebt H v upper B index W d n s i)
        (contDiffOn_pi.mp (continuedDebt_smooth H v upper B index W d n) i)
        (fun _ hs => congrFun (continuedDebt_agrees H v upper B index W d n hs) i)))
    (fun x => (MeanRankUpdate.chartAxial_eq_sum (2 * F.data.h) A C lam ra rb
      (fun z => CorrectionState.debt (CommonBaseContext.context H v upper B index) u n z.2.1) x).symm)

noncomputable def rankPotential (n : ℕ) :
    OffplaneCorrectionExtensions.SupportedContinuation W
      (VariableGaugeMean.rankPotential g (RankStateBounds.normalizedData (2 * F.data.h) A C lam ra rb)
        (CommonBaseContext.context H v upper B index) u n) :=
  Continuation.retarget
    ((rankDesiredAxial H v upper B index W d A C lam ra rb hC hrab hra hrb n).stream
      (by linarith [F.data.h_pos]) (by linarith [F.data.h_lt_half]) P.a_pos P.a_lt_b he
      (g.radial.frequency n) g.radial.radialDirection)
    (fun _ => by simp only [VariableGaugeMean.rankPotential, ha, hb, hell])

noncomputable def rankIncrement (axial : Slow × Slow) : IncrementContinuations P W
    (VariableGaugeMean.rankIncrementState g (RankStateBounds.normalizedData (2 * F.data.h) A C lam ra rb)
      axial (CommonBaseContext.context H v upper B index) u) where
  radial := fun n => Continuation.streamBeta
    (by linarith [F.data.h_pos]) (by linarith [F.data.h_lt_half])
    (rankPotential H v upper B index W d g ha hb hell he A C lam ra rb hC hrab hra hrb n)
    ((CommonBaseContext.context H v upper B index).operators.epsilon n • axial)
  angular := rankAngular H v upper B index W d A C lam ra rb hC hrab hra hrb
  axial := fun n => Continuation.streamGamma
    (by linarith [F.data.h_pos]) (by linarith [F.data.h_lt_half])
    (rankPotential H v upper B index W d g ha hb hell he A C lam ra rb hC hrab hra hrb n)
    g.radial.exponent (g.radial.frequency n) g.radial.radialDirection

/-- The outgoing pressure is reconstructed from the updated means and the
same oscillation.  Its continuation is obtained after constructing the
actual rank increment, rather than assumed for the result. -/
noncomputable def rankPrimitives (axial : Slow × Slow) :
    SignedRequestContinuation.Primitives P W
      (VariableGaugeMean.rankStageState g (RankStateBounds.normalizedData (2 * F.data.h) A C lam ra rb)
        axial (CommonBaseContext.context H v upper B index) u) :=
  SignedRequestContinuation.reconstructPrimitives H v upper B index W
    (addPrimitives d (rankIncrement H v upper B index W d g ha hb hell he A C lam ra rb hC hrab hra hrb axial)
      CorrectionState.ExcludedErrors.zero) g ha hb hell he

theorem rankAngular_periodic (n : ℕ) : PhysicalMeanDomain.PeriodicOn W.carrier
    (rankAngular H v upper B index W d A C lam ra rb hC hrab hra hrb n).value :=
  fun _ _ _ _ _ => rfl

theorem rankDesiredAxial_periodic (n : ℕ) : PhysicalMeanDomain.PeriodicOn W.carrier
    (rankDesiredAxial H v upper B index W d A C lam ra rb hC hrab hra hrb n).value :=
  fun _ _ _ _ _ => rfl

theorem rankPotential_periodic (n : ℕ) : PhysicalMeanDomain.PeriodicOn W.carrier
    (rankPotential H v upper B index W d g ha hb hell he A C lam ra rb hC hrab hra hrb n).value :=
  VariableGaugeMean.streamPotential_periodicOn g.radial.exponent P.a P.b (g.radial.frequency n)
    (OffplaneCorrectionExtensions.stableLength (2 * F.data.h)) g.radial.radialDirection
    (rankDesiredAxial_periodic H v upper B index W d A C lam ra rb hC hrab hra hrb n)

theorem rankIncrement_periodic (axial : Slow × Slow) : PeriodicTriple W.carrier
    (rankIncrement H v upper B index W d g ha hb hell he A C lam ra rb hC hrab hra hrb axial).value := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact streamBeta_periodic W.isOpen
      (rankPotential_periodic H v upper B index W d g ha hb hell he A C lam ra rb hC hrab hra hrb n) _
  · exact rankAngular_periodic H v upper B index W d A C lam ra rb hC hrab hra hrb
  · intro n
    change PhysicalMeanDomain.PeriodicOn W.carrier
      (Continuation.streamGamma _ _
        (rankPotential H v upper B index W d g ha hb hell he A C lam ra rb hC hrab hra hrb n)
        g.radial.exponent (g.radial.frequency n) g.radial.radialDirection).value
    rw [Continuation.streamGamma_value]
    exact streamGamma_periodic W.isOpen
      (rankPotential_periodic H v upper B index W d g ha hb hell he A C lam ra rb hC hrab hra hrb n) _ _ _

theorem rankPrimitives_periodic (hp : PeriodicPrimitives d) (axial : Slow × Slow) :
    PeriodicPrimitives (rankPrimitives H v upper B index W d g ha hb hell he
      A C lam ra rb hC hrab hra hrb axial) :=
  reconstructPrimitives_periodic H v upper B index W _
    (addPrimitives_periodic hp _
      (rankIncrement_periodic H v upper B index W d g ha hb hell he A C lam ra rb hC hrab hra hrb axial) _)
    g ha hb hell he

/-- Two consecutive literal mean stages preserve the same window and
gauge.  The rank debts are measured after the temporal update. -/
noncomputable def temporalRankPrimitives (hp : PeriodicPrimitives d)
    (axialTime axialRank : Slow × Slow) :
    SignedRequestContinuation.Primitives P W
      (VariableGaugeMean.rankStageState g (RankStateBounds.normalizedData (2 * F.data.h) A C lam ra rb)
        axialRank (CommonBaseContext.context H v upper B index)
        (VariableGaugeMean.temporalStageState g F.data.h index axialTime
          (CommonBaseContext.context H v upper B index) u)) :=
  rankPrimitives H v upper B index W
    (temporalPrimitives H v upper B index W d hleft hright g ha hb hell he hp axialTime)
    g ha hb hell he A C lam ra rb hC hrab hra hrb axialRank

theorem temporalRankPrimitives_periodic (hp : PeriodicPrimitives d)
    (axialTime axialRank : Slow × Slow) :
    PeriodicPrimitives (temporalRankPrimitives H v upper B index W d hleft hright
      g ha hb hell he A C lam ra rb hC hrab hra hrb hp axialTime axialRank) :=
  rankPrimitives_periodic H v upper B index W
    (temporalPrimitives H v upper B index W d hleft hright g ha hb hell he hp axialTime)
    g ha hb hell he A C lam ra rb hC hrab hra hrb
    (temporalPrimitives_periodic H v upper B index W d hleft hright g ha hb hell he hp axialTime) axialRank

/-- The retained temporal alias is itself continued by differentiating
the difference between the desired and realized axial increments. -/
noncomputable def temporalAliasComponent (hp : PeriodicPrimitives d) (n : ℕ) :
    OffplaneCorrectionExtensions.SupportedContinuation W
      (fun x => VariableGaugeMean.temporalAliasState g F.data.h index
        (CommonBaseContext.context H v upper B index) u n (x, 0) 2) :=
  Continuation.retarget
    (Continuation.neg (Continuation.coefficientMul
      (Continuation.directional (by linarith [F.data.h_pos]) (by linarith [F.data.h_lt_half])
        (Continuation.add (temporalDesiredAxial H v upper B index W d hleft hright hp n)
          (Continuation.neg ((temporalIncrement H v upper B index W d hleft hright g ha hb hell he hp 0).axial n)))
        (CommonBaseContext.context H v upper B index).operators.vT)
      (fun _ => (CommonBaseContext.context H v upper B index).operators.fastCoefficient n) contDiffOn_const))
    (fun x => by
      simp [VariableGaugeMean.temporalAliasState,
        VariableGaugeMean.temporalIncrementState, MeanIncrementBounds.Operators.fastTime,
        Matrix.cons_val_two]
      left
      unfold VariableGaugeMean.temporalAxialDifference
      simp only [sub_eq_add_neg])

/-! ## Physical stream, direct-angular, and pressure endpoint models -/

noncomputable def temporalStreamExtension (hp : PeriodicPrimitives d) (n : ℕ)
    {x : ProblemStatement.Space} (hx : (0, x 2) ∈ W.carrier) :
    JointResidualLimits.OneSidedExtension
      (OffplaneCorrectionExtensions.azimuthalPotential F.data.h n
        (VariableGaugeMean.temporalPotential g F.data.h index
          (CommonBaseContext.context H v upper B index) u n)) x :=
  (temporalPotential H v upper B index W d hleft hright g ha hb hell he hp n).azimuthalExtension
    F.data.h n hx

noncomputable def temporalAngularExtension (hp : PeriodicPrimitives d) (n : ℕ)
    {x : ProblemStatement.Space} (hx : (0, x 2) ∈ W.carrier) :
    JointResidualLimits.OneSidedExtension
      (OffplaneCorrectionExtensions.angularField F.data.h n
        (MeanChartCompatibility.temporalAtIndex F.data.h n (index n)
          (u.thetaResidual (CommonBaseContext.context H v upper B index) n))) x :=
  (temporalAngular H v upper B index W d hleft hright hp n).angularExtension F.data.h n hx

noncomputable def temporalPressureExtension (hp : PeriodicPrimitives d)
    (axial : Slow × Slow) (n : ℕ) {x : ProblemStatement.Space} (hx : (0, x 2) ∈ W.carrier) :
    JointResidualLimits.OneSidedExtension
      (OffplaneCorrectionExtensions.physicalScalar F.data.h n
        ((VariableGaugeMean.temporalStageState g F.data.h index axial
          (CommonBaseContext.context H v upper B index) u).pressure n)) x :=
  ((temporalPrimitives H v upper B index W d hleft hright g ha hb hell he hp axial).pressure n).physicalExtension
    F.data.h n hx

noncomputable def rankStreamExtension (n : ℕ) {x : ProblemStatement.Space} (hx : (0, x 2) ∈ W.carrier) :
    JointResidualLimits.OneSidedExtension
      (OffplaneCorrectionExtensions.azimuthalPotential F.data.h n
        (VariableGaugeMean.rankPotential g (RankStateBounds.normalizedData (2 * F.data.h) A C lam ra rb)
          (CommonBaseContext.context H v upper B index) u n)) x :=
  (rankPotential H v upper B index W d g ha hb hell he A C lam ra rb hC hrab hra hrb n).azimuthalExtension
    F.data.h n hx

noncomputable def rankAngularExtension (n : ℕ) {x : ProblemStatement.Space} (hx : (0, x 2) ∈ W.carrier) :
    JointResidualLimits.OneSidedExtension
      (OffplaneCorrectionExtensions.angularField F.data.h n
        (MeanRankUpdate.slowLift (CorrectionState.rankAngular
          (RankStateBounds.normalizedData (2 * F.data.h) A C lam ra rb)
          (CommonBaseContext.context H v upper B index) u n))) x :=
  (rankAngular H v upper B index W d A C lam ra rb hC hrab hra hrb n).angularExtension F.data.h n hx

noncomputable def rankPressureExtension (axial : Slow × Slow) (n : ℕ)
    {x : ProblemStatement.Space} (hx : (0, x 2) ∈ W.carrier) :
    JointResidualLimits.OneSidedExtension
      (OffplaneCorrectionExtensions.physicalScalar F.data.h n
        ((VariableGaugeMean.rankStageState g (RankStateBounds.normalizedData (2 * F.data.h) A C lam ra rb)
          axial (CommonBaseContext.context H v upper B index) u).pressure n)) x :=
  ((rankPrimitives H v upper B index W d g ha hb hell he A C lam ra rb hC hrab hra hrb axial).pressure n).physicalExtension
    F.data.h n hx

end Actual

end NavierStokes.MeanStageContinuation
