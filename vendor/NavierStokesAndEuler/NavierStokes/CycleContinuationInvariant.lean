import NavierStokes.WaveStageContinuation
import NavierStokes.MeanStageContinuation
import NavierStokes.CorrectionStep

/-!
# Continuation data for the literal correction cycle

This invariant records continuations of primitive fields and of the finite
harmonic coefficients.  Angular covariances, sources, reconstructed pressures,
and the mean updates are computed from those primitives.  Agreement retains
the entire radial, torus, and angular fibers.

The cycle wrappers below take `WavePrimitives` for the two actual wave
updates.  This file does not infer that input from smooth incoming primitives
alone: an inverse covariance factor may grow at a flat annulus edge, so such
an inference would require additional weighted estimates.  In particular,
the declarations below are a reconstruction algebra, not an unconditional
iteration theorem or an assumed physical endpoint extension.
-/

noncomputable section

namespace NavierStokes.CycleContinuationInvariant

open Set Filter Function CorrectionState CorrectionStep
open scoped Topology ContDiff BigOperators


abbrev Point := LocalSignedRequest.Point
abbrev Slow := TorusInverse.Plane

/-! ## Operations on primitive continuations -/

namespace Field

variable {coord a b : ℝ} {W : OffplaneCorrectionExtensions.Window coord a b}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f g : Point → E}

noncomputable def retarget (e : WaveStageContinuation.FieldContinuation W f)
    (h : ∀ x, f x = g x) : WaveStageContinuation.FieldContinuation W g where
  value := e.value
  smooth := e.smooth
  supported := e.supported
  agrees := fun x hx => (e.agrees hx).trans (h x)

noncomputable def zero : WaveStageContinuation.FieldContinuation W (fun _ : Point => (0 : E)) where
  value := fun _ => 0
  smooth := contDiffOn_const
  supported := fun _ _ hn => (hn rfl).elim
  agrees := fun _ _ => rfl

noncomputable def add (e : WaveStageContinuation.FieldContinuation W f) (d : WaveStageContinuation.FieldContinuation W g) :
    WaveStageContinuation.FieldContinuation W (fun x => f x + g x) where
  value x := e.value x + d.value x
  smooth := e.smooth.add d.smooth
  supported := by
    intro x hx hn
    by_contra hs
    have he : e.value x = 0 := by
      by_contra hz
      exact hs (e.supported x hx hz)
    have hd : d.value x = 0 := by
      by_contra hz
      exact hs (d.supported x hx hz)
    exact hn (by simp [he, hd])
  agrees := fun _ hx => congrArg₂ (· + ·) (e.agrees hx) (d.agrees hx)

noncomputable def neg (e : WaveStageContinuation.FieldContinuation W f) :
    WaveStageContinuation.FieldContinuation W (fun x => -f x) where
  value x := -e.value x
  smooth := e.smooth.neg
  supported := fun x hx hn => e.supported x hx (neg_ne_zero.mp hn)
  agrees := fun _ hx => congrArg Neg.neg (e.agrees hx)

noncomputable def finiteSum {ι : Type*} (s : Finset ι) (f : ι → Point → E)
    (e : ∀ i, WaveStageContinuation.FieldContinuation W (f i)) :
    WaveStageContinuation.FieldContinuation W (fun x => ∑ i ∈ s, f i x) where
  value x := ∑ i ∈ s, (e i).value x
  smooth := ContDiffOn.sum (fun i _ => (e i).smooth)
  supported := by
    intro x hx hn
    by_contra hs
    apply hn
    apply Finset.sum_eq_zero
    intro i hi
    by_contra hz
    exact hs ((e i).supported x hx hz)
  agrees := fun _ hx => Finset.sum_congr rfl (fun i _ => (e i).agrees hx)

noncomputable def ofScalar {f : Point → ℝ} (e : OffplaneCorrectionExtensions.SupportedContinuation W f) :
    WaveStageContinuation.FieldContinuation W f := ⟨e.value, e.smooth, e.supported, e.agrees⟩

noncomputable def pressureSource {f : Point → ℝ}
    (e : OffplaneCorrectionExtensions.SupportedContinuation W f)
    (hc : 0 < coord) (hc1 : coord < 1) (hab : a < b) :
    OffplaneCorrectionExtensions.SupportedContinuation W
      (VariableGaugeMean.pressureSource a b hab (VariableGaugeMean.qLength coord) f) where
  value := VariableGaugeMean.pressureSource a b hab
    (OffplaneCorrectionExtensions.stableLength coord) e.value
  smooth := W.pressureSource_smooth hc hc1 hab e.smooth e.supported
  supported := VariableGaugeMean.pressureSource_supported hab
    (fun _ hs => W.length_pos hs) e.supported
  agrees := OffplaneCorrectionExtensions.pressureSource_agreement hc hc1 e.agrees a b hab

end Field

/-- Periodicity is imposed on coefficient functions and on the exponential
character of the phase, never on an unwrapped phase itself. -/
def PeriodicField {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set Slow) (f : Point → E) : Prop :=
  ∀ r s, s ∈ U → FourierAlias.TorusPeriodic (fun Y => f (r, (s, Y)))

namespace PeriodicField

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {U : Set Slow} {f g : Point → E}

theorem zero : PeriodicField U (fun _ : Point => (0 : E)) := fun _ _ _ _ _ => rfl

theorem add (hf : PeriodicField U f) (hg : PeriodicField U g) :
    PeriodicField U (fun x => f x + g x) :=
  fun r s hs Y k => congrArg₂ (· + ·) (hf r s hs Y k) (hg r s hs Y k)

theorem neg (hf : PeriodicField U f) : PeriodicField U (fun x => -f x) :=
  fun r s hs Y k => congrArg Neg.neg (hf r s hs Y k)

theorem finiteSum {ι : Type*} (s : Finset ι) (f : ι → Point → E)
    (hf : ∀ i ∈ s, PeriodicField U (f i)) :
    PeriodicField U (fun x => ∑ i ∈ s, f i x) :=
  fun r p hp Y k => Finset.sum_congr rfl (fun i hi => hf i hi r p hp Y k)

end PeriodicField

/-! ## Finite harmonic evaluation with the genuine axis zero neighborhood -/

section HarmonicEvaluation

variable {coord a b : ℝ} {W : OffplaneCorrectionExtensions.Window coord a b}

theorem field_eq_of_coefficients (c d : HarmonicFields.Coefficients Point) (k : ℝ)
    (Φ Ψ : Point → ℝ) (kp : ℤ) (x : Point) (θ : ℝ)
    (hc : ∀ j, c j x = d j x) (hΦ : Φ x = Ψ x) :
    HarmonicFields.field c k Φ kp (x, θ) = HarmonicFields.field d k Ψ kp (x, θ) := by
  classical
  let s := c.support ∪ d.support
  unfold HarmonicFields.field
  rw [HarmonicFields.evaluate_over c s Finset.subset_union_left,
    HarmonicFields.evaluate_over d s Finset.subset_union_right, hΦ]
  exact Finset.sum_congr rfl (fun j _ => by rw [hc j])

theorem field_eq_zero (c : HarmonicFields.Coefficients Point) (k : ℝ) (Φ : Point → ℝ)
    (kp : ℤ) (x : Point) (θ : ℝ) (hc : ∀ j, c j x = 0) :
    HarmonicFields.field c k Φ kp (x, θ) = 0 := by
  unfold HarmonicFields.field HarmonicFields.evaluate HarmonicFields.Coefficients.sum Finsupp.sum
  exact Finset.sum_eq_zero (fun j _ => by simp only [hc j, zero_mul])

theorem field_supported (c : HarmonicFields.Coefficients Point) (k : ℝ) (Φ : Point → ℝ)
    (kp : ℤ)
    (hc : ∀ j, WaveStageContinuation.RadialSupport a b (OffplaneCorrectionExtensions.stableLength coord) W.carrier (c j))
    (θ : ℝ) :
    WaveStageContinuation.RadialSupport a b (OffplaneCorrectionExtensions.stableLength coord) W.carrier
      (fun x => HarmonicFields.field c k Φ kp (x, θ)) := by
  intro x hx hn
  by_contra hs
  apply hn
  apply field_eq_zero
  intro j
  by_contra hz
  exact hs (hc j x hx hz)

theorem field_smooth (c : HarmonicFields.Coefficients Point) (k : ℝ) (Φ : Point → ℝ)
    (kp : ℤ)
    (hc : HarmonicResidual.SmoothCoefficients (PhysicalMeanDomain.slowDomain W.carrier) c)
    (hs : ∀ j, WaveStageContinuation.RadialSupport a b (OffplaneCorrectionExtensions.stableLength coord) W.carrier (c j))
    (hΦ : ContDiffOn ℝ ∞ Φ (LocalRankDefect.positiveDomain W.carrier)) :
    ContDiffOn ℝ ∞ (HarmonicFields.field c k Φ kp)
      (PhysicalMeanDomain.slowDomain W.carrier ×ˢ (univ : Set ℝ)) := by
  intro x hx
  by_cases hr : 0 < x.1.1
  · have hh := HarmonicResidual.field_smoothOn
      (fun j => (hc j).mono (fun _ hy => hy.2)) hΦ k kp
    exact (hh.contDiffAt
      (((LocalRankDefect.positiveDomain_open W.isOpen).prod isOpen_univ).mem_nhds
        (show x ∈ LocalRankDefect.positiveDomain W.carrier ×ˢ (univ : Set ℝ) from
          ⟨⟨hr, hx.1⟩, mem_univ _⟩))).contDiffWithinAt
  · have hz : HarmonicFields.field c k Φ kp =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [((PhysicalMeanDomain.slowDomain_open W.isOpen).prod isOpen_univ).mem_nhds hx,
        (isOpen_lt continuous_fst.fst continuous_const).mem_nhds
          (show x.1.1 < W.lower from lt_of_le_of_lt (le_of_not_gt hr) W.lower_pos)]
        with y hy hyr
      exact field_eq_zero c k Φ kp y.1 y.2 (fun j => by
        by_contra hn
        exact (not_lt_of_ge ((W.left _ hy.1).trans (hs j y.1 hy.1 hn).1)) hyr)
    exact (contDiffAt_const.congr_of_eventuallyEq hz).contDiffWithinAt

theorem field_periodic (c : HarmonicFields.Coefficients Point) (k : ℝ) (Φ : Point → ℝ) (kp : ℤ)
    (hc : ∀ j, PeriodicField W.carrier (c j))
    (hΦ : ∀ j, PeriodicField W.carrier (fun x => HarmonicFields.character j (k * Φ x))) (θ : ℝ) :
    PeriodicField W.carrier (fun x => HarmonicFields.field c k Φ kp (x, θ)) := by
  intro r s hs Y m
  simp only [HarmonicFields.field_expansion]
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg (· * HarmonicFields.character (j * kp) θ)
    (congrArg₂ (· * ·) (hc j r s hs Y m) (hΦ j r s hs Y m))

end HarmonicEvaluation

/-! ## Primitive finite blocks -/

section Blocks

variable {coord a b : ℝ} {W : OffplaneCorrectionExtensions.Window coord a b}
  {u v : HarmonicBlock Point} {G A J B : HarmonicResidual.BlockCoefficients Point}

noncomputable def addHarmonics (h : WaveStageContinuation.HarmonicPrimitives W u G A)
    (k : WaveStageContinuation.HarmonicPrimitives W v J B) :
    WaveStageContinuation.HarmonicPrimitives W (HarmonicWaveInteraction.addBlock u v) (G + J) (A + B) where
  velocity n i j := Field.add (h.velocity n i j) (k.velocity n i j)
  pressure n j := Field.add (h.pressure n j) (k.pressure n j)
  gaussian n i j := Field.add (h.gaussian n i j) (k.gaussian n i j)
  aliasError n i j := Field.add (h.aliasError n i j) (k.aliasError n i j)
  phase := h.phase
  phase_smooth := h.phase_smooth
  phase_agrees := h.phase_agrees

structure PeriodicHarmonics (h : WaveStageContinuation.HarmonicPrimitives W u G A) : Prop where
  velocity : ∀ n i j, PeriodicField W.carrier (h.velocity n i j).value
  pressure : ∀ n j, PeriodicField W.carrier (h.pressure n j).value
  gaussian : ∀ n i j, PeriodicField W.carrier (h.gaussian n i j).value
  aliasError : ∀ n i j, PeriodicField W.carrier (h.aliasError n i j).value
  phase : ∀ n j, PeriodicField W.carrier
    (fun x => HarmonicFields.character j (u.frequency n * h.phase n x))

theorem PeriodicHarmonics.add {h : WaveStageContinuation.HarmonicPrimitives W u G A}
    {k : WaveStageContinuation.HarmonicPrimitives W v J B} (hh : PeriodicHarmonics h)
    (hk : PeriodicHarmonics k) : PeriodicHarmonics (addHarmonics h k) where
  velocity n i j := (hh.velocity n i j).add (hk.velocity n i j)
  pressure n j := (hh.pressure n j).add (hk.pressure n j)
  gaussian n i j := (hh.gaussian n i j).add (hk.gaussian n i j)
  aliasError n i j := (hh.aliasError n i j).add (hk.aliasError n i j)
  phase := hh.phase

theorem continuedCoefficients_periodic (c : HarmonicFields.Coefficients Point)
    (e : ∀ j, WaveStageContinuation.FieldContinuation W (c j))
    (he : ∀ j, PeriodicField W.carrier (e j).value) (j : ℤ) :
    PeriodicField W.carrier (WaveStageContinuation.continuedCoefficients c e j) := by
  rw [WaveStageContinuation.continuedCoefficients_apply]
  split_ifs
  · exact he j
  · exact PeriodicField.zero

theorem harmonic_oscillation_smooth (h : WaveStageContinuation.HarmonicPrimitives W u G A) (n : ℕ) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun x => h.continuedBlock.oscillation n x i)
      (PhysicalMeanDomain.slowDomain W.carrier ×ˢ (univ : Set ℝ)) :=
  Complex.reCLM.contDiff.comp_contDiffOn (field_smooth _ _ _ _
    (WaveStageContinuation.continuedCoefficients_smooth _ _) (WaveStageContinuation.continuedCoefficients_supported _ _) (h.phase_smooth n))

theorem harmonic_oscillation_supported (h : WaveStageContinuation.HarmonicPrimitives W u G A)
    (n : ℕ) (i : Fin 3) (θ : ℝ) :
    WaveStageContinuation.RadialSupport a b (OffplaneCorrectionExtensions.stableLength coord) W.carrier
      (fun x => h.continuedBlock.oscillation n (x, θ) i) := by
  intro x hx hn
  apply field_supported _ _ _ _ (WaveStageContinuation.continuedCoefficients_supported _ _) θ x hx
  intro hz
  exact hn (congrArg Complex.re hz)

theorem harmonic_oscillation_agrees (h : WaveStageContinuation.HarmonicPrimitives W u G A)
    (n : ℕ) (i : Fin 3) (θ : ℝ) :
    OffplaneCorrectionExtensions.FiberAgreement W.carrier (fun x => h.continuedBlock.oscillation n (x, θ) i)
      (fun x => u.oscillation n (x, θ) i) := by
  intro x hx
  apply congrArg Complex.re
  exact field_eq_of_coefficients _ _ _ _ _ _ x θ
    (fun j => WaveStageContinuation.continuedCoefficients_agrees _ _ j hx) (h.phase_agrees n hx)

theorem harmonic_oscillation_periodic {h : WaveStageContinuation.HarmonicPrimitives W u G A}
    (hh : PeriodicHarmonics h) (n : ℕ) (i : Fin 3) (θ : ℝ) :
    PhysicalMeanDomain.PeriodicOn W.carrier (fun x => h.continuedBlock.oscillation n (x, θ) i) := by
  intro r s hs Y k
  apply congrArg Complex.re
  exact field_periodic _ _ _ _ (continuedCoefficients_periodic _ _ (hh.velocity n i))
    (hh.phase n) θ r s hs Y k

end Blocks

/-! ## Finite label sums and the actual primitive state -/

section FiniteAssembly

variable {coord : ℝ} {P : SignedStressPrimitive.Patch}
  {W : OffplaneCorrectionExtensions.Window coord P.a P.b}
  {ι : Type} (labels : ℕ → Finset ι) (blocks : ι → HarmonicBlock Point)
  {G A : ι → HarmonicResidual.BlockCoefficients Point}
  (h : ∀ l, WaveStageContinuation.HarmonicPrimitives W (blocks l) (G l) (A l))

noncomputable def continuedOscillation : Oscillation Point :=
  fun n x i => ∑ l ∈ labels n, (h l).continuedBlock.oscillation n x i

theorem continuedOscillation_smooth (n : ℕ) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun x => continuedOscillation labels blocks h n x i)
      (PhysicalMeanDomain.slowDomain W.carrier ×ˢ (univ : Set ℝ)) :=
  ContDiffOn.sum (fun l _ => harmonic_oscillation_smooth (h l) n i)

theorem continuedOscillation_supported (n : ℕ) (i : Fin 3) (θ : ℝ) :
    VariableGaugeMean.SupportedGauge P.a P.b
      (OffplaneCorrectionExtensions.stableLength coord) W.carrier
      (fun x => continuedOscillation labels blocks h n (x, θ) i) := by
  intro x hx hn
  by_contra hs
  apply hn
  apply Finset.sum_eq_zero
  intro l hl
  by_contra hz
  exact hs (harmonic_oscillation_supported (h l) n i θ x hx hz)

theorem continuedOscillation_agrees (n : ℕ) (i : Fin 3) (θ : ℝ) :
    OffplaneCorrectionExtensions.FiberAgreement W.carrier
      (fun x => continuedOscillation labels blocks h n (x, θ) i)
      (fun x => LabelSumBounds.fieldSum labels (fun l => (blocks l).oscillation) n (x, θ) i) :=
  fun _ hx => Finset.sum_congr rfl (fun l _ => harmonic_oscillation_agrees (h l) n i θ hx)

theorem continuedOscillation_periodic (hp : ∀ l, PeriodicHarmonics (h l))
    (n : ℕ) (i : Fin 3) (θ : ℝ) :
    PhysicalMeanDomain.PeriodicOn W.carrier
      (fun x => continuedOscillation labels blocks h n (x, θ) i) := by
  exact PeriodicField.finiteSum (labels n)
    (fun l x => (h l).continuedBlock.oscillation n (x, θ) i)
    (fun l _ => harmonic_oscillation_periodic (hp l) n i θ)

variable {u : State Point}

/-- A wave update changes the oscillation by its literal finite label sum.
This construction uses coefficient continuations, not an extension of the
assembled outgoing velocity. -/
noncomputable def addWavePrimitives (d : SignedRequestContinuation.Primitives P W u)
    (pressure : OscillatoryScalar Point) (err : ExcludedErrors Point) :
    SignedRequestContinuation.Primitives P W
      (u.addIncrement zeroTriple 0 (LabelSumBounds.fieldSum labels (fun l => (blocks l).oscillation))
        pressure err) where
  radial n := MeanStageContinuation.Continuation.retarget (d.radial n) (fun _ => by
    simp only [State.addIncrement, MeanIncrementBounds.updated,
      zeroTriple, add_zero])
  angular n := MeanStageContinuation.Continuation.retarget (d.angular n) (fun _ => by
    simp only [State.addIncrement, MeanIncrementBounds.updated,
      zeroTriple, add_zero])
  axial n := MeanStageContinuation.Continuation.retarget (d.axial n) (fun _ => by
    simp only [State.addIncrement, MeanIncrementBounds.updated,
      zeroTriple, add_zero])
  pressure n := MeanStageContinuation.Continuation.retarget (d.pressure n) (fun _ => by
    simp only [State.addIncrement, add_zero])
  oscillation := d.oscillation + continuedOscillation labels blocks h
  oscillation_smooth n i := (d.oscillation_smooth n i).add
    (continuedOscillation_smooth labels blocks h n i)
  oscillation_supported n i θ := by
    classical
    intro x hx hn
    by_contra hs
    have he : d.oscillation n (x, θ) i = 0 := by
      by_contra hz
      exact hs (d.oscillation_supported n i θ x hx hz)
    have hf : continuedOscillation labels blocks h n (x, θ) i = 0 := by
      by_contra hz
      exact hs (continuedOscillation_supported labels blocks h n i θ x hx hz)
    exact hn (by simp only [Pi.add_apply, he, hf, add_zero])
  oscillation_agrees n i θ x hx := congrArg₂ (· + ·)
    (d.oscillation_agrees n i θ hx) (continuedOscillation_agrees labels blocks h n i θ hx)

theorem addWavePrimitives_periodic {d : SignedRequestContinuation.Primitives P W u}
    (hd : MeanStageContinuation.PeriodicPrimitives d)
    (hp : ∀ l, PeriodicHarmonics (h l))
    (pressure : OscillatoryScalar Point) (err : ExcludedErrors Point) :
    MeanStageContinuation.PeriodicPrimitives (addWavePrimitives labels blocks h d pressure err) where
  mean := hd.mean
  pressure := hd.pressure
  oscillation n i θ := by
    intro r s hs Y k
    exact congrArg₂ (· + ·) (hd.oscillation n i θ r s hs Y k)
      (continuedOscillation_periodic labels blocks h hp n i θ r s hs Y k)

end FiniteAssembly

noncomputable def retargetPrimitives {coord : ℝ} {P : SignedStressPrimitive.Patch}
    {W : OffplaneCorrectionExtensions.Window coord P.a P.b} {u v : State Point}
    (d : SignedRequestContinuation.Primitives P W u) (h : u = v) :
    SignedRequestContinuation.Primitives P W v where
  radial n := MeanStageContinuation.Continuation.retarget (d.radial n)
    (fun x => congrArg (fun s : State Point => s.mean.radial n x) h)
  angular n := MeanStageContinuation.Continuation.retarget (d.angular n)
    (fun x => congrArg (fun s : State Point => s.mean.angular n x) h)
  axial n := MeanStageContinuation.Continuation.retarget (d.axial n)
    (fun x => congrArg (fun s : State Point => s.mean.axial n x) h)
  pressure n := MeanStageContinuation.Continuation.retarget (d.pressure n)
    (fun x => congrArg (fun s : State Point => s.pressure n x) h)
  oscillation := d.oscillation
  oscillation_smooth := d.oscillation_smooth
  oscillation_supported := d.oscillation_supported
  oscillation_agrees n i θ x hx := (d.oscillation_agrees n i θ hx).trans
    (congrArg (fun s : State Point => s.oscillation n (x, θ) i) h)

theorem retargetPrimitives_periodic {coord : ℝ} {P : SignedStressPrimitive.Patch}
    {W : OffplaneCorrectionExtensions.Window coord P.a P.b} {u v : State Point}
    {d : SignedRequestContinuation.Primitives P W u}
    (hd : MeanStageContinuation.PeriodicPrimitives d) (h : u = v) :
    MeanStageContinuation.PeriodicPrimitives (retargetPrimitives d h) :=
  ⟨hd.mean, hd.pressure, hd.oscillation⟩

/-! ## The continuation invariant is attached to the represented state -/

structure Invariant {ι : Type} {coord : ℝ} (P : SignedStressPrimitive.Patch)
    (W : OffplaneCorrectionExtensions.Window coord P.a P.b) (x : CycleState ι) where
  primitives : SignedRequestContinuation.Primitives P W x.state
  periodic : MeanStageContinuation.PeriodicPrimitives primitives
  harmonic : ∀ l, WaveStageContinuation.HarmonicPrimitives W
    (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l)
  harmonic_periodic : ∀ l, PeriodicHarmonics (harmonic l)
  axis : ∀ n i, OffplaneCorrectionExtensions.SupportedContinuation W
    (fun z => x.axisymmetricAlias n z i)
  representation : CycleRepresentation x.coefficients x.state x.axisymmetricAlias

/-! ## Reconstructed pressure and exact wave stages -/

section ActualWaveStage

variable {F : OutgoingProfile.Profile} {W₀ : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W₀) {ld : ModulatedProfileAssembly.LoopData W₀}
  (v : ModulatedProfileAssembly.Witness ld) (upper : ℝ) (B : ℕ) (index : ℕ → ℕ)
  {P : SignedStressPrimitive.Patch}
  (W : OffplaneCorrectionExtensions.Window (2 * F.data.h) P.a P.b)
  (g : VariableGaugeMean.GaugeData Slow)
  (ha : g.radial.inner = P.a) (hb : g.radial.outer = P.b)
  (hell : ∀ n, g.length n = VariableGaugeMean.qLength (2 * F.data.h))
  (he : 0 < g.radial.exponent)
  {ι : Type} (labels : ℕ → Finset ι) (blocks : ι → HarmonicBlock Point)
  {G A : ι → HarmonicResidual.BlockCoefficients Point}
  (h : ∀ l, WaveStageContinuation.HarmonicPrimitives W (blocks l) (G l) (A l))
  {u : State Point} (d : SignedRequestContinuation.Primitives P W u)

noncomputable def wavePrimitives (pressure : OscillatoryScalar Point) (err : ExcludedErrors Point) :
    SignedRequestContinuation.Primitives P W
      (gaugeWaveStage g (CommonBaseContext.context H v upper B index) u
        (LabelSumBounds.fieldSum labels (fun l => (blocks l).oscillation)) pressure err) :=
  SignedRequestContinuation.reconstructPrimitives H v upper B index W
    (addWavePrimitives labels blocks h d pressure err) g ha hb hell he

theorem wavePrimitives_periodic (hd : MeanStageContinuation.PeriodicPrimitives d)
    (hp : ∀ l, PeriodicHarmonics (h l))
    (pressure : OscillatoryScalar Point) (err : ExcludedErrors Point) :
    MeanStageContinuation.PeriodicPrimitives
      (wavePrimitives H v upper B index W g ha hb hell he labels blocks h d pressure err) :=
  MeanStageContinuation.reconstructPrimitives_periodic H v upper B index W
    (addWavePrimitives labels blocks h d pressure err)
    (addWavePrimitives_periodic labels blocks h hd hp pressure err) g ha hb hell he

/-- Refreshing the excluded pressure alias changes no primitive field. -/
noncomputable def refreshPrimitives (old : State Point) :
    SignedRequestContinuation.Primitives P W
      (gaugeRefreshPressureAlias g (CommonBaseContext.context H v upper B index) old u) :=
  { d with }

theorem refreshPrimitives_periodic (hd : MeanStageContinuation.PeriodicPrimitives d)
    (old : State Point) :
    MeanStageContinuation.PeriodicPrimitives
      (refreshPrimitives H v upper B index W g d old) :=
  ⟨hd.mean, hd.pressure, hd.oscillation⟩

/-- The pressure alias uses the compact radial primitive of the actual
continued radial residual. -/
noncomputable def pressureAliasComponent (n : ℕ) :
    OffplaneCorrectionExtensions.SupportedContinuation W
      (fun x => VariableGaugeMean.pressureAliasState g
        (CommonBaseContext.context H v upper B index) u n (x, 0) 0) :=
  MeanStageContinuation.Continuation.retarget
    (MeanStageContinuation.Continuation.neg
      ((Field.pressureSource (SignedRequestContinuation.radialSource H v upper B index W d n)
        (by linarith [F.data.h_pos]) (by linarith [F.data.h_lt_half]) P.a_lt_b).aliasField
        (by linarith [F.data.h_pos]) (by linarith [F.data.h_lt_half]) P.a_pos P.a_lt_b he
        (g.radial.frequency n) g.radial.radialDirection))
    (fun z => by
      have hsource : VariableGaugeMean.pressureSource P.a P.b P.a_lt_b
          (VariableGaugeMean.qLength (2 * F.data.h))
          (u.gr (CommonBaseContext.context H v upper B index) n) =
          VariableGaugeMean.pressureSource g.radial.inner g.radial.outer
            g.radial.inner_lt_outer (g.length n)
            (u.gr (CommonBaseContext.context H v upper B index) n) := by
        funext y
        simp only [VariableGaugeMean.pressureSource, VariableGaugeMean.density, ha, hb, hell]
      simp only [VariableGaugeMean.pressureAliasState, Matrix.cons_val_zero]
      rw [← hsource]
      simp only [ha, hb, hell])

end ActualWaveStage

/-! ## The four literal stages share one gauge and one endpoint window -/

section Cycle

variable {F : OutgoingProfile.Profile} {W₀ : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W₀) {ld : ModulatedProfileAssembly.LoopData W₀}
  (v : ModulatedProfileAssembly.Witness ld) (upper : ℝ) (B : ℕ) (index : ℕ → ℕ)
  {P : SignedStressPrimitive.Patch}
  (W : OffplaneCorrectionExtensions.Window (2 * F.data.h) P.a P.b)
  {ι : Type} (p : CycleParameters ι)

/-- Only the fixed gauge, clock, annulus and rank-kernel parameters occur
here. No continued field or endpoint extension is part of this data. -/
structure MeanConfiguration where
  time : p.timeExponent = F.data.h
  clock : p.commonIndex = index
  patch : p.patch = P
  coordinate : p.coordinate = 2 * F.data.h
  inner : p.gauge.radial.inner = P.a
  outer : p.gauge.radial.outer = P.b
  length : ∀ n, p.gauge.length n = VariableGaugeMean.qLength (2 * F.data.h)
  exponent : 0 < p.gauge.radial.exponent
  left : P.a ≤ PrimaryTargetBounds.leftRadius W₀
  right : PrimaryTargetBounds.rightRadius W₀ ≤ P.b
  amplitude : ℝ
  scale : ℝ
  slope : ℝ
  rankLeft : ℝ
  rankRight : ℝ
  scale_ne : scale ≠ 0
  rank_lt : rankLeft < rankRight
  rank_left : P.a ≤ rankLeft
  rank_right : rankRight ≤ P.b
  rank : p.rank = RankStateBounds.normalizedData (2 * F.data.h)
    amplitude scale slope rankLeft rankRight

variable (cfg : MeanConfiguration (W₀ := W₀) (P := P) (index := index) p) (x : CycleState ι)
  (hx : Invariant P W x)

/-- The source of every nonzero particular harmonic is computed from the
continued current primitives and coefficients. -/
noncomputable def particularSourceContinuation (l : ι) (j : ℤ) (n : ℕ) :
    WaveStageContinuation.FieldContinuation W
      (ParticularWaveAssembly.residualSource (CommonBaseContext.context H v upper B index)
        x.state (x.coefficients.blocks l) (x.coefficients.gaussian l)
        (x.coefficients.aliasCoefficients l) j n) :=
  WaveStageContinuation.actualSourceContinuation H v upper B index W hx.primitives (hx.harmonic l) j n

/-- Primitive coefficient data for the actual particular and signed
updates. The scalar source and the assembled outgoing state are absent:
they are computed by the constructors below. -/
structure WavePrimitives where
  particular : ∀ l, WaveStageContinuation.HarmonicPrimitives W
    (p.particularBlock x.coefficients (CommonBaseContext.context H v upper B index) x.state l)
    (p.particularGaussianBlock x.coefficients (CommonBaseContext.context H v upper B index) x.state l).velocity 0
  particular_periodic : ∀ l, PeriodicHarmonics (particular l)
  signed : ∀ l, WaveStageContinuation.HarmonicPrimitives W
    (p.signedBlock x.coefficients (CommonBaseContext.context H v upper B index) x.state l)
    (p.signedGaussianBlock x.coefficients (CommonBaseContext.context H v upper B index) x.state l).velocity 0
  signed_periodic : ∀ l, PeriodicHarmonics (signed l)
  signed_carrier : ∀ l, SameCarrier (x.coefficients.blocks l)
    (p.signedBlock x.coefficients (CommonBaseContext.context H v upper B index) x.state l)

variable (hw : WavePrimitives H v upper B index W p x)

noncomputable def afterParticularPrimitives : SignedRequestContinuation.Primitives P W
    (p.afterParticular x.coefficients (CommonBaseContext.context H v upper B index) x.state) :=
  wavePrimitives H v upper B index W p.gauge cfg.inner cfg.outer cfg.length cfg.exponent
    x.coefficients.labels _ hw.particular hx.primitives
    (p.particularPressure x.coefficients (CommonBaseContext.context H v upper B index) x.state)
    ⟨0, p.particularGaussian x.coefficients (CommonBaseContext.context H v upper B index) x.state, 0⟩

theorem afterParticularPrimitives_periodic : MeanStageContinuation.PeriodicPrimitives
    (afterParticularPrimitives H v upper B index W p cfg x hx hw) :=
  wavePrimitives_periodic H v upper B index W p.gauge cfg.inner cfg.outer cfg.length cfg.exponent
    x.coefficients.labels _ hw.particular hx.primitives hx.periodic hw.particular_periodic _ _

noncomputable def afterSignedPrimitives : SignedRequestContinuation.Primitives P W
    (p.afterSigned x.coefficients (CommonBaseContext.context H v upper B index) x.state) :=
  wavePrimitives H v upper B index W p.gauge cfg.inner cfg.outer cfg.length cfg.exponent
    x.coefficients.labels _ hw.signed
    (afterParticularPrimitives H v upper B index W p cfg x hx hw)
    (p.signedPressure x.coefficients (CommonBaseContext.context H v upper B index) x.state)
    ⟨0, p.signedGaussian x.coefficients (CommonBaseContext.context H v upper B index) x.state, 0⟩

theorem afterSignedPrimitives_periodic : MeanStageContinuation.PeriodicPrimitives
    (afterSignedPrimitives H v upper B index W p cfg x hx hw) :=
  wavePrimitives_periodic H v upper B index W p.gauge cfg.inner cfg.outer cfg.length cfg.exponent
    x.coefficients.labels _ hw.signed _
    (afterParticularPrimitives_periodic H v upper B index W p cfg x hx hw)
    hw.signed_periodic _ _

noncomputable def afterTemporalPrimitives : SignedRequestContinuation.Primitives P W
    (p.afterTemporal x.coefficients (CommonBaseContext.context H v upper B index) x.state) := by
  refine retargetPrimitives
    (MeanStageContinuation.temporalPrimitives H v upper B index W
      (afterSignedPrimitives H v upper B index W p cfg x hx hw) cfg.left cfg.right
      p.gauge cfg.inner cfg.outer cfg.length cfg.exponent
      (afterSignedPrimitives_periodic H v upper B index W p cfg x hx hw) p.axial) ?_
  simp only [CycleParameters.afterTemporal, cfg.time, cfg.clock]

theorem afterTemporalPrimitives_periodic : MeanStageContinuation.PeriodicPrimitives
    (afterTemporalPrimitives H v upper B index W p cfg x hx hw) := by
  apply retargetPrimitives_periodic
  exact MeanStageContinuation.temporalPrimitives_periodic H v upper B index W
    (afterSignedPrimitives H v upper B index W p cfg x hx hw) cfg.left cfg.right
    p.gauge cfg.inner cfg.outer cfg.length cfg.exponent
    (afterSignedPrimitives_periodic H v upper B index W p cfg x hx hw) p.axial

noncomputable def afterRankPrimitives : SignedRequestContinuation.Primitives P W
    (p.afterRank x.coefficients (CommonBaseContext.context H v upper B index) x.state) := by
  refine retargetPrimitives
    (MeanStageContinuation.rankPrimitives H v upper B index W
      (afterTemporalPrimitives H v upper B index W p cfg x hx hw)
      p.gauge cfg.inner cfg.outer cfg.length cfg.exponent
      cfg.amplitude cfg.scale cfg.slope cfg.rankLeft cfg.rankRight cfg.scale_ne cfg.rank_lt
      cfg.rank_left cfg.rank_right p.axial) ?_
  simp only [CycleParameters.afterRank, cfg.rank]

theorem afterRankPrimitives_periodic : MeanStageContinuation.PeriodicPrimitives
    (afterRankPrimitives H v upper B index W p cfg x hx hw) := by
  apply retargetPrimitives_periodic
  exact MeanStageContinuation.rankPrimitives_periodic H v upper B index W
    (afterTemporalPrimitives H v upper B index W p cfg x hx hw)
    p.gauge cfg.inner cfg.outer cfg.length cfg.exponent
    cfg.amplitude cfg.scale cfg.slope cfg.rankLeft cfg.rankRight cfg.scale_ne cfg.rank_lt
    cfg.rank_left cfg.rank_right
    (afterTemporalPrimitives_periodic H v upper B index W p cfg x hx hw) p.axial

noncomputable def nextPrimitives : SignedRequestContinuation.Primitives P W
    (p.next x.coefficients (CommonBaseContext.context H v upper B index) x.state) :=
  refreshPrimitives H v upper B index W p.gauge
    (afterRankPrimitives H v upper B index W p cfg x hx hw) x.state

theorem nextPrimitives_periodic : MeanStageContinuation.PeriodicPrimitives
    (nextPrimitives H v upper B index W p cfg x hx hw) :=
  refreshPrimitives_periodic H v upper B index W p.gauge
    (afterRankPrimitives H v upper B index W p cfg x hx hw)
    (afterRankPrimitives_periodic H v upper B index W p cfg x hx hw) x.state

/-- Stored coefficients keep the original carrier and alias coefficients;
the Gaussian coefficients are the exact sum of both new contributions. -/
noncomputable def nextHarmonics (l : ι) : WaveStageContinuation.HarmonicPrimitives W
    ((p.nextCoefficients x.coefficients (CommonBaseContext.context H v upper B index) x.state).blocks l)
    ((p.nextCoefficients x.coefficients (CommonBaseContext.context H v upper B index) x.state).gaussian l)
    ((p.nextCoefficients x.coefficients (CommonBaseContext.context H v upper B index) x.state).aliasCoefficients l) where
  velocity n i j := Field.add (Field.add ((hx.harmonic l).velocity n i j)
    ((hw.particular l).velocity n i j)) ((hw.signed l).velocity n i j)
  pressure n j := Field.add (Field.add ((hx.harmonic l).pressure n j)
    ((hw.particular l).pressure n j)) ((hw.signed l).pressure n j)
  gaussian n i j := Field.add (Field.add ((hx.harmonic l).gaussian n i j)
    ((hw.particular l).gaussian n i j)) ((hw.signed l).gaussian n i j)
  aliasError := (hx.harmonic l).aliasError
  phase := (hx.harmonic l).phase
  phase_smooth := (hx.harmonic l).phase_smooth
  phase_agrees := (hx.harmonic l).phase_agrees

theorem nextHarmonics_periodic (l : ι) :
    PeriodicHarmonics (nextHarmonics H v upper B index W p x hx hw l) where
  velocity n i j := (((hx.harmonic_periodic l).velocity n i j).add
    ((hw.particular_periodic l).velocity n i j)).add ((hw.signed_periodic l).velocity n i j)
  pressure n j := (((hx.harmonic_periodic l).pressure n j).add
    ((hw.particular_periodic l).pressure n j)).add ((hw.signed_periodic l).pressure n j)
  gaussian n i j := (((hx.harmonic_periodic l).gaussian n i j).add
    ((hw.particular_periodic l).gaussian n i j)).add ((hw.signed_periodic l).gaussian n i j)
  aliasError := (hx.harmonic_periodic l).aliasError
  phase := (hx.harmonic_periodic l).phase

end Cycle

end NavierStokes.CycleContinuationInvariant
