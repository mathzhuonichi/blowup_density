import NSFormalization.Section3.T23.Rates
import Bindings.Scaling
import Contracts.V1.PacketImport

/-! Exact field consumers on Boundary.lean's canonical vocabulary. The force
hypotheses are U2b/U3/U4/U5 facts, never an assumed BoundaryInsertionAPI. -/
noncomputable section
namespace T23U6Probe
open Set MeasureTheory Filter Topology
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T23
open scoped ENNReal Topology

section Force
variable {ν : ℝ} {u f : VelocityField} {p : PressureField}
    {K Ω : Set Space} {a : Space → Space} {g : VelocityField}
    (place : DomainPlacementData u p f K) {δ : ℝ} (D : CutoffData)
    (reference : ClassicalSolutionOmega ν Ω a g (place.T + δ))
    (force : ℝ → VelocityField) (ε₀ : ℝ) (A B : ℝ → ℝ)
    (he1 : ε₀ ≤ 1)
    (hformula : ∀ ε z, force ε z = g z + correctionForce ν reference.velocity D ε z +
      NSFormalization.Section3.T15.scaledForce f place.x₀ place.T ε z)
    (hsupport : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t,
      Function.support (fun x => force ε (t, x) - g (t, x)) ⊆ Ω)
    (hleft : ∀ s, ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      domainForceSobolevENorm Ω s (fun z => force ε z - g z) ≤
        zeroExtForceSobolevENorm Ω s (fun z => force ε z - g z))
    (hF : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t, 0 ≤ t → Continuous
      (fun x => NSFormalization.Section3.T15.scaledForce f place.x₀ place.T ε (t, x)))
    (hH : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t, 0 ≤ t → Continuous
      (fun x => correctionForce ν reference.velocity D ε (t, x)))
    (hpacket : ∀ s, 0 ≤ s → s < 1 / 2 → ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      NSFormalization.Section4.D01.forceSobolevENorm 1 s
        (NSFormalization.Section3.T15.scaledForce f place.x₀ place.T ε) ≤
      ENNReal.ofReal (A s * (ε ^ ((1 : ℝ) / 2) + ε ^ ((1 : ℝ) / 2 - s))))
    (hcorr : ∀ s, 0 ≤ s → s < 1 / 2 → ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      NSFormalization.Section4.D01.forceSobolevENorm 1 s
        (correctionForce ν reference.velocity D ε) ≤
      ENNReal.ofReal (B s * (ε ^ ((3 : ℝ) / 2) + ε ^ ((3 : ℝ) / 2 - s))))

-- Data and positivity fields.
example : ℝ → ℝ := by
  exact forceDiffSobolevConst A B
example : ∀ s : ℝ, 0 ≤ s → s < 1 / 2 → 0 < forceDiffSobolevConst A B s := by
  exact fun s _ _ => forceDiffSobolevConst_pos A B s

-- Literal forceDifference_sobolev_bound field.
example :
    ∀ s, 0 ≤ s → s < 1 / 2 → ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      domainForceSobolevENorm Ω s (fun z => force ε z - g z) ≤
        ENNReal.ofReal (forceDiffSobolevConst A B s *
          (ε ^ ((1 : ℝ) / 2 - s) + ε ^ ((3 : ℝ) / 2 - s))) := by
  exact forceDifference_sobolev_bound place D reference force ε₀ A B he1 hformula hsupport hleft hF hH hpacket hcorr

-- Both convergence fields are instantiated at the proved supplier-based bound.
example (he : 0 < ε₀) : ∀ s : ℝ, s < 0 →
    Tendsto (fun ε : ℝ => domainForceSobolevENorm Ω s (fun z => force ε z - g z))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
  exact forceDifference_negativeSobolev_tendsto Ω force g ε₀
    (forceDiffSobolevConst A B) he
    (forceDifference_sobolev_bound place D reference force ε₀ A B he1 hformula hsupport hleft hF hH hpacket hcorr)

example (he : 0 < ε₀) : ∀ s : ℝ, 0 ≤ s → s < 1 / 2 →
    Tendsto (fun ε : ℝ => domainForceSobolevENorm Ω s (fun z => force ε z - g z))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
  exact forceDifference_convergence Ω force g ε₀
    (forceDiffSobolevConst A B) he
    (forceDifference_sobolev_bound place D reference force ε₀ A B he1 hformula hsupport hleft hF hH hpacket hcorr)
end Force

section Energy
open BlowupDensity.Contracts.V1 (PacketImportAPI CorrectionAPI ThresholdAPI)
variable {ν : ℝ} (P : PacketImportAPI ν)
  (place : NSFormalization.Section3.T23.DomainPlacementData P.velocity P.pressure P.force P.carrier)
  {Ω : Set Space} {a : Space → Space} {g : VelocityField} {δ : ℝ}
  (D : NSFormalization.Section3.T23.CutoffData)
  (reference : NSFormalization.Section3.T23.ClassicalSolutionOmega ν Ω a g (place.T + δ))
  (C : CorrectionAPI ν P.toPacketAPI) (th : ThresholdAPI)

-- Consume the canonical implementation, retaining the identical correction.
example : (BlowupDensity.Bindings.scaling C th).correction = C := by
  rfl

example : ℝ := by
  exact energyConst (BlowupDensity.Bindings.scaling C th).correctionEnergyConst

example : 0 ≤ energyConst (BlowupDensity.Bindings.scaling C th).correctionEnergyConst := by
  exact energyConst_nonneg _

example (velocity : ℝ → VelocityField) (ε₀ : ℝ)
    (hT : C.T = place.T) (hx : C.x₀ = place.x₀)
    (hD : C.correction = D.correction)
    (he : ε₀ ≤ (BlowupDensity.Bindings.scaling C th).ε₀)
    (hformula : ∀ ε z, velocity ε z = reference.velocity z + D.correction ε z +
      NSFormalization.Section3.T15.scaledVelocity P.velocity place.x₀ place.T ε z) :
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      domainEnergyENorm Ω place.T (fun z => velocity ε z - reference.velocity z) ≤
        ENNReal.ofReal ((P.energyBound + P.dissipationBound) * ε ^ ((1 : ℝ) / 2) +
          energyConst (BlowupDensity.Bindings.scaling C th).correctionEnergyConst *
            ε ^ ((3 : ℝ) / 2)) := by
  have hwhole : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      NSFormalization.Section3.T24.energyENorm place.T
        (fun z => D.correction ε z + NSFormalization.Section3.T15.scaledVelocity
          P.velocity place.x₀ place.T ε z) ≤
        ENNReal.ofReal ((P.energyBound + P.dissipationBound) * ε ^ ((1 : ℝ) / 2) +
          (BlowupDensity.Bindings.scaling C th).correctionEnergyConst * ε ^ ((3 : ℝ) / 2)) := by
    intro ε hε
    have h := (BlowupDensity.Bindings.scaling C th).perturbationEnergyBound ε
      ⟨hε.1, hε.2.trans he⟩
    change NSFormalization.Section3.T24.energyENorm C.T
      (fun z => C.correction ε z + NSFormalization.Section3.T15.scaledVelocity
        P.velocity C.x₀ C.T ε z) ≤ _ at h
    rw [hT, hx, hD] at h
    exact h
  exact energyRate place D reference velocity P.energyBound P.dissipationBound
    (BlowupDensity.Bindings.scaling C th).correctionEnergyConst ε₀ hformula hwhole

-- The normalized q = 1 supplier clauses consumed by Rates.lean.
example (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (ε : ℝ) (hε : ε ∈ Ioc (0 : ℝ) (BlowupDensity.Bindings.scaling C th).ε₀) :
    NSFormalization.Section4.D01.forceSobolevENorm 1 s
      (NSFormalization.Section3.T15.scaledForce P.force C.x₀ C.T ε) ≤
      ENNReal.ofReal ((BlowupDensity.Bindings.scaling C th).positiveConst 1 s *
        (ε ^ ((1 : ℝ) / 2) + ε ^ ((1 : ℝ) / 2 - s))) := by
  have h := (BlowupDensity.Bindings.scaling C th).packetPositiveScaling 1 le_rfl s hs hs1 ε hε
  change NSFormalization.Section4.D01.forceSobolevENorm 1 s
    (NSFormalization.Section3.T15.scaledForce P.force C.x₀ C.T ε) ≤
    ENNReal.ofReal ((BlowupDensity.Bindings.scaling C th).positiveConst 1 s *
      (ε ^ (th.exponent (1 : ℝ≥0∞).toReal 0) +
        ε ^ (th.exponent (1 : ℝ≥0∞).toReal s))) at h
  simpa only [ENNReal.toReal_one, th.l1, sub_zero] using h

example (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (ε : ℝ) (hε : ε ∈ Ioc (0 : ℝ) (BlowupDensity.Bindings.scaling C th).ε₀) :
    NSFormalization.Section4.D01.forceSobolevENorm 1 s (C.forceCorrection ε) ≤
      ENNReal.ofReal ((BlowupDensity.Bindings.scaling C th).correctionPositiveConst 1 s *
        (ε ^ ((3 : ℝ) / 2) + ε ^ ((3 : ℝ) / 2 - s))) := by
  have h := (BlowupDensity.Bindings.scaling C th).correctionPositiveScaling 1 le_rfl s hs hs1 ε hε
  have h0 : th.exponent (1 : ℝ≥0∞).toReal 0 + 1 = (3 : ℝ) / 2 := by
    rw [ENNReal.toReal_one, th.l1]
    norm_num
  have hs' : th.exponent (1 : ℝ≥0∞).toReal s + 1 = (3 : ℝ) / 2 - s := by
    rw [ENNReal.toReal_one, th.l1]
    ring
  change _ ≤ ENNReal.ofReal (_ * (ε ^ (th.exponent _ 0 + 1) + ε ^ (th.exponent _ s + 1))) at h
  rw [h0, hs'] at h
  exact h
end Energy

-- Definition-level drift checks for the registered norm spelling.
example (s : ℝ) (f : VelocityField) :
    NSFormalization.Section4.D01.forceSobolevENorm 1 s f =
      BlowupDensity.Contracts.V1.Data.forceSobolevENorm 1 s f := rfl
example (T : ℝ) (f : VelocityField) :
    NSFormalization.Section3.T24.energyENorm T f =
      BlowupDensity.Contracts.V1.Data.energyENorm T f := rfl

end T23U6Probe
