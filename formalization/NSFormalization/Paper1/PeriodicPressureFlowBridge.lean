import NSFormalization.Paper1.PeriodicPressureRecoveryBridge
import NSFormalization.Paper1.PeriodicPressureSymbolOperator

/-!
# Conditional bridge from Fourier pressure certificates to a periodic `Flow`

No Fourier reconstruction is assumed.  The coefficient certificate and its
identification with a physical pressure witness are explicit fields.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicPressureFlowBridge

open Set
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Paper1.PeriodicLifespan
open NSFormalization.Paper1.PeriodicPressureSymbol
open NSFormalization.Paper1.PeriodicPressureRecoveryBridge
open NavierStokes.PeriodicIntegration
open NSFormalization.Paper1.PeriodicLocalLifespan
open NSFormalization.Paper1.PeriodicPressureNormalization

/-- A zero-mode-compatible discrete Poisson certificate. -/
structure FourierPressureCertificate (g p : PeriodicFrequency → ℂ) : Prop where
  source_zero : g 0 = 0
  pressure_zero : p 0 = 0
  equation : ∀ k, -(laplaceEigenvalue k : ℂ) * p k = g k

theorem FourierPressureCertificate.unique {g p q : PeriodicFrequency → ℂ}
    (hp : FourierPressureCertificate g p)
    (hq : FourierPressureCertificate g q) : p = q := by
  exact pressureCoeff_unique g p hp.pressure_zero hp.equation
    |>.trans (pressureCoeff_unique g q hq.pressure_zero hq.equation).symm

/-- A supplied identification of a coefficient certificate with a physical
`Flow` pressure witness.  This does not assert Fourier reconstruction. -/
structure FlowPressureWitness {ν S : ℝ} {a : Space → Space} {f : VelocityField}
    (W : Flow ν a f S) (g p : PeriodicFrequency → ℂ) where
  certificate : FourierPressureCertificate g p
  physical_pressure : PressureField
  physical_agreement : physical_pressure = W.pressure

/-- Explicit contract for the missing mild-to-classical pressure bridge. -/
structure MildPressureResidualContract (M : Prop)
    {ν S : ℝ} {a : Space → Space} {f : VelocityField}
    (W : Flow ν a f S) (g p : PeriodicFrequency → ℂ) where
  mild_divergence_free : M
  pressure_witness : FlowPressureWitness W g p

theorem MildPressureResidualContract.normalized_residual
    {M : Prop} {ν S : ℝ} {a : Space → Space} {f : VelocityField}
    {W : Flow ν a f S} {g p : PeriodicFrequency → ℂ}
    (H : MildPressureResidualContract M W g p)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) S) (x : Space) :
    NSFormalization.Source.residual ν
        (normalizedFlow W).velocity (normalizedFlow W).pressure t x = f (t, x) :=
  normalizedFlow_equation W ht x




theorem normalized_pressure_zero_mean_witness {ν S : ℝ} {a : Space → Space}
    {f : VelocityField} (W : Flow ν a f S) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) S) :
    cubeIntegral (fun x : Space => gaugePressure W (t, x)) = 0 :=
  gaugePressure_zero_mean W ht

theorem normalized_pressure_preserves_witness_residual
    {ν S : ℝ} {a : Space → Space} {f : VelocityField}
    (W : Flow ν a f S) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) S) (x : Space) :
    NSFormalization.Source.residual ν W.velocity (gaugePressure W) t x =
      NSFormalization.Source.residual ν W.velocity W.pressure t x :=
  gaugePressure_residual_eq W ht x

/-- An explicit physical residual certificate yields the canonical normalized
flow witness.  The supplied `Flow` remains the source of existence; this
theorem only packages gauge normalization and residual preservation. -/
theorem normalized_flow_witness_of_residual
    {ν S : ℝ} {a : Space → Space} {f : VelocityField}
    (W : Flow ν a f S)
    (hres : ∀ t ∈ Ioo (0 : ℝ) S, ∀ x : Space,
      NSFormalization.Source.residual ν W.velocity W.pressure t x = f (t, x)) :
    ∃ U : Flow ν a f S, IsNormalized U ∧
      (∀ t ∈ Ioo (0 : ℝ) S, ∀ x : Space,
        NSFormalization.Source.residual ν U.velocity U.pressure t x = f (t, x)) := by
  refine ⟨normalizedFlow W, normalizedFlow_isNormalized W, ?_⟩
  intro t ht x
  change NSFormalization.Source.residual ν W.velocity (gaugePressure W) t x = f (t, x)
  calc
    _ = NSFormalization.Source.residual ν W.velocity W.pressure t x :=
      gaugePressure_residual_eq W ⟨ht.1.le, ht.2⟩ x
    _ = f (t, x) := hres t ht x

/-- A Fourier/physical pressure witness restricts without changing its
coefficient certificate.  The physical pressure agreement is preserved
because `Flow.restrict` changes only proof fields. -/
def FlowPressureWitness.restrict
    {ν S R : ℝ} {a : Space → Space} {f : VelocityField}
    {W : Flow ν a f S} {g p : PeriodicFrequency → ℂ}
    (H : FlowPressureWitness W g p) (hR : 0 < R) (hRS : R ≤ S) :
    FlowPressureWitness (W.restrict hR hRS) g p := by
  refine ⟨H.certificate, H.physical_pressure, ?_⟩
  exact H.physical_agreement

/-- Restriction is compatible with the canonical pressure gauge on the
shorter physical slab. -/
theorem restricted_witness_gauge_agrees
    {ν S R : ℝ} {a : Space → Space} {f : VelocityField}
    {W : Flow ν a f S} {g p : PeriodicFrequency → ℂ}
    (H : FlowPressureWitness W g p) (hR : 0 < R) (hRS : R ≤ S)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) R) (x : Space) :
    gaugePressure (W.restrict hR hRS) (t, x) = gaugePressure W (t, x) := by
  exact gaugePressure_restrict_eq W hR hRS ht x

/-- The restricted witness remains a normalized forced solution on the open
interior of its shorter horizon. -/
theorem restricted_witness_normalized_equation
    {ν S R : ℝ} {a : Space → Space} {f : VelocityField}
    {W : Flow ν a f S} {g p : PeriodicFrequency → ℂ}
    (H : FlowPressureWitness W g p) (hR : 0 < R) (hRS : R ≤ S)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) R) (x : Space) :
    NSFormalization.Source.residual ν
        (normalizedFlow (W.restrict hR hRS)).velocity
        (normalizedFlow (W.restrict hR hRS)).pressure t x = f (t, x) := by
  exact normalizedFlow_restrict_equation W hR hRS ht x

/-- Combined restart compatibility: the restricted gauge agrees with the
original gauge on its slab, and the normalized restriction satisfies the
forced residual equation in its interior. -/
theorem restricted_witness_gauge_residual_pair
    {ν S R : ℝ} {a : Space → Space} {f : VelocityField}
    {W : Flow ν a f S} {g p : PeriodicFrequency → ℂ}
    (H : FlowPressureWitness W g p) (hR : 0 < R) (hRS : R ≤ S)
    {t : ℝ} (htIco : t ∈ Ico (0 : ℝ) R)
    (htIoo : t ∈ Ioo (0 : ℝ) R) (x : Space) :
    gaugePressure (W.restrict hR hRS) (t, x) = gaugePressure W (t, x) ∧
      NSFormalization.Source.residual ν
          (normalizedFlow (W.restrict hR hRS)).velocity
          (normalizedFlow (W.restrict hR hRS)).pressure t x = f (t, x) := by
  exact ⟨restricted_witness_gauge_agrees H hR hRS htIco x,
    restricted_witness_normalized_equation H hR hRS htIoo x⟩

/-- High-level restriction summary exposing normalization and both
compatibility facts for downstream restart assembly. -/
theorem restricted_witness_summary
    {ν S R : ℝ} {a : Space → Space} {f : VelocityField}
    {W : Flow ν a f S} {g p : PeriodicFrequency → ℂ}
    (H : FlowPressureWitness W g p) (hR : 0 < R) (hRS : R ≤ S) :
    IsNormalized (normalizedFlow (W.restrict hR hRS)) ∧
      (∀ t ∈ Ico (0 : ℝ) R, ∀ x : Space,
        gaugePressure (W.restrict hR hRS) (t, x) = gaugePressure W (t, x)) ∧
      (∀ t ∈ Ioo (0 : ℝ) R, ∀ x : Space,
        NSFormalization.Source.residual ν
            (normalizedFlow (W.restrict hR hRS)).velocity
            (normalizedFlow (W.restrict hR hRS)).pressure t x = f (t, x)) := by
  refine ⟨normalizedFlow_isNormalized (W.restrict hR hRS), ?_, ?_⟩
  · intro t ht x
    exact restricted_witness_gauge_agrees H hR hRS ht x
  · intro t ht x
    exact restricted_witness_normalized_equation H hR hRS ht x

/-- Restriction leaves the unique Fourier pressure certificate unchanged. -/
theorem restricted_witness_certificate_unique
    {ν S R : ℝ} {a : Space → Space} {f : VelocityField}
    {W : Flow ν a f S} {g p q : PeriodicFrequency → ℂ}
    (H : FlowPressureWitness W g p) (Hq : FourierPressureCertificate g q)
    (hR : 0 < R) (hRS : R ≤ S) :
    p = q := by
  exact H.certificate.unique Hq

/-- Combined certificate and physical restart summary. -/
theorem restricted_witness_certificate_and_summary
    {ν S R : ℝ} {a : Space → Space} {f : VelocityField}
    {W : Flow ν a f S} {g p q : PeriodicFrequency → ℂ}
    (H : FlowPressureWitness W g p) (Hq : FourierPressureCertificate g q)
    (hR : 0 < R) (hRS : R ≤ S) :
    (p = q) ∧
      IsNormalized (normalizedFlow (W.restrict hR hRS)) ∧
      (∀ t ∈ Ico (0 : ℝ) R, ∀ x : Space,
        gaugePressure (W.restrict hR hRS) (t, x) = gaugePressure W (t, x)) ∧
      (∀ t ∈ Ioo (0 : ℝ) R, ∀ x : Space,
        NSFormalization.Source.residual ν
            (normalizedFlow (W.restrict hR hRS)).velocity
            (normalizedFlow (W.restrict hR hRS)).pressure t x = f (t, x)) := by
  refine ⟨restricted_witness_certificate_unique H Hq hR hRS, ?_⟩
  exact restricted_witness_summary H hR hRS


end NSFormalization.Paper1.PeriodicPressureFlowBridge
