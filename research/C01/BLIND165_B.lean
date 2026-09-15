import Contracts.V3.EnergyAbsorptionPartial

/- Independent paper-only statement draft B. No witness is asserted. -/
noncomputable section
namespace BlowupDensity.Research.C01.Blind165B
open Set MeasureTheory
open NSFormalization.Paper3
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1 (laplacian)
open BlowupDensity.Contracts.V1.EnergyAbsorptionPartial
open BlowupDensity.Contracts.V2.EnergyAbsorptionPartial
open BlowupDensity.Contracts.V3.EnergyAbsorptionPartial
open scoped ENNReal

/-- Smallness is imposed only on the interval being estimated. -/
def AbsorptionOn (C ν : ℝ) (u : SpaceTimeField) (S : ℝ) : Prop :=
  ∀ t ∈ Ico (0 : ℝ) S,
    criticalL3 (slice u t) ≤ ENNReal.ofReal (ν / (4 * C))

/-- Full ordinary-energy, H¹ absorption and H²-integral interface of §4:106–131.
All constants precede all viscosities, data, forces, solutions and horizons. -/
structure EnergyAbsorptionFullBAPI extends EnergyAbsorptionPartialV3API where
  CRH1 : ℝ
  CRH1_pos : 0 < CRH1
  CH2 : ℝ
  CH2_pos : 0 < CH2
  Cassembly : ℝ
  Cassembly_pos : 0 < Cassembly
  /-- Testing against -Δu; the sign of nonlinear work is positive on the RHS. -/
  enstrophyIdentity :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ioo (0 : ℝ) T,
          HasDerivAt (fun s => gradientSq (slice w.velocity s))
            (-2 * ν * laplacianSq (slice w.velocity t) +
              2 * advectionWork (slice w.velocity t) -
              2 * pairing (slice f t) (laplacian (slice w.velocity t))) t
  /-- eq:RH1, with a pointwise L³ threshold and no assumed derivative regularity. -/
  enstrophyAbsorption :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ioo (0 : ℝ) T,
          criticalL3 (slice w.velocity t) ≤ ENNReal.ofReal (ν / (4 * C₁)) →
          ∀ E' : ℝ, HasDerivAt (fun s => gradientSq (slice w.velocity s)) E' t →
            E' + ν * laplacianSq (slice w.velocity t) ≤
              CRH1 * ν⁻¹ * l2Sq (slice f t)
  /-- Integrated eq:RH1 at ordinary presingular times; initial energy is retained. -/
  enstrophyIntegrated :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ico (0 : ℝ) T,
          AbsorptionOn C₁ ν w.velocity t →
          IntegrableOn (fun s => laplacianSq (slice w.velocity s)) (Ioo 0 t) ∧
          gradientSq (slice w.velocity t) +
              ν * (∫ s in Ioo (0 : ℝ) t, laplacianSq (slice w.velocity s)) ≤
            gradientSq a + CRH1 * ν⁻¹ * (∫ s in Ioo (0 : ℝ) t, l2Sq (slice f s))
  /-- Endpoint passage controls dissipation without asserting a velocity at T. -/
  laplacianTimeIntegral :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ S : ℝ,
          0 ≤ S → S ≤ T → AbsorptionOn C₁ ν w.velocity S →
          IntegrableOn (fun s => laplacianSq (slice w.velocity s)) (Ioo 0 S) ∧
          (∫ s in Ioo (0 : ℝ) S, laplacianSq (slice w.velocity s)) ≤
            ν⁻¹ * gradientSq a +
              CRH1 * ν⁻¹ ^ 2 * (∫ s in Ioo (0 : ℝ) S, l2Sq (slice f s))
  /-- §4:121–124, genuine angular Sobolev norm, not a derivative proxy. -/
  sobolevTwoFourier :
    ∀ z : SpatialField, MemHInfty z → ∀ A : RealVectorSobolev 2,
      IsSobolevDatum 2 z A → ‖A‖ ^ 2 ≤ CH2 * (l2Sq z + laplacianSq z)
  /-- §4:127–130. Integrability is a conclusion, preventing totalized-integral vacuity.
  A datum path is only a representation of u; no additional smoothness is assumed. -/
  h2TimeIntegral :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ S : ℝ,
          0 ≤ S → S ≤ T → AbsorptionOn C₁ ν w.velocity S →
          ∀ G : ℝ → RealVectorSobolev 2,
            (∀ t ∈ Ioo (0 : ℝ) S, IsSobolevDatum 2 (slice w.velocity t) (G t)) →
            IntegrableOn (fun t => ‖G t‖ ^ 2) (Ioo 0 S) ∧
            (∫ t in Ioo (0 : ℝ) S, ‖G t‖ ^ 2) ≤
              Cassembly * S * energyBudget a f S ^ 2 +
              Cassembly * ν⁻¹ * gradientSq a +
              Cassembly * ν⁻¹ ^ 2 * (∫ t in Ioo (0 : ℝ) S, l2Sq (slice f t))
end BlowupDensity.Research.C01.Blind165B
