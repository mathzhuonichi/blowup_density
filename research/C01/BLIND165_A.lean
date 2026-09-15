import Contracts.V3.EnergyAbsorptionPartial

/-! Independent manuscript-only C01 completion draft A. No witness is asserted. -/
noncomputable section
namespace BlowupDensity.Contracts.Blind165A
open Set MeasureTheory
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1 (laplacian)
open BlowupDensity.Contracts.V1.EnergyAbsorptionPartial
open BlowupDensity.Contracts.V2.EnergyAbsorptionPartial
open BlowupDensity.Contracts.V3.EnergyAbsorptionPartial
open scoped ENNReal

/-- Smallness concerns only times at which the solution is defined. -/
def Absorbs (C ν : ℝ) (u : SpaceTimeField) (S : ℝ) : Prop :=
  ∀ t ∈ Ico (0 : ℝ) S,
    ENNReal.ofReal C * criticalL3 (slice u t) ≤ ENNReal.ofReal (ν / 4)

/-- Actual angular inhomogeneous H² norm, not a substitute graph norm. -/
def h2Integral (u : SpaceTimeField) (S : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioo (0 : ℝ) S, sobolevENorm 2 (slice u t) ^ (2 : ℕ)

/-- All constants precede all solutions and viscosities. Inheritance is literal. -/
structure EnergyAbsorptionFullAPI extends EnergyAbsorptionPartialV3API where
  CRH1 : ℝ
  CRH1_pos : 0 < CRH1
  CH2 : ℝ
  CH2_pos : 0 < CH2
  Cassembly : ℝ
  Cassembly_pos : 0 < Cassembly

  /-- Testing against -Δu: positive transport work, negative force work. -/
  enstrophyIdentity :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ioo (0 : ℝ) T,
          HasDerivAt (fun s => gradientSq (slice w.velocity s))
            (-2 * ν * laplacianSq (slice w.velocity t) +
              2 * advectionWork (slice w.velocity t) -
              2 * pairing (slice f t) (laplacian (slice w.velocity t))) t

  /-- eq:RH1, local in time; no derivative existence assumed in the API overall. -/
  enstrophyDifferentialBound :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ioo (0 : ℝ) T,
          ENNReal.ofReal C₁ * criticalL3 (slice w.velocity t) ≤
              ENNReal.ofReal (ν / 4) →
          ∀ E' : ℝ, HasDerivAt (fun s => gradientSq (slice w.velocity s)) E' t →
            E' + ν * laplacianSq (slice w.velocity t) ≤
              CRH1 * ν⁻¹ * l2Sq (slice f t)

  /-- Integrated eq:RH1 at an actual presingular time, including t = 0. -/
  enstrophyIntegralBound :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ico (0 : ℝ) T,
          Absorbs C₁ ν w.velocity t →
          gradientSq (slice w.velocity t) +
              ν * (∫ s in (0 : ℝ)..t, laplacianSq (slice w.velocity s)) ≤
            gradientSq a + CRH1 * ν⁻¹ * (∫ s in (0 : ℝ)..t, l2Sq (slice f s))

  /-- Endpoint dissipation includes S = T but never evaluates u(T). -/
  laplacianTimeIntegral :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ S : ℝ, 0 ≤ S → S ≤ T →
          Absorbs C₁ ν w.velocity S →
          (∫⁻ t in Ioo (0 : ℝ) S, ENNReal.ofReal (laplacianSq (slice w.velocity t))) ≤
            ENNReal.ofReal (ν⁻¹ * gradientSq a +
              CRH1 * (ν⁻¹) ^ 2 * (∫ t in (0 : ℝ)..S, l2Sq (slice f t)))

  /-- The Fourier weight inequality (1+r²)² ≤ 2(1+r⁴). -/
  sobolevTwoFourier :
    ∀ z : SpatialField, MemHInfty z →
      sobolevENorm 2 z ^ (2 : ℕ) ≤ ENNReal.ofReal (CH2 * (l2Sq z + laplacianSq z))

  /-- eq:4.3 continuation calculation, valid at a possibly singular endpoint. -/
  h2TimeIntegral :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ S : ℝ, 0 ≤ S → S ≤ T →
          Absorbs C₁ ν w.velocity S →
          h2Integral w.velocity S ≤
            ENNReal.ofReal (Cassembly * S * energyBudget a f S ^ 2 +
              Cassembly * ν⁻¹ * gradientSq a +
              Cassembly * (ν⁻¹) ^ 2 * (∫ t in (0 : ℝ)..S, l2Sq (slice f t)))

  /-- The zero-datum instance consumed in §4.4; force norms need not be small. -/
  h2TimeIntegralZeroDatum :
    ∀ (ν : ℝ), 0 < ν → ∀ f : SpaceTimeField, MemForceR f →
      ∀ (T : ℝ) (w : ClassicalSolutionR ν (fun _ => 0) f T),
        ∀ S : ℝ, 0 ≤ S → S ≤ T → Absorbs C₁ ν w.velocity S →
          h2Integral w.velocity S ≤
            ENNReal.ofReal (Cassembly * S * forcePrimitive f S ^ 2 +
              Cassembly * (ν⁻¹) ^ 2 * (∫ t in (0 : ℝ)..S, l2Sq (slice f t)))

end BlowupDensity.Contracts.Blind165A
