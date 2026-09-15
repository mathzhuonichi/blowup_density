import Contracts.V3.EnergyAbsorptionPartial

/-!
# Full C01 ordinary-energy and H¹-absorption interface, version 4

Extends the frozen V3 interface without changing any inherited field. Adds the
six remaining mathematical fields of `research/C01/Spec.lean:487–607`, with
its three global positive constants (`:266–281`). The statement reconciliation
is recorded in `research/C01/COMPARISON_165.md`.

Scope: ordinary energy, enstrophy absorption and the actual angular H² time
integral in `paper/sections/04-whole-space.tex:106–130`, reused at `:171`.
Critical half-order estimates, bootstrap, Grönwall and continuation remain
separate downstream results. This module defines the interface only.

All quantities are imported from frozen Contracts, with no redefinitions.
The new field types match the original specification verbatim. In particular,
interval integrability is proved, never assumed; S=T is permitted only for
the open-interval H² integral; constants are selected before ν and all data.
-/
noncomputable section
namespace BlowupDensity.Contracts.V4.EnergyAbsorption
open Set MeasureTheory
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1 (laplacian)
open BlowupDensity.Contracts.V1.EnergyAbsorptionPartial
open BlowupDensity.Contracts.V2.EnergyAbsorptionPartial
open BlowupDensity.Contracts.V3.EnergyAbsorptionPartial
open scoped ENNReal

/-- Complete C01 interface. The inherited V3 projection preserves all earlier obligations. -/
structure EnergyAbsorptionAPI extends EnergyAbsorptionPartialV3API where
  /-- Universal constant in eq:RH1; independent of viscosity, horizon and fields. -/
  CRH1 : ℝ
  CRH1_pos : 0 < CRH1
  /-- Universal constant in the angular H² Fourier inequality. -/
  CH2 : ℝ
  CH2_pos : 0 < CH2
  /-- One universal constant for all three H² assembly summands. -/
  Cassembly : ℝ
  Cassembly_pos : 0 < Cassembly

  /-- 04-whole-space.tex:106–112: exact test against -Δu, including derivative existence and pressure cancellation. -/
  enstrophyIdentity :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ioo (0 : ℝ) T,
          HasDerivAt (fun s => gradientSq (slice w.velocity s))
            (2 * advectionWork (slice w.velocity t) -
              2 * ν * laplacianSq (slice w.velocity t) -
              2 * pairing (slice f t) (laplacian (slice w.velocity t))) t

  /-- 04-whole-space.tex:112–115: eq:RH1 under the inherited C₁ times L³ absorption threshold. -/
  enstrophyDifferentialBound :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ioo (0 : ℝ) T,
          ENNReal.ofReal C₁ * criticalL3 (slice w.velocity t) ≤
              ENNReal.ofReal (ν / 4) →
            ∀ E' : ℝ, HasDerivAt (fun s => gradientSq (slice w.velocity s)) E' t →
              E' + ν * laplacianSq (slice w.velocity t) ≤
                CRH1 * ν⁻¹ * l2Sq (slice f t)

  /-- 04-whole-space.tex:114–117: integrate eq:RH1 at t<T; integrability is a conclusion. -/
  enstrophyIntegralBound :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ico (0 : ℝ) T,
          (∀ s ∈ Ico (0 : ℝ) t, ENNReal.ofReal C₁ * criticalL3 (slice w.velocity s) ≤
              ENNReal.ofReal (ν / 4)) →
            IntervalIntegrable (fun s => laplacianSq (slice w.velocity s)) volume 0 t ∧
              gradientSq (slice w.velocity t) +
                  ν * ∫ s in (0 : ℝ)..t, laplacianSq (slice w.velocity s) ≤
                gradientSq a + CRH1 * ν⁻¹ * ∫ s in (0 : ℝ)..t, l2Sq (slice f s)

  /-- 04-whole-space.tex:121–124: actual angular H² norm bounded by L² and Laplacian squares. -/
  sobolevTwoFourier :
    ∀ z : SpatialField, MemHInfty z →
      sobolevENorm 2 z ^ (2 : ℝ) ≤
        ENNReal.ofReal (CH2 * (l2Sq z + laplacianSq z))

  /-- 04-whole-space.tex:119–130: H² time bound for 0<S≤T, including S=T without evaluating u(T). -/
  h2TimeIntegral :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T) (S : ℝ), 0 < S → S ≤ T →
          (∀ t ∈ Ico (0 : ℝ) S, ENNReal.ofReal C₁ * criticalL3 (slice w.velocity t) ≤
              ENNReal.ofReal (ν / 4)) →
            ∫⁻ t in Ioo (0 : ℝ) S, sobolevENorm 2 (slice w.velocity t) ^ (2 : ℝ) ≤
              ENNReal.ofReal
                (Cassembly * S * energyBudget a f S ^ 2 +
                  Cassembly * ν⁻¹ * gradientSq a +
                  Cassembly * (ν⁻¹) ^ 2 * ∫ s in (0 : ℝ)..S, l2Sq (slice f s))

  /-- 04-whole-space.tex:137–141,171: zero initial datum, with the same global assembly constant. -/
  h2TimeIntegralZeroDatum :
    ∀ (ν : ℝ), 0 < ν → ∀ f : SpaceTimeField, MemForceR f →
      ∀ (T : ℝ) (w : ClassicalSolutionR ν (fun _ => 0) f T) (S : ℝ), 0 < S → S ≤ T →
        (∀ t ∈ Ico (0 : ℝ) S, ENNReal.ofReal C₁ * criticalL3 (slice w.velocity t) ≤
            ENNReal.ofReal (ν / 4)) →
          ∫⁻ t in Ioo (0 : ℝ) S, sobolevENorm 2 (slice w.velocity t) ^ (2 : ℝ) ≤
            ENNReal.ofReal
              (Cassembly * S * forcePrimitive f S ^ 2 +
                Cassembly * (ν⁻¹) ^ 2 * ∫ s in (0 : ℝ)..S, l2Sq (slice f s))

end BlowupDensity.Contracts.V4.EnergyAbsorption
