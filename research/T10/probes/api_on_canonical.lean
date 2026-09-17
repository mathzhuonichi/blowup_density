import NSFormalization.Section3.T10.PeriodicData
import Contracts.V1.Data

noncomputable section

namespace NSFormalization.Section3.T10

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal BigOperators

/-! The five local TorusCube declarations are reused definitionally. -/

example : PeriodicFrequency = NSFormalization.Paper1.PeriodicFrequency := rfl

example : PeriodicTorus = NSFormalization.Paper1.PeriodicTorus := rfl

example : (periodicTorusMeasure : Measure PeriodicTorus) =
    NSFormalization.Paper1.periodicTorusMeasure := rfl

example : (torusLift : (Space → Space) → PeriodicTorus → Space) =
    NSFormalization.Paper1.torusLift := rfl

example : (periodicFourierCoeff : (Space → ℂ) → PeriodicFrequency → ℂ) =
    NSFormalization.Paper1.periodicFourierCoeff := rfl

/-! ## Reconciled consumer-facing facts -/

/-- Basic facts of the periodic data layer selected by
`research/T10/RECONCILIATION.md`.  Every field is a concrete mathematical
statement over the definitions above; there is no unspecified proposition
parameter and no placeholder field. -/
structure TorusDataAPI : Prop where
  /-- `01-introduction.tex:83-103`: weighted Fourier data representing one
  physical periodic field are unique.

  Exact quantifier order: `∀ s, ∀ z, ∀ A, ∀ B`, followed by the two datum
  hypotheses.

  Non-vacuity: the conclusion is equality in the complete real coefficient
  carrier, not equality of an auxiliary proposition or an existential shadow. -/
  datum_unique :
    ∀ (s : ℝ) (z : SpatialField) (A B : PeriodicSobolev s),
      IsPeriodicDatum s z A → IsPeriodicDatum s z B → A = B

  /-- `02-preliminaries.tex:72-73`: an `IsPeriodicDatum` has the manuscript's
  conjugate-reflection symmetry.

  Exact quantifier order: `∀ s, ∀ z, ∀ A`, datum membership, then
  `∀ i : Fin 3, ∀ k : PeriodicFrequency`.

  Non-vacuity: this exposes an equality of actual complex Fourier
  coefficients at `k` and `-k`; it is the public fact that the datum lands in
  the real closed submodule. -/
  datum_real :
    ∀ (s : ℝ) (z : SpatialField) (A : PeriodicSobolev s),
      IsPeriodicDatum s z A →
        ∀ (i : Fin 3) (k : PeriodicFrequency), A.1 i (-k) = star (A.1 i k)

  /-- `01-introduction.tex:83-103`: vector Parseval in the forward direction.

  Exact quantifier order: `∀ z, ∀ A`, followed by the order-zero datum
  hypothesis, then physical `L²` membership of the lift (lead amendment,
  `RECONCILIATION.md` §5: the datum alone only gives `L¹`, and the identity
  is the paper's `L²` Parseval).

  Non-vacuity: it equates the extended norm of a concrete coefficient datum
  with the physical Haar `L²(T³)` norm, including the normalization constant. -/
  parseval_forward :
    ∀ (z : SpatialField) (A : PeriodicSobolev 0), IsPeriodicDatum 0 z A →
      MemLp (torusLift z) 2 periodicTorusMeasure →
      ‖A‖ₑ = eLpNorm (torusLift z) 2 periodicTorusMeasure

  /-- `01-introduction.tex:83-103`: vector Parseval in the reverse direction.

  Exact quantifier order: `∀ z`, physical periodicity, then physical `L²`
  membership, then `∃ A`.

  Non-vacuity: the conclusion supplies an inhabitant of the real complete
  coefficient carrier whose coefficients are pinned by `IsPeriodicDatum`. -/
  parseval_backward :
    ∀ z : SpatialField, IsPeriodicSpatial z →
      MemLp (torusLift z) 2 periodicTorusMeasure →
        ∃ A : PeriodicSobolev 0, IsPeriodicDatum 0 z A

  /-- `03-torus.tex:2-4` and the physical representation (P): lifting to the
  quotient torus is injective on unit-periodic physical vector fields.

  Exact quantifier order: `∀ z, ∀ w`, the two periodicity hypotheses, then
  equality of their torus lifts.

  Non-vacuity: the conclusion is pointwise equality of the original physical
  fields, so no information is lost by the chosen `(0,1]³` representative. -/
  torusLift_injective :
    ∀ z w : SpatialField, IsPeriodicSpatial z → IsPeriodicSpatial w →
      torusLift z = torusLift w → z = w

  /-- `03-torus.tex:2-4` and the physical representation (P): every torus
  vector field has a unit-periodic physical representative.

  Exact quantifier order: `∀ Z : PeriodicTorus → Space`, then `∃ z` carrying
  periodicity and exact lift equality.

  Non-vacuity: the witness is a physical `Space → Space` field, and its lift
  must equal the caller's entire torus function. -/
  torusLift_surjective :
    ∀ Z : PeriodicTorus → Space,
      ∃ z : SpatialField, IsPeriodicSpatial z ∧ torusLift z = Z

  /-- `03-torus.tex:395-411`: the normalized mean gives the literal
  constant/mean-zero decomposition.

  Exact quantifier order: `∀ z`, periodicity, Haar integrability, then the
  reconstruction identity and zero-mean conclusion.

  Non-vacuity: the field is reconstructed pointwise for every `x`, and the
  second conjunct is the actual Haar-integral equation `meanT = 0`. -/
  mean_decomposition :
    ∀ z : SpatialField, IsPeriodicSpatial z →
      Integrable (torusLift z) periodicTorusMeasure →
        (∀ x : Space, constantPartT z x + meanZeroPartT z x = z x) ∧
          IsMeanZeroT (meanZeroPartT z)

  /-- `01-introduction.tex:105-109` and `03-torus.tex:395-411`: removing the
  mean removes exactly the zero Fourier mode at every Sobolev order.

  Exact quantifier order: `∀ s, ∀ z, ∀ A`, the datum hypothesis, then `∃ B`
  with both its physical realization and zero-mode membership.

  Non-vacuity: the existential datum represents the concrete field
  `meanZeroPartT z` and belongs to the concrete submodule
  `meanZeroPeriodicSobolev s`. -/
  meanZero_datum :
    ∀ (s : ℝ) (z : SpatialField) (A : PeriodicSobolev s),
      IsPeriodicDatum s z A →
        ∃ B : PeriodicSobolev s,
          IsPeriodicDatum s (meanZeroPartT z) B ∧ B ∈ meanZeroPeriodicSobolev s

  /-- `02-preliminaries.tex:76-80`: the coefficient formula defines the
  periodic Leray projection, which is a contraction and has solenoidal range.

  Exact quantifier order: `∀ s, ∀ A`, then `∃ B`; the returned datum carries
  the graph equation, norm bound, and solenoidality together.

  Non-vacuity: `B` is an element of the same complete real Hilbert carrier as
  `A`, not merely a coefficient function outside `ℓ²`. -/
  leray_exists_contraction :
    ∀ (s : ℝ) (A : PeriodicSobolev s),
      ∃ B : PeriodicSobolev s,
        IsPeriodicLerayDatum A B ∧ ‖B‖ ≤ ‖A‖ ∧ IsSolenoidalPeriodicDatum B

  /-- `02-preliminaries.tex:76-80`: the periodic Leray map is idempotent.

  Exact quantifier order: `∀ s, ∀ A, ∀ B, ∀ C`, followed by the graph
  equations `B=P A` and `C=P B`.

  Non-vacuity: the conclusion identifies two concrete same-order data, and so
  states projector idempotence rather than only coefficientwise solenoidality. -/
  leray_projector :
    ∀ (s : ℝ) (A B C : PeriodicSobolev s),
      IsPeriodicLerayDatum A B → IsPeriodicLerayDatum B C → C = B

  /-- `02-preliminaries.tex:76-80`: the periodic Leray map fixes every
  solenoidal datum.

  Exact quantifier order: `∀ s, ∀ A, ∀ B`, solenoidality of `A`, then the
  graph equation `B=P A`.

  Non-vacuity: the conclusion is equality in `PeriodicSobolev s`, making the
  range/fixed-point characterization directly usable. -/
  leray_fixes_solenoidal :
    ∀ (s : ℝ) (A B : PeriodicSobolev s), IsSolenoidalPeriodicDatum A →
      IsPeriodicLerayDatum A B → B = A

  /-- `02-preliminaries.tex:79-80`: Leray commutes with scalar Bessel
  reweighting between any two Sobolev orders.

  Exact quantifier order: `∀ s, ∀ t, ∀ A, ∀ B, ∀ PA, ∀ PB`, followed by the
  reweight and two Leray graph hypotheses.

  Non-vacuity: the conclusion is the coefficientwise relation transporting
  `PA` from order `s` to `PB` at order `t`; it is not an untyped commutation
  slogan. -/
  leray_commutes_weight :
    ∀ (s t : ℝ) (A : PeriodicSobolev s) (B : PeriodicSobolev t)
        (PA : PeriodicSobolev s) (PB : PeriodicSobolev t),
      IsPeriodicReweight s t A B → IsPeriodicLerayDatum A PA →
        IsPeriodicLerayDatum B PB → IsPeriodicReweight s t PA PB

  /-- `02-preliminaries.tex:76-80` and `03-torus.tex:395-411`: Leray preserves
  the mean-zero coefficient subspace because its zero-mode symbol is identity.

  Exact quantifier order: `∀ s, ∀ A, ∀ B`, zero-mode membership of `A`, then
  the Leray graph equation.

  Non-vacuity: the result is membership of the actual output datum in the
  closed zero-mode submodule. -/
  leray_preserves_meanZero :
    ∀ (s : ℝ) (A B : PeriodicSobolev s), A ∈ meanZeroPeriodicSobolev s →
      IsPeriodicLerayDatum A B → B ∈ meanZeroPeriodicSobolev s

  /-- `02-preliminaries.tex:28,84-88` and `03-torus.tex:319`: subtracting the
  spatial pressure mean produces the chosen gauge without changing its spatial
  gradient or the momentum equation.

  Exact quantifier order: `∀ I, ∀ p`, periodicity and slice integrability,
  then the normalized periodicity/gauge conclusions and finally
  `∀ ν, ∀ u, ∀ f, ∀ t ∈ I, ∀ x` for equation preservation.

  Non-vacuity: the result simultaneously supplies the normalized periodic
  pressure, its zero integral, pointwise gradient equality, and preservation of
  every concrete Navier--Stokes residual equation on `I`. -/
  pressure_normalization :
    ∀ (I : Set ℝ) (p : SpaceTimeScalar), IsPeriodicOn I p →
      (∀ t ∈ I, Integrable (torusLift (fun x ↦ p (t, x))) periodicTorusMeasure) →
        IsPeriodicOn I (normalizePressureT p) ∧
        PressureGaugeT I (normalizePressureT p) ∧
        (∀ t ∈ I, ∀ x : Space,
          pressureGradient (normalizePressureT p) t x = pressureGradient p t x) ∧
        ∀ (ν : ℝ) (u : SpaceTimeField) (f : SpaceTimeField),
          ∀ t ∈ I, ∀ x : Space,
            NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x = f (t, x) →
              NavierStokesR3.ProblemStatement.navierStokesResidual ν u
                (normalizePressureT p) t x = f (t, x)

  /-- `01-introduction.tex:143-150` and `03-torus.tex:299,540-561`: the
  coefficient `E_T` expression agrees with the physical Haar-space expression
  on every classical periodic velocity.

  Exact quantifier order: `∀ ν, ∀ a, ∀ f, ∀ T`, then
  `∀ U : ClassicalSolutionT ν a f T`.

  Non-vacuity: this equates two independently defined `ℝ≥0∞` quantities on the
  concrete velocity carried by a genuine classical solution. -/
  energy_eq_physical :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ),
      ∀ U : ClassicalSolutionT ν a f T,
        coefficientEnergyENormT T U.velocity = energyENormT T U.velocity

  /-- `02-preliminaries.tex:32-36,105-114`: a classical periodic solution
  transports to every shorter positive horizon without changing its fields.

  Exact quantifier order: `∀ ν, ∀ a, ∀ f, ∀ T, ∀ U, ∀ S`, positivity of `S`,
  then `S ≤ T`, then `∃ V`.

  Non-vacuity: `V` is a full `ClassicalSolutionT` and both its velocity and
  pressure are pinned to those of the given solution. -/
  classicalSolution_restrict :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
        (U : ClassicalSolutionT ν a f T) (S : ℝ),
      0 < S → S ≤ T →
        ∃ V : ClassicalSolutionT ν a f S,
          V.velocity = U.velocity ∧ V.pressure = U.pressure

  /-- `01-introduction.tex:4-7` and `02-preliminaries.tex:32-36`: the solution
  predicate transports across forces equal at every interior spacetime point.

  Exact quantifier order: `∀ ν, ∀ a, ∀ f, ∀ T, ∀ U, ∀ g`, pointwise force
  equality with order `∀ t ∈ Ioo 0 T, ∀ x`, then `∃ V`.

  Non-vacuity: the witness is a full classical solution for the replacement
  force and retains the original velocity and pressure, rather than merely
  asserting equality of lifespan numbers. -/
  classicalSolution_force_transport :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
        (U : ClassicalSolutionT ν a f T) (g : SpaceTimeField),
      (∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space, f (t, x) = g (t, x)) →
        ∃ V : ClassicalSolutionT ν a g T,
          V.velocity = U.velocity ∧ V.pressure = U.pressure

end NSFormalization.Section3.T10
