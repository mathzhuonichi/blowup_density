import Tests.DatumLemmasV3
import NSFormalization.Section4.A03.VectorTameProduct
import NSFormalization.Section4.D01.DatumToJets

/-!
# V4 candidate probe — the order-`m` Helmholtz split in pure contract vocabulary

Source: the lane-120 reviewer's appendix E (`research/D01/REVIEW_CONTRACT_V3.md`,
finding 1).  Reproduced here verbatim so the V4 lane starts from compiled code.

The order-`m` eq:Rpressure identity `datumᵐ ∇p = (I−P)ₘ (datumᵐ h)` is in
*operator* form — `(I−P)ₘ` (`D01.Leray.lerayComplement`) has no `Contracts/V1`
counterpart, which is the real reason it is not a V3 field (not the momentum
residual, which IS `Contracts.V1.Packet` vocabulary).  Its **operator-free** form,
the Helmholtz split `datumᵐ h = datumᵐ ∂ₜu + datumᵐ ∇p` (i.e. `Am = D + P`), is
statable in pure `Contracts.V1.Data`/`Packet` vocabulary and provable in ~20 lines
with standard axioms; with V1's registered `isSobolevDatum_unique` it pins
`datumᵐ ∇p` from `Am` and `datumᵐ ∂ₜu`.  This is the recommended V4 field.

Run: `cd verification && lake env lean ../research/D01/probes/v4_split_identity.lean`
Expected: `'Rev120V4.splitIdentity' depends on axioms: [propext, Classical.choice, Quot.sound]`.

Note (LESSONS): `linear_combination (norm := module) hm0` fails here — `ring`/`module`
treat `Contracts.V1.temporalDerivative` and `NavierStokes.ProblemStatement.temporalDerivative`
as different atoms even though they are `rfl`-equal (`ring failed … ⊢ 1 = 0`).  The
fix is an explicit `show` into one vocabulary before the algebra tactic.
-/

open Set MeasureTheory
open BlowupDensity
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open NSFormalization.Paper3 (RealVectorSobolev)
open scoped ContDiff

namespace Rev120V4

/-- Contract-vocabulary statement.  Only `Contracts.V1.Data` / `Contracts.V1.Packet`
notions appear: `ClassicalSolutionR`, `MemForceR`, `IsSobolevDatum`, `advection`,
`spatialLaplacian`, `temporalDerivative`, `pressureGradient`, `RealVectorSobolev`. -/
def SplitIdentity : Prop :=
  ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
    (u : ClassicalSolutionR ν a f T), MemForceR f → ∀ t : ℝ, t ∈ Ioo (0 : ℝ) T →
    ∀ m : ℕ, 2 ≤ m → ∀ Am D P : RealVectorSobolev (m : ℝ),
      IsSobolevDatum (m : ℝ) (fun x : Space => f (t, x) - advection u.velocity t x
          + ν • spatialLaplacian u.velocity t x) Am →
      IsSobolevDatum (m : ℝ) (fun x : Space => temporalDerivative u.velocity t x) D →
      IsSobolevDatum (m : ℝ) (fun x : Space => pressureGradient u.pressure t x) P →
      Am = D + P

theorem splitIdentity : SplitIdentity := by
  intro ν a f T u hf t ht m hm Am D P hAm hD hP
  have hsR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hcD : ContDiff ℝ ∞ (fun x : Space => temporalDerivative u.velocity t x) :=
    (Tests.checkedDatumLemmasV3.solution_slice_temporalDerivative_smoothJets ν a f T u hf t ht).1
  have hcP : ContDiff ℝ ∞ (fun x : Space => pressureGradient u.pressure t x) :=
    (Tests.checkedDatumLemmasV3.solution_slice_pressureGradient_smoothJets ν a f T u hf t ht).1
  have mD := NSFormalization.Section4.D01.memLp_of_isSobolevDatum hcD hD
  have mP := NSFormalization.Section4.D01.memLp_of_isSobolevDatum hcP hP
  have hsum := NSFormalization.Section4.A03.isSobolevDatum_add hsR
    (NSFormalization.Section4.A03.locIntField_of_memLp mD)
    (NSFormalization.Section4.A03.locIntField_of_memLp mP) hD hP
  have hpt : (fun x : Space =>
        temporalDerivative u.velocity t x + pressureGradient u.pressure t x)
      = fun x : Space => f (t, x) - advection u.velocity t x
          + ν • spatialLaplacian u.velocity t x := by
    funext x
    have hm0 := u.momentum t ht x
    simp only [NavierStokesR3.ProblemStatement.navierStokesResidual] at hm0
    show NavierStokes.ProblemStatement.temporalDerivative u.velocity t x
        + NavierStokes.ProblemStatement.pressureGradient u.pressure t x
      = f (t, x) - NavierStokes.ProblemStatement.advection u.velocity t x
        + ν • NavierStokes.ProblemStatement.spatialLaplacian u.velocity t x
    rw [← hm0]
    module
  rw [hpt] at hsum
  exact NSFormalization.Section4.D01.isSobolevDatum_unique hAm hsum

#print axioms splitIdentity

end Rev120V4
