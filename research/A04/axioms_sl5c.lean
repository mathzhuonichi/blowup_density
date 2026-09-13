import NSFormalization.Section4.A04.NonlinearBound
import NSFormalization.Section4.A04.HighEnergy

/-!
Axiom audit for SL5 rows 5c + 5h (`Section4/A04/NonlinearDatum.lean`, `NonlinearBound.lean`).
Every public declaration must depend on exactly `propext`, `Classical.choice`, `Quot.sound`.
The final `example` is the conformance check: it feeds `inner_advection_bound_slice` into the `hnl`
slot of `A04.inner_energy_assembly` (`HighEnergy.lean:100`), proving the whole energy inequality — so
the bound has exactly the `hnl` shape the assembly consumes.
-/

noncomputable section
open Set MeasureTheory
open NavierStokes.ProblemStatement

open NSFormalization.Section4.A04
open NSFormalization.Section4.D01 (IsSobolevDatum)
open NSFormalization.Section4.A03 (outerSobolevENorm)
open NSFormalization.Section4.A02 (SpaceTimeField ClassicalSolutionR SpatialField)
open NSFormalization.Paper3 (RealVectorSobolev)

-- Row 5c (NonlinearDatum.lean)
#print axioms outerColumn_smoothL2
#print axioms outerColumnField
#print axioms outerColumnField_field
#print axioms isSobolevDatum_advection_sum
#print axioms advection_slice_datum_eq
-- Row 5h (NonlinearBound.lean)
#print axioms inner_component_advection
#print axioms inner_datum_advectionDir
#print axioms inner_advection_bound
#print axioms inner_advection_bound_slice

/-- Conformance: `inner_advection_bound_slice` is exactly the `hnl` hypothesis of
`A04.inner_energy_assembly`.  Feeding it (plus placeholder `hd`/`hmom`/`hlap`/`hpr`/`hG`/`hF` for the
other slots) yields the full energy inequality `½ d + ν grad² ≤ NLbound + fNorm·uNorm`, with
`grad = gradientSobolevNormAt (m:ℝ) w.velocity t` and
`NLbound = grad · (outerSobolevENorm (m:ℝ) (u t·) (u t·)).toReal`. -/
example {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T) {m : ℕ} (hm : 2 ≤ m) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    {G N Gt P L F : RealVectorSobolev (m : ℝ)} {νc uNorm fNorm d : ℝ} (hν : 0 ≤ νc)
    (hG : IsSobolevDatum (m : ℝ) (fun x => w.velocity (t, x)) G)
    (hNdat : IsSobolevDatum (m : ℝ) (fun x => advection w.velocity t x) N)
    (hd : d = 2 * (inner ℝ G Gt : ℝ))
    (hmom : Gt = νc • L - N - P + F)
    (hlap : (inner ℝ G L : ℝ) ≤ - (gradientSobolevNormAt (m : ℝ) w.velocity t) ^ 2)
    (hpr : (inner ℝ G P : ℝ) = 0)
    (hnormG : ‖G‖ = uNorm) (hnormF : ‖F‖ = fNorm) :
    (1 / 2) * d + νc * (gradientSobolevNormAt (m : ℝ) w.velocity t) ^ 2
      ≤ gradientSobolevNormAt (m : ℝ) w.velocity t
          * (outerSobolevENorm (m : ℝ)
              (fun x => w.velocity (t, x)) (fun x => w.velocity (t, x))).toReal
        + fNorm * uNorm :=
  inner_energy_assembly hν hd hmom hlap hpr
    (inner_advection_bound_slice w hm ht hG hNdat) hnormG hnormF

/-
`lake env lean ../research/A04/axioms_sl5c.lean` output (2026-09-13), exit 0
(the conformance `example` above elaborated with no error, i.e. `inner_advection_bound_slice`
type-checks in `inner_energy_assembly`'s `hnl` slot):

'NSFormalization.Section4.A04.outerColumn_smoothL2' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.outerColumnField' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.outerColumnField_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.isSobolevDatum_advection_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.advection_slice_datum_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.inner_component_advection' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.inner_datum_advectionDir' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.inner_advection_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.inner_advection_bound_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
