import NSFormalization.Section4.A04.MomentumDatum
import NSFormalization.Section4.A04.HighEnergy

/-!
Conformance / axiom audit for A04 unit G1, sub-lemma SL2 (the momentum equation in
datum form) and the datum-linearity lemmas it adds.  Expected: only the standard
logical axioms `propext`, `Classical.choice`, `Quot.sound`.

The `composed` example checks the deliverable claim that `momentum_datum`
produces exactly the `hmom` hypothesis `inner_energy_assembly` (SL8) consumes at
`E = RealVectorSobolev (m:ℝ)`, with `Gt := deriv G t` — applied with no glue.

Run: `cd verification && lake env lean ../research/A04/axioms_sl2.lean`.
-/

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source.RealSobolev
open scoped ContDiff RealInnerProductSpace

open NSFormalization.Section4.A04
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR MemForceR)
open NSFormalization.Section4.D01 (IsSobolevDatum)

-- SL2 and the datum-linearity lemmas added for it
#print axioms momentum_datum
#print axioms isSobolevDatum_smul
#print axioms isScalarSobolevDatum_smul
#print axioms isSobolevDatum_neg
#print axioms isScalarSobolevDatum_neg

/-- The momentum datum equation feeds `inner_energy_assembly` (SL8) directly as
`hmom`, at `E = RealVectorSobolev (m:ℝ)`, `Gt := deriv G t`.  No glue between SL2
and SL8. -/
example
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {m : ℕ} (hm : 2 ≤ m)
    {G : ℝ → RealVectorSobolev (m : ℝ)}
    (hGd : ∀ t ∈ Ico (0 : ℝ) T, IsSobolevDatum (m : ℝ) (fun x => w.velocity (t, x)) (G t))
    (hGc : ContDiffOn ℝ ∞ G (Ico (0 : ℝ) T))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    {L N P F : RealVectorSobolev (m : ℝ)}
    (hL : IsSobolevDatum (m : ℝ) (fun x => spatialLaplacian w.velocity t x) L)
    (hN : IsSobolevDatum (m : ℝ) (fun x => advection w.velocity t x) N)
    (hP : IsSobolevDatum (m : ℝ) (fun x => pressureGradient w.pressure t x) P)
    (hF : IsSobolevDatum (m : ℝ) (fun x => f (t, x)) F)
    {grad NLbound uNorm fNorm d : ℝ} (hν : 0 ≤ ν)
    (hd : d = 2 * ⟪G t, deriv G t⟫)
    (hlap : ⟪G t, L⟫ ≤ - grad ^ 2)
    (hpr : ⟪G t, P⟫ = 0)
    (hnl : - ⟪G t, N⟫ ≤ NLbound)
    (hG : ‖G t‖ = uNorm) (hFn : ‖F‖ = fNorm) :
    (1 / 2) * d + ν * grad ^ 2 ≤ NLbound + fNorm * uNorm :=
  inner_energy_assembly hν hd
    (momentum_datum w hf hm hGd hGc ht hL hN hP hF) hlap hpr hnl hG hFn
