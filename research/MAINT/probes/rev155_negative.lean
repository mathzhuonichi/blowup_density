import NSFormalization.Section4.A04.ZeroSolution
import NSFormalization.Section4.D01.FiniteOrderConstructor

/-! # Reviewer probe (lane 155): the moved lemma is load-bearing for its consumer.

`isSobolevDatum_zero` was sunk from `A04.PressureDrop` to `D01.SmoothDatum` (lane 155).
This probe checks the move is not cosmetic slack: the consumer
`A04.ZeroSolution.hasSmoothSobolevPath_zero` (`ZeroSolution.lean:150`) and the
`sobolev` field of `zeroSol` (`:104`) need the *specific* content
"`0` is a datum of the zero field", and break under a weakened substitute.

Control (must SUCCEED) uses the real statement as a hypothesis; the two mutants
(must FAIL) weaken it in ways a careless restatement could.  Uncomment one mutant
at a time; the recorded errors are in `research/MAINT/REVIEW_SIMP_155.md`. -/

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.D01 (IsSobolevDatum)
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Section4.A04 (HasSmoothSobolevPath)
open scoped ContDiff

set_option autoImplicit false

/-- CONTROL: with the real statement the consumer term elaborates. -/
example (ok : ∀ s : ℝ, IsSobolevDatum s (fun _ : Space => (0 : Space)) 0) (T : ℝ) :
    HasSmoothSobolevPath T (0 : SpaceTimeField) := by
  intro m
  exact ⟨fun _ => 0, fun t _ => ok _, contDiffOn_const⟩

/-- MUTANT 1 (expected to FAIL): the datum is only asserted to *exist*, not to be `0`. -/
example (weakened : ∀ s : ℝ, ∃ A : NSFormalization.Paper3.RealVectorSobolev s,
      IsSobolevDatum s (fun _ : Space => (0 : Space)) A) (T : ℝ) :
    HasSmoothSobolevPath T (0 : SpaceTimeField) := by
  intro m
  exact ⟨fun _ => 0, fun t _ => weakened _, contDiffOn_const⟩

/-! ## Part 2: the hoisted `coord_smul_deriv_ae` keeps its exact statement.

The lemma was lifted verbatim out of `memLp_coord_smul_datum`'s inline `heq` into
`FiniteOrderConstructor.lean:159`.  POSITIVE pins the exported type; MUTANT 2 doubles the
`frequencyUnit` on the right and must fail, i.e. the constant carries real content. -/

section Hoisted
open NSFormalization.Section4.D01
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Source (frequencyUnit)
open NSFormalization.Source.RealSobolev (FourierData RealSobolevHilbert)
open scoped ENNReal ComplexConjugate LineDeriv SchwartzMap

variable {s : ℝ} {z : Space → Space} {w : Fin 3 → Space → Space}
  {A : RealVectorSobolev s} {C : Fin 3 → RealVectorSobolev s}

/-- POSITIVE: the exported statement is exactly the former inline `heq`. -/
example (hA : IsSobolevDatum s z A) (hC : ∀ j, IsSobolevDatum s (w j) (C j))
    (hw : ∀ (j i : Fin 3) (ψ : SchwartzMap Space ℂ),
      ∫ x, ψ x * ((w j x i : ℝ) : ℂ)
        = ∫ x, (-∂_{coordinateVector j} ψ) x * ((z x i : ℝ) : ℂ)) (i j : Fin 3) :
    (fun ξ => (2 * (Real.pi : ℂ) * Complex.I) *
        ((ξ j : ℂ) • (((A i : RealSobolevHilbert s) : FourierData) : Space → ℂ) ξ))
      =ᵐ[MeasureTheory.volume]
      fun ξ => ((frequencyUnit : ℝ) : ℂ) *
        (((C j i : RealSobolevHilbert s) : FourierData) : Space → ℂ) ξ :=
  coord_smul_deriv_ae hA hC hw i j

/-- MUTANT 2 (expected to FAIL): doubling the constant. -/
example (hA : IsSobolevDatum s z A) (hC : ∀ j, IsSobolevDatum s (w j) (C j))
    (hw : ∀ (j i : Fin 3) (ψ : SchwartzMap Space ℂ),
      ∫ x, ψ x * ((w j x i : ℝ) : ℂ)
        = ∫ x, (-∂_{coordinateVector j} ψ) x * ((z x i : ℝ) : ℂ)) (i j : Fin 3) :
    (fun ξ => (2 * (Real.pi : ℂ) * Complex.I) *
        ((ξ j : ℂ) • (((A i : RealSobolevHilbert s) : FourierData) : Space → ℂ) ξ))
      =ᵐ[MeasureTheory.volume]
      fun ξ => ((2 * frequencyUnit : ℝ) : ℂ) *
        (((C j i : RealSobolevHilbert s) : FourierData) : Space → ℂ) ξ :=
  coord_smul_deriv_ae hA hC hw i j

end Hoisted
