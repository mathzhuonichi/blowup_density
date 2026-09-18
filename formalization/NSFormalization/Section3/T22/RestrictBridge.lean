import NSFormalization.Section3.T22.Domain

/-!
# T22 restriction bridge

A datum representing the literal zero extension restricts, on compactly
supported interior Schwartz tests, to the physical field integral over the
domain.  The quotient-norm inequality is then pure `iInf` bookkeeping.
-/

noncomputable section

namespace NSFormalization.Section3.T22

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Section4.D01
open NSFormalization.Section4.A02 (SpatialField)
open scoped ENNReal SchwartzMap

/-- Restricting a datum of the zero extension gives the physical domain
functional.  No measurability of `Ω` is needed: the test vanishes pointwise
outside `Ω`. -/
theorem restrictDatum_eq_restrictField {Ω : Set Space} {s : ℝ}
    {z : SpatialField} {A : RealVectorSobolev s}
    (hA : IsSobolevDatum s (zeroExtension Ω z) A) :
    restrictDatum Ω s A = restrictField Ω z := by
  funext i ψ
  rw [restrictDatum, restrictField, hA]
  have hzero : ∀ x ∉ Ω, ψ.1 x * ((z x i : ℝ) : ℂ) = 0 := by
    intro x hx
    have hxpsi : ψ.1 x = 0 := by
      by_contra hne
      have hsupp : x ∈ Function.support (ψ.1 : Space → ℂ) := hne
      have htsupp : x ∈ tsupport ψ.1 := subset_closure hsupp
      exact hx (ψ.2.2 htsupp)
    simp [hxpsi]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ Ω
  · simp [zeroExtension, Set.indicator_of_mem hx]
  · simp [zeroExtension, hx, hzero x hx]

/-- The zero extension is one admissible extension in the definition of the
domain quotient norm. -/
theorem domainSobolevENorm_le_sobolevENorm {Ω : Set Space} {s : ℝ}
    {z : SpatialField} :
    domainSobolevENorm Ω s (restrictField Ω z) ≤
      sobolevENorm s (zeroExtension Ω z) := by
  apply le_iInf
  intro A
  exact iInf_le_of_le
    ⟨A.1, restrictDatum_eq_restrictField A.2⟩ le_rfl


end NSFormalization.Section3.T22
