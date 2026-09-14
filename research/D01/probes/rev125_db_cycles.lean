-- Reviewer probe from lane-125 review (research/D01/REVIEW_FINITE_ORDER.md), preserved verbatim.
-- Original reviewer path: /tmp/rev125/p9_db.lean . Compiles under `lake env lean` from verification/.
-- Exploratory probe (not a registered module): shows row D-b and the Schwartz-duality removal
-- of the smoothness hypothesis are reachable from in-tree lemmas.
import NSFormalization.Section4.D01.FiniteOrderDatum

open MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3 NSFormalization.Source.RealSobolev
open NSFormalization.Section4.D01
open NSFormalization.Section4.D01.Leray (isSobolevDatum_lower)
open NSFormalization.Section4.A03 (lowerDatum coe_lowerDatum)
open scoped ContDiff ENNReal LineDeriv SchwartzMap

noncomputable section

theorem isSobolevDatum_partialDeriv_weak {s : ℝ} {z w : Space → Space} (j : Fin 3)
    {A : RealVectorSobolev s} (hA : IsSobolevDatum s z A)
    (hw : ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
      ∫ x, ψ x * ((w x i : ℝ) : ℂ)
        = ∫ x, (-∂_{coordinateVector j} ψ) x * ((z x i : ℝ) : ℂ)) :
    IsSobolevDatum (s - 1) w
      (WithLp.toLp 2 fun i => angularDirectionalDerivativeReal s (coordinateVector j) (A i)) := by
  intro i ψ
  have hcoe : (((WithLp.toLp 2 fun k =>
        angularDirectionalDerivativeReal s (coordinateVector j) (A k)) i :
          RealSobolevHilbert (s - 1)) : FourierData)
      = angularDirectionalDerivative s (coordinateVector j) ((A i : FourierData)) :=
    angularDirectionalDerivativeReal_coe s (coordinateVector j) (A i)
  rw [hcoe, angularRealization_directionalDerivative s (coordinateVector j) ((A i : FourierData)),
    TemperedDistribution.lineDerivOp_apply_apply, hA i (-∂_{coordinateVector j} ψ), hw i ψ]

/-- **Row D-b, in the cycles variable, with no smoothness anywhere.**  If `A` is an order-`s` datum
of `z`, `C` an order-`s` datum of the weak `j`-th derivative `w` of `z`, then in the pre-dilation
(cycles) frequency variable `2πi·ξⱼ·k_A = k_C` a.e. -/
theorem db_cycles_full {s : ℝ} (j : Fin 3) {z w : Space → Space}
    {A : RealVectorSobolev s} (hA : IsSobolevDatum s z A)
    {C : RealVectorSobolev s} (hC : IsSobolevDatum s w C)
    (hw : ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
      ∫ x, ψ x * ((w x i : ℝ) : ℂ)
        = ∫ x, (-∂_{coordinateVector j} ψ) x * ((z x i : ℝ) : ℂ))
    (i : Fin 3) :
    ∀ᵐ ξ ∂(volume : Measure Space),
      (2 * (Real.pi : ℂ) * Complex.I) * ((ξ j : ℝ) : ℂ) *
          (((cyclesToAngular s).symm ((A i : RealSobolevHilbert s) : FourierData)) : Space → ℂ) ξ
        = (((cyclesToAngular s).symm ((C i : RealSobolevHilbert s) : FourierData)) : Space → ℂ) ξ := by
  have hle : s - 1 ≤ s := by linarith
  have hB := isSobolevDatum_partialDeriv_weak j hA hw
  have hlow := isSobolevDatum_lower hle hC
  have heq := isSobolevDatum_unique hB hlow
  have hcomp : angularDirectionalDerivative s (coordinateVector j) ((A i : FourierData))
      = angularOrderLowering s (s - 1) hle ((C i : FourierData)) := by
    have h := congrArg
      (fun B : RealVectorSobolev (s - 1) => ((B i : RealSobolevHilbert (s - 1)) : FourierData)) heq
    simpa [angularDirectionalDerivativeReal_coe, lowerVectorL_apply, coe_lowerDatum] using h
  have hcyc : sobolevDirectionalDerivative s (coordinateVector j)
        ((cyclesToAngular s).symm ((A i : FourierData)))
      = sobolevOrderLowering s (s - 1) hle ((cyclesToAngular s).symm ((C i : FourierData))) := by
    have h1 : (cyclesToAngular (s - 1)).symm
          (angularDirectionalDerivative s (coordinateVector j) ((A i : FourierData)))
        = sobolevDirectionalDerivative s (coordinateVector j)
          ((cyclesToAngular s).symm ((A i : FourierData))) :=
      (cyclesToAngular (s - 1)).symm_apply_apply _
    rw [← h1, hcomp, cyclesToAngular_symm_orderLowering]
  have hsigma : ∀ ξ : Space, sobolevDirectionalSymbol (coordinateVector j) ξ
      = (2 * (Real.pi : ℂ) * Complex.I) * (((ξ j : ℝ) : ℂ) * sobolevBesselWeight (-1) ξ) := by
    intro ξ
    rw [sobolevDirectionalSymbol]
    congr 3
    rw [coordinateVector, EuclideanSpace.inner_single_right]; simp
  have hae : (fun ξ => sobolevDirectionalSymbol (coordinateVector j) ξ *
      (((cyclesToAngular s).symm ((A i : FourierData))) : Space → ℂ) ξ)
        =ᵐ[volume] ((sobolevOrderLowering s (s - 1) hle
          ((cyclesToAngular s).symm ((C i : FourierData)))) : Space → ℂ) := by
    refine (sobolevDirectionalDerivative_coeFn s (coordinateVector j)
      ((cyclesToAngular s).symm ((A i : FourierData)))).symm.trans ?_
    rw [hcyc]
  filter_upwards [hae, sobolevOrderLowering_coeFn s (s - 1) hle
      ((cyclesToAngular s).symm ((C i : FourierData)))] with ξ e e2
  have hW : sobolevBesselWeight (-1) ξ ≠ 0 := by
    simp only [sobolevBesselWeight]; rw [Complex.ofReal_ne_zero]; positivity
  rw [e2, show s - 1 - s = (-1 : ℝ) by ring, hsigma ξ] at e
  refine mul_right_cancel₀ hW ?_
  linear_combination e
