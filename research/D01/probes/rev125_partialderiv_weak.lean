-- Reviewer probe from lane-125 review (research/D01/REVIEW_FINITE_ORDER.md), preserved verbatim.
-- Original reviewer path: /tmp/rev125/p8_weakdatum.lean . Compiles under `lake env lean` from verification/.
-- Exploratory probe (not a registered module): shows row D-b and the Schwartz-duality removal
-- of the smoothness hypothesis are reachable from in-tree lemmas.
import NSFormalization.Section4.D01.FiniteOrderDatum

open MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3 NSFormalization.Source.RealSobolev
open NSFormalization.Section4.D01
open scoped ContDiff ENNReal LineDeriv SchwartzMap

noncomputable section

/-- **The Schwartz-duality route, smoothness-free.**  If `A` is an order-`s` datum of `z` and `w`
is the `j`-th weak derivative of `z` in the Schwartz-pairing sense, then the angular directional
derivative of `A` is an order-`(s-1)` datum of `w`.  No `SmoothL2Field`, no `ContDiff`. -/
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
