import Mathlib
import Mathlib.Analysis.Calculus.ParametricIntegral
import Formal.QuadraticLinearizedMild

namespace MNS2

open Set MeasureTheory Filter Metric
open scoped Interval Topology

noncomputable section

section QuadraticDuhamelDifferentiation

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- The quadratic Duhamel integrand at a fixed endpoint time `t`. -/
def quadraticDuhamelIntegrand
    (H : ℝ → V →L[ℝ] V)
    (Q : V →L[ℝ] V →L[ℝ] V)
    (t : ℝ) (U : V → ℝ → V) (x : V) (s : ℝ) : V :=
  H (t - s) (quadraticDiagonal Q (U x s))

/--
The candidate Fréchet derivative of `quadraticDuhamelIntegrand` with respect to the
initial-data parameter `x`, evaluated at `x₀`, when `J s` is the derivative of
`x ↦ U x s` at `x₀`.
-/
def quadraticDuhamelDerivativeIntegrand
    (H : ℝ → V →L[ℝ] V)
    (Q : V →L[ℝ] V →L[ℝ] V)
    (t : ℝ) (U : V → ℝ → V) (x₀ : V)
    (J : ℝ → V →L[ℝ] V) (s : ℝ) : V →L[ℝ] V :=
  (H (t - s)).comp ((quadraticDerivative Q (U x₀ s)).comp (J s))

/--
Pointwise chain-rule derivation of the quadratic Duhamel integrand derivative.
No differentiation-under-the-integral theorem is used here yet.
-/
theorem quadraticDuhamelIntegrand_hasFDerivAt
    (H : ℝ → V →L[ℝ] V)
    (Q : V →L[ℝ] V →L[ℝ] V)
    (t : ℝ) (U : V → ℝ → V) (x₀ : V)
    (J : ℝ → V →L[ℝ] V) (s : ℝ)
    (hU : HasFDerivAt (fun x : V => U x s) (J s) x₀) :
    HasFDerivAt
      (fun x : V => quadraticDuhamelIntegrand H Q t U x s)
      (quadraticDuhamelDerivativeIntegrand H Q t U x₀ J s)
      x₀ := by
  unfold quadraticDuhamelIntegrand quadraticDuhamelDerivativeIntegrand
  have hquad :
      HasFDerivAt
        (fun x : V => quadraticDiagonal Q (U x s))
        ((quadraticDerivative Q (U x₀ s)).comp (J s))
        x₀ := by
    simpa only [Function.comp_def] using
      ((hasFDerivAt_quadraticDiagonal Q (U x₀ s)).comp x₀ hU)
  simpa only [Function.comp_def] using
    ((H (t - s)).hasFDerivAt.comp x₀ hquad)

/--
Differentiate the quadratic Duhamel interval integral with respect to initial data.

The hard analytic interchange is discharged by mathlib's
`hasFDerivAt_integral_of_dominated_loc_of_lip_interval`. Its domination hypotheses
are kept explicit here: a common initial-data neighborhood, measurability/integrability,
a locally uniform Lipschitz majorant, and an integrable scalar bound.

The pointwise derivative hypothesis is required only for the trajectory map `U`; the
quadratic and linear chain rules are proved internally by
`quadraticDuhamelIntegrand_hasFDerivAt`.
-/
theorem quadraticDuhamelIntegral_hasFDerivAt_of_dominated
    (H : ℝ → V →L[ℝ] V)
    (Q : V →L[ℝ] V →L[ℝ] V)
    (t : ℝ) (U : V → ℝ → V) (x₀ : V)
    (J : ℝ → V →L[ℝ] V)
    (N : Set V) (hN : N ∈ 𝓝 x₀)
    (bound : ℝ → ℝ)
    (hF_meas : ∀ᶠ x in 𝓝 x₀,
      AEStronglyMeasurable
        (fun s : ℝ => quadraticDuhamelIntegrand H Q t U x s)
        (volume.restrict (Ι (0 : ℝ) t)))
    (hF_int : IntervalIntegrable
      (fun s : ℝ => quadraticDuhamelIntegrand H Q t U x₀ s)
      volume 0 t)
    (hF'_meas : AEStronglyMeasurable
      (quadraticDuhamelDerivativeIntegrand H Q t U x₀ J)
      (volume.restrict (Ι (0 : ℝ) t)))
    (h_lip : ∀ᵐ s ∂volume.restrict (Ι (0 : ℝ) t),
      LipschitzOnWith (Real.nnabs (bound s))
        (fun x : V => quadraticDuhamelIntegrand H Q t U x s) N)
    (hbound : IntervalIntegrable bound volume 0 t)
    (hUdiff : ∀ᵐ s ∂volume.restrict (Ι (0 : ℝ) t),
      HasFDerivAt (fun x : V => U x s) (J s) x₀) :
    IntervalIntegrable
      (quadraticDuhamelDerivativeIntegrand H Q t U x₀ J)
      volume 0 t ∧
    HasFDerivAt
      (fun x : V =>
        ∫ s in (0 : ℝ)..t, quadraticDuhamelIntegrand H Q t U x s)
      (∫ s in (0 : ℝ)..t,
        quadraticDuhamelDerivativeIntegrand H Q t U x₀ J s)
      x₀ := by
  have hdiff : ∀ᵐ s ∂volume.restrict (Ι (0 : ℝ) t),
      HasFDerivAt
        (fun x : V => quadraticDuhamelIntegrand H Q t U x s)
        (quadraticDuhamelDerivativeIntegrand H Q t U x₀ J s)
        x₀ := by
    filter_upwards [hUdiff] with s hs
    exact quadraticDuhamelIntegrand_hasFDerivAt H Q t U x₀ J s hs
  exact hasFDerivAt_integral_of_dominated_loc_of_lip_interval
    (x₀ := x₀) (s := N) (μ := volume)
    hN hF_meas hF_int hF'_meas h_lip hbound hdiff

/-- The fixed-time quadratic mild right-hand side, viewed as a function of initial data. -/
def quadraticMildRHSAtTime
    (H : ℝ → V →L[ℝ] V)
    (Q : V →L[ℝ] V →L[ℝ] V)
    (t : ℝ) (U : V → ℝ → V) (x : V) : V :=
  H t x - ∫ s in (0 : ℝ)..t, quadraticDuhamelIntegrand H Q t U x s

/-- Candidate Fréchet derivative of the fixed-time quadratic mild right-hand side. -/
def quadraticMildRHSDerivativeAtTime
    (H : ℝ → V →L[ℝ] V)
    (Q : V →L[ℝ] V →L[ℝ] V)
    (t : ℝ) (U : V → ℝ → V) (x₀ : V)
    (J : ℝ → V →L[ℝ] V) : V →L[ℝ] V :=
  H t - ∫ s in (0 : ℝ)..t, quadraticDuhamelDerivativeIntegrand H Q t U x₀ J s

/--
Under the same domination hypotheses, the complete fixed-time quadratic mild RHS is
Fréchet differentiable and its derivative is the linear evolution minus the integral of
the exact quadratic variational derivative.
-/
theorem quadraticMildRHSAtTime_hasFDerivAt_of_dominated
    (H : ℝ → V →L[ℝ] V)
    (Q : V →L[ℝ] V →L[ℝ] V)
    (t : ℝ) (U : V → ℝ → V) (x₀ : V)
    (J : ℝ → V →L[ℝ] V)
    (N : Set V) (hN : N ∈ 𝓝 x₀)
    (bound : ℝ → ℝ)
    (hF_meas : ∀ᶠ x in 𝓝 x₀,
      AEStronglyMeasurable
        (fun s : ℝ => quadraticDuhamelIntegrand H Q t U x s)
        (volume.restrict (Ι (0 : ℝ) t)))
    (hF_int : IntervalIntegrable
      (fun s : ℝ => quadraticDuhamelIntegrand H Q t U x₀ s)
      volume 0 t)
    (hF'_meas : AEStronglyMeasurable
      (quadraticDuhamelDerivativeIntegrand H Q t U x₀ J)
      (volume.restrict (Ι (0 : ℝ) t)))
    (h_lip : ∀ᵐ s ∂volume.restrict (Ι (0 : ℝ) t),
      LipschitzOnWith (Real.nnabs (bound s))
        (fun x : V => quadraticDuhamelIntegrand H Q t U x s) N)
    (hbound : IntervalIntegrable bound volume 0 t)
    (hUdiff : ∀ᵐ s ∂volume.restrict (Ι (0 : ℝ) t),
      HasFDerivAt (fun x : V => U x s) (J s) x₀) :
    HasFDerivAt
      (quadraticMildRHSAtTime H Q t U)
      (quadraticMildRHSDerivativeAtTime H Q t U x₀ J)
      x₀ := by
  have hint := quadraticDuhamelIntegral_hasFDerivAt_of_dominated
    H Q t U x₀ J N hN bound
    hF_meas hF_int hF'_meas h_lip hbound hUdiff
  change HasFDerivAt
    (fun x : V =>
      H t x - ∫ s in (0 : ℝ)..t, quadraticDuhamelIntegrand H Q t U x s)
    (H t - ∫ s in (0 : ℝ)..t,
      quadraticDuhamelDerivativeIntegrand H Q t U x₀ J s)
    x₀
  exact (H t).hasFDerivAt.sub hint.2

end QuadraticDuhamelDifferentiation

end

end MNS2
