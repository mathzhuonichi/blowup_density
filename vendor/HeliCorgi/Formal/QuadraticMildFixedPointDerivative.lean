import Mathlib
import Mathlib.Analysis.Calculus.ParametricIntegral
import Formal.QuadraticDuhamelDifferentiation

namespace MNS2

open Set MeasureTheory Filter Metric
open scoped Interval Topology

noncomputable section

section QuadraticMildFixedPointDerivative

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/--
If a parameterized trajectory family is a fixed point of the quadratic mild right-hand
side at time `t`, then the derivative of that family at `x₀` is exactly the derivative
of the quadratic mild right-hand side supplied by
`quadraticMildRHSAtTime_hasFDerivAt_of_dominated`.

The differentiation-under-the-integral assumptions remain explicit.  This theorem only
performs the missing fixed-point derivative identification; it does not prove that a
Navier--Stokes solution family satisfies those hypotheses.
-/
theorem quadraticMild_fixedPoint_fderiv_eq_of_dominated
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
      HasFDerivAt (fun x : V => U x s) (J s) x₀)
    (hUdiff_t : HasFDerivAt (fun x : V => U x t) (J t) x₀)
    (hfixed : ∀ x : V,
      U x t = quadraticMildRHSAtTime H Q t U x) :
    J t = quadraticMildRHSDerivativeAtTime H Q t U x₀ J := by
  have hRHS := quadraticMildRHSAtTime_hasFDerivAt_of_dominated
    H Q t U x₀ J N hN bound
    hF_meas hF_int hF'_meas h_lip hbound hUdiff
  have hfun :
      (fun x : V => U x t) = quadraticMildRHSAtTime H Q t U := by
    funext x
    exact hfixed x
  rw [hfun] at hUdiff_t
  exact hUdiff_t.unique hRHS

/--
Directional form of `quadraticMild_fixedPoint_fderiv_eq_of_dominated`.
The direction `h` is arbitrary and is not normalized or rescaled.
-/
theorem quadraticMild_fixedPoint_fderiv_apply_eq_of_dominated
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
      HasFDerivAt (fun x : V => U x s) (J s) x₀)
    (hUdiff_t : HasFDerivAt (fun x : V => U x t) (J t) x₀)
    (hfixed : ∀ x : V,
      U x t = quadraticMildRHSAtTime H Q t U x)
    (h : V) :
    (J t) h = (quadraticMildRHSDerivativeAtTime H Q t U x₀ J) h := by
  exact congrArg (fun A : V →L[ℝ] V => A h)
    (quadraticMild_fixedPoint_fderiv_eq_of_dominated
      H Q t U x₀ J N hN bound
      hF_meas hF_int hF'_meas h_lip hbound hUdiff hUdiff_t hfixed)

/--
Local-neighborhood version of the quadratic mild fixed-point derivative theorem.

Unlike `quadraticMild_fixedPoint_fderiv_eq_of_dominated`, the fixed-point equation is
required only on the neighborhood `N` already used by the dominated differentiation
hypotheses.  This is the form needed for a local solution map: values outside the
admissible-data neighborhood need not solve the mild equation.
-/
theorem quadraticMild_fixedPoint_fderiv_eq_of_dominated_on_nhds
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
      HasFDerivAt (fun x : V => U x s) (J s) x₀)
    (hUdiff_t : HasFDerivAt (fun x : V => U x t) (J t) x₀)
    (hfixed : ∀ x ∈ N,
      U x t = quadraticMildRHSAtTime H Q t U x) :
    J t = quadraticMildRHSDerivativeAtTime H Q t U x₀ J := by
  have hRHS := quadraticMildRHSAtTime_hasFDerivAt_of_dominated
    H Q t U x₀ J N hN bound
    hF_meas hF_int hF'_meas h_lip hbound hUdiff
  have heq :
      (fun x : V => U x t) =ᶠ[𝓝 x₀]
        quadraticMildRHSAtTime H Q t U := by
    filter_upwards [hN] with x hx
    exact hfixed x hx
  have hUasRHS :
      HasFDerivAt (quadraticMildRHSAtTime H Q t U) (J t) x₀ :=
    hUdiff_t.congr_of_eventuallyEq heq.symm
  exact hUasRHS.unique hRHS

/--
Directional form of the local-neighborhood fixed-point derivative theorem.
-/
theorem quadraticMild_fixedPoint_fderiv_apply_eq_of_dominated_on_nhds
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
      HasFDerivAt (fun x : V => U x s) (J s) x₀)
    (hUdiff_t : HasFDerivAt (fun x : V => U x t) (J t) x₀)
    (hfixed : ∀ x ∈ N,
      U x t = quadraticMildRHSAtTime H Q t U x)
    (h : V) :
    (J t) h = (quadraticMildRHSDerivativeAtTime H Q t U x₀ J) h := by
  exact congrArg (fun A : V →L[ℝ] V => A h)
    (quadraticMild_fixedPoint_fderiv_eq_of_dominated_on_nhds
      H Q t U x₀ J N hN bound
      hF_meas hF_int hF'_meas h_lip hbound hUdiff hUdiff_t hfixed)

end QuadraticMildFixedPointDerivative

end

end MNS2
