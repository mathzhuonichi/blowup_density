import NavierStokes.ResidualCalculus
import NavierStokes.SpatialCurl

/-!
# Concrete local insertion calculus shared by Papers 1 and 3

All differential operators are the actual Frechet derivatives from the OpenAI
library. Viscosity is an arbitrary real parameter. This file proves the exact
PDE algebra and the support cancellation; existence of the vector potential,
scale-dependent norm estimates and classical lifespan are separate obligations.
-/

noncomputable section

namespace NSFormalization.Source

open NavierStokes NavierStokes.ProblemStatement Set Filter
open scoped ContDiff Topology

/-- The physical residual with explicit viscosity. -/
def residual (ν : ℝ) (u : VelocityField) (p : PressureField)
    (t : ℝ) (x : Space) : Space :=
  temporalDerivative u t x + advection u t x - ν • spatialLaplacian u t x +
    pressureGradient p t x

theorem residual_one (u : VelocityField) (p : PressureField) (t : ℝ) (x : Space) :
    residual 1 u p t x = navierStokesResidual u p t x := by
  simp [residual, navierStokesResidual]

/-- Exact residual expansion, including both physical cross-advection terms. -/
theorem residual_add (ν : ℝ) (u w : VelocityField) (p q : PressureField)
    (t : ℝ) (x : Space)
    (hut : DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t)
    (hwt : DifferentiableAt ℝ (fun s : ℝ => w (s, x)) t)
    (hu : ContDiff ℝ 2 (fun y : Space => u (t, y)))
    (hw : ContDiff ℝ 2 (fun y : Space => w (t, y)))
    (hp : DifferentiableAt ℝ (fun y : Space => p (t, y)) x)
    (hq : DifferentiableAt ℝ (fun y : Space => q (t, y)) x) :
    residual ν (fun z => u z + w z) (fun z => p z + q z) t x =
      residual ν u p t x + residual ν w q t x +
        spatialDerivative u t x (w (t, x)) +
        spatialDerivative w t x (u (t, x)) := by
  unfold residual
  rw [ResidualCalculus.temporalDerivative_add u w t x hut hwt,
    ResidualCalculus.advection_add u w t x
      (hu.differentiable (by norm_num) x) (hw.differentiable (by norm_num) x),
    ResidualCalculus.spatialLaplacian_add u w t x hu hw,
    ResidualCalculus.pressureGradient_add p q t x hp hq, smul_add]
  abel

/-- Removing the background on a neighborhood of the closed packet support
kills both interaction terms, including points outside that support. -/
theorem cross_advection_eq_zero (b U : VelocityField) (t : ℝ)
    (hremove : ∀ x ∈ tsupport (fun y => U (t, y)),
      ∀ᶠ y in 𝓝 x, b (t, y) = 0) (x : Space) :
    spatialDerivative b t x (U (t, x)) = 0 ∧
      spatialDerivative U t x (b (t, x)) = 0 := by
  by_cases hx : x ∈ tsupport (fun y => U (t, y))
  · have hb := hremove x hx
    have hder : spatialDerivative b t x = 0 := by
      unfold spatialDerivative
      have heq : (fun y => b (t, y)) =ᶠ[𝓝 x] (fun _ => (0 : Space)) := hb
      rw [heq.fderiv_eq]
      simp
    simp [hder, hb.self_of_nhds]
  · have hU : U (t, x) = 0 := image_eq_zero_of_notMem_tsupport
      (f := fun y => U (t, y)) hx
    have hder : spatialDerivative U t x = 0 := fderiv_of_notMem_tsupport ℝ hx
    simp [hU, hder]

/-- The inserted fields solve the sum-forcing equation at every point where
the background and packet solve their respective equations. -/
theorem exact_insertion (ν : ℝ) (b U : VelocityField) (p P : PressureField)
    (g F : VelocityField) (t : ℝ) (x : Space)
    (hbt : DifferentiableAt ℝ (fun s : ℝ => b (s, x)) t)
    (hUt : DifferentiableAt ℝ (fun s : ℝ => U (s, x)) t)
    (hb : ContDiff ℝ 2 (fun y : Space => b (t, y)))
    (hU : ContDiff ℝ 2 (fun y : Space => U (t, y)))
    (hp : DifferentiableAt ℝ (fun y : Space => p (t, y)) x)
    (hP : DifferentiableAt ℝ (fun y : Space => P (t, y)) x)
    (hremove : ∀ y ∈ tsupport (fun z => U (t, z)),
      ∀ᶠ z in 𝓝 y, b (t, z) = 0)
    (heqb : residual ν b p t x = g (t, x))
    (heqU : residual ν U P t x = F (t, x)) :
    residual ν (fun z => b z + U z) (fun z => p z + P z) t x =
      g (t, x) + F (t, x) := by
  rw [residual_add ν b U p P t x hbt hUt hb hU hp hP]
  obtain ⟨hcross₁, hcross₂⟩ := cross_advection_eq_zero b U t hremove x
  simp [heqb, heqU, hcross₁, hcross₂]

/-- The background correction force in equations (H) of both papers. -/
def correctionForce (ν : ℝ) (v w : VelocityField) : VelocityField := fun z =>
  temporalDerivative w z.1 z.2 - ν • spatialLaplacian w z.1 z.2 +
    spatialDerivative v z.1 z.2 (w z) + spatialDerivative w z.1 z.2 (v z) +
    advection w z.1 z.2

theorem corrected_background (ν : ℝ) (v w : VelocityField) (p : PressureField)
    (t : ℝ) (x : Space)
    (hvt : DifferentiableAt ℝ (fun s : ℝ => v (s, x)) t)
    (hwt : DifferentiableAt ℝ (fun s : ℝ => w (s, x)) t)
    (hv : ContDiff ℝ 2 (fun y : Space => v (t, y)))
    (hw : ContDiff ℝ 2 (fun y : Space => w (t, y)))
    (hp : DifferentiableAt ℝ (fun y : Space => p (t, y)) x) :
    residual ν (fun z => v z + w z) p t x =
      residual ν v p t x + correctionForce ν v w (t, x) := by
  have h := residual_add ν v w p (fun _ => 0) t x hvt hwt hv hw hp
    (differentiableAt_const (0 : ℝ))
  simp only [add_zero] at h
  rw [h]
  simp only [residual, correctionForce]
  have hz : pressureGradient (fun _ => 0) t x = 0 := by simp [pressureGradient]
  rw [hz]
  abel

/-- At a positive-speed packet point the removed background is exactly zero. -/
theorem insertion_preserves_speed (b U : VelocityField) (t : ℝ) (x : Space)
    (hremove : ∀ y ∈ tsupport (fun z => U (t, z)), b (t, y) = 0)
    (hU : U (t, x) ≠ 0) : ‖b (t, x) + U (t, x)‖ = ‖U (t, x)‖ := by
  rw [hremove x (subset_tsupport _ hU), zero_add]

theorem insertion_preserves_blowup (b U : VelocityField)
    (hU : SpeedUnboundedAtOne U)
    (hremove : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x ∈ tsupport (fun y => U (t, y)),
      b (t, x) = 0) : SpeedUnboundedAtOne (fun z => b z + U z) := by
  intro M hM δ hδ
  obtain ⟨t, x, ht, hnear, hlarge⟩ := hU M hM δ hδ
  refine ⟨t, x, ht, hnear, ?_⟩
  have hn : U (t, x) ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hlarge
    exact (not_lt_of_ge hM.le) hlarge
  simpa only [insertion_preserves_speed b U t x (hremove t ht) hn] using hlarge

/-- An earlier interval with zero perturbations retains the entire history. -/
theorem earlier_history (v w U : VelocityField) (S : Set ℝ)
    (hw : ∀ t ∈ S, ∀ x, w (t, x) = 0)
    (hU : ∀ t ∈ S, ∀ x, U (t, x) = 0) :
    ∀ t ∈ S, ∀ x, v (t, x) + w (t, x) + U (t, x) = v (t, x) := by
  intro t ht x
  simp [hw t ht x, hU t ht x]

end NSFormalization.Source
