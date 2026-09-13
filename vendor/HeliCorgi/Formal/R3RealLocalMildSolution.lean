import Formal.R3ConvectionConjugationEquivariance
import Formal.R3EndpointSafeProjectedLocalExistence

/-!
# Realness of the local mild solution

With the operator-realness gate closed, the local mild solution of the projected `R³`
Navier–Stokes equation is physically real for physically real initial data — and no new
fixed point is needed: the conjugated trajectory `t ↦ r3L2Conj (u t)` is itself a mild
solution on the same horizon, staying in the same ball, with the same (real) initial datum;
the ball-uniqueness clause of the existence theorem then pins it to `u`.

Ingredients: conjugation equivariance of the Stokes evolution, the `H² → H³` smoothing, and
the projected convection (which combine into equivariance of the endpoint-safe Duhamel
integrand), and commutation of the continuous real-linear conjugation with the interval
Bochner integral.

Scope guard: this upgrades the complex-carrier local theory to a physically real one on the
certified horizon and ball. It proves no quantitative lifespan bound, no unconditional
uniqueness, no continuation criterion, and no Clay statement.
-/

namespace MNS2

open MeasureTheory Set
open scoped NNReal

noncomputable section

/-- Conjugation equivariance of the endpoint-safe projected Duhamel integrand. -/
theorem r3L2Conj_r3EndpointSafeProjectedDuhamelIntegrand {nu : ℝ} (hnu : 0 < nu)
    (t : ℝ) (u : ℝ → R3HsVelocity 3) (s : ℝ) :
    r3EndpointSafeProjectedDuhamelIntegrand hnu t (fun τ => r3L2Conj (u τ)) s =
      r3L2Conj (r3EndpointSafeProjectedDuhamelIntegrand hnu t u s) := by
  by_cases hs : s < t
  · rw [r3EndpointSafeProjectedDuhamelIntegrand_of_lt hnu t _ hs,
      r3EndpointSafeProjectedDuhamelIntegrand_of_lt hnu t u hs,
      ← r3L2Conj_r3ProjectedConvectionH3ToH2, ← r3L2Conj_r3StokesH2ToH3Operator]
  · rw [r3EndpointSafeProjectedDuhamelIntegrand_of_le hnu t _ (not_lt.mp hs),
      r3EndpointSafeProjectedDuhamelIntegrand_of_le hnu t u (not_lt.mp hs), map_zero]

/-- The conjugated trajectory of a mild solution with real initial datum is again a mild
solution. -/
theorem IsR3EndpointSafeProjectedMildSolutionOn.r3L2Conj_comp {nu T : ℝ} (hnu : 0 < nu)
    {u0 : R3HsVelocity 3} {u : ℝ → R3HsVelocity 3}
    (h : IsR3EndpointSafeProjectedMildSolutionOn hnu T u0 u)
    (hu0 : IsR3RealVelocity u0) :
    IsR3EndpointSafeProjectedMildSolutionOn hnu T u0 (fun τ => r3L2Conj (u τ)) := by
  have hu0' : r3L2Conj u0 = u0 := hu0
  obtain ⟨hT0, hucont, hu0eq, humild⟩ := h
  refine ⟨hT0, r3L2Conj.continuous.comp_continuousOn hucont, ?_, ?_⟩
  · show r3L2Conj (u 0) = u0
    rw [hu0eq, hu0']
  · intro t ht
    have hvcont : ContinuousOn (fun τ => r3L2Conj (u τ)) (Icc (0 : ℝ) t) :=
      (r3L2Conj.continuous.comp_continuousOn hucont).mono
        (Icc_subset_Icc le_rfl ht.2)
    obtain ⟨hint_u, heq_u⟩ :=
      r3EndpointSafeProjectedMild_equation_at_time hnu ⟨hT0, hucont, hu0eq, humild⟩ ht
    have hpt := r3L2Conj_r3EndpointSafeProjectedDuhamelIntegrand hnu t u
    have heq_v : (fun τ => r3L2Conj (u τ)) t =
        r3StokesH3Evolution hnu.le ⟨t, ht.1⟩ u0 -
          ∫ s in (0 : ℝ)..t,
            r3EndpointSafeProjectedDuhamelIntegrand hnu t (fun τ => r3L2Conj (u τ)) s := by
      calc
        (fun τ => r3L2Conj (u τ)) t = r3L2Conj (u t) := rfl
        _ = r3L2Conj (r3StokesH3Evolution hnu.le ⟨t, ht.1⟩ u0 -
              ∫ s in (0 : ℝ)..t,
                r3EndpointSafeProjectedDuhamelIntegrand hnu t u s) := by rw [heq_u]
        _ = r3L2Conj (r3StokesH3Evolution hnu.le ⟨t, ht.1⟩ u0) -
              r3L2Conj (∫ s in (0 : ℝ)..t,
                r3EndpointSafeProjectedDuhamelIntegrand hnu t u s) := map_sub _ _ _
        _ = r3StokesH3Evolution hnu.le ⟨t, ht.1⟩ u0 -
              ∫ s in (0 : ℝ)..t,
                r3L2Conj (r3EndpointSafeProjectedDuhamelIntegrand hnu t u s) := by
            rw [r3L2Conj_r3StokesH3Evolution, hu0',
              ← r3L2Conj.intervalIntegral_comp_comm hint_u]
        _ = r3StokesH3Evolution hnu.le ⟨t, ht.1⟩ u0 -
              ∫ s in (0 : ℝ)..t,
                r3EndpointSafeProjectedDuhamelIntegrand hnu t
                  (fun τ => r3L2Conj (u τ)) s := by
            congr 1
            exact intervalIntegral.integral_congr fun s _ => (hpt s).symm
    refine ⟨?_, heq_v⟩
    exact intervalIntegrable_r3EndpointSafeProjectedDuhamelIntegrand hnu ht.1 hvcont

/--
Local existence of a **physically real** mild solution for physically real initial data,
with the ball bound, pointwise realness on the certified horizon, and ball uniqueness.
-/
theorem r3EndpointSafeProjected_exists_realLocalMildSolution {nu : ℝ} (hnu : 0 < nu)
    {u0 : R3HsVelocity 3} (hu0 : IsR3RealVelocity u0) :
    ∃ T : ℝ, 0 < T ∧ T ≤ 1 ∧ ∃ u : ℝ → R3HsVelocity 3,
      IsR3EndpointSafeProjectedMildSolutionOn hnu T u0 u ∧
      (∀ t ∈ Icc (0 : ℝ) T, ‖u t‖ ≤ ‖u0‖ + 1) ∧
      (∀ t ∈ Icc (0 : ℝ) T, IsR3RealVelocity (u t)) ∧
      ∀ v : ℝ → R3HsVelocity 3, IsR3EndpointSafeProjectedMildSolutionOn hnu T u0 v →
        (∀ t ∈ Icc (0 : ℝ) T, ‖v t‖ ≤ ‖u0‖ + 1) →
        ∀ t ∈ Icc (0 : ℝ) T, v t = u t := by
  obtain ⟨T, hT, hT1, u, hmild, hball, huniq⟩ :=
    r3EndpointSafeProjected_exists_localMildSolution hnu u0
  refine ⟨T, hT, hT1, u, hmild, hball, ?_, huniq⟩
  have hvmild := hmild.r3L2Conj_comp hnu hu0
  have hvball : ∀ t ∈ Icc (0 : ℝ) T, ‖r3L2Conj (u t)‖ ≤ ‖u0‖ + 1 := fun t ht => by
    rw [norm_r3L2Conj]
    exact hball t ht
  have hfix := huniq (fun τ => r3L2Conj (u τ)) hvmild hvball
  intro t ht
  show r3L2Conj (u t) = u t
  exact hfix t ht

end

end MNS2
