import Formal.R3EndpointSafeProjectedDuhamel
import Formal.EndpointSafeTwoSpacePicard

/-!
# Local existence for the R³ endpoint-safe projected mild equation

This file instantiates the abstract Picard fixed-point theorem of
`Formal/EndpointSafeTwoSpacePicard.lean` on the concrete complex Bessel-coordinate carriers.

For every viscosity `ν > 0` and every order-three Bessel coordinate `u₀`, there is a positive
horizon `T ≤ 1` and a trajectory `u` with `IsR3EndpointSafeProjectedMildSolutionOn hnu T u₀ u`;
the trajectory stays in the closed ball of radius `‖u₀‖ + 1`, and every mild solution on the
same horizon staying in that ball agrees with it there.

The required contractivity of the same-space initial evolution is exactly
`norm_r3StokesH3Evolution_apply_le`.

Scope guard: the carrier is the complex Bessel-coordinate model.  This theorem is existence and
closed-ball uniqueness for the projected two-space mild equation in that carrier.  It is not a
physical (real-valued) local well-posedness statement, it reconstructs no pressure, and it is
not a Clay statement.
-/

namespace MNS2

open Set
open scoped NNReal

noncomputable section

/--
Local-in-time existence with closed-ball uniqueness for the concrete `R³` endpoint-safe
projected mild equation on the order-three Bessel-coordinate carrier.
-/
theorem r3EndpointSafeProjected_exists_localMildSolution {nu : ℝ} (hnu : 0 < nu)
    (u0 : R3HsVelocity 3) :
    ∃ T : ℝ, 0 < T ∧ T ≤ 1 ∧ ∃ u : ℝ → R3HsVelocity 3,
      IsR3EndpointSafeProjectedMildSolutionOn hnu T u0 u ∧
      (∀ t ∈ Icc (0 : ℝ) T, ‖u t‖ ≤ ‖u0‖ + 1) ∧
      ∀ v : ℝ → R3HsVelocity 3, IsR3EndpointSafeProjectedMildSolutionOn hnu T u0 v →
        (∀ t ∈ Icc (0 : ℝ) T, ‖v t‖ ≤ ‖u0‖ + 1) →
        ∀ t ∈ Icc (0 : ℝ) T, v t = u t :=
  (r3EndpointSafeProjectedDuhamelContract hnu).exists_pos_time_isMildSolutionOn
    (fun t x => norm_r3StokesH3Evolution_apply_le hnu.le t x) u0

/-- The certified local trajectory satisfies the concrete mild equation at every certified time. -/
theorem r3EndpointSafeProjected_localMildSolution_equation {nu : ℝ} (hnu : 0 < nu)
    (u0 : R3HsVelocity 3) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → R3HsVelocity 3,
      ∀ t : ℝ, ∀ ht : t ∈ Icc (0 : ℝ) T,
        u t =
          r3StokesH3Evolution hnu.le ⟨t, ht.1⟩ u0 -
            ∫ s in (0 : ℝ)..t, r3EndpointSafeProjectedDuhamelIntegrand hnu t u s := by
  obtain ⟨T, hT, _hT1, u, hmild, _hball, _huniq⟩ :=
    r3EndpointSafeProjected_exists_localMildSolution hnu u0
  exact ⟨T, hT, u, fun t ht => (r3EndpointSafeProjectedMild_equation_at_time hnu hmild ht).2⟩

end

end MNS2
