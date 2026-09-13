import Formal.R3NavierStokesEquation

/-!
# Finite-energy semantics of the decoded velocity (Clay semantic-promotion edge 4)

This file provides the **pointwise-in-time half** of the edge-4 semantic bridge: the
decoded physical velocity of *every* order-three Bessel coordinate has square-integrable
pointwise norm, `∫_{ℝ³} ‖U(x)‖² dx < ∞`, and its energy integral is exactly the square of
its `L²` carrier norm.  Instantiations are recorded for the initial datum and along mild
solutions.

**Not proved here (honest scope):** the endpoint predicate this repository is aligned
against (`LEAN_MILLENNIUM_ALIGNMENT.md`, Fefferman (A)) is **uniform in time on
`[0,∞)`** — a single constant bounding the energy at all times.  No uniform constant is
proved: that needs the energy inequality and global existence, neither of which is built,
and even the local-uniform version on a certified horizon would additionally need the
decoder's operator-norm bound (`‖r3H3ToL2Operator‖ ≤ 1`, not yet in the repository)
applied to the existence theorem's ball clause.  Edge 4 therefore remains `PARTIAL`, not
closed.  No energy *inequality* (dissipation) is built, per the project's stop rule.
-/

namespace MNS2

open MeasureTheory

noncomputable section

/-- Every `L²` velocity field has square-integrable pointwise norm. -/
theorem integrable_norm_sq_r3L2 (g : R3L2Velocity) :
    Integrable (fun x : R3 => ‖((g : R3L2Velocity) : R3 → R3C) x‖ ^ 2) volume := by
  have hmem : MemLp (fun x : R3 => ‖((g : R3L2Velocity) : R3 → R3C) x‖) 2 volume :=
    (Lp.memLp g).norm
  exact (memLp_two_iff_integrable_sq hmem.aestronglyMeasurable).mp hmem

/-- The energy integral of an `L²` velocity field is the square of its carrier norm. -/
theorem integral_norm_sq_r3L2 (g : R3L2Velocity) :
    (∫ x : R3, ‖((g : R3L2Velocity) : R3 → R3C) x‖ ^ 2) = ‖g‖ ^ 2 := by
  rw [norm_r3L2_eq_sqrt_integral_norm_sq g,
    Real.sq_sqrt (integral_nonneg fun x => by positivity)]

/-- **Clay semantic-promotion edge 4: finite-energy semantics.**  The decoded physical
velocity of every order-three Bessel coordinate has finite kinetic energy
`∫_{ℝ³} ‖U(x)‖² dx < ∞`, and the energy equals the square of the `L²` carrier norm of
the decode. -/
theorem r3DecodedVelocity_finiteEnergy (f : R3HsVelocity 3) :
    Integrable (fun x : R3 =>
      ‖((r3H3ToL2Operator f : R3L2Velocity) : R3 → R3C) x‖ ^ 2) volume ∧
    (∫ x : R3, ‖((r3H3ToL2Operator f : R3L2Velocity) : R3 → R3C) x‖ ^ 2) =
      ‖r3H3ToL2Operator f‖ ^ 2 :=
  ⟨integrable_norm_sq_r3L2 (r3H3ToL2Operator f),
    integral_norm_sq_r3L2 (r3H3ToL2Operator f)⟩

/-- Finite kinetic energy recorded along a mild solution for convenience (the
mild-solution hypothesis is not used: the statement holds for any trajectory and every
`t : ℝ`, in particular at the initial time). -/
theorem r3MildDecodedVelocity_finiteEnergy {ν T : ℝ} {u₀ : R3HsVelocity 3}
    {u : ℝ → R3HsVelocity 3} (hnu : 0 < ν)
    (_hu : IsR3EndpointSafeProjectedMildSolutionOn hnu T u₀ u) (t : ℝ) :
    Integrable (fun x : R3 =>
      ‖((r3H3ToL2Operator (u t) : R3L2Velocity) : R3 → R3C) x‖ ^ 2) volume ∧
    (∫ x : R3, ‖((r3H3ToL2Operator (u t) : R3L2Velocity) : R3 → R3C) x‖ ^ 2) =
      ‖r3H3ToL2Operator (u t)‖ ^ 2 :=
  r3DecodedVelocity_finiteEnergy (u t)

end

end MNS2
