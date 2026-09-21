import Mathlib.Analysis.Distribution.Sobolev
import Formal.R3StokesL2Operator
import Formal.UniformRestartContinuation

namespace MNS2

open MeasureTheory
open scoped SchwartzMap

noncomputable section

/--
A bundled coordinate model for the complexified Sobolev space `H^s(R³; C³)`.

The stored coordinate is `J^s u = (1 - (2π)⁻² Δ)^(s/2) u` in `L²(R³; C³)`. Thus the carrier is
literally a complete `L²` Hilbert space, while the physical tempered distribution represented by a
coordinate `g` is `J^{-s} g`.

`R3HsVelocity s` is deliberately an `abbrev`: different values of `s` use the same underlying
coordinate Hilbert space, and the Sobolev order is carried semantically by the `s`-dependent decoder
below. This lets the coordinate carrier inherit the exact `L²` normed/complete structure instead of
silently inventing a second topology.

This choice avoids pretending that mathlib's current `TemperedDistribution.MemSobolev` predicate is
already a bundled Banach space. It also keeps the norm interpretation explicit: the carrier norm is
the `L²` norm of the Bessel coordinate, i.e. the standard Bessel-potential `H^s` norm under this
Fourier convention.
-/
abbrev R3HsVelocity (_s : ℝ) := R3L2Velocity

/-- Integer-order alias used by the strong-solution track in `SPEC.md`. -/
abbrev R3HmVelocity (m : ℕ) := R3HsVelocity (m : ℝ)

/-- For integer orders, `m ≥ 3` is exactly the present `m > 5/2` strong-theory threshold. -/
def R3StrongSobolevOrder (m : ℕ) : Prop := 3 ≤ m

/-- The Bessel-coordinate carrier is complete because its coordinate space is `L²`. -/
theorem r3HsVelocity_complete (s : ℝ) : CompleteSpace (R3HsVelocity s) := by
  infer_instance

/-- Explicit embedding of the coordinate `L²` space into tempered distributions. -/
def r3L2ToTemperedCLM :
    R3L2Velocity →L[ℂ] 𝓢'(R3, R3C) :=
  MeasureTheory.Lp.toTemperedDistributionCLM R3C (volume : Measure R3) 2

/--
Decode an `H^s` Bessel coordinate into its represented physical tempered distribution.
-/
def r3HsToTemperedCLM (s : ℝ) :
    R3HsVelocity s →L[ℂ] 𝓢'(R3, R3C) :=
  TemperedDistribution.besselPotential R3 R3C (-s) ∘L r3L2ToTemperedCLM

/-- Pointwise form of the Bessel-coordinate decoder. -/
@[simp]
theorem r3HsToTemperedCLM_apply (s : ℝ) (f : R3HsVelocity s) :
    r3HsToTemperedCLM s f =
      TemperedDistribution.besselPotential R3 R3C (-s) (r3L2ToTemperedCLM f) := by
  rfl

/--
Applying `J^s` to the decoded distribution recovers the stored `L²` Bessel coordinate exactly,
viewed through the explicit `L² → 𝓢'` embedding.
-/
theorem besselPotential_r3HsToTempered_eq_coordinate
    (s : ℝ) (f : R3HsVelocity s) :
    TemperedDistribution.besselPotential R3 R3C s (r3HsToTemperedCLM s f) =
      r3L2ToTemperedCLM f := by
  rw [r3HsToTemperedCLM_apply,
    TemperedDistribution.besselPotential_besselPotential_apply]
  simp

/--
Every decoded Bessel coordinate is genuinely a mathlib Sobolev distribution of order `s` and
exponent `p = 2`.
-/
theorem r3HsToTempered_memSobolev
    (s : ℝ) (f : R3HsVelocity s) :
    TemperedDistribution.MemSobolev s 2 (r3HsToTemperedCLM s f) := by
  refine ⟨f, ?_⟩
  simpa [r3L2ToTemperedCLM] using
    besselPotential_r3HsToTempered_eq_coordinate s f

/-- The integer-order carrier decodes into `H^m` in mathlib's `MemSobolev` sense. -/
theorem r3HmToTempered_memSobolev
    (m : ℕ) (f : R3HmVelocity m) :
    TemperedDistribution.MemSobolev (m : ℝ) 2
      (r3HsToTemperedCLM (m : ℝ) f) := by
  exact r3HsToTempered_memSobolev (m : ℝ) f

/-- The first integer order above the `5/2` threshold is available to the strong track. -/
theorem r3StrongSobolevOrder_three : R3StrongSobolevOrder 3 := by
  norm_num [R3StrongSobolevOrder]

end

end MNS2
