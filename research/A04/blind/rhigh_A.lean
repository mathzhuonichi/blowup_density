import Contracts.V1.Data
import Contracts.V1.TameProduct
import Mathlib

/-!
# Blind statement A of `eq:Rhigh` (high-order energy inequality)

`paper/sections/appendix-a-local-theory.tex:132-137`, the display `eq:Rhigh`,
inside the proof of `prop:local` (`:127-137`).  For every integer `m ≥ 3`
(`:129`, "For every integer m ≥ 3") and every interior time `t`, a classical
whole-space solution `u` with viscosity `ν`, initial datum `a ∈ X_R` and force
`f ∈ F_R` satisfies

    ½ d/dt ‖u‖²_{H^m} + ν ‖∇u‖²_{H^m}
        ≤ C_m ‖u‖_{H²} ‖u‖_{H^m} ‖∇u‖_{H^m} + ‖f‖_{H^m} ‖u‖_{H^m}.

This is blind writer A's independent transcription (lane 130); the modelling
decisions and rejected alternatives are recorded in `rhigh_A.md`.  It uses only
the frozen contract vocabulary of `Contracts.V1.Data` and
`Contracts.V1.TameProduct` (`gradientSobolevENorm`), plus Mathlib.
-/

noncomputable section

open Set MeasureTheory
open scoped ENNReal
open BlowupDensity.Contracts.V1

namespace BlindRhighA

/-- Real-valued spatial `H^m(R³)` norm of the time-`t` slice of a spacetime field
`u`, as `ENNReal.toReal` of the frozen `Data.sobolevENorm` (`Contracts/V1/Data.lean`).

`eq:Rhigh` is a statement about a *real*, possibly signed, time-derivative, so
every norm in it must be a real number; the frozen norms are `ℝ≥0∞`-valued and
are read here through `.toReal`.

**Caveat `⊤ ↦ 0`.**  `ENNReal.toReal ⊤ = 0`, so a slice with no order-`m` datum
would report a spurious `0`.  This never occurs on the class quantified over
below: a `Data.ClassicalSolutionR` velocity lies in `C([0,S];H^m)` for every `m`
(structure field `sobolev`, `02-preliminaries.tex:29`), and an `F_R` force is
smooth into every `H^m` with a genuine datum at each `t ≥ 0`
(`Data.MemForceR`), so every slice appearing below has a finite order-`m` norm
and `.toReal` is faithful. -/
def hmNorm (m : ℕ) (u : Data.SpaceTimeField) (t : ℝ) : ℝ :=
  (Data.sobolevENorm (m : ℝ) (fun x => u (t, x))).toReal

/-- Real-valued spatial `H²(R³)` norm of the time-`t` slice, the low factor
`‖u‖_{H²}` of `eq:Rhigh`.  Same `.toReal` caveat as `hmNorm`. -/
def h2Norm (u : Data.SpaceTimeField) (t : ℝ) : ℝ :=
  (Data.sobolevENorm (2 : ℝ) (fun x => u (t, x))).toReal

/-- Real-valued spatial `H^m(R³)` norm of the *gradient tensor* `∇u` of the
time-`t` slice, via the frozen `TameProduct.gradientSobolevENorm`.

That definition's own docstring pins it to `appendix-a-local-theory.tex:134`
(the display line of `eq:Rhigh`) as `‖∇v‖_{H^s}`, the nine-entry Frobenius
quantity `(∑_j ‖∂_j v‖²_{H^s})^{1/2}` where each `∂_j v` is the classical spatial
derivative.  This is the reading of `‖∇u‖_{H^m}` chosen here; the alternative
`‖u‖_{H^{m+1}}` (equivalent up to constants) is rejected — see `rhigh_A.md`.
Same `.toReal` caveat as `hmNorm`; faithful on the smooth solution slice. -/
def gradHmNorm (m : ℕ) (u : Data.SpaceTimeField) (t : ℝ) : ℝ :=
  (TameProduct.gradientSobolevENorm (m : ℝ) (fun x => u (t, x))).toReal

/-- The real time-path `t ↦ ‖u(t)‖²_{H^m}` (the *squared* `H^m` norm) whose
time-derivative appears on the left of `eq:Rhigh`. -/
def hmNormSq (m : ℕ) (u : Data.SpaceTimeField) (t : ℝ) : ℝ := (hmNorm m u t) ^ 2

/-- **`eq:Rhigh`** (`paper/sections/appendix-a-local-theory.tex:132-137`), blind
transcription A.

A single family of constants `C_m`, positive and depending only on the integer
order `m` (and the fixed domain `R³`, per `appendix-a-local-theory.tex:10`),
is quantified *outside* `ν, a, f, T` and the solution.  For each viscosity
`ν > 0`, initial datum `a ∈ X_R` (`Data.initialClassR`), force `f ∈ F_R`
(`Data.MemForceR`), classical solution `w` on `[0,T)`
(`Data.ClassicalSolutionR ν a f T`), integer order `m ≥ 3`, and interior time
`t ∈ (0,T)`, and **assuming the squared `H^m` norm path is differentiable at `t`**
— the time-regularity that the paper's `d/dt ‖u‖²_{H^m}` needs, which the paper
obtains "by Fourier approximation on compact intervals of smooth existence"
(`:139`) but which the frozen `ClassicalSolutionR` exposes only as *continuity*
of the `H^m` datum path (field `sobolev`), so it is stated here as an explicit
hypothesis — the energy inequality

    ½ d/dt‖u‖²_{H^m} + ν‖∇u‖²_{H^m}
        ≤ C_m‖u‖_{H²}‖u‖_{H^m}‖∇u‖_{H^m} + ‖f‖_{H^m}‖u‖_{H^m}

holds, with `u = w.velocity` and `f` the force of the momentum equation. -/
def eqRhigh_A : Prop :=
  ∃ C : ℕ → ℝ, (∀ m : ℕ, 0 < C m) ∧
    ∀ (ν : ℝ), 0 < ν →
      ∀ (a : Data.SpatialField), a ∈ Data.initialClassR →
        ∀ (f : Data.SpaceTimeField), Data.MemForceR f →
          ∀ (T : ℝ) (w : Data.ClassicalSolutionR ν a f T) (m : ℕ), 3 ≤ m →
            ∀ (t : ℝ), t ∈ Ioo (0 : ℝ) T →
              DifferentiableAt ℝ (hmNormSq m w.velocity) t →
                (1 / 2 : ℝ) * deriv (hmNormSq m w.velocity) t
                    + ν * (gradHmNorm m w.velocity t) ^ 2
                  ≤ C m * h2Norm w.velocity t * hmNorm m w.velocity t
                        * gradHmNorm m w.velocity t
                    + hmNorm m f t * hmNorm m w.velocity t

#check eqRhigh_A

end BlindRhighA
