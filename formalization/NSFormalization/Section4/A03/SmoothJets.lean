import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import NavierStokes.ProblemStatement

/-!
# Smooth fields with square-integrable jets

Support layer for task `A03` (`collaboration/tasks/A03.md`), the bounded
representative clause of Lemma A.1 (`lem:calculus`,
`paper/sections/appendix-a-local-theory.tex:7-27`, second half of
`eq:Rproduct` at `:12`).

`SmoothL2` is the **jet form** of the manuscript's smooth `H^∞` class
(`paper/sections/02-preliminaries.tex:12` eq:Rinitial and `:29-30`, "a classical
velocity belongs to `C([0,S];H^m)` for every integer `m ≥ 0`"): a smooth field
all of whose Fréchet jets are square integrable.

Attribution.  This is a **copy**, field for field, of
`NSFormalization.Section4.A05.SmoothL2`
(lane 019, `formalization/NSFormalization/Section4/A05/SmoothJets.lean:44`),
which is itself a copy of the vendor's `EulerLpTranslation.SmoothL2Field`
(`vendor/NavierStokesAndEuler/Euler/LpSmoothField.lean:31-34`) written as a
predicate on the field instead of a bundled structure.  It is copied rather than
imported because lane 019 had not been merged when this module was written, and
a worktree may not import another worktree; the two definitions are
syntactically identical, so nothing separates them once both are on the
integration branch.

`SmoothL2UpTo m` is the same class truncated at order `m`.  It, not `SmoothL2`,
is the hypothesis the bounded-representative clause runs on: only the jets of
order `0`, `1` and `2` enter that proof, and at `m = 2` the class is the
manuscript's `v ∈ H²` for a smooth field.  `SmoothL2.upTo` is the one-line
implication that keeps A05-style consumers applicable.

Only the projections actually used by
`NSFormalization.Section4.A03.BoundedRepresentative` are restated here; the
derivative and post-composition closure lemmas of the A05 copy
(`SmoothL2.fderiv`, `SmoothL2.clm`, `SmoothL2.dir`) are **not** duplicated, so
neither class is closed under `∂_j` in this development — a consumer that needs
that, such as the uniqueness coefficient `‖∇u₂‖_∞` of
`paper/sections/appendix-a-local-theory.tex:120-123`, must supply it.
-/

noncomputable section

open MeasureTheory
open NavierStokes.ProblemStatement
open scoped ContDiff ENNReal

namespace NSFormalization.Section4.A03

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A smooth field on `R³` all of whose Fréchet jets are square integrable.
This is `EulerLpTranslation.SmoothL2Field`
(`vendor/NavierStokesAndEuler/Euler/LpSmoothField.lean:31-34`) as a predicate on
the field, and is syntactically `NSFormalization.Section4.A05.SmoothL2`. -/
def SmoothL2 (w : Space → F) : Prop :=
  ContDiff ℝ ∞ w ∧ ∀ n : ℕ, MemLp (iteratedFDeriv ℝ n w) 2 volume

namespace SmoothL2

theorem contDiff {w : Space → F} (h : SmoothL2 w) : ContDiff ℝ ∞ w := h.1

/-- The order-`n` jet is square integrable. -/
theorem jetMemLp {w : Space → F} (h : SmoothL2 w) (n : ℕ) :
    MemLp (iteratedFDeriv ℝ n w) 2 volume := h.2 n

end SmoothL2

/-- A smooth field on `R³` whose Fréchet jets **of order at most `m`** are
square integrable.  At `m = 2` this is the manuscript's `v ∈ H²` for a smooth
field, and it is the exact hypothesis of the vendor input
`EulerSmoothSobolev.smooth_pointwise_le_H2`
(`vendor/NavierStokesAndEuler/Euler/EulerProof.lean:8237-8239`). -/
def SmoothL2UpTo (m : ℕ) (w : Space → F) : Prop :=
  ContDiff ℝ ∞ w ∧ ∀ j ≤ m, MemLp (iteratedFDeriv ℝ j w) 2 volume

namespace SmoothL2UpTo

theorem contDiff {m : ℕ} {w : Space → F} (h : SmoothL2UpTo m w) : ContDiff ℝ ∞ w := h.1

/-- Every jet of order at most `m` is square integrable. -/
theorem jetMemLp {m : ℕ} {w : Space → F} (h : SmoothL2UpTo m w) {j : ℕ} (hj : j ≤ m) :
    MemLp (iteratedFDeriv ℝ j w) 2 volume := h.2 j hj

end SmoothL2UpTo

/-- The all-order class truncates to every order.  This is the implication that
keeps a consumer holding the A05-style all-order class applicable to the
bounded-representative clause, which is stated at `SmoothL2UpTo 2`. -/
theorem SmoothL2.upTo {w : Space → F} (h : SmoothL2 w) (m : ℕ) : SmoothL2UpTo m w :=
  ⟨h.1, fun j _ => h.2 j⟩

end NSFormalization.Section4.A03
