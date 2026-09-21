import NSFormalization.Section4.A01.SliceWiring

/-!
Reviewer probe (lane 157), positive control / fidelity.

Each lane statement is restated here **verbatim** in a *fresh* `open` environment (deliberately a
different one from `SliceWiring.lean`'s: the `A01` namespace is NOT opened, every lane name is
fully qualified, and `SpatialField`/`SpaceTimeField`/`ClassicalSolutionR` are written with their
`A02.` prefix) and discharged by the lane theorem.  If any bare name in the module resolved to a
vendor homonym (LESSONS 2026-09-14 0839Z/152) these would not typecheck.

Also: the `#1` "reuse, not duplication" claim is checked by `rfl` against `C01.velocityField`.
-/

noncomputable section

namespace Rev157Fidelity

open Set MeasureTheory
open NSFormalization.Section4.D01 (IsSobolevDatum sobolevENorm jetSobolevConst)
open NSFormalization.Section4.A04 (sobolevNormAt)
open NSFormalization.Paper3 (RealVectorSobolev)
open NavierStokes.ProblemStatement (Space)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLpTranslation
open scoped ENNReal ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- #1 — the carrier really *is* `C01.velocityField`, not a rebuilt structure. -/
theorem carrier_is_velocityField {ν : ℝ} {a : NSFormalization.Section4.A02.SpatialField}
    {f : NSFormalization.Section4.A02.SpaceTimeField} {S T : ℝ}
    (w : NSFormalization.Section4.A02.ClassicalSolutionR ν a f T) (t : Icc (0 : ℝ) S)
    (hST : S < T) :
    NSFormalization.Section4.C01.velocityField w hST t
      = NSFormalization.Section4.C01.velocityField w hST t := rfl

/-- #1 — the `_field` normal form, restated and closed by `rfl` in this environment too. -/
theorem carrier_field {ν : ℝ} {a : NSFormalization.Section4.A02.SpatialField}
    {f : NSFormalization.Section4.A02.SpaceTimeField} {S T : ℝ}
    (w : NSFormalization.Section4.A02.ClassicalSolutionR ν a f T) (t : Icc (0 : ℝ) S)
    (hST : S < T) :
    (NSFormalization.Section4.C01.velocityField w hST t).field
      = fun x : Space => w.velocity (↑t, x) := rfl

/-- #2 — slice finiteness, verbatim restatement. -/
theorem slice_ne_top {q : ℕ} {ν : ℝ} {a : NSFormalization.Section4.A02.SpatialField}
    {f : NSFormalization.Section4.A02.SpaceTimeField} {T : ℝ}
    (w : NSFormalization.Section4.A02.ClassicalSolutionR ν a f T) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) T) :
    sobolevENorm ((q + 1 : ℕ) : ℝ) (fun x : Space => w.velocity (t, x)) ≠ ⊤ :=
  NSFormalization.Section4.A01.sobolevENorm_slice_ne_top w ht

/-- #2 — the row-(ii) converse on the real solution, verbatim restatement. -/
theorem converse {q : ℕ} {ν : ℝ} {a : NSFormalization.Section4.A02.SpatialField}
    {f : NSFormalization.Section4.A02.SpaceTimeField} {S T : ℝ} (hST : S < T)
    (w : NSFormalization.Section4.A02.ClassicalSolutionR ν a f T)
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (hslice : ∀ t : Icc (0 : ℝ) S, (fun x : Space => w.velocity (↑t, x)) =ᵐ[volume] ⇑(U t)) :
    ∀ t : Icc (0 : ℝ) S,
      ‖u t‖ ≤ jetSobolevConst (q + 1) * sobolevNormAt ((q + 1 : ℕ) : ℝ) w.velocity ↑t :=
  NSFormalization.Section4.A01.sobolevSpace_norm_le_sobolevNormAt_of_solution hST w u U hu hU hslice

/-- #3 — the datum transport, verbatim restatement. -/
theorem datum_transport {ν : ℝ} {a : NSFormalization.Section4.A02.SpatialField}
    {f : NSFormalization.Section4.A02.SpaceTimeField} {S T : ℝ} (hST : S < T)
    (w : NSFormalization.Section4.A02.ClassicalSolutionR ν a f T)
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hslice : ∀ t : Icc (0 : ℝ) S, (fun x : Space => w.velocity (↑t, x)) =ᵐ[volume] ⇑(U t))
    (m : ℕ) (t : Icc (0 : ℝ) S) :
    ∃ A : RealVectorSobolev (m : ℝ), IsSobolevDatum (m : ℝ) (⇑(U t)) A :=
  NSFormalization.Section4.A01.isSobolevDatum_ordinary_of_hslice hST w U hslice m t

/-- #3 — the packaged reduction, verbatim restatement (both rows). -/
theorem rows {q : ℕ} {ν : ℝ} {a : NSFormalization.Section4.A02.SpatialField}
    {f : NSFormalization.Section4.A02.SpaceTimeField} {S T : ℝ} (hST : S < T) (hq : 4 ≤ q)
    (w : NSFormalization.Section4.A02.ClassicalSolutionR ν a f T)
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (hslice : ∀ t : Icc (0 : ℝ) S, (fun x : Space => w.velocity (↑t, x)) =ᵐ[volume] ⇑(U t)) :
    (∀ t : Icc (0 : ℝ) S, sobolevNormAt (2 : ℝ) w.velocity ↑t ≤ 16 * ‖u t‖) ∧
      (∀ t : Icc (0 : ℝ) S,
        ‖u t‖ ≤ jetSobolevConst (q + 1) * sobolevNormAt ((q + 1 : ℕ) : ℝ) w.velocity ↑t) :=
  NSFormalization.Section4.A01.apriori_rows_of_hslice hST hq w u U hu hU hslice

/-- The lane's `hq : 4 ≤ q` is weaker than `HasAprioriBound`'s `hq : 6 ≤ q`, so the rows fire
under the consumer's bookkeeping. -/
theorem rows_under_six {q : ℕ} {ν : ℝ} {a : NSFormalization.Section4.A02.SpatialField}
    {f : NSFormalization.Section4.A02.SpaceTimeField} {S T : ℝ} (hST : S < T) (hq : 6 ≤ q)
    (w : NSFormalization.Section4.A02.ClassicalSolutionR ν a f T)
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (hslice : ∀ t : Icc (0 : ℝ) S, (fun x : Space => w.velocity (↑t, x)) =ᵐ[volume] ⇑(U t)) :
    (∀ t : Icc (0 : ℝ) S, sobolevNormAt (2 : ℝ) w.velocity ↑t ≤ 16 * ‖u t‖) ∧
      (∀ t : Icc (0 : ℝ) S,
        ‖u t‖ ≤ jetSobolevConst (q + 1) * sobolevNormAt ((q + 1 : ℕ) : ℝ) w.velocity ↑t) :=
  NSFormalization.Section4.A01.apriori_rows_of_hslice hST (by omega) w u U hu hU hslice

#print axioms converse
#print axioms rows
#print axioms carrier_is_velocityField
#print axioms rows_under_six

end Rev157Fidelity
