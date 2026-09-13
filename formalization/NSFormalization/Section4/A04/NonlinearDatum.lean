import NSFormalization.Section4.A04.NonlinearColumns
import NSFormalization.Section4.A04.AdvectionDivergence
import NSFormalization.Section4.C01.VelocityJets

/-!
# A04 unit G1, sub-lemma SL5 row 5c: the advection slice as a sum of column-derivative data

Task `A04` (graph node `formalization/blueprint/DEPENDENCY_GRAPH.md`), the force-density energy
estimate `eq:Rhigh` (`paper/sections/appendix-a-local-theory.tex:132`).  Row 5c of the SL5 split
(`research/A04/SL5_SPLIT.md`) produces the order-`m` datum `N` of the nonlinear (advection) slice
`(u·∇)u(t,·)` as the sum over the three directions of the derivative data of the outer-product
columns `Wⱼ = uⱼ·u`.  It is the `hN` input of `A04.momentum_datum` /
`A04.inner_energy_assembly` (`MomentumDatum.lean:167`, `hN : IsSobolevDatum (m:ℝ)
(fun x => advection w.velocity t x) N`), identified here as `N = ∑ⱼ Dⱼ Bⱼ` with `Bⱼ` the
order-`(m+1)` column datum of row 5b.

This module has two parts (the split the task mandates).

**Part 1 — the column wrapper (mandatory).**  `outerColumn_smoothL2`: each column
`Wⱼ = outerColumn z z j = uⱼ·u` of a field `z` in the datum-form `H^∞` class `A02.MemHInfty` is a
smooth square-integrable field `A05.SmoothL2`.  This is the `SmoothL2Field` datum the derivative
step `D01.isSobolevDatum_partialDeriv` consumes.  It is packaged as
`EulerLpTranslation.SmoothL2Field` `outerColumnField`, whose `.field` is `outerColumn z z j`
by `rfl` (`outerColumnField_field`).

The route is the **datum route**, not a Leibniz jet expansion (see `research/A04/ATTEMPTS_SL5C.md`).
`MemHInfty z` is exactly `ContDiff ℝ ∞ z ∧ (datum at every ℕ order)` (`A02/SolutionClass.lean:88`,
verbatim `Contracts.V1.Data.MemHInfty`).  Smoothness of the column is the cheap half
(`ContDiff.smul` of the coordinate projection `z·ⱼ` against `z`, `contDiff_euclidean`); the genuinely
new content — every iterated Fréchet jet of `Wⱼ` square integrable — is obtained *without* the
`L^∞`-factor Leibniz argument, from the outer-product Sobolev finiteness `A04.exists_outerColumn_datum`
(row 5b, lane 102) supplying a datum at every integer order, then `D01.memHInfty_jets`
(`DatumToJets.lean:287`) turning "smooth + datum at every order" into the square-integrable jets that
are the second field of `A05.SmoothL2`.  The two orders `0`, `1` below the row-5b threshold `2 ≤ m`
are covered by order-lowering `A04.isSobolevDatum_lowerVectorL` from order `max n 2` (088).

**Part 2 — the advection datum.**  `isSobolevDatum_advection_sum`: on a divergence-free
space-differentiable spacetime field, the order-`m` datum of the advection slice is
`∑ⱼ derivDatumStep m j Bⱼ`, with `Bⱼ` the order-`(m+1)` datum of `Wⱼ`.  The structure copies 088's
`isSobolevDatum_laplacian` with **one** derivative step instead of two: lane 100's divergence-form
identity `advection_eq_sum_partialDeriv_outerColumn` rewrites the field to `∑ⱼ ∂ⱼWⱼ`, one
`D01.isSobolevDatum_partialDeriv` per column with `Z := outerColumnField …` produces the order-`m`
datum of `∂ⱼWⱼ`, and `D01.isSobolevDatum_add` over the three directions folds them (pairability from
`D01.schwartzPairable_of_isSobolevDatum`).  The `ClassicalSolutionR` slice corollary
`advection_slice_datum_eq` identifies **any** given datum `N` of the advection slice with the sum by
`D01.isSobolevDatum_unique`, discharging the hypotheses from `C01.velocity_slice_memHInfty` (whose
`ContDiff` conjunct also supplies space-differentiability) and the `divergence` field.

## Reuse

Nothing here restates a definition.  `outerColumn`, `partialDeriv` are `A03.OuterTameProduct.lean:68,59`;
`exists_outerColumn_datum` is lane 102 (`A04.NonlinearColumns.lean`); `derivDatumStep`,
`isSobolevDatum_lowerVectorL`, `lowerVectorL` are 088 (`A04.LaplacianAssembly.lean` / `D01.HalfOrder`);
`isSobolevDatum_partialDeriv`, `isSobolevDatum_add`, `isSobolevDatum_unique`,
`schwartzPairable_of_isSobolevDatum`, `memHInfty_jets` are D01's;
`advection_eq_sum_partialDeriv_outerColumn` is lane 100 (`A04.AdvectionDivergence.lean`);
`velocity_slice_memHInfty` is C01's; `SmoothL2Field` is the vendor's
(`vendor/…/Euler/LpSmoothField.lean:31`).  `A05.SmoothL2`, `A03.SmoothL2` and
`D01.SmoothSquareIntegrableJets` share the field-for-field body
`ContDiff ℝ ∞ · ∧ ∀ n, MemLp (iteratedFDeriv ℝ n ·) 2 volume`, so the pair produced by
`memHInfty_jets` is directly the `A05.SmoothL2` conclusion.
-/

noncomputable section

open Set MeasureTheory
open NavierStokes.ProblemStatement
open scoped ContDiff ENNReal

namespace NSFormalization.Section4.A04

open NSFormalization.Section4.D01 (IsSobolevDatum isSobolevDatum_add isSobolevDatum_unique
  schwartzPairable_of_isSobolevDatum SchwartzPairable memHInfty_jets isSobolevDatum_partialDeriv
  lowerVectorL)
open NSFormalization.Section4.A03 (outerColumn partialDeriv)
open NSFormalization.Section4.A02 (SpaceTimeField ClassicalSolutionR MemHInfty SpatialField)
open NSFormalization.Paper3 (RealVectorSobolev)
open EulerLpTranslation (SmoothL2Field)

/-! ## 1. Part 1 — the `SmoothL2Field` wrapper of each column -/

/-- **Part 1 (SL5 row 5c).**  Each outer-product column `Wⱼ = outerColumn z z j = uⱼ·u` of a
field `z` in the datum-form `H^∞` class `A02.MemHInfty` is a smooth square-integrable field
`A05.SmoothL2`.

Datum route (no Leibniz jet expansion): `MemHInfty z` is `ContDiff ℝ ∞ z ∧ (datum at every ℕ order)`.
Smoothness of the column is `ContDiff.smul` of the coordinate projection `x ↦ z x j`
(`contDiff_euclidean`) against `z`.  For the jets: `z` is `A03.SmoothL2` (its jet form, from
`memHInfty_jets`), so `A03.SmoothL2.memHmVector` makes it admissible at every integer order;
`A04.exists_outerColumn_datum` (row 5b) then gives the column a datum at every order `≥ 2`, lowered to
orders `0, 1` by `A04.isSobolevDatum_lowerVectorL`; `D01.memHInfty_jets` turns smooth + datum at every
order into the square-integrable jets that are the second field of `A05.SmoothL2`. -/
theorem outerColumn_smoothL2 {z : Space → Space} (hH : MemHInfty z) (j : Fin 3) :
    NSFormalization.Section4.A05.SmoothL2 (outerColumn z z j) := by
  have hzc : ContDiff ℝ ∞ z := hH.1
  have hcontdiff : ContDiff ℝ ∞ (outerColumn z z j) := by
    have hcomp : ContDiff ℝ ∞ (fun x => z x j) := (contDiff_euclidean.mp hzc) j
    exact hcomp.smul hzc
  -- `z` in its jet form, so it is admissible at every integer order.
  have hSL2 : NSFormalization.Section4.A03.SmoothL2 z := ⟨hzc, memHInfty_jets hzc hH.2⟩
  -- the column has a datum at every integer order
  have hdata : ∀ n : ℕ, ∃ A : RealVectorSobolev (n : ℝ),
      IsSobolevDatum (n : ℝ) (outerColumn z z j) A := by
    intro n
    obtain ⟨A, hA⟩ := exists_outerColumn_datum (max n 2) (le_max_right n 2)
      (NSFormalization.Section4.A03.SmoothL2.memHmVector hSL2 (max n 2)) j
    have hle : (n : ℝ) ≤ ((max n 2 : ℕ) : ℝ) := by exact_mod_cast le_max_left n 2
    exact ⟨lowerVectorL _ _ hle A, isSobolevDatum_lowerVectorL _ _ hle hA⟩
  exact ⟨hcontdiff, memHInfty_jets hcontdiff hdata⟩

/-- The `EulerLpTranslation.SmoothL2Field` wrapper of the column `Wⱼ = outerColumn z z j`, the
carrier `D01.isSobolevDatum_partialDeriv` consumes for the derivative step of Part 2. -/
def outerColumnField {z : Space → Space} (hH : MemHInfty z) (j : Fin 3) : SmoothL2Field Space :=
  let h := outerColumn_smoothL2 hH j
  ⟨outerColumn z z j, h.1, h.2⟩

/-- The field of the column wrapper is the column, by `rfl`. -/
@[simp] theorem outerColumnField_field {z : Space → Space} (hH : MemHInfty z) (j : Fin 3) :
    (outerColumnField hH j).field = outerColumn z z j := rfl

/-! ## 2. Part 2 — the advection datum -/

/-- **Part 2 (SL5 row 5c).**  For a spacetime field `u` whose slice `z := u(t,·)` is in the class
`A02.MemHInfty` and is divergence free, the order-`m` datum of the advection slice `(u·∇)u(t,·)` is
`∑ⱼ derivDatumStep m j Bⱼ`, where `Bⱼ` is the order-`(m+1)` datum of the column `Wⱼ = outerColumn z z j`.

Space-differentiability of the slice is **not** a separate hypothesis (review N1): it follows from the
`ContDiff ℝ ∞` conjunct `hH.1` of `MemHInfty`, so the lemma is strictly stronger than the earlier
draft that took an explicit `hdiff`.  Copies 088's `isSobolevDatum_laplacian` with a **single**
derivative step.  Lane 100's `advection_eq_sum_partialDeriv_outerColumn` rewrites the field to
`∑ⱼ ∂ⱼWⱼ`; one `isSobolevDatum_partialDeriv` per column with `Z := outerColumnField hH j` gives the
order-`m` datum of `∂ⱼWⱼ` (its output multiplier is definitionally `derivDatumStep m j (Bⱼ)`);
`isSobolevDatum_add` folds the three directions (pairability from `schwartzPairable_of_isSobolevDatum`,
the column partial derivatives being continuous via the `SmoothL2Field` repackaging). -/
theorem isSobolevDatum_advection_sum {u : SpaceTimeField} {t : ℝ} (m : ℕ)
    (hH : MemHInfty (fun x => u (t, x)))
    {B : Fin 3 → RealVectorSobolev ((m : ℝ) + 1)}
    (hB : ∀ j, IsSobolevDatum ((m : ℝ) + 1)
      (outerColumn (fun y => u (t, y)) (fun y => u (t, y)) j) (B j))
    (hdiv : ∀ x, spatialDivergence u t x = 0) :
    IsSobolevDatum (m : ℝ) (fun x => advection u t x)
      (∑ j : Fin 3, derivDatumStep m j (B j)) := by
  -- space-differentiability of the slice from the `ContDiff` conjunct of `MemHInfty`
  have hdiff : ∀ x, DifferentiableAt ℝ (fun y => u (t, y)) x :=
    fun x => (hH.1.differentiable (by simp)).differentiableAt
  -- per direction: the order-`m` datum of `∂ⱼWⱼ`
  have key : ∀ j : Fin 3,
      IsSobolevDatum (m : ℝ)
        (partialDeriv j (outerColumn (fun y => u (t, y)) (fun y => u (t, y)) j))
        (derivDatumStep m j (B j)) := by
    intro j
    exact isSobolevDatum_partialDeriv (Z := outerColumnField hH j) j m (hB j)
  -- pairability of each column partial derivative (continuous, nonnegative order)
  have cont : ∀ j : Fin 3,
      Continuous (partialDeriv j (outerColumn (fun y => u (t, y)) (fun y => u (t, y)) j)) :=
    fun j => ((outerColumnField hH j).directionalField (coordinateVector j)).smooth.continuous
  have hpair : ∀ j : Fin 3,
      SchwartzPairable (partialDeriv j (outerColumn (fun y => u (t, y)) (fun y => u (t, y)) j)) :=
    fun j => schwartzPairable_of_isSobolevDatum (Nat.cast_nonneg m) (cont j) (key j)
  -- fold the three directions with `isSobolevDatum_add`
  have h01 := isSobolevDatum_add (hpair 0) (hpair 1) (key 0) (key 1)
  have hpair01 : SchwartzPairable
      (partialDeriv 0 (outerColumn (fun y => u (t, y)) (fun y => u (t, y)) 0)
        + partialDeriv 1 (outerColumn (fun y => u (t, y)) (fun y => u (t, y)) 1)) :=
    schwartzPairable_of_isSobolevDatum (Nat.cast_nonneg m) ((cont 0).add (cont 1)) h01
  have h012 := isSobolevDatum_add hpair01 (hpair 2) h01 (key 2)
  -- reconcile the folded field with `∑ⱼ ∂ⱼWⱼ`
  have hfield :
      (partialDeriv 0 (outerColumn (fun y => u (t, y)) (fun y => u (t, y)) 0)
          + partialDeriv 1 (outerColumn (fun y => u (t, y)) (fun y => u (t, y)) 1))
          + partialDeriv 2 (outerColumn (fun y => u (t, y)) (fun y => u (t, y)) 2)
        = (fun x => ∑ j : Fin 3,
            partialDeriv j (outerColumn (fun y => u (t, y)) (fun y => u (t, y)) j) x) := by
    funext x; rw [Fin.sum_univ_three]; rfl
  rw [hfield] at h012
  -- rewrite the advection field to divergence form and match the datum sum
  rw [advection_eq_sum_partialDeriv_outerColumn hdiff hdiv, Fin.sum_univ_three]
  exact h012

/-- **Part 2, the `ClassicalSolutionR` slice corollary.**  For a classical whole-space solution `w`
and `t ∈ [0,T)`, **any** given order-`m` datum `N` of the advection slice `(u·∇)u(t,·)` equals
`∑ⱼ derivDatumStep m j Bⱼ`, with `Bⱼ` the order-`(m+1)` column data.  This is the identification the
G1 assembly (SL5 row 5h) applies to `A04.momentum_datum`'s `hN`.  The `MemHInfty` of the slice is
`C01.velocity_slice_memHInfty`, divergence vanishing is the `divergence` field, and uniqueness is
`D01.isSobolevDatum_unique`. -/
theorem advection_slice_datum_eq
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T) (m : ℕ) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T)
    {N : RealVectorSobolev (m : ℝ)}
    (hN : IsSobolevDatum (m : ℝ) (fun x => advection w.velocity t x) N)
    {B : Fin 3 → RealVectorSobolev ((m : ℝ) + 1)}
    (hB : ∀ j, IsSobolevDatum ((m : ℝ) + 1)
      (outerColumn (fun y => w.velocity (t, y)) (fun y => w.velocity (t, y)) j) (B j)) :
    N = ∑ j : Fin 3, derivDatumStep m j (B j) := by
  have hmain := isSobolevDatum_advection_sum (u := w.velocity) (t := t) m
    (NSFormalization.Section4.C01.velocity_slice_memHInfty w ht) hB (w.divergence t ht)
  exact isSobolevDatum_unique hN hmain

end NSFormalization.Section4.A04
