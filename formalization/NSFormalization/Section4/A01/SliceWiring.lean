import NSFormalization.Section4.A01.L2Descent
import NSFormalization.Section4.A01.AprioriRows
import NSFormalization.Section4.C01.Evolution

/-!
# A01 unit A3 row (i)/(ii) — wiring the smooth slice `Z` to a real `ClassicalSolutionR` (lane 157)

Lanes 149/151/153 reduced the a-priori rows to the single carrier hand-off `hslice`:
`AprioriRows.sobolevSpace_norm_le_sobolevNormAt` (the row-(ii) converse) still carries the smooth
slice `z`, the finiteness `hfin`, and the per-word bound `hword_jet`, and `L2Descent.hword_jet_full`
discharges `hword_jet` for **every** `n ≤ q+1` once a `Z : SmoothL2Field Space` with `⇑(U t) =ᵐ
Z.field` is supplied.  This module supplies `Z`, `hfin` and `hslice`-driven wiring **from a genuine
`ClassicalSolutionR`**, closing residual rows #1 and #2 of `research/A01/REVIEW_L2_DESCENT.md` §3 and
producing the packaged reduction for row #3.

## What is proved

* The former `velocitySliceSmoothL2` name was a pure alias for `C01.velocityField`; its only
  term-level use is in the row-(ii) wiring below, which now takes `C01.velocityField` directly.
  The compatibility theorem `velocitySliceSmoothL2_field` remains as a direct `rfl` lemma.
* **`sobolevENorm_slice_ne_top`** (#2, S) — the slice finiteness `hfin`: the order-`(q+1)` energy
  norm of a velocity slice of a classical solution is finite, straight from
  `ClassicalSolutionR.sobolev`'s datum (`sobolevENorm_le_of_isSobolevDatum`, a datum has finite
  enorm).  No `⊤`-vacuity (LESSONS 09-14 0707Z/149).
* **`sobolevSpace_norm_le_sobolevNormAt_of_solution`** (#2, the row-(ii) converse on the real
  solution) — for a `ClassicalSolutionR w`, a cylinder pair `(u, U)` on `[0,S]` (`S < T`) with
  angle invariance `hu`, descent `hU : ordinaryLift (U t) = value 1 (u t)`, and the carrier
  hand-off `hslice : ∀ t, (fun x => w.velocity (↑t,x)) =ᵐ ⇑(U t)`:
  `‖u t‖ ≤ jetSobolevConst (q+1) · sobolevNormAt (q+1) w.velocity ↑t` at every `t`.  This is
  `AprioriRows.sobolevSpace_norm_le_sobolevNormAt` with **all three** of its remaining hypotheses
  discharged from the solution: `hz` by `D01.contDiff_slice`, `hfin` by `sobolevENorm_slice_ne_top`,
  and `hword_jet` by `L2Descent.hword_jet_full` fed the carrier `C01.velocityField w hST t`.
  **No named hypothesis is left except the carrier hand-off `hslice`.**
* **`isSobolevDatum_ordinary_of_hslice`** (#3, the datum transport) — `hslice` carries the physical
  slice's order-`m` datum onto the abstract carrier `⇑(U t)` at every order (`IsSobolevDatum.congr_field`,
  the mirror of lane 140's `EulerPairing.exists_isSobolevDatum_m_of_ae`).
* **`apriori_rows_of_hslice`** (#3, the packaged reduction) — from `w`, `(u, U)` and `hslice` alone,
  **both** directions of the a-priori row comparison at once: the forward order-2 cap
  `sobolevNormAt 2 w.velocity ↑t ≤ 16·‖u t‖` (`OrderTwoCap.sobolevNormAt_two_le_of_cylinder`) **and**
  the converse `‖u t‖ ≤ jetSobolevConst (q+1) · sobolevNormAt (q+1) w.velocity ↑t`.  So the whole
  row (i)/(ii) hand-off is reduced to the single `hslice`.

## The one remaining obligation (carrier constructor B1/B2)

`localTheory_on_prescribed_horizon` (`Horizon.lean:137`; `exists_local_shape_of_aprioriBound` at `:166` only gives `∃ T' ≤ S`) yields the cylinder pair `(u, U)` on
`Icc 0 S` (with `S := horizonOf … = S`), the descent `ordinaryLift (U t) = value 1 (u t)` and the
angle invariance, but **not** a `ClassicalSolutionR` and **not** `hslice`.  No `Section4/A01` module
constructs a `ClassicalSolutionR` from that cylinder pair (verified by
`grep ClassicalSolutionR Section4/A01`, and by lane 149's review; the structure appears only as an
*input* — `GronwallInstance`, `AprioriRows`, `PressureGauge`).  Every theorem here is therefore
stated against a *given* `w` and consumes `hslice`.  Row (i) is now the single constructor

```
-- with the ClassicalSolutionR horizon `T` strictly above the cylinder path horizon `S`:
∀ {q ν} (hq : 6 ≤ q) {a : SmoothL2Field Space} {S : ℝ} (hν : 0 < ν) (hS : 0 < S)
  {F hF R} (hb : HasAprioriBound hq hν a F hF R) …,
  -- for the (u, U) of `localTheory_on_prescribed_horizon … hb` on `Icc 0 S`:
  ∃ (a' : SpatialField) (f' : SpaceTimeField) (T : ℝ) (hST : S < T)
    (w : ClassicalSolutionR ν a' f' T),
      ∀ t : Icc (0 : ℝ) S, (fun x : Space => w.velocity (↑t, x)) =ᵐ[volume] ⇑(U t)
```

i.e. "the abstract mild carrier `U` is a.e. the velocity slice of an actual classical solution on a
strictly longer horizon".  Once that single existence is provided, `apriori_rows_of_hslice` gives
both a-priori rows and `HasAprioriBound`'s consumer closes (modulo unit (iv) `hinv`, which is already
carried by the consumer's pair but still owed on the supply side A3-M2, where the `u` that
`HasAprioriBound` quantifies over carries only the Duhamel constraint — review 157 N2; and the
Grönwall endpoint of row (iii)).  The constructor is unit B1 (L) + B2 (S) over C1b/C1c plus
row (v): a multi-lane obligation, one statement (review 157 N3).

`#print axioms` is the standard three for every declaration (`research/A01/axioms_slice_wiring.lean`).
-/

noncomputable section

namespace NSFormalization.Section4.A01

open Set MeasureTheory
open NSFormalization.Section4.D01
open NSFormalization.Section4.A04 (sobolevNormAt)
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR)
open NSFormalization.Paper3 (RealVectorSobolev)
open NavierStokes.ProblemStatement (Space)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerCylinderSobolev EulerPressureSpatialRegularity EulerLpTranslation
open scoped ENNReal ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-! ## 1. The jet carrier `Z` from the classical velocity slice (residual row #1) -/

/-- **#1 — the order-`(q+1)` jet carrier at a time `t ∈ [0,S]`, `S < T`.**  This is *not* a new
`SmoothL2Field`: it is `C01.velocityField w hST t` (`Evolution.lean:115`), whose underlying field is
already the velocity slice `fun x => w.velocity (↑t, x)` and whose `smooth`/`integrable` proofs come
from unit U1 (`velocity_slice_smoothL2`).  Reused verbatim so the smoothness and all-order `L²` jet
finiteness are not reproved (LESSONS: do not duplicate an existing `SmoothL2Field` construction). -/
/- The former alias is retired; the carrier is `C01.velocityField w hST t`. -/
@[simp] theorem velocitySliceSmoothL2_field {ν : ℝ} {a : SpatialField} {f : SpaceTimeField}
    {S T : ℝ} (w : ClassicalSolutionR ν a f T) (t : Icc (0 : ℝ) S) (hST : S < T) :
    (C01.velocityField w hST t).field = fun x : Space => w.velocity (↑t, x) := rfl

/-! ## 2. Slice finiteness and the row-(ii) converse on the real solution (residual row #2) -/

/-- **#2 — the slice `hfin`.**  The order-`(q+1)` energy norm of a velocity slice of a classical
solution is finite at every interior time `t ∈ [0,T)`.  Direct from `ClassicalSolutionR.sobolev`:
its order-`(q+1)` datum `G t` realizes the slice, and a datum has finite enorm, so the datum
infimum `sobolevENorm` is `≤ ‖G t‖ₑ ≠ ⊤`.  (Same move as `OrderTwoCap.sobolevENorm_two_ne_top`; no
`⊤`-vacuity — LESSONS 09-14 0707Z/149.) -/
theorem sobolevENorm_slice_ne_top_order {m : ℕ} {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    sobolevENorm (m : ℝ) (fun x : Space => w.velocity (t, x)) ≠ ⊤ := by
  obtain ⟨G, _, hGd⟩ := w.sobolev m
  exact ne_top_of_le_ne_top (by simp) (sobolevENorm_le_of_isSobolevDatum (hGd t ht))

/-- The order-`q+1` spelling retained for existing consumers. -/
theorem sobolevENorm_slice_ne_top {q : ℕ} {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    sobolevENorm ((q + 1 : ℕ) : ℝ) (fun x : Space => w.velocity (t, x)) ≠ ⊤ :=
  sobolevENorm_slice_ne_top_order (m := q + 1) w ht

/-- **#2 — the row-(ii) converse on a genuine `ClassicalSolutionR`.**  For a classical solution `w`
on `[0,T)`, a cylinder pair `(u, U)` over the compact slab `[0,S] ⊂ [0,T)` (`S < T`) with angle
invariance `hu`, descent `hU : ordinaryLift (U t) = value 1 (u t)`, and the carrier hand-off
`hslice : ∀ t, (fun x => w.velocity (↑t,x)) =ᵐ ⇑(U t)`, the cylinder-array norm is bounded at every
time by the order-`(q+1)` energy norm with the explicit `t`-free constant `jetSobolevConst (q+1)`:

`‖u t‖ ≤ jetSobolevConst (q+1) · sobolevNormAt (q+1) w.velocity ↑t`.

This is `AprioriRows.sobolevSpace_norm_le_sobolevNormAt` with its three remaining hypotheses all
discharged from the solution: `hz` by `D01.contDiff_slice w.velocity_smooth` (each `t ≤ S < T` lies
in the smoothness slab `[0,T)`), `hfin` by `sobolevENorm_slice_ne_top`, and `hword_jet` (for **all**
`n ≤ q+1`) by `L2Descent.hword_jet_full` fed the carrier `C01.velocityField w hST t` and the a.e.
identity `(hslice t).symm`.  **The only named hypothesis left is the carrier hand-off `hslice`.** -/
theorem sobolevSpace_norm_le_sobolevNormAt_of_solution {q : ℕ} {ν : ℝ} {a : SpatialField}
    {f : SpaceTimeField} {S T : ℝ} (hST : S < T) (w : ClassicalSolutionR ν a f T)
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (hslice : ∀ t : Icc (0 : ℝ) S, (fun x : Space => w.velocity (↑t, x)) =ᵐ[volume] ⇑(U t)) :
    ∀ t : Icc (0 : ℝ) S,
      ‖u t‖ ≤ jetSobolevConst (q + 1) * sobolevNormAt ((q + 1 : ℕ) : ℝ) w.velocity ↑t := by
  refine sobolevSpace_norm_le_sobolevNormAt u w.velocity
    (fun t => contDiff_slice w.velocity_smooth ⟨t.2.1, lt_of_le_of_lt t.2.2 hST⟩)
    (fun t => sobolevENorm_slice_ne_top w ⟨t.2.1, lt_of_le_of_lt t.2.2 hST⟩)
    (fun t n hn wrd => ?_)
  exact hword_jet_full (u t) (fun θ => hu θ t) (U t) (hU t)
    (C01.velocityField w hST t) (hslice t).symm n hn wrd

/-! ## 3. The packaged reduction of both a-priori rows to `hslice` (residual row #3) -/

/-- **#3 — datum transport across the carrier hand-off.**  Under `hslice`, the physical slice's
order-`m` datum (from `ClassicalSolutionR.sobolev`) is also a datum of the abstract carrier `⇑(U t)`
at every order, by `IsSobolevDatum.congr_field`.  This is the mirror direction of lane 140's
`EulerPairing.exists_isSobolevDatum_m_of_ae` (which moves `⇑U`'s datum onto a physical field); here
the classical solution *supplies* the regularity and `hslice` moves it onto the mild carrier. -/
theorem isSobolevDatum_ordinary_of_hslice {ν : ℝ} {a : SpatialField} {f : SpaceTimeField}
    {S T : ℝ} (hST : S < T) (w : ClassicalSolutionR ν a f T)
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hslice : ∀ t : Icc (0 : ℝ) S, (fun x : Space => w.velocity (↑t, x)) =ᵐ[volume] ⇑(U t))
    (m : ℕ) (t : Icc (0 : ℝ) S) :
    ∃ A : RealVectorSobolev (m : ℝ), IsSobolevDatum (m : ℝ) (⇑(U t)) A := by
  obtain ⟨G, _, hGd⟩ := w.sobolev m
  exact ⟨G ↑t, IsSobolevDatum.congr_field (hGd ↑t ⟨t.2.1, lt_of_le_of_lt t.2.2 hST⟩) (hslice t)⟩

/-- **#3 — the packaged reduction: both a-priori rows from `hslice` alone.**  Given a classical
solution `w` on `[0,T)` and a cylinder pair `(u, U)` over `[0,S]` (`S < T`) with `hu`, `hU` and the
single carrier hand-off `hslice`, **both** directions of the a-priori row comparison hold at once:

* forward (order-2 driver, `OrderTwoCap.sobolevNormAt_two_le_of_cylinder`):
  `sobolevNormAt 2 w.velocity ↑t ≤ 16·‖u t‖`;
* converse (`sobolevSpace_norm_le_sobolevNormAt_of_solution`):
  `‖u t‖ ≤ jetSobolevConst (q+1)·sobolevNormAt (q+1) w.velocity ↑t`.

So the entire row (i)/(ii) hand-off between the cylinder sup-norm and the energy norm is reduced to
the single a.e. identity `hslice`; the one remaining obligation is the carrier constructor B1/B2 of
the module header (produce `w` and `hslice` for the `(u, U)` of `exists_local_shape_of_aprioriBound`,
on a strictly longer horizon `T > S`). -/
theorem apriori_rows_of_hslice {q : ℕ} {ν : ℝ} {a : SpatialField} {f : SpaceTimeField}
    {S T : ℝ} (hST : S < T) (hq : 4 ≤ q) (w : ClassicalSolutionR ν a f T)
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (hslice : ∀ t : Icc (0 : ℝ) S, (fun x : Space => w.velocity (↑t, x)) =ᵐ[volume] ⇑(U t)) :
    (∀ t : Icc (0 : ℝ) S, sobolevNormAt (2 : ℝ) w.velocity ↑t ≤ 16 * ‖u t‖) ∧
      (∀ t : Icc (0 : ℝ) S,
        ‖u t‖ ≤ jetSobolevConst (q + 1) * sobolevNormAt ((q + 1 : ℕ) : ℝ) w.velocity ↑t) :=
  ⟨sobolevNormAt_two_le_of_cylinder u U hu hU hq w.velocity hslice,
    sobolevSpace_norm_le_sobolevNormAt_of_solution hST w u U hu hU hslice⟩

end NSFormalization.Section4.A01
