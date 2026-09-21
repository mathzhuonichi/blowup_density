# ATTEMPTS — lane 157 (`157-A01-slice-wiring`): wiring the smooth slice `Z` / `hslice` to a real `ClassicalSolutionR`

Module: `formalization/NSFormalization/Section4/A01/SliceWiring.lean` (namespace
`NSFormalization.Section4.A01`). Conformance: `research/A01/axioms_slice_wiring.lean`.
Rows #1–#3 of `research/A01/REVIEW_L2_DESCENT.md` §3.

## What was proved (names + exact statements)

1. **`velocitySliceSmoothL2` (#1, S)** — the order-`(q+1)` jet carrier `Z` at a time `t ∈ [0,S]`,
   `S < T`:
   ```
   def velocitySliceSmoothL2 {ν a f S T} (w : ClassicalSolutionR ν a f T)
       (t : Icc 0 S) (hST : S < T) : SmoothL2Field Space := C01.velocityField w hST t
   @[simp] theorem velocitySliceSmoothL2_field … :
       (velocitySliceSmoothL2 w t hST).field = fun x => w.velocity (↑t, x) := rfl
   ```
   **Reuse, not duplication.** `C01.velocityField` (`Section4/C01/Evolution.lean:115`) already IS the
   velocity-slice `SmoothL2Field` with `field = fun x => u.velocity (t.1, x)` (its `_field` lemma is
   `rfl`); its `smooth`/`integrable` come from unit U1 `velocity_slice_smoothL2`
   (`C01/VelocityJets.lean:85`). So `velocitySliceSmoothL2 := C01.velocityField` and the `_field` rfl
   is the only new content. (`C01.velocitySliceField` in `MomentumCarrierB.lean:93` is the same object
   with a plain `t ∈ Ico 0 T` index; `velocityField` was chosen because its `Icc 0 S`+`hST : S < T`
   signature matches the cylinder pair exactly.) — LESSONS "do not duplicate an existing
   `SmoothL2Field`".

2. **`sobolevENorm_slice_ne_top` (#2, S)** — the slice finiteness `hfin`:
   ```
   theorem sobolevENorm_slice_ne_top {q ν a f T} (w : ClassicalSolutionR ν a f T)
       {t} (ht : t ∈ Ico 0 T) :
       sobolevENorm ((q+1 : ℕ) : ℝ) (fun x => w.velocity (t, x)) ≠ ⊤
   ```
   Proof: `w.sobolev (q+1)` gives a datum `G t` of the slice; `sobolevENorm_le_of_isSobolevDatum`
   makes `sobolevENorm ≤ ‖G t‖ₑ`, and `‖G t‖ₑ ≠ ⊤` (`by simp`). Same pattern as
   `OrderTwoCap.sobolevENorm_two_ne_top`. No `⊤`-vacuity (LESSONS 09-14 0707Z/149).

3. **`sobolevSpace_norm_le_sobolevNormAt_of_solution` (#2, the converse on the real solution)** — the
   row-(ii) converse with **no** named hypothesis left except the carrier hand-off `hslice`:
   ```
   theorem sobolevSpace_norm_le_sobolevNormAt_of_solution {q ν a f S T}
       (hST : S < T) (w : ClassicalSolutionR ν a f T)
       (u : C(Icc 0 S, SobolevSpace 1 (q+1))) (U : C(Icc 0 S, EulerMeanSolenoidal.L2))
       (hu : ∀ θ t, sobolevTranslation 1 (q+1) (0,θ) (u t) = u t)
       (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
       (hslice : ∀ t : Icc 0 S, (fun x => w.velocity (↑t, x)) =ᵐ[volume] ⇑(U t)) :
       ∀ t : Icc 0 S, ‖u t‖ ≤ jetSobolevConst (q+1) * sobolevNormAt ((q+1 : ℕ) : ℝ) w.velocity ↑t
   ```
   Proof: `AprioriRows.sobolevSpace_norm_le_sobolevNormAt u w.velocity hz hfin hword_jet` at horizon
   `T := S`, with all three discharged from the solution — `hz t := D01.contDiff_slice
   w.velocity_smooth ⟨t.2.1, lt_of_le_of_lt t.2.2 hST⟩` (each `t ≤ S < T` is in the smoothness slab
   `Ico 0 T`), `hfin t := sobolevENorm_slice_ne_top …`, and `hword_jet t n hn w :=
   L2Descent.hword_jet_full (u t) (fun θ => hu θ t) (U t) (hU t) (velocitySliceSmoothL2 w t hST)
   (hslice t).symm n hn w`. The `hword_jet_full` conclusion mentions `Z.field`, which is defeq
   `fun x => w.velocity (↑t,x)` (the `_field` rfl), so the two eLpNorm terms unify by `exact`.

4. **`isSobolevDatum_ordinary_of_hslice` (#3, datum transport)** — `hslice` moves the physical slice's
   order-`m` datum onto the mild carrier `⇑(U t)`:
   ```
   theorem isSobolevDatum_ordinary_of_hslice {ν a f S T}
       (hST : S < T) (w : ClassicalSolutionR ν a f T) (U : C(Icc 0 S, EulerMeanSolenoidal.L2))
       (hslice : ∀ t : Icc 0 S, (fun x => w.velocity (↑t,x)) =ᵐ[volume] ⇑(U t)) (m) (t : Icc 0 S) :
       ∃ A : RealVectorSobolev (m:ℝ), IsSobolevDatum (m:ℝ) (⇑(U t)) A
   ```
   `w.sobolev m` gives the physical datum `G ↑t`; `IsSobolevDatum.congr_field … (hslice t)` transports
   it onto `⇑(U t)`. This is the mirror direction of lane 140's `EulerPairing.exists_isSobolevDatum_m_of_ae`
   (which needs `HasWeakDerivsL2 (⇑U) m` to go `U → physical`; here the classical solution *supplies*
   the regularity and `hslice` moves it onto `U`).

5. **`apriori_rows_of_hslice` (#3, the packaged reduction)** — both a-priori rows from `hslice` alone:
   ```
   theorem apriori_rows_of_hslice {q ν a f S T}
       (hST : S < T) (hq : 4 ≤ q) (w : ClassicalSolutionR ν a f T)
       (u …) (U …) (hu …) (hU …) (hslice …) :
       (∀ t : Icc 0 S, sobolevNormAt 2 w.velocity ↑t ≤ 16 * ‖u t‖) ∧
       (∀ t : Icc 0 S, ‖u t‖ ≤ jetSobolevConst (q+1) * sobolevNormAt ((q+1 : ℕ) : ℝ) w.velocity ↑t)
   ```
   forward = `OrderTwoCap.sobolevNormAt_two_le_of_cylinder`; converse = theorem 3. So the whole
   row (i)/(ii) hand-off between the cylinder sup-norm and the energy norm reduces to the single
   `hslice`.

All five (+ the `_field` rfl) print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity
fires each row theorem on `A04.zeroSol 1 2` with `u := 0`, `U := 0` (genuine `0 ≤ …` conclusions).

## The remaining obligation (carrier constructor B1 + B2 over C1b/C1c, plus row (v)) — one statement, L, multi-lane (review 157 N3)

`Horizon.localTheory_on_prescribed_horizon` (`Horizon.lean:137`) yields the cylinder pair `(u, U)` on `Icc 0 S` (`exists_local_shape_of_aprioriBound`, `:166`, only gives `∃ T' ≤ S` — review 157 N1)
on `Icc 0 S` (with `S := horizonOf … = S`), the descent `ordinaryLift (U t) = value 1 (u t)` and the
angle invariance — but **not** a `ClassicalSolutionR` and **not** `hslice`. **No `Section4/A01` module
constructs a `ClassicalSolutionR` from that cylinder pair** (`grep ClassicalSolutionR
formalization/NSFormalization/Section4/A01/*.lean`: the structure appears only as an *input* —
`GronwallInstance`, `AprioriRows`, `PressureGauge`, `ProjectedEquation`, `RadialPotential`,
`ConvectionDivergence`; confirmed by lane 149's review). Row (i) is therefore reduced to the single
constructor, with the `ClassicalSolutionR` horizon `T` **strictly above** the cylinder path horizon
`S` (so `velocitySliceSmoothL2` / `contDiff_slice` have `↑t ≤ S < T ∈ Ico 0 T` at every `t`):

```
∀ {q ν} (hq : 6 ≤ q) {a : SmoothL2Field Space} {S} (hν : 0 < ν) (hS : 0 < S)
  {F hF R} (hb : HasAprioriBound hq hν a F hF R) …,
  -- for the (u, U) of `localTheory_on_prescribed_horizon … hb` on `Icc 0 S`:
  ∃ (a' : SpatialField) (f' : SpaceTimeField) (T) (hST : S < T)
    (w : ClassicalSolutionR ν a' f' T),
      ∀ t : Icc 0 S, (fun x => w.velocity (↑t, x)) =ᵐ[volume] ⇑(U t)
```

i.e. "the abstract mild carrier `U` is a.e. the velocity slice of an actual classical solution on a
strictly longer horizon". Once provided, `apriori_rows_of_hslice` gives both a-priori rows. This is the
row-(i)/B1-B2 content of `research/A01/A01_SPLIT.md`; it needs the mild ⇒ classical bridge (the
HeliCorgi/OpenAI local-existence stack producing a `ClassicalSolutionR` whose velocity slices are
`U`'s representatives), plus the datum/forcing bridge (residual row (v)).

## Failed / rejected approaches

* **Building `Z` inline from `contDiff_slice` + `memHInfty_jets`** (as `exists_smoothL2Field_of_memHInfty`
  does) — rejected: it re-proves `smooth`/`integrable` that `C01.velocityField` already carries, i.e.
  a duplicate `SmoothL2Field` construction. Reused `C01.velocityField` instead (LESSONS). Also
  `exists_smoothL2Field_of_memHInfty` returns an *existential*, not a `def` with a `field` rfl, so it
  cannot supply the concrete `Z` that `hword_jet_full` and the `_field` normal form need.
* **Constructing a `ClassicalSolutionR` from `(u, U)` inside this lane** (to *produce* `hslice`
  rather than consume it) — not attempted: no A01 module does this, and it is the mild ⇒ classical
  bridge (B1/B2), an L-unit outside this lane's scope. Delivered the reduction instead.
* **A datum-transport clause via `exists_isSobolevDatum_m_of_ae` (U → physical) inside
  `apriori_rows_of_hslice`** — the reverse direction needs `HasWeakDerivsL2 (⇑(U t)) m` at *all*
  orders, which the cylinder descent gives only with an order bound; the physical → `U` direction
  (`isSobolevDatum_ordinary_of_hslice`) is free from `w.sobolev` + `hslice` and is what the reduction
  actually wants, so that is the clause delivered.

## Notes for the next lane

* `sobolevSpace_norm_le_sobolevNormAt_of_solution` and `apriori_rows_of_hslice` are stated over the
  cylinder horizon `Icc 0 S` (the pair's index); the `AprioriRows.sobolevSpace_norm_le_sobolevNormAt`
  they call is generic in its horizon, instantiated at `T := S`.
* `SliceWiring` belongs to no registered contract closure yet (same status as `AprioriRows`,
  `L2Descent`, `CarrierWords`, `OrderTwoCap`); add all of them to the next A01 contract bundle so
  `make test` keeps compiling them.
* The two `IsSobolevDatum` defs (`A02/SolutionClass.lean:79`, `D01/SmoothDatum.lean:237`) have
  token-identical bodies and unify by defeq; `w.sobolev`'s datum feeds `D01.sobolevENorm_le_of_isSobolevDatum`
  directly (as A04.Continuity / A02.Bounds already do).
