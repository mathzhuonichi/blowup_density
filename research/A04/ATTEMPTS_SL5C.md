# A04 unit G1, SL5 row 5c — attempts (lane 105)

Module: `formalization/NSFormalization/Section4/A04/NonlinearDatum.lean`.
Row 5c of `research/A04/SL5_SPLIT.md`: the order-`m` datum of the advection slice as the sum over
`j` of the derivative data of the outer-product columns `Wⱼ = uⱼ·u`.

## Route as executed

**Part 1 — `outerColumn_smoothL2` (the `SmoothL2Field` wrapper of each column).**
The **datum route** was used, not a Leibniz jet expansion.  `A02.MemHInfty z` is definitionally
`ContDiff ℝ ∞ z ∧ (∀ m : ℕ, ∃ A, IsSobolevDatum (m:ℝ) z A)` (`A02/SolutionClass.lean:88`).

* Smoothness of `Wⱼ = fun x => (z x j) • z x`: `contDiff_euclidean.mp hzc j` gives
  `ContDiff ℝ ∞ (fun x => z x j)` (the `j`-th coordinate of `z`), then `ContDiff.smul` against
  `hzc : ContDiff ℝ ∞ z`.  Cheap, no `L^∞` factor.
* Square-integrable jets, **without** the Leibniz argument REVIEW_SL5A F3 anticipated:
  1. `z` is `A03.SmoothL2` (its jet form): `⟨hzc, memHInfty_jets hzc hH.2⟩`
     (`D01.memHInfty_jets`, `DatumToJets.lean:298`).
  2. `A03.SmoothL2.memHmVector` (`VectorTameProduct.lean:346`) makes `z` admissible at every integer
     order.
  3. `A04.exists_outerColumn_datum` (row 5b, lane 102) then hands the column a datum at every order
     `≥ 2`; orders `0, 1` are covered by lowering the order-`max n 2` datum with
     `A04.isSobolevDatum_lowerVectorL` (088) — the uniform `max n 2` handles all `n` in one branch
     (lowering from `k` to `k` when `n ≥ 2` is the identity direction).
  4. `D01.memHInfty_jets hcontdiff hdata` converts "smooth + datum at every order" into
     `∀ n, MemLp (iteratedFDeriv ℝ n Wⱼ) 2 volume`, the second field of `A05.SmoothL2`.
  5. `⟨hcontdiff, memHInfty_jets hcontdiff hdata⟩` is the anonymous constructor of `A05.SmoothL2 Wⱼ`
     directly (its body is `ContDiff ∧ ∀ n, MemLp …`), so the `SmoothSquareIntegrableJets`
     ↔ `MemHInfty` iff wrapper is not even needed.

Minimal hypothesis: `MemHInfty z` **alone** (the datum-at-every-order route goes through), not
`SmoothL2 z + MemHInfty z` — `A03/A05.SmoothL2 z` is recovered from `MemHInfty z` internally.

Packaged as `outerColumnField hH j : SmoothL2Field Space := ⟨outerColumn z z j, _, _⟩` with
`outerColumnField_field : (outerColumnField hH j).field = outerColumn z z j := rfl`.

**Part 2 — `isSobolevDatum_advection_sum` + `advection_slice_datum_eq`.**
Copied 088's `isSobolevDatum_laplacian` with **one** derivative step:

* `key j := isSobolevDatum_partialDeriv (Z := outerColumnField hH j) j m (hB j)` — one derivative
  step per column.  Relies on `(outerColumnField hH j).field ≡ outerColumn z z j` by `rfl`
  (projection of the constructor); the output multiplier `WithLp.toLp 2 fun i => …` is definitionally
  `derivDatumStep m j (B j)`, so the `have key j : … (derivDatumStep m j (B j))` ascription closes by
  defeq.
* continuity of each `∂ⱼWⱼ` from `((outerColumnField hH j).directionalField (coordinateVector j)).smooth.continuous`
  (the `directionalField` `.field` is `partialDeriv j Wⱼ` by `rfl`), exactly 088's pattern;
  pairability via `schwartzPairable_of_isSobolevDatum (Nat.cast_nonneg m)`.
* `isSobolevDatum_add` over the three directions (`D01.isSobolevDatum_add`, the `SchwartzPairable`
  version, as in 088), field reconciled by `Fin.sum_univ_three`.
* the field is rewritten to `∑ⱼ ∂ⱼWⱼ` with lane 100's `advection_eq_sum_partialDeriv_outerColumn`
  and the datum sum matched by `Fin.sum_univ_three`.
* corollary `advection_slice_datum_eq`: discharges the hypotheses of the main lemma from a
  `ClassicalSolutionR` (`C01.velocity_slice_memHInfty`, `D01.contDiff_slice`, the `divergence` field)
  and pins any given `N` to the sum by `D01.isSobolevDatum_unique`.

## Failed / rejected approaches

* **Leibniz jet expansion for Part 1 (the F3 route) — deliberately not attempted.**
  `A05.SmoothL2 (uⱼ • u)` by expanding `iteratedFDeriv ℝ n (uⱼ • u)` with the multilinear Leibniz
  rule and bounding the smooth scalar factor `uⱼ` and its jets in `L^∞`.  Rejected in favour of the
  datum route: no reusable "smooth bounded scalar × `SmoothL2` ∈ `SmoothL2`" closure exists in the
  tree (searched `A03/A05/*`, `LpSmoothFieldAlgebra.lean`; only `mapField`/`addField`/`derivative`/
  `directionalField` and Sobolev-*norm* products `outerProductTame`/`tameProductVector` are present,
  none at the jet level for a scalar·vector product), and the datum route reuses row 5b wholesale.

* **`set z := fun y => u (t, y)` in Part 2 — abandoned.**  `set` introduces `z` as an opaque local
  and rewrites existing occurrences, but (i) it retypes `hdiff`/`hdiv` so they no longer match
  `advection_eq_sum_partialDeriv_outerColumn`'s literal `fun y => u (t, y)` hypotheses, and (ii) the
  `rw` of that lemma reintroduces fresh unfolded `fun y => u (t, y)` occurrences that `set` cannot
  fold, so the final `exact h012` fails to unify `outerColumn z z j` (opaque fvar) with the fresh
  `outerColumn (fun y => u (t, y)) …`.  Resolved by spelling `fun y => u (t, y)` out everywhere so
  every field term is syntactically the one lane 100's identity produces.

* **Passing `A05.SmoothL2 z` as a separate hypothesis — dropped as redundant.**  It is derivable from
  `MemHInfty z` (`⟨hH.1, memHInfty_jets hH.1 hH.2⟩`), so the task's fallback signature
  `SmoothL2 z + MemHInfty z` is not needed.

## Commands (from the lane worktree, `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, lake from `verification/`)

* `lake build NSFormalization.Section4.A04.NonlinearColumns NSFormalization.Section4.A04.AdvectionDivergence NSFormalization.Section4.C01.VelocityJets` → `Build completed successfully (9900 jobs).`
* `lake build NSFormalization.Section4.A04.NonlinearDatum` → `Built … (4.1s)`, `Build completed successfully (9901 jobs).` (only replayed upstream `SobolevDirectionalDerivative` deprecation warning).
* `lake env lean ../formalization/NSFormalization/Section4/A04/NonlinearDatum.lean` → printed nothing, exit 0.
* `lake env lean ../research/A04/axioms_sl5c.lean` → all 5 public declarations `depends on axioms: [propext, Classical.choice, Quot.sound]`, exit 0.
* `grep -nE 'sorry|admit|native_decide|maxHeartbeats'` and axiom-keyword grep → no match.

## Row 5h (added in the same lane after the 5c review)

Module: `formalization/NSFormalization/Section4/A04/NonlinearBound.lean` (imports `NonlinearDatum`,
`NonlinearPairing`).  Delivers the `hnl` of `A04.inner_energy_assembly`
(`HighEnergy.lean:100`): `−⟪G, N⟫_ℝ ≤ gradientSobolevNormAt (m:ℝ) u t · (outerSobolevENorm (m:ℝ) (u t·) (u t·)).toReal`.

### Route as executed

The analytic core (`inner_component_advection`, `inner_datum_advectionDir`, `inner_advection_bound`)
was authored by the lane-105 reviewer (`REVIEW_SL5C.md` §5, verified compiling as `/tmp/sl5h/full.lean`)
and is reproduced verbatim with credit.  I added the `ClassicalSolutionR` corollary
`inner_advection_bound_slice`, which discharges `inner_advection_bound`'s hypotheses from a solution:

* `hsl : A05.SmoothL2 slice` from `C01.velocity_slice_smoothL2 w ht'`.
* `hmv : MemHmVector (m+1) slice` from `A03.SmoothL2.memHmVector hsl (m+1)`, feeding
  `exists_outerColumn_datum_succ m (by omega) hmv j` (row 5b) `choose`n into per-column data `B, hB`.
* order-`(m+1)` slice datum `A'` from the slice's `MemHInfty` (`C01.velocity_slice_memHInfty`, integer
  order `m+1`) cast to `(m:ℝ)+1` by `isSobolevDatum_castOrder (cast_mid_order m)`.
* `N = ∑ⱼ derivDatumStep m j Bⱼ` from row 5c's `advection_slice_datum_eq w m ht' hN hB`.
* `Ioo 0 T → Ico 0 T` glue: `ht' := ⟨le_of_lt ht.1, ht.2⟩` (review N4).

Then `inner_advection_bound m hsl hG hA' hB hNsum` closes it.

The three order reconciliations are exactly the reviewer's §6 list: `Cⱼ := Λ_{m+1→m} Bⱼ`
(`isSobolevDatum_lowerVectorL`), `G = Λ_{m+1→m} A'` (`isSobolevDatum_unique`), and
`Dⱼ(Λ A'ᵢ) = Λ(Dⱼ A'ᵢ)` (`directionalDerivative_orderLowering_comm` + `real_inner_lowering_transfer`,
with the `(m:ℝ)+1−1 = (m:ℝ)` normalisation an explicit `simp only [show … from by ring]`).

### Conformance

`research/A04/axioms_sl5c.lean` now contains an `example` that feeds `inner_advection_bound_slice`
into the `hnl` slot of `inner_energy_assembly` (placeholders for the other slots) and derives the full
energy inequality — so the bound has exactly the shape the assembly consumes.  It compiles.

### Review notes folded in (5c, review N1–N3)

* **N1** — dropped the redundant `hdiff` hypothesis of `isSobolevDatum_advection_sum`; it is now
  derived internally as `fun x => (hH.1.differentiable (by simp)).differentiableAt` from the `ContDiff`
  conjunct of `MemHInfty`, making the lemma strictly stronger.  `advection_slice_datum_eq` lost its
  `hcd`/`contDiff_slice` plumbing accordingly (and `contDiff_slice` was dropped from the `open` list).
* **N2** — `outerColumnField` now binds `let h := outerColumn_smoothL2 hH j` once instead of computing
  it twice; `outerColumnField_field := rfl` still holds.
* **N3** — corrected the `memHInfty_jets` citation `DatumToJets.lean:298 → :287` in the module header
  and in this file.

### Failed / rejected approaches (5h)

None specific to 5h — the reviewer's core compiled first try in my worktree
(`lake env lean /tmp/sl5h/full.lean`, exit 0), and the corollary's only friction was the standard
`A05.SmoothL2 ≡ A03.SmoothL2` defeq when calling `A03.SmoothL2.memHmVector` on the slice's
`velocity_slice_smoothL2` output (resolved automatically, both defs share the body) and the integer
vs real order of the `(m+1)` datum (resolved by `cast_mid_order`, 088).

### Commands (5h)

* `lake build NSFormalization.Section4.A04.NonlinearBound` → `Built … (3.9s)`, `Build completed successfully (9903 jobs).`
* `lake env lean ../formalization/NSFormalization/Section4/A04/NonlinearBound.lean` → silent, exit 0.
* `lake env lean ../formalization/NSFormalization/Section4/A04/NonlinearDatum.lean` (after N1–N3) → silent, exit 0.
* `lake env lean ../research/A04/axioms_sl5c.lean` → all 9 declarations standard 3 axioms, conformance `example` compiles, exit 0.
