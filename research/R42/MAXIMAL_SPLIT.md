# R42 — the `IsMaximalSolution` half of the A02-side gap (Lemma C)

Lane 098, task R42 (full horizon). This records the `IsMaximalSolution`
identification of the inserted pair.

**Status: DONE (Bindings).** Item 1 of the lane-098 review follow-up is folded in:
`isMaximalSolution_of_inserted` is proved in `verification/Bindings/InsertionLifespan.lean`
§9 (reviewer-verified as `/tmp/r42rev098/Scratch.lean` §B2). This document is the
spec/table that motivated it; the "route" below is now the implemented route.

## The registered target predicate (primary route — Data/V2 vocabulary)

`IsMaximalSolution` is a **registered contract** object:
`A02.maximal_partial_v2` (`verification/contracts.json:148`) restates it
token-for-token in `Contracts.V1.Data` vocabulary at
`Contracts/V2/MaximalPartial.lean:106`:

```
def IsMaximalSolution (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (u : SpaceTimeField) (p : SpaceTimeScalar) : Prop :=
  0 < maximalLifespanR ν a f ∧
    ∀ S : ℝ, 0 < S → ENNReal.ofReal S < maximalLifespanR ν a f →
      ∃ w : ClassicalSolutionR ν a f S, w.velocity = u ∧ w.pressure = p
```

Here `maximalLifespanR` / `ClassicalSolutionR` are the `Data` objects (V1
MaximalPartial vocabulary), so this is the vocabulary in which the merged R42
Bindings lemmas already speak: `InsertionLifespan.sol_on_shorter` returns
`Data.ClassicalSolutionR` and `InsertionLifespan.lifespan_eq` is about
`Data.maximalLifespanR`. Stating Lemma C here therefore needs **no bridging at
all**.

The inhabited binding `BlowupDensity.Bindings.maximalPartialV2`
(`Bindings/MaximalPartialV2.lean`) supplies `exists_maximal` and `maximal_unique`
over this predicate, and `maximalPartial_isMaximalSolution_iff`
(`Bindings/MaximalPartialV2.lean:83`) transports it to/from the A02 restatement.

## What `IsMaximalSolution ν a gε (u_ε, p_ε)` requires — beyond `lifespan_eq`

The decisive observation: clause (ii) quantifies over the **shorter** horizons
`S` with `ofReal S < maximalLifespanR` (a *strict* guard — the endpoint `S = T` is
never asked for). With `lifespan_eq : maximalLifespanR ν a gε = ENNReal.ofReal T`
(lane 092/096, `Bindings/InsertionLifespan.lean`), `ofReal S < maximalLifespanR`
becomes `S < T` (for `0 < T`). So clause (ii) is **exactly** lane 087's
`sol_on_shorter` (`classicalSolutionR_of_inserted`), which already delivers, for
each `0 < S < T`, a `Data.ClassicalSolutionR ν a gε S` with `velocity = u_ε`,
`pressure = p_ε`.

**Consequence.** `IsMaximalSolution` needs **nothing beyond** `lifespan_eq` + the
shorter-horizon family (lane 087) + `0 < T`. In particular it does **not** consume
Lemma B (the horizon-`T` solution `classicalSolutionR_of_inserted_fullHorizon`,
`Section4/R42/FullHorizon.lean`): Lemma B is the *stronger* natural statement ("the
inserted pair solves NS on the full `[0,T)` as one object"), but
`IsMaximalSolution` only ever asks for solutions on the open family of shorter
horizons `[0,S)`, `S < T`. Lemma B is the deliverable of this lane for its own
sake (it is the single object carrying `sobolev` and `pressure_gradient` on all of
`[0,T)`, which the family from `sol_on_shorter` does not export —
`contracts.json:188`); the `IsMaximalSolution` identification is a strictly smaller
obligation.

## The implemented Bindings statement (Data/V2 vocabulary, proved)

`verification/Bindings/InsertionLifespan.lean` §9 (5 proof lines, no conversions):

```
theorem isMaximalSolution_of_inserted (hg : Data.MemForceR F.g)
    (hε : ε ∈ Ioc (0 : ℝ) F.ε₀) :
    Contracts.V2.MaximalPartial.IsMaximalSolution ν F.a (F.force ε)
      (F.velocity ε) (F.pressure ε) := by
  have hlife := lifespan_eq F hg hε
  refine ⟨hlife ▸ ENNReal.ofReal_pos.mpr F.scaling.correction.time_pos,
    fun S hS0 hSlt => ?_⟩
  rw [hlife] at hSlt
  exact sol_on_shorter F hε S hS0
    ((ENNReal.ofReal_lt_ofReal_iff F.scaling.correction.time_pos).mp hSlt)
```

**Size: S** (trivial ENNReal bookkeeping over the lane-087 family; no new analytic
content). Inputs, all at the Bindings level:

| input | source |
|---|---|
| `sol_on_shorter` (the shorter-horizon family) | `Bindings.InsertionLifespan.sol_on_shorter` (lane 087/096) |
| `lifespan_eq` | `Bindings.InsertionLifespan.lifespan_eq` (lane 092/096), needing only `hg` |
| `0 < T` | `F.scaling.correction.time_pos` (`CorrectionAPI.time_pos`) |
| `ENNReal.ofReal_pos` / `ENNReal.ofReal_lt_ofReal_iff` | `Data/ENNReal/Real.lean:176` / `:167` |

## The A02-restatement route (secondary — needs one transport)

The formalization-level A02 predicate
`NSFormalization.Section4.A02.IsMaximalSolution` (`Section4/A02/Maximal.lean:85`,
token-identical to the V2 def above but over `A02.maximalLifespanR` /
`A02.ClassicalSolutionR`) is obtained from the V2 result by **one extra step and
one extra import**:

```
theorem isMaximalSolution_of_inserted_A02 (hg : Data.MemForceR F.g)
    (hε : ε ∈ Ioc (0 : ℝ) F.ε₀) :
    NSFormalization.Section4.A02.IsMaximalSolution ν F.a (F.force ε)
      (F.velocity ε) (F.pressure ε) :=
  (maximalPartial_isMaximalSolution_iff ν F.a (F.force ε) (F.velocity ε)
    (F.pressure ε)).mpr (isMaximalSolution_of_inserted F hg hε)
```

needing `import Bindings.MaximalPartialV2` for
`maximalPartial_isMaximalSolution_iff`. This transport exists because
`sol_on_shorter` / `lifespan_eq` live on the `Data` side of the two-`structure`
divide, while `A02.IsMaximalSolution` speaks `A02.maximalLifespanR` /
`A02.ClassicalSolutionR`. This lane implements only the V2 form (§9); the A02 form
is a one-liner a consumer can add when it needs the A02 vocabulary.
(`contracts.json:155` already names the eventual home — Theorem 4.2's packaged
`insertion_lifespan_eq` — as owed to a later lane.)

## Does `maximal_unique` then identify it with `exists_maximal`'s solution?

**Yes.** Once `IsMaximalSolution ν a gε (u_ε, p_ε)` holds, A02's registered U7
interface (`maximalPartialV2`) identifies the inserted pair with *the* maximal
solution:

* `maximalPartialV2.exists_maximal`, given A01's `localSolution`, produces
  `(u*, p*)` with `IsMaximalSolution ν a gε u* p*`.
* `maximalPartialV2.maximal_unique`, applied to `(u*, p*)` and `(u_ε, p_ε)`, yields
  ```
  (∀ t ∈ presingularTimes ν a gε, ∀ x, u* (t,x) = u_ε (t,x))
    ∧ PressureGaugeEquivOn (presingularTimes ν a gε) p* p_ε.
  ```
  Its side hypotheses are exactly `0 < ν`, `a ∈ initialClassR`, `MemForceR gε`
  (`Maximal.lean:192-197`), all in hand at the Bindings level
  (`P.viscosity_pos`, `initialClassR_a F`, `memForceR_force F hg hε`).
* `presingularTimes ν a gε = {t | 0 ≤ t ∧ ofReal t < maximalLifespanR ν a gε}`
  `= {t | 0 ≤ t ∧ t < T} = Ico 0 T` (using `lifespan_eq` and `0 < T`; reviewer's
  `/tmp/r42rev098/Scratch.lean` §B4), so the identification holds on the whole
  singular interval `[0,T)`: velocity equal everywhere on `[0,T)`, pressure equal
  up to a `c : ℝ → ℝ` gauge.

So the inserted pair `(u_ε, p_ε)` **is** the maximal classical solution of
`(ν, a, gε)` on `[0,T)` — the "definite article" of `04-whole-space.tex:53`. No
further A02 lemma is required.

## Summary

| item | needs Lemma B? | needs `lifespan_eq`? | size | status |
|---|---|---|---|---|
| Lemma A (glue datum paths) | — | — | M | **proved** (`FullHorizon.lean`, this lane) |
| Lemma B (solution on `[0,T)`) | — | — | M | **proved** (`FullHorizon.lean`, this lane) |
| Lemma C (`IsMaximalSolution`, V2) | **no** | yes | S | **proved** (`Bindings/InsertionLifespan.lean` §9, this lane) |
| Lemma C, A02 vocabulary | no | yes | S | one `.mpr` of `maximalPartial_isMaximalSolution_iff` (not implemented; on demand) |
| `sol_fullHorizon` (Lemma B binding) | — | — | S | **proved** (`Bindings/InsertionLifespan.lean` §9, this lane) |
| identification via `maximal_unique` | no | yes (for `presingularTimes = [0,T)`) | S | registered `maximalPartialV2`; consumer applies it |
