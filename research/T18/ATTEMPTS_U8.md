# T18 U8 attempts — lane 436 (`Section3/T18/Lifespan.lean`)

Target: the five `PeriodicInsertionAPI` fields `solution` (`Spec.lean:1796`),
`maximal` (`:1806`), `lifespan` (`:1812`), `blowup` (`:1818`),
`blowup_limsup` (`:1825`).  All five are closed; nothing is left residual.

## Successful routes

### (a) `solution` — the full-horizon `ClassicalSolutionT`

Eight of the thirteen fields are the U3/U4/U6 theorems verbatim
(`velocity_smooth`, `pressure_smooth`, `initial`, `divergence` = U4
`incompressible`, `momentum`, `velocity_periodic`), plus `horizon_pos` =
`place.time_pos`.  The remaining four:

- **`sobolev` is cheap on the torus.**  The R³ twin (`research/R42/LIFESPAN_SPLIT.md`
  residual 1a/1e-i) has to cut the compact-support difference off in time, run
  `D01.contDiff_angularPath`, and glue the datum path back with
  `isSobolevDatum_add`.  **None of that is needed here.**  A torus slice of a
  slab-smooth unit-periodic field already has a datum at every real order
  (`T11.exists_periodicDatum_smooth`, `CriterionBridge.lean:27`) because the
  torus is compact, and the selected path is automatically continuous on the
  same `Ico 0 T` by `T11.continuousOn_periodicDatum_path_of_slab`
  (`Maximal.lean:155`).  `sobolev_path` is therefore `T11.flow_sobolev`'s proof
  with `U.velocity_smooth`/`U.velocity_periodic` replaced by U3's two theorems
  (≈12 lines, `Classical.choice` on the per-time datum).
- **`pressure_gradient`** is one application of `T10.memLp_torusLift_vector` to
  `NavierStokes.PeriodicUniqueness.pressureGradient_contDiff` on the slice —
  again compactness of the torus, not the R³ compact-support argument (R42
  residual 1f).
- **`pressure_gauge`** is a general lemma `pressureGaugeT_normalize`: on a
  probability measure the mean of `p − mean p` is `0` as soon as the slice is
  integrable.  Integrability of the inserted slice is
  `reference_pressureSlice_integrable` (smooth slice ⟹ `MemLp 1`) `+`
  `scaling.pressureSlice_integrable` — exactly the two facts U3 already used
  for `pressure_smooth`.
- **`pressure_periodic`** reduces to periodicity of the *raw* sum because the
  gauge shift is spatially constant (`isPeriodicOn_normalizePressureT`).  The
  packet half is recovered from `S.pressure_periodic` for
  `S.pressure = normalizedScaledPressure …` by cancelling the (x-independent)
  mean with `sub_left_injective`.

### (b) `blowup`

`scaling.unboundedSpeed` supplies `t, x` with `M < ‖U_ε(t,x)‖`.  Since `M > 0`
the packet is nonzero at `x`, so (i) `t ≥ T − ε²` — otherwise the slice is the
constant zero field by U5's `packet_slice_zero` — and (ii) `x ∈ tsupport` of the
packet slice.  `correction.potential.correction_cancels` at that `t` then gives
an open `O ⊇ tsupport` on which `correctedBackground = 0`, so
`velocity data ε (t,x) = U_ε(t,x)` **at that very point** and the inequality
transfers unchanged.  No support/localisation lemma of U7 is needed.

### (c) `blowup_limsup`

Reused verbatim from Section 4: `R42.limsupLeft_speedENorm_eq_top` +
`R42.continuous_slice_of_velocity_smooth` (`Section4/R42/BlowupEssSup.lean`).
Both are stated for a bare `u : ℝ × Space → Space` with the `A02.limsupLeft` /
`A02.speedENorm` spellings, which are `rfl`-equal to the contract's
(`Bindings/MaximalPartial.lean:57,61`), so (b) + U3 close the field in two lines.

### (d) `lifespan = ofReal T`

- `≥` is `T11.lifespan_ge_of_horizon` (`ExtendsBeyond.lean:73`) applied to (a):
  the full horizon `T` is itself a term of the `⨆`.  The split's "every `S < T`
  plus `velocity_unique`" is unnecessary once (a) is a *full*-horizon solution.
- `≤` is by contradiction.  `ofReal T < ⨆ S, ⨆ _ : Nonempty …, ofReal S` gives,
  by two `lt_iSup_iff`, a horizon `S > T` and a solution `w` there.
  `T11.velocity_unique` (with `0 < ν` = `correction.viscosity_pos`,
  `a ∈ initialClassT` = `data.ha`, `g_ε ∈ forceClassT` = U2 `force_mem`)
  identifies `w.velocity` with `u_ε` on `Ico 0 (min T S) = Ico 0 T`.  But
  `w.velocity` is `ContDiffOn ℝ ∞` on `Ico 0 S ×ˢ univ` and unit-periodic there,
  so it is **bounded** on `Icc 0 T × Space`: bounded on the compact
  `Icc 0 T ×ˢ fundamentalCube` (`IsCompact.exists_bound_of_continuousOn`), and
  every point of space is an integer translate of a cube point
  (`x ↦ ⌊x i⌋`, `Int.fract`), so `T13.periodic_latticeVector` carries the bound
  everywhere.  That contradicts (b) at `M = max C 0 + 1`, `δ = T`.

### (e) `maximal`

`0 < maximalLifespanT` from (d) and `place.time_pos`; the shorter-horizon
witness is the *same* fields restricted (`insertedSolutionOn`), so
`w.velocity = velocity ε` and `w.pressure = pressure ε` hold by `rfl` and
`velocity_unique` is not needed a second time.

## Rejected / failed approaches

1. **The split's `≤` route (`lifespanInfiniteOfLocallyFinite` + `higherOrderBound`
   at `m = 3` + `boundedRepresentative`) was abandoned, and it does not close as
   written.**  Two independent obstructions:
   - `T11.lifespanInfiniteOfLocallyFiniteH3` concludes `maximalLifespanT = ⊤`
     from *local finiteness of the `H²` criterion*.  That is the global-existence
     direction; it is not an upper bound on the lifespan, and the torus tree has
     **no** analogue of A02's registered `MaximalPartial.lifespan_le_of_unbounded`
     (`grep -rn "maximalLifespanT" formalization/` lists only
     `lifespan_ge_of_horizon`, `lifespan_ge_of_extends`,
     `maximalLifespanT_eq_lifespan`, `horizon_le_lifespan` — all lower bounds).
   - `T12.boundedRepresentative` (`FourierEmbeddings.lean:386`) bounds
     `periodicLpENorm ⊤ v = eLpNorm (torusLift v) ⊤ periodicTorusMeasure`, an
     essential supremum against **Haar measure on `T³`**, whereas the Spec's
     `blowup_limsup` is `speedENorm z = eLpNorm z ⊤ (volume : Measure Space)`,
     against **Lebesgue measure on `R³`**.  These are equal for a continuous
     periodic field, but the tree contains no such bridge (`grep` for
     `periodicLpENorm ⊤` finds only `FourierEmbeddings.lean:388,464,472`,
     `Contracts/V1/MeanZeroCalculus.lean:223`, `Tests/MeanZeroCalculus.lean:69`),
     and proving it needs an `IsOpenPosMeasure`-style argument on
     `PeriodicTorus` that is also absent.
   The periodicity/compactness route above needs neither, uses only
   `torusLocalTheoryAPI.velocity_unique` from T11, and is ~40 elementary lines.
   **Consequence for the split:** U8 consumes **none** of
   `torusContinuationH3API` (`higherOrderBound`, `extendsBeyond`,
   `lifespanInfiniteOfLocallyFinite`, `restartBeyondH3`) and none of T12.  The
   `H1_GAP.md` §4 "expected OK" verdict therefore holds a fortiori: the only T11
   field U8 touches is `velocity_unique`, which carries no ball at all.
2. `integral_sub (hq t ht) (integrable_const _)` for the gauge:
   *Application type mismatch* — after `torusLift` unfolds, the subtracted
   constant reads `pressureMeanT q (t, toSpace ↑((UnitAddTorus.measurableEquivPiIoc 0) y)).1`,
   which is not *syntactically* a constant function, so `integrable_const`'s
   metavariable never unifies.  Fix: give the constant's integrability its own
   `have hconst : Integrable (fun _ : PeriodicTorus ↦ pressureMeanT q t) …`, and
   state the `integral_sub` instance as a `have` with the `normalizePressureT`
   spelling on the left (the defeq check then succeeds).
3. `simpa using h.symm` for the lattice shift produced the reversed equation
   (`u (t, x − v) = u (t, x)` instead of the stated `u (t,x) = u (t, x − v)`):
   `simp` already normalises `(x − v) + v` to `x` inside `h`, so the `.symm` is
   one flip too many.  Use `simpa using h`.
4. Two linter-only failures worth recording because the gate is "0 output":
   `hT₀ : 0 ≤ T₀` in `exists_speed_bound` is genuinely unused (membership in
   `Icc 0 T₀` already supplies `0 ≤ t`) and had to be deleted, and
   `fun ε hε ↦ …` bodies that mention `ε` only through `hε`'s type need an
   explicit `(ε := ε)` to silence `Variable name ε is not explicitly referenced`.
