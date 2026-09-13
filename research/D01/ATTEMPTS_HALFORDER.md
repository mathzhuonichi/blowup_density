# D01 / lane 042 — half-order force norms (G3, G2)

Gaps from R43 (`research/R43/COMPARISON.md` §4, `research/D01/RECONCILIATION.md`):

- **G3**: `MemForceR f → forceSobolevENormL1 (1/2) f ≠ ⊤` (inhomogeneous) and
  `MemForceR f → forceHomogeneousENorm 1 (1/2) f ≠ ⊤` (homogeneous). Non-vacuity
  of Props 4.3/4.4 smallness hypotheses.
- **G2**: `forceHomogeneousENorm 1 (1/2) f ≤ forceSobolevENormL1 (1/2) f`
  (`04-whole-space.tex:132`).

## Result

- **G3 inhomogeneous — DONE**, and more general than asked: for every real order
  `s ≤ m` (`m : ℕ`) and every `q ∈ {1,2}`,
  `forceSobolevENorm q s f ≠ ⊤` on `MemForceR f`. Specialized to `s = 1/2`,
  `q ∈ {1,2}`. Module `formalization/NSFormalization/Section4/D01/HalfOrder.lean`,
  axioms `propext, Classical.choice, Quot.sound`.
- **G3 homogeneous and G2 — GAP** (recorded below). Both need a homogeneous datum
  for a *general* `H^∞` slice, which requires genuinely new Fourier analysis
  beyond order monotonicity; per the task's fallback the monotonicity route was
  proven first and the rest reported.

## The route that worked (G3 inhomogeneous)

`MemForceR f` gives, for each integer `m`, an order-`m` datum path
`G : ℝ → RealVectorSobolev m` with `IsSobolevPath m f G`,
`MemLp G 1 forceTimeMeasure`, `MemLp G 2 forceTimeMeasure`
(`ForceClass.lean:158`). The order-`s` force norm is an infimum over order-`s`
datum paths (`Data.lean:225`). Bridge = monotonicity of the Sobolev norm in the
order (`‖z‖_{H^s} ≤ C ‖z‖_{H^m}` for `s ≤ m`), taken at the datum level.

Pieces reused (all pre-existing, no new Fourier analysis):

| need | reused declaration | file |
|---|---|---|
| datum order-lowering operator (real) | `A03.lowerDatum` | `Section4/A03/RealAngularProduct.lean:140` |
| its contraction bound `‖lowerDatum A‖ ≤ lowerConst·‖A‖` | `A03.norm_lowerDatum_le` | `RealAngularProduct.lean:198` |
| lowered datum realizes the same field | `A03.IsScalarSobolevDatum.lower` | `Section4/A03/ScalarTameProduct.lean:114` |
| `IsSobolevDatum ↔ componentwise scalar` | `A03.isSobolevDatum_iff` | `Section4/A03/VectorTameProduct.lean:54` |
| underlying distribution invariance | `Paper3.angularRealization_orderLowering` | `Paper3/AngularTameProduct.lean:51` |
| PiLp componentwise CLM assembly template | `Paper3.cyclesToAngularRealVector` | `Paper3/AngularRealVectorBochner.lean:14` |
| CLM transports `MemLp` | `ContinuousLinearMap.comp_memLp'` | Mathlib |

New code (in `HalfOrder.lean`):

1. `lowerDatumLM` : `A03.lowerDatum` is `ℝ`-linear (it is `angularOrderLowering`,
   a `ContinuousLinearMap`, corestricted to `realSubspace`).
2. `lowerDatumL` : `LinearMap.mkContinuous lowerDatumLM lowerConst norm_lowerDatum_le`
   — the CLM form.
3. `lowerVectorL` : componentwise CLM on `RealVectorSobolev`, via
   `PiLp.continuousLinearEquiv` + `ContinuousLinearMap.pi` (same shape as
   `cyclesToAngularRealVector`); `lowerVectorL_apply` is `rfl`.
4. `isSobolevPath_lower` : lifts an order-`s` datum path to order `r ≤ s` slicewise.
5. `forceSobolevENorm_ne_top` : lower the order-`m` path to order `s`, use
   `comp_memLp'` to keep `MemLp` (hence finite `eLpNorm`), then `iInf_le`.

Because `lowerVectorL` is a genuine `ContinuousLinearMap`, `comp_memLp'` handles
measurability **and** finiteness in one step — the interpolation inequality
`‖z‖_{H^{1/2}} ≤ ‖z‖_{H^0}^{1/2}‖z‖_{H^1}^{1/2}` was *not* needed; the cheaper
monotonicity `‖z‖_{H^{1/2}} ≤ C‖z‖_{H^1}` (via `lowerDatum` from order 1) suffices.

## Tactical failures / notes (G3 route)

- `SetLike.coe_injective` does **not** prove element equality in
  `↥(realSubspace r)`; that subtype needs `Subtype.ext`.
- The coercion lemmas for the `ClosedSubmodule` element carrier are
  `AddMemClass.coe_add` (with `map_add`) and `SetLike.val_smul` (with
  `ContinuousLinearMap.map_smul_of_tower`, because `angularOrderLowering` is
  `ℂ`-linear and the scalar is `ℝ`). Found via `simp?`.
- `iInf_le _ ⟨…⟩` with the infimand left implicit and the RHS a
  `bochnerDatumENorm` (an `eLpNorm`) caused a `whnf` heartbeat timeout during
  unification. Fixed by giving `iInf_le` its function argument explicitly and
  discharging the `≠ ⊤` side with an explicit `show eLpNorm … ≠ ⊤`.

## Why G2 and the homogeneous half of G3 are gaps

Both require, for a **general** `H^∞` slice `z` (smooth, all derivatives `L²`,
but not Schwartz nor compactly supported — the slices `MemForceR` produces), a
homogeneous datum `B : RealVectorSobolev (1/2)` with
`IsHomogeneousSliceDatum (1/2) z B` and `‖B‖ ≤ ‖A‖`, where `A` is the
inhomogeneous order-`1/2` datum.

The construction is the `L²` Fourier multiplier
`m(ξ) = |ξ|^{1/2} (1+|ξ|²)^{-1/4}` (so `0 ≤ m ≤ 1`, giving `‖B‖ ≤ ‖A‖`), with
`B = m · A`, together with the identification of the two realizations via
`Paper3.weightedAngularFourier_realization`
(`Paper3/AngularFourierDilation.lean:192`):
`sobolevWeightMultiplier s (angularFourierDistribution (angularRealization s l)) = l`,
i.e. `angularFourierDistribution (angularRealization s A_i)` is represented by
`(1+|ξ|²)^{-s/2} A_i`, so `|ξ|^{-s} · (m·A_i) = (1+|ξ|²)^{-s/2} A_i` matches the
`IsHomogeneousDatum` integrand.

**What is missing in tree.** `IsHomogeneousSliceDatum` / `homogeneousDatum` and
every existence lemma live only in `Section4/D01/HomogeneousWitness.lean` and are
built from `angularFourier φ` of a **Schwartz** `φ` (or a compactly supported
field via `compactSchwartzComponents`); `angularFourier` totalizes to junk `0`
off `L¹`, so they do not extend to a general `H^∞` slice. `A05`'s
`homogeneousLeSobolev` (`research/A05/Spec.lean:268`) is only a *spec field*, not
a proved lemma, and it is the **spatial-slice** inequality anyway; G2 additionally
needs the datum-path lift with `AEStronglyMeasurable`.

Estimated new work for G2/G3-homogeneous: the distributional multiplier lemma
(`angularFourierDistribution (angularRealization s A)` is represented by the `L²`
function `(1+|ξ|²)^{-s/2} A`, from `weightedAngularFourier_realization` +
invertibility of `sobolevWeightMultiplier`), plus reality preservation of `m·A`,
plus measurability/continuity of `A ↦ m·A` as an `L²` operator, plus the vector
and path lifts. This is a multi-lemma Fourier-analysis unit, not a single bounded
lemma; recommended as its own lane (natural home D01 `DatumLemmas` or A05).

## Commands

- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.D01.HalfOrder`
  → `Built … HalfOrder`.
- `cd verification && lake env lean ../research/D01/axioms_halforder.lean`
  → all `example`s and `rfl` bridges check; `#print axioms` =
  `[propext, Classical.choice, Quot.sound]` for all three theorems.
