# A04 SL2 — momentum equation in datum form (lane 065)

`research/A04/G1_SPLIT.md` sub-lemma **SL2**.  Goal: `deriv G t = ν • L − N − P + F`
on the datum carrier `RealVectorSobolev (m:ℝ)`, the `hmom` hypothesis of
`inner_energy_assembly` / `inner_energy_Rhigh` (SL8, `A04/HighEnergy.lean`).

Deliverable: `formalization/NSFormalization/Section4/A04/MomentumDatum.lean`
(`theorem momentum_datum`), builds clean, `#print axioms` = standard three.
Composed example wiring it to `inner_energy_assembly` with no glue:
`research/A04/axioms_sl2.lean`.

## What was proved

`momentum_datum` (statement `MomentumDatum.lean`): for `w : ClassicalSolutionR ν a f T`,
`MemForceR f`, `2 ≤ m`, a `C^∞`-in-time velocity datum path `G` on `Ico 0 T`,
`t ∈ Ioo 0 T`, and order-`m` data `L N P F` of the Laplacian / advection /
pressure-gradient / force slices, `deriv G t = ν • L − N − P + F`.

## Route (worked first time, no dead ends of substance)

1. **SL1/D2** `timeDeriv_isSobolevDatum` (already on branch): `deriv G t` is the
   datum of `x ↦ deriv (fun r => u(r,x)) t`.
2. The datum-side field is **definitionally** `x ↦ temporalDerivative u t x`:
   `deriv f t = fderiv ℝ f t 1` and `temporalDerivative u t x = fderiv ℝ (fun s => u(s,x)) t 1`
   are the same term.  So `show temporalDerivative w.velocity t x = _` (a `change`)
   is accepted, and `D01.temporalDerivative_slice_eq` (momentum rearranged, one
   `abel`) gives `∂ₜu = f − (u·∇)u + νΔu − ∇p`; a further `abel` matches
   `νΔu − (u·∇)u − ∇p + f`.
3. **Datum linearity** builds `ν • L − N − P + F` as the datum of that RHS:
   `isSobolevDatum_smul ν hL`, then `A03.isSobolevDatum_sub` twice and
   `A03.isSobolevDatum_add` once.
4. **Uniqueness** `A03.IsSobolevDatum.unique` (D01 unit L1) on the two data of the
   one field.

## Datum-linearity lemmas: which existed, which were added

Checked with `grep isSobolevDatum_ formalization/NSFormalization/Section4 -r`.

Existed and reused:
- vector `A03.isSobolevDatum_add` / `A03.isSobolevDatum_sub`
  (`A03/VectorTameProduct.lean:180,186`; hypotheses `2 ≤ s`, `LocIntField F`,
  `LocIntField G`).
- vector `A03.IsSobolevDatum.unique` (`VectorTameProduct.lean`, no `2 ≤ s`), also
  `D01.isSobolevDatum_unique`.
- `A03.locIntField_of_memLp`, `A03.isSobolevDatum_iff`, `A03.IsSobolevDatum.component`.
- scalar `A03.isScalarSobolevDatum_add/sub/mul` (`ScalarTameProduct.lean`).

**Absent, added here** (A04 namespace — existing A03/D01 files may not be edited):
- `isScalarSobolevDatum_smul` (scalar), `isSobolevDatum_smul` (vector).
- `isScalarSobolevDatum_neg`, `isSobolevDatum_neg` (bonus; `c = −1` of `smul`;
  not used by `momentum_datum`, which uses `sub` for the `−N`, `−P` terms, but
  requested by the split and one line each).

`isSobolevDatum_smul` proof choice.  Two candidate routes:
- **Representative route** (mirror of `A03.isScalarSobolevDatum_add`): rewrite
  `angularRealization_boundedRepresentative`, then `map_smul` on the ℝ-linear
  `angularBoundedRepresentative`.  Needs `2 ≤ s` **and** local integrability of `a`.
- **Raw route (chosen):** from the datum definition directly.  `angularRealization`
  is `ℂ`-linear (`AngularFourierDilation.lean:176`, `→L[ℂ]`), so a **real** scalar
  passes through it with `LinearMapClass.map_smul_of_tower` (a `ℂ`-linear map is
  `ℝ`-linear via the `ℝ→ℂ` scalar tower); the physical side scales by
  `MeasureTheory.integral_smul`; the pointwise cast `c • ((a x:ℝ):ℂ) = ((c*a x):ℂ)`
  is `Complex.real_smul` + `push_cast; ring`.  This needs **neither** `2 ≤ s` **nor**
  local integrability, so it is strictly more general than the representative route.

Failed name (5-minute fix, recorded): `map_smul_of_tower` alone is
`unknownIdentifier`; the usable spelling is `LinearMapClass.map_smul_of_tower`
(`Mathlib/Algebra/Module/LinearMap/Defs.lean:374`, via the `LinearMapClass`
instance of `ContinuousLinearMap`).  `ContinuousLinearMap.smul_apply` compiles but
is deprecated → use bare `smul_apply`.

## Hypotheses beyond the class

- `2 ≤ m` — for SL1/D2 and the `2 ≤ s` of `A03.isSobolevDatum_add/sub`
  (`s = (m:ℝ)`).  `m ≥ 3` is not needed here (SL2 alone); the split's `m ≥ 3`
  comes from other sub-lemmas.
- `MemForceR f` — used **only** to make the force slice `f(t,·)` smooth (hence
  `MemLp`) via `D01.forceSlice_smoothL2_of_memForceR`, which feeds the
  `LocIntField` side condition of the final `isSobolevDatum_add`.  (Nothing else
  in SL2 touches the force class.)
- `hP : IsSobolevDatum m (∇p(t,·)) P` — the **pressure datum at order `m`**, D01
  obligation **P2**.  `D01/Pressure.lean` documents (module docstring, and the
  `pressureGradient_slice_smoothL2_iff_temporalDerivative` repackaging) that this
  is **not** available unconditionally from `ClassicalSolutionR` — it is the Leray
  L9(c) gap.  Taken as an explicit hypothesis, exactly as C01 does.  Only its
  continuity (from `D01.contDiff_pressureGradient_slice`, cheap, from
  `pressure_smooth`) is used to get `MemLp (∇p) 2`; the datum itself feeds the
  `sub` step and uniqueness.
- `hL, hN, hF` (data of `Δu`, `(u·∇)u`, `f`) — taken as inputs so the **same**
  `L, N, P, F` feed the other G1 sub-lemmas (SL3 `hlap` uses `L`, SL4 `hpr` uses
  `P`, SL7 `hF` norm uses `F`).  They are *constructible* from the class
  (`D01.laplacian_slice_smoothL2` / `advection_slice_smoothL2` /
  `forceSlice_smoothL2_of_memForceR` are `SmoothSquareIntegrableJets`, so
  `D01.memHInfty_iff_smoothSquareIntegrableJets .mpr .2 m` gives a datum), but
  keeping them as inputs is the modular interface `inner_energy_assembly` wants
  (it takes `L N P F` as free variables).

## Commands and results

- `bash scripts/lean-install.sh` — OK.
- `lake build NSFormalization.Section4.A04.{TimeDerivative,HighEnergy,D01.Pressure,A03.VectorTameProduct}`
  (dependency closure) — `Build completed successfully (9892 jobs)`.
- iterative scratch `research/A04/scratch_sl2.lean` (removed) — smul (raw), vector
  smul, full `momentum_datum`, neg lemmas, and the composed example all compiled.
- `lake build NSFormalization.Section4.A04.MomentumDatum` —
  `✔ Built NSFormalization.Section4.A04.MomentumDatum (7.4s)`, no warnings on the
  new file (the replayed-cache warnings are all from unrelated upstream `Source/`
  and `Paper3/` modules).
- `lake env lean ../research/A04/axioms_sl2.lean` — `momentum_datum`,
  `isSobolevDatum_smul`, `isScalarSobolevDatum_smul`, `isSobolevDatum_neg`,
  `isScalarSobolevDatum_neg` each depend on `[propext, Classical.choice, Quot.sound]`;
  the composed `example` (SL2 → `inner_energy_assembly`) type-checks.
- `grep -nE "sorry|admit|native_decide|\\baxiom\\b" MomentumDatum.lean` — none.
