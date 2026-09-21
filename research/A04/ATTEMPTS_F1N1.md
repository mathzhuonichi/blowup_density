# A04 units F1 and N1 — attempts and record (lane 039)

Scope: units **F1** and **N1** of `research/A04/COMPARISON.md` §4.  Modules
`formalization/NSFormalization/Section4/A04/{Forcing,Continuity}.lean`;
conformance `research/A04/axioms_f1n1.lean`.

## What was proved

### F1 (`Forcing.lean`)
* `memL1Hm_of_memForceR : MemForceR f → MemL1Hm f`.
* `exists_boundedIntoHOne_of_memForceR : MemForceR f → ∀ b, ∃ K ≠ ⊤, BoundedIntoHOne (Icc 0 b) K f`.
* helper `sobolevENorm_eq : IsSobolevDatum s z A → sobolevENorm s z = ‖A‖ₑ`.

### N1 (`Continuity.lean`)
* `sobolevENorm_velocity_ne_top`, `sobolevENorm_force_ne_top` — finiteness of the `ℝ≥0∞` norm.
* `continuousOn_sobolevNormAt_of_datumPath` — the core continuity step.
* `continuousOn_sobolevNormAt_velocity`, `continuousOn_sobolevNormAt_force` — the two instances.
* `intervalIntegrable_highContinuationIntegrand` — the payoff: the exact integrand of
  `ContinuationAPI.highContinuationIntegral` is `IntervalIntegrable` on `[t₀,t] ⊆ [0,T)`.

All `sorry`-free; `#print axioms` = `propext, Classical.choice, Quot.sound` for every theorem
(and for the spec-vocabulary conformance theorems that chase the `toA02` bridge).

## Which clause of `ClassicalSolutionR.sobolev` / `MemForceR` each result uses

`MemForceR f` = `ContDiffOn ℝ ∞ f futureDomain ∧ ∀ m, ∃ G, IsSobolevPath (m:ℝ) f G ∧
ContDiffOn ℝ ∞ G futureTimes ∧ MemLp G 1 forceTimeMeasure ∧ MemLp G 2 forceTimeMeasure`
(`SolutionClass.lean:86`, = `Data.lean:544`).

`ClassicalSolutionR.sobolev` = `∀ m, ∃ G, ContinuousOn G (Ico 0 T) ∧ ∀ t ∈ Ico 0 T,
IsSobolevDatum (m:ℝ) (velocity(t,·)) (G t)` (`SolutionClass.lean:119`, = `Data.lean:643`).

| result | clause consumed |
|---|---|
| `memL1Hm_of_memForceR` | `MemForceR.2 m` → the **`MemLp G 1 forceTimeMeasure`** conjunct (3rd); its `.1` (`AEStronglyMeasurable`) puts `G` in the `forceSobolevENorm` index set, its `.2` (`eLpNorm < ⊤`) bounds the infimum. The `L²_t` conjunct (4th) is unused (matches Spec: "the `L²_t` half is never used by A04"). |
| `exists_boundedIntoHOne_of_memForceR` | `MemForceR.2 1` → the **`IsSobolevPath`** conjunct (1st, for the datum at each `t`) and the **`ContDiffOn ℝ ∞ G futureTimes`** conjunct (2nd, for `ContinuousOn` on the compact `Icc 0 b ⊆ Ici 0`, hence `IsCompact.exists_bound_of_continuousOn`). |
| `sobolevENorm_velocity_ne_top` | `sobolev m` → the **`IsSobolevDatum`** conjunct (2nd) only; the `ContinuousOn G` conjunct is unused here. |
| `sobolevENorm_force_ne_top` | `MemForceR.2 m` → the **`IsSobolevPath`** conjunct (1st) only. |
| `continuousOn_sobolevNormAt_velocity` | `sobolev m` → **both** conjuncts: `ContinuousOn G (Ico 0 T)` (1st) and `IsSobolevDatum` (2nd). Not `HasSmoothSobolevPath`. |
| `continuousOn_sobolevNormAt_force` | `MemForceR.2 m` → `IsSobolevPath` (1st) and `ContDiffOn ℝ ∞ G futureTimes` (2nd, via `.continuousOn`). |
| `intervalIntegrable_highContinuationIntegrand` | the three continuity lemmas above (so: `sobolev`'s both conjuncts for the two velocity terms, `MemForceR`'s 1st+2nd for the force term). |

`ClassicalSolutionR`'s other fields (`velocity_smooth`, `pressure`, `momentum`, `divergence`,
`pressure_gradient`, …) are **not** used by F1/N1; nor is the `ContDiffOn ℝ ∞ f futureDomain`
half of `MemForceR` (F1a/b work entirely off the datum-path clauses).

## A02 vs D01 name coincidence (checked)

`@A02.MemForceR = @D01.MemForceR`, `@A02.IsSobolevPath = @D01.IsSobolevPath`,
`@A02.IsSobolevDatum = @D01.IsSobolevDatum`, `A02.futureTimes = D01.futureTimes`,
`A02.forceTimeMeasure = D01.forceTimeMeasure` — all by `rfl` (verified in a scratch example).
The modules open the **A02** copy for the class vocabulary (`MemForceR`, `IsSobolevPath`,
`ClassicalSolutionR`, `forceTimeMeasure`, `SpaceTimeField`) and the **D01** copy for the norm
vocabulary (`sobolevENorm`, `sobolevENorm_le_of_isSobolevDatum`, `isSobolevDatum_unique`,
`IsSobolevDatum`); they interoperate definitionally (e.g. `w.sobolev` yields
`A02.IsSobolevDatum` and is fed to `sobolevENorm_eq`, stated over `D01.IsSobolevDatum`, by defeq).

## What worked, first try after prototyping

The proofs are short and matched the COMPARISON.md F1/N1 sketch exactly:
* F1a is `iInf_le` on the `MemLp`-witnessed datum path + `ne_top_of_le_ne_top`.
* F1b is `IsCompact.exists_bound_of_continuousOn` on the order-1 path + `sobolevENorm ≤ ‖G t‖ₑ`.
* N1 continuity is `ContinuousOn.congr` from `‖G ·‖` using `sobolevENorm_eq` and
  `(‖·‖ₑ).toReal = ‖·‖`; integrability is `ContinuousOn.intervalIntegrable` on `uIcc = Icc`.

## Failures / pitfalls encountered and resolved

1. **Ambiguous opens.** Opening both `Section4.A02` and `Section4.D01` wholesale made
   `MemForceR`, `IsSobolevPath`, `IsSobolevDatum`, `forceTimeMeasure` ambiguous (both namespaces
   define them). Fixed by selective `open ... (...)` lists — A02 for class names, D01 for norm
   names — since the two copies are `rfl`-equal and interoperate anyway.

2. **`Nat.cast` on the order argument — only order 1 needs a rewrite.** `MemForceR.2 1` and
   `w.sobolev 2` produce datum paths at orders `((1:ℕ):ℝ)` and `((2:ℕ):ℝ)`, but `BoundedIntoHOne`
   and the integrand use the numerals `(1:ℝ)` / `(2:ℝ)`. Only `Nat.cast_one`, `((1:ℕ):ℝ) = (1:ℝ)`,
   is **not** `rfl` (Lean reports a `↑1 = 1` type mismatch), so F1b genuinely needs
   `simpa only [Nat.cast_one]`. But `((2:ℕ):ℝ) = (2:ℝ)` **is** `rfl` at this toolchain (`instOfNat`
   for `n ≥ 2` unfolds to `Nat.cast`), so `continuousOn_sobolevNormAt_velocity w 2` already has the
   `sobolevNormAt (2:ℝ)` type and needs no rewrite: the `simp only [Nat.cast_ofNat]` I first wrote
   in `intervalIntegrable_highContinuationIntegrand` was dead weight and has been removed
   (`REVIEW_F1N1.md` finding 3). Where a rewrite *is* needed it is sound because
   `sobolevENorm`/`sobolevNormAt` take the order as a plain `ℝ` argument, so the rewrite has a
   well-typed motive despite the dependent `RealVectorSobolev s` living *inside* those definitions.

3. **Structure bridge for N1 conformance.** `Data.ClassicalSolutionR` and
   `A02.ClassicalSolutionR` are distinct inductive types (a `rfl` bridge is impossible for a
   structure — the standing repo rule). The N1 conformance statements are stated over
   `Data.ClassicalSolutionR` (spec vocabulary) and bridged by the field-by-field literal `toA02`
   in `axioms_f1n1.lean`; every field type is defeq, and `(toA02 w).velocity` reduces to
   `w.velocity` by iota, so the discharge is by `exact`. This is exactly what a
   `verification/Bindings` module does.

4. **`sobolevENorm_eq` not imported.** The needed `sobolevENorm s z = ‖A‖ₑ` lemma lives in
   `A03.VectorTameProduct`, but importing A03 would pull in its scalar/jet tame-product closure
   for a 4-line fact. Reproved it locally in `Forcing.lean` from `D01.sobolevENorm_le_of_isSobolevDatum`
   + `D01.isSobolevDatum_unique` (both already in the `D01.ForceClass` closure). `DatumToJets` was
   **not** imported either: none of its lemmas are needed for F1/N1 (continuity comes from the
   `ContinuousOn G` clause of `sobolev`, not from the jet reassembly). Originally the closure was
   only `A02.SolutionClass` + `D01.ForceClass`; the review (finding 1) later added
   `D01.HomogeneousWitness` for the `bochnerDatumENorm_eq_homogeneous` bridge, measured at
   +~0.7 s — see "Review fixes" below. `A03.VectorTameProduct` and `D01.DatumToJets` remain
   excluded.

## Commands

```
cd verification && lake build NSFormalization.Section4.A04.Forcing NSFormalization.Section4.A04.Continuity
  -> Build completed successfully.
cd verification && lake env lean ../research/A04/axioms_f1n1.lean
  -> all 10 theorems: depends on axioms [propext, Classical.choice, Quot.sound]; no errors/warnings.
```

## Review fixes (REVIEW_F1N1.md, verdict ACCEPT-WITH-NOTES)

All five findings addressed; the Lean was already correct and axiom-clean, so
these are docstring/one-line changes plus one added `rfl` bridge and one exported
lemma.

1. **Finding 1 (third `bochnerDatumENorm` copy).** `Forcing.lean` now imports
   `Section4/D01/HomogeneousWitness`, its `bochnerDatumENorm` docstring names the
   in-package copy `D01.Homogeneous.bochnerDatumENorm` (`HomogeneousWitness.lean:620`),
   and a new bridge `bochnerDatumENorm_eq_homogeneous :
   @bochnerDatumENorm = @NSFormalization.Section4.D01.Homogeneous.bochnerDatumENorm := rfl`
   records that they agree. Import cost measured: Forcing rebuild 2.7 s → 3.4 s
   (+~0.7 s, +2 jobs), i.e. small — comparable to lane 035's +0.4 s — so the bridge
   was kept rather than skipped. The `def` stays local (not opened) so the
   `forceSobolevENorm` restatement reads token-for-token against `Data.lean` in one
   place; the docstring says so.

2. **Finding 2 (wrong `Data.lean` cites).** `Forcing.lean` §0: `213 → 205`
   (`bochnerDatumENorm`), `228 → 225` (`forceSobolevENorm`), `236 → 231`
   (`forceSobolevENormL1`). The `236` cite had pointed at `forceSobolevENormL2`.

3. **Finding 3 (dead `Nat.cast_ofNat` step).** `Continuity.lean`
   `intervalIntegrable_highContinuationIntegrand`: the `have h := … ; simp only
   [Nat.cast_ofNat] at h ; exact h.mono hsub` block for `hv2` is replaced by
   `(continuousOn_sobolevNormAt_velocity w 2).mono hsub`, since `((2:ℕ):ℝ) = (2:ℝ)`
   is `rfl` at this toolchain. The `Nat.cast` failure note above is narrowed to
   `Nat.cast_one` (order 1), the only one that is genuinely non-`rfl`.

4. **Finding 4 (off-by-one conjunct index).** The clause table's
   `memL1Hm_of_memForceR` row now calls `MemLp G 1 forceTimeMeasure` the **3rd**
   conjunct (the `L²_t` conjunct being the 4th), matching the numbering the other
   rows use.

5. **Finding 5 (real-valued half not exported).** `Continuity.lean` now exports
   `sobolevNormAt_eq : IsSobolevDatum s (u(t,·)) A → sobolevNormAt s u t = ‖A‖`, and
   `continuousOn_sobolevNormAt_of_datumPath` uses it in its `congr` step, so the
   `sobolevNormAt = ‖G t‖` identity of `COMPARISON.md:208` is a one-liner for
   consumers rather than buried in a `show`/`rw`.

### Commands (review fixes)

```
cd verification && lake build NSFormalization.Section4.A04.Forcing NSFormalization.Section4.A04.Continuity
  -> Build completed successfully (9882 jobs).   [Forcing 3.4s, Continuity 3.5s]
cd verification && lake env lean ../research/A04/axioms_f1n1.lean
  -> 10/10 declarations: [propext, Classical.choice, Quot.sound]; no errors, no warnings.
make check
  -> EXIT 0 (check_formalization_plan; check_contracts; test_contract_policy 13 OK; 30 work items consistent).
```
