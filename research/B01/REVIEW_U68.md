# Review — lane 048, B01 units 6 (`separatedAssembly`) and 8 (`spatialApprox`)

Reviewer: independent opus reviewer. Worktree `.claude/worktrees/048-B01-units-6-8` at
`43d25d1`. Modules `formalization/NSFormalization/Section4/B01/{Separated,Spatial}.lean`,
conformance `research/B01/axioms_u68.lean`, log `research/B01/ATTEMPTS_U68.md`.

## Verdict: ACCEPT-WITH-NOTES

The mathematics is right, the two theorems are the spec fields verbatim, the axiom audit is
clean, and both recorded snags reproduce exactly. Two merge/hygiene findings must be fixed
(one of them *before* this branch is merged onto the current `origin/erenup/integration`,
because lane 035 is already there): a same-namespace `SpaceTimeField` collision, and an
over-wide file-level heartbeat bump. Neither touches the proofs.

---

## Findings

### F1 — MEDIUM. `Separated.lean` re-declares `NSFormalization.Section4.B01.SpaceTimeField`, which lane 035's already-merged `B01/Compact.lean` also declares

* Declaration: `abbrev SpaceTimeField := VelocityField`
  * `formalization/NSFormalization/Section4/B01/Separated.lean:54`, inside
    `namespace NSFormalization.Section4.B01` (opened at `:39`).
  * `formalization/NSFormalization/Section4/B01/Compact.lean:64`, inside the **same**
    `namespace NSFormalization.Section4.B01` (opened at `:52`). That file is on
    `origin/erenup/integration` already (`git ls-tree -r origin/erenup/integration --
    formalization/NSFormalization/Section4/B01/` lists `Compact.lean`, `Completion.lean`;
    merged as PR #39, `45e07e2`). The *local* `refs/heads/erenup/integration` (`f999b41`) is
    behind and has no `B01/` directory, which is why this lane never saw it.
* What is wrong: two modules in one tree declaring the same constant is a hard Lean import
  error as soon as any single module imports both. That module is coming: B01 unit 10
  assembles units 2–9 into the `BochnerApproxAPI` term and will import `Compact`,
  `Completion`, `Separated` and `Spatial` together (`research/B01/COMPARISON.md:151`, row 10),
  as will the promoted `verification/Contracts/V1/BochnerApprox.lean` and its `#print axioms`
  test. Reproduced in isolation (identical namespace + name, two modules, one importer):

  ```
  DupC.lean:1:0: error: import DupB failed, environment already contains
  'NSFormalization.Section4.B01.SpaceTimeField' from DupA
  ```

  It is *not* an immediate break today: neither module imports the other, and
  `formalization/NSFormalization.lean` (the default `lean_lib` root) imports no `Section4`
  module at all, so `lake build` of the default target never puts both in one environment.
  This is a latent break, not a live one — which is exactly why it must be caught at merge.
* Names declared in both files (full comparison, `§0` and below):
  * `Separated.lean`: `SpatialField`, **`SpaceTimeField`**, `separatedField`, `separatedPath`,
    `integrable_schwartz_mul`, `coe_sum_smul_apply`, `space_sum_apply`, `angReal_sum_smul`,
    `hasCompactSupport_sepTerm`, `tsupport_sepTerm_subset`, `tsupport_finsetSum_subset`,
    `contDiff_separatedField`, `hasCompactSupport_separatedField`,
    `tsupport_separatedField_pos`, `isSobolevPath_separated`,
    `aestronglyMeasurable_separatedPath`, `separatedAssembly`.
  * `Compact.lean` (035): **`SpaceTimeField`**, `MemBochnerDatum`, `bochnerDatumENorm`,
    `bochnerDatumENorm_eq_homogeneous`, `CompletedDenseVia`, `CompletedDense`,
    `forceClassCompact`, `bochnerSpace`, `isSobolevPath_angularRealVectorSlice`,
    `aestronglyMeasurable_angularRealVectorSlice`, `bochnerDatumENorm_toLp_sub`,
    `approxCompact`.
  * `Completion.lean` (035): `completionRepresentative`, `completionSurjective`,
    `completionNorm`, `completionCongr`.
  * Intersection: exactly `{SpaceTimeField}`. `SpatialField` is **not** declared by 035, so it
    does not collide.
* Fix (one line, in this lane, not in 035): delete `Separated.lean:53-54`
  (`/-- Contracts.V1.Data.SpaceTimeField … -/ abbrev SpaceTimeField := VelocityField`) and
  write the return type of `separatedField` (`Separated.lean:59`) as `VelocityField` — which is
  what the abbrev unfolds to, is already in scope via `open NavierStokes.ProblemStatement`, and
  is the spelling `D01/ForceClass.lean` itself uses for `IsSobolevPath`/`MemForceCompact`.
  The alternative (`import NSFormalization.Section4.B01.Compact` and drop the abbrev) also
  works but drags the whole Bochner vocabulary of unit 2 into unit 6 for one abbreviation.
  Adjust the `§0` docstring at `Separated.lean:28-34` accordingly. Nothing else changes:
  `SpaceTimeField` occurs exactly once in the lane's code.

### F2 — MEDIUM. The file-level `set_option maxHeartbeats 2000000` in `Spatial.lean` is ~5.7× wider than needed, in scope and in magnitude

* Declaration: `formalization/NSFormalization/Section4/B01/Spatial.lean:38`.
* What I measured (scratch copies in `/tmp`, deleted afterwards; each run
  `lake env lean <copy>` from `verification`):

  | value | result |
  |---|---|
  | `200000` (Lean default) | **fails**: `Spatial.lean:178:10: error: (deterministic) timeout at whnf, maximum number of heartbeats (200000)` and `:183:4: … timeout at «tactic execution»` |
  | `250000` | fails (3 errors) |
  | `300000` | fails (3 errors) |
  | `350000` | passes (exit 0) |
  | `400000` | passes (exit 0) |
  | `800000` | passes (exit 0) |
  | `2000000` (as committed) | passes |

* Which declaration needs it: only `spatialApprox` (`Spatial.lean:132-188`). Both failing
  positions — `:178` (`rw [spatialDatum_eq, map_sub, hAc, ContinuousLinearEquiv.apply_symm_apply]`)
  and `:183` (`rw [← ofReal_norm]`) — are inside it. Every other declaration in the file
  (`spatialVector`, `spatialVector_{apply,smooth,support,compact}`, `spatialCyclesVector`,
  `spatialDatum`, `spatialDatum_eq`, `spatialDatum_isSobolevDatum`, `norm_le_sum_coord`)
  compiles at the default.
* A targeted option **suffices**, and I verified it: deleting the file-level `set_option`
  entirely and inserting

  ```lean
  set_option maxHeartbeats 400000 in
  /-- **Unit 8, `spatialApprox`.** … -/
  theorem spatialApprox …
  ```

  (i.e. *above* the docstring — the parse error `ATTEMPTS_U68.md:86` records came from putting
  it *between* the docstring and the `theorem`) compiles the whole file, exit 0.
* Why MEDIUM rather than LOW: a bump is genuinely needed (350000 is the floor), so the *need*
  has tree precedent — but the *form* committed does not. The tree's targeted precedent is
  `Section4/A03/RealAngularProduct.lean:111`, which is literally `set_option maxHeartbeats
  400000 in`; also `Section4/A03/ScalarTameProduct.lean:226` (`1200000 in`) and
  `Source/LocalReferenceInsertion.lean:17` (`800000 in`). As committed, `2000000` is the
  second-largest budget anywhere in `formalization/` (only `Paper3/RealPositiveDensity.lean:8`
  at `8000000` is larger) and it silently covers ten declarations that do not need it, so any
  future defeq regression in them goes unnoticed.
* Fix: replace `Spatial.lean:38` with `set_option maxHeartbeats 400000 in` placed immediately
  above the `spatialApprox` docstring (`:129`). `400000` leaves ~14% headroom over the
  measured 350000 floor and matches the existing A03 precedent. Update
  `ATTEMPTS_U68.md:83-85`, which currently justifies the file-level `2000000`.

### F3 — LOW. `SpatialField`/`SpaceTimeField` in `Separated.lean` also duplicate canonical D01 copies

`D01/HomogeneousWitness.lean:226` already declares `abbrev SpatialField := Space → Space` and
`:614` `abbrev SpaceTimeField := VelocityField`, both citing `Data.lean:99,104` — the same
restatements, in namespace `NSFormalization.Section4.D01.Homogeneous`. No collision (different
namespace, and Lean prefers the current namespace over `open`ed names, which is why the build is
green), but the tree now carries three copies of each. Not blocking; folding `SpaceTimeField`
away per F1 halves it. Reuse of `D01.Homogeneous.SpatialField` would require importing
`HomogeneousWitness`, which `Separated.lean` does not currently need — leaving `SpatialField`
where it is, is defensible.

### F4 — NIT. Stale `Spec.lean` line references

`separatedField` is at `research/B01/Spec.lean:140` and `separatedPath` at `:147`; the code
cites `:135,143` at `Separated.lean:31`, `:48`, `:56`, `:62` and `axioms_u68.lean:16`, `:29`,
`:34`. (`:250` and `:292` for the two fields are correct.) One-character-class fix.

### F5 — NIT. `Spatial.lean:64-65` is a double blank line between `spatialVector_smooth` and `spatialVector_support`.

---

## What checks out

### Builds — clean

```
$ cd WT && bash scripts/lean-install.sh
… == OK

$ cd WT/verification && . ../scripts/lean-env.sh && export LEAN_NUM_THREADS=6
$ lake build NSFormalization.Section4.B01.Separated NSFormalization.Section4.B01.Spatial
EXIT=0 — "Build completed successfully (9879 jobs)."
$ grep -n "B01" <build log>        # no matches
$ grep -c "^warning" <build log>   # 15
```

All 15 warnings are replay warnings from pre-existing modules — `Source/RealSobolev.lean:90`
(unused simp arg, `<;>` style), `Paper3/SpatiallyCompactTime.lean:88` and
`Paper3/SobolevDirectionalDerivative.lean:103` (deprecated `ContinuousLinearMap.sub_apply`,
`SchwartzMap.smul_apply`), `Paper3/RealPositiveDensity.lean:57,66,78,90` (`<;>` style),
`Paper3/RealVectorPositiveDensity.lean:29` (unused binder). **Zero** warnings mention
`Section4/B01`. Compiling each module standalone with `lake env lean` likewise produces no
output.

### Axiom audit — exactly the three standard axioms, and both `example`s typecheck

```
$ lake env lean ../research/B01/axioms_u68.lean
'NSFormalization.Section4.B01.separatedAssembly' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.B01.spatialApprox' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT=0
```

No other output, so both `example`s elaborated. Note this file `import Contracts.V1.Data`, so
the predicates in the `example` types (`SpatialField`, `SpaceTimeField`, `IsSobolevDatum`,
`IsSobolevPath`, `MemForceCompact`, `forceTimeMeasure`) are the **contract's own**, not the
formalization's restatements; the discharge goes through genuine definitional equality.

### No `sorry`/`admit`/`native_decide`/`axiom`

```
$ grep -n "sorry\|admit\|native_decide\|axiom" \
    formalization/NSFormalization/Section4/B01/{Separated,Spatial}.lean \
    research/B01/axioms_u68.lean
```

Five hits, all benign: `Separated.lean:33`, `Spatial.lean:32`, `axioms_u68.lean:11` mention the
*filename* `axioms_u68.lean` in docstrings; `axioms_u68.lean:62,63` are the two `#print axioms`
commands. Nothing in tactic or term position.

### `make check` — passes

```
$ make check        # check_formalization_plan.py --check; check_contracts.py;
                    # test_contract_policy.py (13 tests, OK); check_work_queue.py
EXIT=0 — "30 work items: ownership, contract registration and task cards consistent."
```

### Spec conformance — the fields verbatim, no extra hypotheses

Compared token-for-token after whitespace normalization.

* **Unit 6.** `Spec.lean:292-302` `separatedAssembly` vs `axioms_u68.lean:41-49`: identical
  binder list, identical six implications, identical three-way conjunction
  (`MemForceCompact (separatedField φ h) ∧ IsSobolevPath s (separatedField φ h)
  (separatedPath φ A) ∧ AEStronglyMeasurable (separatedPath φ A) forceTimeMeasure`).
  Discharged at `axioms_u68.lean:50-51` by `fun s _J φ h A hφs hφc hφpos hhs hhc hA =>
  NSFormalization.Section4.B01.separatedAssembly s φ h A hφs hφc hφpos hhs hhc hA` — a pure
  eta-expansion, arguments in order, no extra hypotheses, no side conditions. (`J` is explicit
  in the spec and implicit in the theorem; the `example` supplies it as `_J`, so the *spec's*
  type is what is proved.)
* **Unit 8.** `Spec.lean:250-252` `spatialApprox` vs `axioms_u68.lean:55-57`: identical.
  Discharged by `fun s A η hη => …spatialApprox s A η hη`. No extra hypotheses; in particular
  **no lower bound on `s`** — the theorem is for every real `s`, as `04-whole-space.tex:238`
  ("for every real `s`") demands. Contrast `D01.schwartzPairable_of_isSobolevDatum`, which
  needs `0 ≤ s`; unit 6 avoids that too by using compact support rather than an order bound
  (`integrable_schwartz_mul`, `Separated.lean:73`).
* **`§0` restatements.** `Spec.lean:140` `separatedField` and `:147` `separatedPath` appear
  character-identical in `axioms_u68.lean:30-37` and `Separated.lean:58-65`:
  `fun z => ∑ j, φ j z.1 • h j z.2` and `fun t => ∑ j, φ j t • A j`.
  `SpatialField := Space → Space` and `SpaceTimeField := VelocityField` match
  `Contracts/V1/Data.lean:99,104`. `IsSobolevPath`, `MemForceCompact`, `forceTimeMeasure`
  are reused from `D01/ForceClass.lean:152,169,147` and `IsSobolevDatum` from
  `D01/SmoothDatum.lean:237`; I re-checked each against `Data.lean:174,559,118,160` and they
  are token-identical modulo the `SpaceTimeField`/`VelocityField` and
  `SpatialField`/`Space → Space` abbrev spellings, which are the same constants. (Those
  restatements predate this lane.)

### Unit 8 against the manuscript — the approximant is real, smooth, compact, and `< η` is genuine

* `paper/sections/04-whole-space.tex:249` reads: *"These constructions also prove the real
  vector-valued versions: take real parts of each component of the approximants. Complex
  conjugation is an isometry for every Fourier norm here because its weight is real and even,
  so taking real parts is a contraction and preserves convergence to real data, smoothness and
  compact support."* The lane implements exactly that: the physical field is
  `spatialVector (fun i x => (ψ i x).re)` (`Spatial.lean:158`), componentwise real parts.
* **Real**: `h : SpatialField = Space → Space` by type — a real Euclidean three-vector field.
  `Complex.re` is applied componentwise; nothing complex survives.
* **Smooth**: `Spatial.lean:160`, `Complex.reCLM.contDiff.comp ((ψ i).smooth ⊤)` through
  `spatialVector_smooth` (`(contDiff_piLp 2).mpr`).
* **Compactly supported**: `Spatial.lean:161-162`, `(hψc i).comp_left Complex.zero_re` through
  `spatialVector_compact`; `hψc` comes from `dense_compact_weightedFourierLp`, so the `ψ i`
  really are compactly supported, matching `:239`'s stage-2 cutoff conclusion.
* **`IsSobolevDatum s h H`**: `spatialDatum_isSobolevDatum` (`Spatial.lean:100-116`). It never
  assumes reality of `compactFourierLp` and never needs idempotency of `realProjection`; it
  goes `cyclesToAngularRealVector_apply` → `angularRealization_cyclesToAngularReal` →
  `weightedFourierLp_realPart` (used right-to-left) → `sobolevRealization_weightedFourierLp`,
  landing on `∫ x, ψt x * ((Re (ψ i x) : ℝ) : ℂ)`, which is `Data.IsSobolevDatum`'s right-hand
  side for the physical field actually returned.
* **`‖H − A‖ₑ < η`, not `< C·η`** — checked arithmetically. `cyclesToAngularRealVector_norm_le`
  (`Paper3/AngularRealVectorBochner.lean:24`) is `‖cyclesToAngularRealVector s v‖ ≤
  frequencyUnit ^ |s| * ‖v‖`, a bounded equivalence and not an isometry, exactly as
  `COMPARISON.md:130-135` warns. The lane absorbs the constant *before* choosing the
  approximants rather than after: with `C := frequencyUnit ^ |s|` it sets
  `δ := η.toReal / (3 * (C + 1))` (`Spatial.lean:145`), obtains `‖·‖ ≤ 3δ` per the
  three-component triangle inequality `norm_le_sum_coord`, and then
  `C * (3δ) = C·η.toReal/(C+1) < η.toReal` strictly (`nlinarith` at `:148`, the `+1` in the
  denominator is what makes it strict and also removes any need for `C ≠ 0`). The conclusion is
  transported to `ℝ≥0∞` by `ofReal_norm` and
  `ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)`, with `η = ⊤` handled separately by
  `ENNReal.ofReal_lt_top` (`:184-188`). So the bound delivered is the spec's `< η` on the nose.
  `hη : 0 < η` is used only to get `0 < η.toReal`.

### Unit 6 — the three conjuncts

Nothing to flag. `MemForceCompact` via `D01.memForceCompact_of_smooth_support` fed by
`ContDiff.sum`, a Finset-induction support lemma (`tsupport_finsetSum_subset`) over the
vector-valued generalization of `PBD:54`, and the `PPD:47-53` `tsupport ⊆ Prod.fst ⁻¹' …`
pattern. `IsSobolevPath` by the direct `map_sum` route `COMPARISON.md:150` recommends rather
than iterating `D01.isSobolevDatum_add` — both sides collapse to
`∑ j, φ j t • ∫ x, ψ x * (h j x i : ℂ)`, the left by ℂ-linearity of `angularRealization`
(through `map_smul_of_tower`, since the scalars are real), the right by `integral_finsetSum`
with integrability from compact support. Measurability from continuity of the path.

### Honesty of `ATTEMPTS_U68.md` — both spot-checked snags reproduce exactly

1. **`PiLp.sum_apply` / `PiLp.finset_sum_apply` do not exist** (`ATTEMPTS_U68.md:43-44`).
   Confirmed: `grep -rn "PiLp\.sum_apply\|PiLp\.finset_sum_apply"` over the pinned
   `verification/.lake/packages/mathlib/Mathlib` returns **no matches**, and
   `Mathlib/Analysis/Normed/Lp/{PiLp,WithLp}.lean` declare no `*sum_apply` at all. The
   workaround the lane used (`coord`/`EuclideanSpace.proj` as bundled CLMs + `map_sum`,
   `Separated.lean:90-102`) is the right one.
2. **`SecondCountableTopologyEither` instance timeout** (`ATTEMPTS_U68.md:36-38, 45`).
   Confirmed. Deleting line `Separated.lean:210`
   (`have : SecondCountableTopologyEither ℝ (RealVectorSobolev s) := ⟨Or.inl inferInstance⟩`)
   and recompiling gives

   ```
   Sep_noSCT.lean:210:8: error: failed to synthesize
     SecondCountableTopologyEither ℝ (RealVectorSobolev s)
   (deterministic) timeout at `typeclass`, maximum number of heartbeats (20000) has been reached
   ```

   i.e. `synthInstance.maxHeartbeats`, not `maxHeartbeats` — the explicit `have` is the correct
   and cheapest fix, and no `set_option` is needed in `Separated.lean`. (`Separated.lean` carries
   no heartbeat option at all, which is right.)

The log's own recorded command results (`ATTEMPTS_U68.md:101-107`) reproduce; the only
discrepancy is cosmetic — the log reports 9878 jobs for the `Separated` build alone, I see 9879
for the two-target build.

---

## Commands run, in order

```
cd WT && bash scripts/lean-install.sh                                  → "== OK"
. WT/scripts/lean-env.sh ; export LEAN_NUM_THREADS=6                   (no -j anywhere)

cd WT/verification
lake build NSFormalization.Section4.B01.Separated \
           NSFormalization.Section4.B01.Spatial                        → EXIT 0, 9879 jobs
  grep "B01" <log> → no matches ; grep -c "^warning" <log> → 15 (all pre-existing modules)
lake env lean ../research/B01/axioms_u68.lean                          → EXIT 0, both
  #print axioms = [propext, Classical.choice, Quot.sound], no other output
grep -n "sorry\|admit\|native_decide\|axiom" <2 modules + axioms file> → 5 hits, all comments
                                                                          or the #print lines
cd WT && make check                                                    → EXIT 0

heartbeats (scratch copies in /tmp, since deleted):
  lake env lean <Spatial @200000>   → EXIT 1: :178 whnf timeout, :183 tactic-execution timeout
  lake env lean <Spatial @250000>   → EXIT 1
  lake env lean <Spatial @300000>   → EXIT 1
  lake env lean <Spatial @350000>   → EXIT 0
  lake env lean <Spatial @400000>   → EXIT 0
  lake env lean <Spatial @800000>   → EXIT 0
  lake env lean <Spatial, file-level option deleted,
                 `set_option maxHeartbeats 400000 in` above the spatialApprox docstring>
                                    → EXIT 0
honesty:
  lake env lean <Separated minus the SecondCountableTopologyEither have>
                                    → EXIT 1: failed to synthesize …, typeclass timeout (20000)
  grep -rn "PiLp\.sum_apply\|PiLp\.finset_sum_apply" <pinned Mathlib> → no matches
duplication:
  git ls-tree -r origin/erenup/integration -- .../Section4/B01/ → Compact.lean, Completion.lean
  lean DupA.lean/DupB.lean/DupC.lean (same namespace + name, /tmp)
                                    → "import DupB failed, environment already contains
                                       'NSFormalization.Section4.B01.SpaceTimeField' from DupA"
```

All scratch files under `/tmp/b48scratch` were deleted; `git status` in the worktree shows
only this review file. No code was modified.

## Merge checklist

1. Apply F1 before merging (delete `Separated.lean:53-54`, return type `VelocityField`) — this
   branch's base predates lane 035's merge, so the collision will not show up until after the
   rebase.
2. Apply F2 (targeted `set_option maxHeartbeats 400000 in` on `spatialApprox`; drop the
   file-level `2000000`) and refresh `ATTEMPTS_U68.md:83-85`.
3. F4/F5 are optional tidy-ups.
4. After the rebase, re-run `lake build NSFormalization.Section4.B01.{Compact,Completion,Separated,Spatial}`
   and `lake env lean ../research/B01/axioms_u68.lean` once more on the merged tree.
