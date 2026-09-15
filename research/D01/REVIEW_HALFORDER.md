# Review — lane 042 (D01), G3 inhomogeneous half: `Section4/D01/HalfOrder.lean`

**Verdict: ACCEPT-WITH-NOTES.**

The theorem is real, it is exactly the statement R43's G3 asks for (inhomogeneous
half), it is proved from `MemForceR` alone on standard axioms, the reuse claims
check out, and the recorded failures are reproducible. Two non-blocking notes: the
module is outside every default build closure so nothing re-checks it or its
contract bridge automatically (finding 1), and the order-lowering CLM is built by
hand where a `codRestrict` of the existing CLM would do (finding 2).

Diff is additive only — 3 new files, 354 insertions, 0 deletions, nothing under
`verification/` touched, so no contract drift is possible.

---

## 1. Commands and results

All from the worktree `/data_8T/ping/blowup_density/.claude/worktrees/042-D01-halforder-force-norms`
(WT) after `bash scripts/lean-install.sh` (ended `== OK`), `. scripts/lean-env.sh`,
`LEAN_NUM_THREADS=6`, no `-j`, one lake at a time, all lake commands from
`WT/verification`.

| # | command | result |
|---|---|---|
| C1 | `lake build NSFormalization.Section4.D01.HalfOrder` | **exit 0**, `Build completed successfully (9884 jobs)`. `grep -i halforder` over the full build log: **no line**, i.e. no error, warning or info from this module. (The warnings in the log are pre-existing ones replayed from `Paper3/*`, `Source/*`.) |
| C2 | `lake env lean ../formalization/NSFormalization/Section4/D01/HalfOrder.lean` (fresh standalone elaboration, so all linters actually run) | **exit 0, zero bytes of output**. No linter warnings. |
| C3 | `lake env lean ../research/D01/axioms_halforder.lean` | **exit 0**. Both `rfl` bridges and all three `example`s typecheck. `#print axioms` = `[propext, Classical.choice, Quot.sound]` for `forceSobolevENormL1_half_ne_top`, `forceSobolevENorm_ne_top`, `forceSobolevENormL2_half_ne_top` — exactly the three standard axioms, nothing else. |
| C4 | `grep -n "sorry\|admit\|native_decide\|axiom\|maxHeartbeats"` on both new Lean files | only the word "axioms" inside docstrings/`#print axioms` lines (`HalfOrder.lean:136`, `axioms_halforder.lean:10,12,47,48,49`). **No `sorry`, `admit`, `native_decide`, `axiom` declaration or `maxHeartbeats` bump.** Also checked: no `set_option`, no `attribute`, no `unsafe`/`partial`, no floating `variable`. |
| C5 | `make check` | **exit 0** — `check_formalization_plan.py --check`, `check_contracts.py`, `test_contract_policy.py` (13 tests OK), `check_work_queue.py` (`30 work items: ownership, contract registration and task cards consistent`). |
| C6 (my own, independent of the lane's conformance file) | a scratch file stating the obligation with **fully qualified** contract names and no `namespace`/`open` in play: `∀ f : BlowupDensity.Contracts.V1.Data.SpaceTimeField, BlowupDensity.Contracts.V1.Data.MemForceR f → BlowupDensity.Contracts.V1.Data.forceSobolevENormL1 (1/2) f ≠ ⊤ := fun _ hf => NSFormalization.Section4.D01.forceSobolevENormL1_half_ne_top hf` | **exit 0, no output.** This is the decisive check: the lane's theorem discharges the R43 obligation stated purely in frozen-contract vocabulary. |

## 2. The statement is the one R43 needs

`research/R43/COMPARISON.md:109` (§4, row **G3**) asks for **two** things:
`∀ f, MemForceR f → forceSobolevENormL1 (1/2) f ≠ ⊤` (inhomogeneous) and
`forceHomogeneousENorm 1 (1/2) f ≠ ⊤` (homogeneous). This lane's brief is the
inhomogeneous half; that half is delivered literally.

* `HalfOrder.lean:178` `forceSobolevENormL1_half_ne_top {f} (hf : MemForceR f) : forceSobolevENormL1 (1/2) f ≠ ⊤`.
  Via C3/C6 this *is* `Contracts.V1.Data.forceSobolevENormL1 (1/2) f ≠ ⊤` for
  `Contracts.V1.Data.MemForceR f`. The `1/2` is the real number one-half
  (`forceSobolevENormL1 : ℝ → …`), not a natural-number division.
* `HalfOrder.lean:183` `forceSobolevENormL2_half_ne_top` is the `q = 2` companion (bonus).
* `HalfOrder.lean:156` `forceSobolevENorm_ne_top {f} (hf : MemForceR f) {s : ℝ} {m : ℕ} (hsm : s ≤ (m:ℝ)) {q : ℝ≥0∞} (hq : q = 1 ∨ q = 2) : forceSobolevENorm q s f ≠ ⊤`.
  **Hypotheses:** exactly `MemForceR f`, `s ≤ (m : ℝ)` with `m` a natural number,
  and the disjunction `q = 1 ∨ q = 2`. **Nothing else** — no smoothness, decay,
  support, measurability or instance side conditions, no `Fact` instances, no
  implicit assumptions hidden in `variable`s (C4).
  `q` is restricted by a plain disjunction rather than by a class or an interval,
  and that is the honest restriction: `MemForceR` (`Data.lean:544-551`) carries
  exactly two finiteness clauses, `MemLp G 1 forceTimeMeasure` and `MemLp G 2
  forceTimeMeasure`, so `q ∈ {1,2}` is all the class can give.
  **`q = 1` is the case R43 uses** (Prop 4.3's `‖f‖_{L¹_t H^{1/2}_x} ≤ c`), and it
  is supplied at `:180` as `Or.inl rfl` with `m = 1`, `1/2 ≤ 1` by `norm_num`.

**Token-for-token diff of the local restatement against `Data.lean:225`.** I
diffed `verification/Contracts/V1/Data.lean:225-232` against
`HalfOrder.lean:141-149`. The body is character-identical:

```
  ⨅ G : {G : ℝ → RealVectorSobolev s //
      IsSobolevPath s f G ∧ AEStronglyMeasurable G forceTimeMeasure},
```

Exactly two token differences, both benign and both certified by the `rfl` bridge
`halforder_forceSobolevENorm_eq` (C3):

1. `f : SpaceTimeField` → `f : VelocityField`. `Data.lean:104` is
   `abbrev SpaceTimeField := VelocityField`, so this is the same type.
2. `bochnerDatumENorm` → `Homogeneous.bochnerDatumENorm`, i.e. the existing local
   copy at `HomogeneousWitness.lean:620`, whose body is `eLpNorm G q forceTimeMeasure`,
   character-identical to `Data.lean:205-206`.

`IsSobolevPath` and `forceTimeMeasure` inside the restatement resolve to the
same-namespace copies `ForceClass.lean:152` and `ForceClass.lean:147`, each a
verbatim restatement of `Data.lean:174` / `Data.lean:118`. No same-namespace
duplicate trap: `HalfOrder.lean` and `ForceClass.lean` are both in
`NSFormalization.Section4.D01`, while `HomogeneousWitness.lean`'s copies live in the
strictly deeper `…D01.Homogeneous`, so `forceTimeMeasure` in the restatement is
unambiguously ForceClass's (and `Homogeneous.forceTimeMeasure` is the same
`abbrev … := positiveTimeMeasure`, hence reducibly equal — which is why the `rfl`
bridge goes through and why the `show eLpNorm …` at `:172` typechecks).

**The proof.** `MemForceR` at `m` gives `G` with `IsSobolevPath m f G` and `MemLp G
q`; `isSobolevPath_lower` (`:120`) lowers the path to order `s`; `comp_memLp'` of
the CLM `lowerVectorL` keeps `MemLp`, hence `AEStronglyMeasurable` and finite
`eLpNorm`; `iInf_le` at that witness bounds the infimum; `ne_top_of_le_ne_top`
closes. Directions are right (`iInf_le f i : iInf f ≤ f i`), and the witness really
is an element of the infimum's index subtype, so nothing is proved by an empty
infimum or a junk value.

**Gaps declared honestly.** `research/D01/ATTEMPTS_HALFORDER.md` names G2 and the
homogeneous half of G3 as **GAP** in its Result section and devotes a section to
why, with the estimated new work and a recommended home. I spot-checked its two
load-bearing claims: `research/A05/Spec.lean:268` `homogeneousLeSobolev` is indeed a
**field of a spec structure**, not a proved lemma, and is the spatial-slice
inequality; and `HomogeneousWitness.lean:473,519`
`exists_isHomogeneousSliceDatum` / `isHomogeneousSliceDatum_compact` do carry a
Schwartz-component / compact-support hypothesis, so they do not reach a general
`H^∞` slice. `HalfOrder.lean`'s own module docstring (`:40-54`) repeats the
declaration in the file itself, where a reader will see it. No overclaiming.

## 3. Reuse and duplication — clean

All three cited reuses check out at the cited lines:

* `Section4/A03/RealAngularProduct.lean:140` `lowerDatum`, `:198`
  `norm_lowerDatum_le`, `:189` `lowerConst` — opened and used at `HalfOrder.lean:67,94,95`.
* `Section4/A03/ScalarTameProduct.lean:114` `IsScalarSobolevDatum.lower` — used at
  `:127` (with `hrs : r ≤ s` in the right direction).
* `Section4/A03/VectorTameProduct.lean:54` `isSobolevDatum_iff` — used at `:124,127`.
* `Section4/D01/HomogeneousWitness.lean:620` `bochnerDatumENorm` — used at `:144`.

**No duplicated definition.** I grepped the whole `formalization/NSFormalization`
tree for every notion the file introduces or restates:

* `def forceSobolevENorm` / `abbrev forceSobolevENormL1`: the *only* occurrences in
  the tree are the new ones in `HalfOrder.lean`. The docstring's claim "no local
  copy in tree" is true, so the restatement is necessary, not duplicative.
* `lowerDatumL` / `lowerDatumLM` / `lowerVectorL`: unique. The only other
  `RealSobolevHilbert s →L[ℝ] …` in the tree is
  `Paper3/RealPositiveDensity.lean:24` `realSobolevInclusion`, a different map.
* No vector-level `IsSobolevDatum.lower` exists in `A03`, so going componentwise in
  `isSobolevPath_lower` is not bypassing an existing lemma.
* The pre-existing multiple copies of `forceTimeMeasure` (4) and `IsSobolevPath`
  (3) are all older; this lane **reuses** the D01 ones rather than adding a fifth
  and a fourth.

## 4. Honesty of the recorded failures — two of three reproduced

`ATTEMPTS_HALFORDER.md` "Tactical failures / notes". I reproduced two:

* **`SetLike.coe_injective` vs `Subtype.ext`** — I replaced both
  `refine Subtype.ext ?_` (`:82`, `:86`) with `refine SetLike.coe_injective ?_` in a
  `/tmp` copy and elaborated it:
  `error: failed to synthesize instance of type class SetLike ↥(RealSobolevHilbert r) ?m` at
  both sites, followed by `No goals to be solved`. The note is accurate — the
  element type of the `ClosedSubmodule` carrier has no `SetLike` instance.
* **The `iInf_le` heartbeat** — I replaced the explicit infimand at `:168-170` with
  `iInf_le _ ⟨_, hpath', hmem.aestronglyMeasurable⟩` and dropped the
  `show eLpNorm …` at `:172`:
  `error: (deterministic) timeout at 'whnf', maximum number of heartbeats (200000) has
  been reached` at the theorem, and the two corollaries then fail with
  `(kernel) unknown constant`. The note is accurate, and the fix chosen (explicit
  function argument + explicit `show`) is the right one — no `maxHeartbeats` bump
  was used to paper over it.

(The third note, about `AddMemClass.coe_add` / `SetLike.val_smul` /
`ContinuousLinearMap.map_smul_of_tower` being the right coercion lemmas, is
consistent with the code at `:84,88` and was not separately mutated.)

---

## Findings

### Finding 1 — `HalfOrder.lean` sits outside every build closure, so neither the theorem nor its contract bridge is re-checked automatically (severity: **medium**, non-blocking)

**Declarations:** the module `NSFormalization.Section4.D01.HalfOrder` as a whole,
and `research/D01/axioms_halforder.lean`.

**What is wrong.** Nothing imports the new module:

* `formalization/NSFormalization.lean` (the library root, 281 imports) imports **no
  `Section4` module at all** — `grep -n "Section4" formalization/NSFormalization.lean`
  is empty.
* `verification/Bindings/DatumLemmas.lean:3-5` imports `Section4.D01.DatumToJets`,
  `Section4.D01.HomogeneousWitness` and `Section4.D01.ForceClass` — **but not
  `HalfOrder`**. That import list is how every other D01 lane module reaches
  `verification`'s default targets (`defaultTargets = ["Tests", "Contracts"]`).
* CI (`.github/workflows/contracts.yml:21`) runs only `make check`, which is the
  four Python architecture checks — no Lean build at all.

So `HalfOrder.lean` compiles only when someone names it explicitly, and
`axioms_halforder.lean` — which is where the `rfl` bridge to
`Contracts.V1.Data.forceSobolevENorm` and the contract-vocabulary `example`s live —
runs only when someone runs it by hand. This is precisely the state
`Bindings/DatumLemmas.lean`'s own docstring says the binding layer exists to end:
"until now that was checked only in throwaway scratch files … §1 below commits them,
so CI fails if either side drifts." The new restatement has no such commitment.

Consequence for R43: R43's G3 row assigns this to **D01 (`DatumLemmas`)**, and the
frozen `D01.datum_lemmas` contract (`verification/contracts.json:104-111`,
`Contracts/V1/DatumLemmas.lean`) has no field for it, so a consumer working in the
contract layer cannot see this theorem yet. Its scope text explicitly lists
"finiteness of `forceHomogeneousENorm`" under "Not asserted anywhere" — consistent,
not contradicted, but the inhomogeneous finiteness is likewise absent.

**Fix** (a follow-up lane, since it edits a frozen contract and so needs the D01
owner): add `import NSFormalization.Section4.D01.HalfOrder` to
`verification/Bindings/DatumLemmas.lean`, move the two `rfl` bridges of
`axioms_halforder.lean` into its §1, add a
`forceSobolevENormL1_half_ne_top : ∀ f, MemForceR f → forceSobolevENormL1 (1/2) f ≠ ⊤`
field (and its `L²`/general companions if wanted) to `DatumLemmasAPI` in
`Contracts/V1/DatumLemmas.lean`, and extend the `D01.datum_lemmas` scope text in
`contracts.json`. Then `lake test` re-proves the bridge on every change and R43 can
consume it through the API. Nothing about the present lane needs to change.

### Finding 2 — `lowerDatumLM` + `LinearMap.mkContinuous` is avoidable; a `codRestrict` of the existing CLM gives the same map in four lines (severity: **low**, quality/reuse)

**Declarations:** `HalfOrder.lean:79-95` (`lowerDatumLM`, `lowerDatumL`).

**What is wrong.** `angularOrderLowering s r hrs` is *already* a
`ContinuousLinearMap` (`Paper3/AngularTameProduct.lean:39-42`,
`Lp ℂ 2 volume →L[ℂ] Lp ℂ 2 volume`), and `realSubspace` is a
`ClosedSubmodule ℝ FourierData` whose parameter `_s` is unused
(`Source/RealSobolev.lean:118`). So the corestriction to the reality subspace needs
neither a hand-built `LinearMap` (17 lines with two `Subtype.ext` goals and the
`AddMemClass.coe_add` / `SetLike.val_smul` coercion hunt that the ATTEMPTS file
records as friction) nor the norm bound `norm_lowerDatum_le`/`lowerConst` to obtain
continuity.

**Verified alternative** — I compiled this in a scratch file against the same
imports, and it elaborates with no errors:

```lean
def lowerDatumL' (s r : ℝ) (hrs : r ≤ s) : RealSobolevHilbert s →L[ℝ] RealSobolevHilbert r :=
  (((angularOrderLowering s r hrs).restrictScalars ℝ).comp (realSubspace s).subtypeL).codRestrict
    (realSubspace r).toSubmodule
    (fun A => NSFormalization.Section4.A03.angularOrderLowering_mem_realSubspace s r hrs A.property)

example (s r : ℝ) (hrs : r ≤ s) (A : RealSobolevHilbert s) :
    lowerDatumL' s r hrs A = NSFormalization.Section4.A03.lowerDatum s r hrs A := rfl   -- checks
```

The `rfl` example shows it is *definitionally* the lane's map, so
`lowerDatumL_apply`, `lowerVectorL_apply` and `isSobolevPath_lower` stay `rfl` and
nothing downstream changes. `norm_lowerDatum_le` would then be unused by this file
(it is still the right citation for the mathematical content, and stays used
elsewhere in A03).

**Fix.** Optional cleanup: delete `lowerDatumLM`, define `lowerDatumL` as above.
Not required for acceptance — the current code is correct, builds warning-free and
is `rfl`-compatible.

### Non-findings, recorded so they show as checked

* No new copy of any `Section4/**` definition (§3). The one new restatement,
  `forceSobolevENorm`, genuinely had no in-tree copy, is character-identical to
  `Data.lean:225` modulo the `SpaceTimeField`/`VelocityField` abbrev and the
  `Homogeneous.` qualifier, and is pinned by a `rfl` bridge.
* Line citations in the docstrings and in ATTEMPTS all resolve to the cited
  declarations (`RealAngularProduct.lean:140,198`, `ScalarTameProduct.lean:114`,
  `VectorTameProduct.lean:54`, `HomogeneousWitness.lean:620`,
  `AngularTameProduct.lean:51`, `AngularFourierDilation.lean:191-192`,
  `AngularRealVectorBochner.lean:14-15`, `Data.lean:118,174,205,225,231,544`).
* The claim in ATTEMPTS that interpolation was not needed is correct: order
  monotonicity from `m = 1` alone carries `s = 1/2`.
* Non-vacuity of the *class* `𝓕_ℝ` itself (some `f` with `MemForceR f` exists) is
  neither claimed nor needed here; G3 is about the norm, and this is the right
  scope.
