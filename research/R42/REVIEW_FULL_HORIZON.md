# Lane 098 review — R42 full horizon (`Section4/R42/FullHorizon.lean`)

**Verdict: ACCEPT-WITH-NOTES.**

The Lean is correct and clean: both theorems compile, the module is silent under
`lake env lean`, both declarations rest on exactly
`[propext, Classical.choice, Quot.sound]`, and `make check` is green. The two
statements are *exactly* the shapes they claim to be — Lemma A's hypothesis is
token-for-token `ClassicalSolutionR.sobolev` at horizon `S` and its conclusion the
same field at horizon `T` (printed with `pp.fullNames`, §Commands), and Lemma B's
hypothesis list is lane 087's `classicalSolutionR_of_inserted` verbatim with
`{S} (hS0 : 0 < S) (hST : S < T)` replaced by a single `(hT : 0 < T)`.

The two load-bearing claims of the brief both check out empirically:

* **Lemma B instantiates from `InsertionFamilyAPI` in the lane-092 pattern with
  zero mismatch** — 22 proof-body lines, byte-for-byte lane 092's `sol_on_shorter`
  except for the theorem name, the dropped `intro S hS0 hST`, and `hS0 hST` →
  `F.scaling.correction.time_pos` (`/tmp/r42rev098/Scratch.lean` §B1, compiles).
* **`IsMaximalSolution` does not need Lemma B.** `Maximal.lean:85-89` quantifies
  clause (ii) over `S` with `ENNReal.ofReal S < maximalLifespanR`; under
  `lifespan_eq` that is `S < T` *strictly*, never `S = T`, so clause (ii) is
  literally `sol_on_shorter`. I wrote the lemma at the Bindings level and it is
  **5 proof lines, compiles, and never mentions `FullHorizon`**
  (`/tmp/r42rev098/Scratch.lean` §B2). `MAXIMAL_SPLIT.md`'s central claim is
  confirmed.

The notes are documentation-level only. No code change is requested.

---

## Findings

### 1. `MAXIMAL_SPLIT.md` targets the A02 restatement and misses the **registered** V2 contract — *severity: medium (record completeness; costs the next lane a detour)*

**Location:** `research/R42/MAXIMAL_SPLIT.md`, §"The target predicate", §"Lean-ready
statement", §"Inputs (all available at the Bindings level)".

The table states Lemma C over `NSFormalization.Section4.A02.IsMaximalSolution`
(`Section4/A02/Maximal.lean:85`) and over `A02.maximalLifespanR` /
`A02.ClassicalSolutionR`. But `IsMaximalSolution` is already a **registered
contract** object: `A02.maximal_partial_v2` (`verification/contracts.json:148`)
restates it token-for-token in `Contracts.V1.Data` vocabulary
(`Contracts/V2/MaximalPartial.lean:106`), with the inhabited binding
`BlowupDensity.Bindings.maximalPartialV2` supplying `exists_maximal` and
`maximal_unique` and the transport `maximalPartial_isMaximalSolution_iff`
(`Bindings/MaximalPartialV2.lean:83`). The table never mentions V2.

This matters concretely, not cosmetically:

* `InsertionLifespan.sol_on_shorter` returns `Data.ClassicalSolutionR` and
  `InsertionLifespan.lifespan_eq` is about `Data.maximalLifespanR`. In **Data/V2
  vocabulary** Lemma C is therefore 5 lines with **no bridging at all**:

  ```
  theorem isMaximalSolution_of_inserted (hg : Data.MemForceR F.g)
      (hε : ε ∈ Ioc (0 : ℝ) F.ε₀) :
      Contracts.V2.MaximalPartial.IsMaximalSolution ν F.a (F.force ε)
        (F.velocity ε) (F.pressure ε) := by
    have hlife := InsertionLifespan.lifespan_eq F hg hε
    refine ⟨hlife ▸ ENNReal.ofReal_pos.mpr F.scaling.correction.time_pos,
      fun S hS0 hSlt => ?_⟩
    rw [hlife] at hSlt
    exact InsertionLifespan.sol_on_shorter F hε S hS0
      ((ENNReal.ofReal_lt_ofReal_iff F.scaling.correction.time_pos).mp hSlt)
  ```

  Compiles (`/tmp/r42rev098/Scratch.lean` §B2).
* In the table's **A02 vocabulary** the same result needs one extra line and one
  extra import — `(maximalPartial_isMaximalSolution_iff …).mpr`, plus
  `import Bindings.MaximalPartialV2` — because `sol_on_shorter` and `lifespan_eq`
  live on the other side of the two-`structure` divide. Verified as §B2' of the
  same scratch. The table's "Inputs (all available at the Bindings level)" lists
  only `sol_on_shorter`, `lifespan_eq`, `time_pos` and omits this transport.

**Fix (one paragraph, no Lean):** in `MAXIMAL_SPLIT.md`, add that the registered
vehicle is `A02.maximal_partial_v2` /
`Contracts.V2.MaximalPartial.IsMaximalSolution` (Data vocabulary), that the
Bindings-level lemma should be stated there (5 lines, no conversions), and that
the A02-vocabulary form is obtained by `maximalPartial_isMaximalSolution_iff`.
Also worth recording: `contracts.json:155` already names the eventual home —
"Theorem 4.2's packaged identification `insertion_lifespan_eq`" is listed there as
owed to a later lane.

The table's *other* claims all survive checking:

* `maximal_unique`'s side hypotheses are exactly `0 < ν`, `a ∈ initialClassR`,
  `MemForceR f` (`Maximal.lean:192-197`) — matching the table's list. (They are
  bound as `_ha`, `_hf` and unused in the proof, so the table's "all in hand at
  the Bindings level" via `P.viscosity_pos` / `initialClassR_a` / `memForceR_force`
  is right and sufficient.)
* `presingularTimes ν a gε = Ico 0 T` under `lifespan_eq` and `0 < T` — compiles
  (`/tmp/r42rev098/Scratch.lean` §B4).
* The table's literal formalization-level statement **and** its 5-line proof
  sketch (`ENNReal.ofReal_pos`, `ENNReal.ofReal_lt_ofReal_iff`) compile verbatim
  (§B3). Both cited Mathlib line numbers are exact: `ofReal_lt_ofReal_iff` at
  `Mathlib/Data/ENNReal/Real.lean:167`, `ofReal_pos` at `:176`.

### 2. Module docstring: "the only field that genuinely needs work is `sobolev`" is not accurate — *severity: low (wording)*

**Location:** `Section4/R42/FullHorizon.lean:11-17`.

Three fields are not handed over by the hypotheses: `sobolev` (Lemma A),
`pressure_gradient` (lane 083's `memLp_pressureGradient_of_difference_support` at
horizon `T`, plus the `.mono` restriction of `ref.pressure_smooth`), and
`horizon_pos` (the new `hT`, which is precisely why `hT` is a genuine extra
hypothesis — `ref.horizon_pos` only gives `0 < T + δ`). The docstring contradicts
itself two paragraphs later, where it correctly describes the `pressure_gradient`
route. **Fix:** change "The only field that genuinely needs work is `sobolev`" to
"`sobolev` is the only field needing a *new* lemma; `pressure_gradient` reuses
lane 083 at horizon `T` and `horizon_pos` is the new hypothesis `hT`."

### 3. Lemma B re-derives a whole shorter-horizon solution per `(m, S)` — *severity: nit, no action*

**Location:** `FullHorizon.lean:157-167`.

The `sobolev` field calls `classicalSolutionR_of_inserted` inside the
`∀ S, 0 < S → S < T` binder, i.e. once per `(m, S)` pair, rebuilding all ten
fields to read off one. Everything involved is `Prop`-valued, so this is pure
elaboration, not a soundness or cost issue, and hoisting the family would not
shorten the proof. Recorded only so a later reader does not mistake it for a bug.

### 4. Nothing binds `FullHorizon.lean`, so after merge it leaves the `lake test` closure — *severity: low (record/process, not this lane's bug)*

CI's `build_changed_lean.py --base-ref` step (`.github/workflows/contracts.yml:81`)
compiles changed modules outside the registered closure, so the module **is**
gated in this PR. But `make test` only builds the registered-contract closure, and
unlike lane 087's `SolutionOnShorter.lean` (pulled in by
`Bindings/InsertionLifespan.lean`), nothing in `verification/` imports
`FullHorizon.lean`. Once merged it is only rebuilt when a lane touches it. The fix
is the next lane's Bindings instantiation (finding-1 scratch §B1), not an edit
here.

---

## Detailed check results

### 1. Compiles — **pass**

| command (from `verification/`, `LEAN_NUM_THREADS=6`) | result |
|---|---|
| `lake build NSFormalization.Section4.R42.FullHorizon` | `Build completed successfully (9884 jobs).` (only a pre-existing `SchwartzMap.smul_apply` deprecation replayed from `Paper3/SobolevDirectionalDerivative.lean:103`, not from this module) |
| `lake env lean ../formalization/NSFormalization/Section4/R42/FullHorizon.lean` | **silent**, exit 0 |
| `lake env lean ../research/R42/axioms_full_horizon.lean` | 2 declarations, each `depends on axioms: [propext, Classical.choice, Quot.sound]` |
| `grep -nE 'sorry\|admit\|axiom\|native_decide\|maxHeartbeats' …/FullHorizon.lean` | no match (exit 1) |
| `make check` (worktree root) | exit 0 — plan, contracts, 13 policy tests, 30 work items all OK |
| `bash scripts/lean-install.sh` (runs `lake test`) | `== OK`, every registered `Tests.*` "checked; standard logical axioms only" |

### 2. Statement fidelity — **pass**

**(a) Lemma A.** `#check @exists_datumPath_of_forall_shorter` with `pp.fullNames`
against `#check @A02.ClassicalSolutionR.sobolev`:

```
hypothesis:  ∀ S, 0 < S → S < T →
  ∃ G, ContinuousOn G (Set.Ico 0 S) ∧
    ∀ t ∈ Set.Ico 0 S, A02.IsSobolevDatum ↑m (fun x => u (t, x)) (G t)
sobolev field: ∀ m, ∃ G, ContinuousOn G (Set.Ico 0 T) ∧
    ∀ t ∈ Set.Ico 0 T, A02.IsSobolevDatum ↑m (fun x => self.velocity (t, x)) (G t)
```

The hypothesis is the field at `T := S` with `self.velocity ↦ u`; the conclusion is
the field at `T` with the same substitution. Exact, no adapter, no `Ioo`/`Ico`
slippage. The datum predicate resolves to `A02.IsSobolevDatum` (via
`open NSFormalization.Section4.A02`), and
`example : @A02.IsSobolevDatum = @D01.IsSobolevDatum := rfl` compiles — so the use
of `D01.isSobolevDatum_unique` on A02-flavoured data is legitimate, as the
docstring claims.

**Well-defined at `t = 0`, and one-sided continuity genuinely proved.** With
`hT : 0 < T`, the `dite` guard `0 ≤ 0 ∧ 0 < T` holds, so `G 0 = Gs (T/2) _ _ 0`
and `0 ∈ Ico 0 (T/2)`, i.e. the value at the endpoint is a real datum, not the
`else 0` fallback. The continuity proof is uniform in `t₀ ∈ Ico 0 T` and never
splits off the interior: `ContinuousOn` is unfolded to `ContinuousWithinAt … (Ico 0 T) t₀`,
the transfer neighbourhood is `Ico 0 ((t₀+T)/2) ∈ 𝓝[Ico 0 T] t₀` proved through
`mem_nhdsWithin` with the open witness `Iio ((t₀+T)/2)` — at `t₀ = 0` this is
`Ico 0 (T/2) ∈ 𝓝[Ico 0 T] 0`, correct one-sided `nhdsWithin` usage — then
`ContinuousWithinAt.mono_of_mem_nhdsWithin` and
`ContinuousWithinAt.congr_of_eventuallyEq_of_mem`. The words `ContinuousAt` and
`interior` do not occur in the file (grep). Probe: the conclusion yields
`ContinuousWithinAt G (Ico 0 T) 0 ∧ IsSobolevDatum ↑m (fun x => u (0,x)) (G 0)`
directly — compiles (`/tmp/r42rev098/Probe.lean`, silent).

**(b) Lemma B.** Printed side by side with `classicalSolutionR_of_inserted`: the
two hypothesis lists are identical through `hpsupp`; lane 087 then has
`∀ {S : ℝ}, 0 < S → S < T → ∃ w : … S, …`, Lemma B has `0 < T → ∃ w : … T, …`.
Conclusion is exactly `∃ w : ClassicalSolutionR ν a gε T, w.velocity = u ∧ w.pressure = p`.

Bindings instantiation (`/tmp/r42rev098/Scratch.lean` §B1, compiles silently):
**22 proof-body lines**, against lane 092's 22. The diff against `sol_on_shorter`
is exactly: name, no `intro S hS0 hST`, and the trailing `hS0 hST` replaced by
`F.scaling.correction.time_pos`. `uniqueness_toA02 F.reference` / `ht₁` from
`ScalingAPI.eps_time` / the three `reference_velocity`/`reference_pressure`
rewrites / `maximalPartial_ofA02` on the way out all go through unchanged. **No
mismatch of any kind.**

**(c) Vacuity.** Lemma A's hypothesis is satisfiable: for `0 < T` the range
`S ∈ (0,T)` is nonempty, and lane 087's `classicalSolutionR_of_inserted` supplies
a witness at every such `S` — compiled as a standalone derivation of the exact
hypothesis shape from lane 087's hypothesis list (`/tmp/r42rev098/Probe.lean`,
second example). So a "vacuously true" reading is ruled out from below. It is also
ruled out from above: `isSobolevDatum_unique` pins `G t` for every
`t ∈ Ico 0 T`, so the conclusion's existential has at most one solution on the
interval and cannot be discharged by a junk path. (Separately: the detour through
shorter horizons is *forced*, not gold-plating — `exists_datumPath_of_localized`
(`R42/CorrectionPath.lean:64`) requires `hS : S < T` and has no `S = T` form, so
there is no way to build the horizon-`T` datum path directly.)

### 3. Consistency — **pass**

* **Imports:** the single line `import NSFormalization.Section4.R42.SolutionOnShorter`
  — the canonical closure carrier, as instructed. Nothing else.
* **No restated definitions:** the module declares no `def` / `abbrev` /
  `structure` / `instance`; it is two theorems and a docstring.
* **Uniqueness:** the glue uses `D01.isSobolevDatum_unique`
  (`Section4/D01/ForceClass.lean:286`) directly; no new uniqueness lemma, no local
  copy.
* **`dite` glue:** the `if … then … else 0` is decided by `classical`
  (`Classical.propDecidable`); `choose` is the only other classical step. The
  axiom audit shows exactly the three standard axioms, so nothing beyond
  `Classical.choice` is in play. The `dite_eq_left` collapse used twice matches
  the repo's existing usage (`A02/Maximal.lean:124,141`); the `hb0/hbT` proof
  arguments differ syntactically between `hGt` and the `dite` binder but are
  proof-irrelevant, which is why the `rw` closes.

### 4. The `IsMaximalSolution` table — **claim verified**

`Maximal.lean:85-89` reads, verbatim:

```
def IsMaximalSolution (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (u : SpaceTimeField) (p : SpaceTimeScalar) : Prop :=
  0 < maximalLifespanR ν a f ∧
    ∀ S : ℝ, 0 < S → ENNReal.ofReal S < maximalLifespanR ν a f →
      ∃ w : ClassicalSolutionR ν a f S, w.velocity = u ∧ w.pressure = p
```

Clause (ii) quantifies **only** over horizons strictly below the lifespan. With
`lifespan_eq : maximalLifespanR ν a (F.force ε) = ENNReal.ofReal F.T` and
`0 < F.T`, `ENNReal.ofReal_lt_ofReal_iff` turns the guard into `S < T` — the
endpoint `S = T` is never asked for. So **Lemma B is not on the A02 path**:
`isMaximalSolution_of_inserted` is `lifespan_eq` + `sol_on_shorter` + `time_pos`
and nothing else. Written at the Bindings level it is 5 proof lines and compiles
(finding 1 for the text; `/tmp/r42rev098/Scratch.lean` §B2). Side hypotheses of
`maximal_unique` (`Maximal.lean:192-197`) are `0 < ν`, `a ∈ initialClassR`,
`MemForceR f` — exactly the table's list, all available as `P.viscosity_pos`,
`initialClassR_a F`, `memForceR_force F hg hε`.

**What Lemma B is actually for.** It is the only thing in the repo that produces a
*single* `ClassicalSolutionR ν a gε T` object — one velocity, one pressure, one
datum path continuous on all of `[0,T)`, and `∇p_ε ∈ L²` at every `t < T`. The
`IsMaximalSolution` route hands consumers an `S`-indexed *family* of solutions
whose `sobolev` paths are a priori unrelated across `S`; a consumer that needs
`u_ε ∈ C([0,T); H^m)` as one statement (Theorem 4.2's `E_T` estimate
`eq:REclose`, `04-whole-space.tex:39-41`, and the R46/R47 energy/density arguments
that integrate over the whole singular interval) cannot assemble that from the
family without exactly Lemma A. `contracts.json:188` is explicit that the
registered `R42.insertion_lifespan` does **not** export them: "NOT asserted: the
`ClassicalSolutionR` fields `sobolev` and `pressure_gradient` for `u_eps` (built
inside `sol_on_shorter`, not exported)". Lemma B is the object that closes that
hole.

---

## Commands run

All from `/data_8T/ping/blowup_density/.claude/worktrees/098-R42-full-horizon`,
after `bash scripts/lean-install.sh` (idempotent, ended `== OK`),
`. scripts/lean-env.sh`, `export LEAN_NUM_THREADS=6`, one `lake` at a time.

```
cd verification && lake build NSFormalization.Section4.R42.FullHorizon
  → Build completed successfully (9884 jobs).
cd verification && lake env lean ../formalization/NSFormalization/Section4/R42/FullHorizon.lean
  → (silent), exit 0
cd verification && lake env lean ../research/R42/axioms_full_horizon.lean
  → exists_datumPath_of_forall_shorter          : [propext, Classical.choice, Quot.sound]
  → classicalSolutionR_of_inserted_fullHorizon  : [propext, Classical.choice, Quot.sound]
grep -nE 'sorry|admit|axiom|native_decide|maxHeartbeats' \
  formalization/NSFormalization/Section4/R42/FullHorizon.lean   → no match
make check                                                       → exit 0
cd verification && lake env lean /tmp/r42rev098/Print.lean
  → the two statements + the sobolev field, pp.fullNames; the
    A02/D01 `IsSobolevDatum` defeq `example … := rfl` compiles
cd verification && lake env lean /tmp/r42rev098/Scratch.lean
  → silent but for one deprecation in my own scratch
    (Set.mem_setOf_eq).  §B1 Lemma B from InsertionFamilyAPI, 22 proof lines;
    §B2 isMaximalSolution_of_inserted in Data/V2 vocabulary, 5 proof lines;
    §B2' the same in A02 vocabulary via maximalPartial_isMaximalSolution_iff;
    §B3 MAXIMAL_SPLIT.md's literal statement + its literal 5-line proof;
    §B4 presingularTimes ν a gε = Ico 0 T
cd verification && lake env lean /tmp/r42rev098/Probe.lean
  → (silent).  t = 0 endpoint yields ContinuousWithinAt G (Ico 0 T) 0 and the
    datum at 0; Lemma A's hypothesis derived from lane 087's hypothesis list
```

---

## What R42 still lacks for its consumers after this lane

Lemma B exists but is **not reachable from `verification/`**. Nothing in
`Bindings/` imports `FullHorizon.lean`, so (i) no contract exposes a horizon-`T`
`ClassicalSolutionR` for `u_ε`, and (ii) the module sits outside `make test`'s
registered closure once this PR merges — CI's changed-module step covers it today
and nothing covers it tomorrow. The missing piece is small and already
type-checked in this review: the 22-line `sol_fullHorizon` binding (scratch §B1)
plus, if a consumer wants the definite article, the 5-line
`isMaximalSolution_of_inserted` in Data/V2 vocabulary (§B2) — after which
`maximalPartialV2.maximal_unique` identifies `(u_ε, p_ε)` with A02's maximal
solution on `presingularTimes = Ico 0 T` (§B4), which is the "Proposition
\ref{prop:local} identifies the solution with the unique maximal solution" step of
`04-whole-space.tex:53`. Beyond that, R42's remaining debt is unchanged by this
lane: the registered `R42.insertion_lifespan` still asserts only the two lifespan
clauses, so the eventual `insertion_lifespan_eq` packaging named in
`contracts.json:155` — the one that would hand R46/R47 the solution object, its
`sobolev` path and its `pressure_gradient` together with `T^ν_{max,R} = T` — is
still owed, and Lemma C is still table-only.
