# Review — lane 036, B02 units 3 & 4

Reviewer: opus reviewer (lane-review), 2026-09-13.
Commit under review: `fe0a426` "[036-B02] Units 3 and 4: low-frequency weight
integrability and exact integral, angular Fourier sup bound".
Worktree: `.claude/worktrees/036-B02-units-3-4` (read/build only).

Scope: `research/B02/COMPARISON.md` units **3** (`low_frequency_weight`) and **4**
(`angular_fourier_sup_bound`), i.e. the three `HomogeneousApproxAPI` fields
`lowFrequencyIntegrable` (`Spec.lean:370`), `lowFrequencyIntegral`
(`Spec.lean:379`), `fourierSupBound` (`Spec.lean:397`).

Diff is 3 files, all additions, nothing else touched:

```
$ git show --stat fe0a426
 formalization/NSFormalization/Section4/B02/LowFrequency.lean | 196 ++++++++++
 research/B02/ATTEMPTS.md                                     | 114 ++++++
 research/B02/axioms_u34.lean                                 |  37 ++++
 3 files changed, 347 insertions(+)
```

---

## Verdict: **ACCEPT-WITH-NOTES**

The three theorems are the spec fields verbatim, proved `sorry`-free on the
standard axioms, with the paper's constants correct. **No change is required in
this lane.** The three notes below are forward-looking items for B02 unit 9
(registration) and for the ATTEMPTS log; none of them blocks the merge.

---

## 1. Build and hygiene — all pass

Setup (each command re-sources the env; `LEAN_NUM_THREADS=6`, no `-j`; every
`lake` invoked from `verification/`, one at a time):

```
$ cd <WT> && bash scripts/lean-install.sh
… == OK
$ . <WT>/scripts/lean-env.sh ; export LEAN_NUM_THREADS=6
$ cd <WT>/verification && lake --version
Lake version 5.0.0-src+6a10ac8 (Lean version 4.34.0-rc2)
```

| Check | Command | Result |
|---|---|---|
| Module builds | `lake build NSFormalization.Section4.B02.LowFrequency` | `Build completed successfully (8777 jobs).` exit 0 |
| No warnings at all from the new file | `lake env lean ../formalization/NSFormalization/Section4/B02/LowFrequency.lean` | **zero messages**, exit 0 (fresh elaboration, not a replay: no `sorry`, no linter/unused-variable output) |
| Conformance + axioms | `lake env lean ../research/B02/axioms_u34.lean` | exit 0; three lines below |
| Forbidden tokens | `grep -nE 'sorry\|admit\|native_decide\|\baxiom\b\|maxHeartbeats\|set_option\|decide' formalization/.../LowFrequency.lean` | no matches |
| Forbidden tokens (conformance file) | same grep on `research/B02/axioms_u34.lean` | one hit, line 12, inside the module docstring ("the transitive axiom set is exactly …") |
| Repo gate | `make check` | **exit 0** (`check_formalization_plan`, `check_contracts`, `test_contract_policy` 13 tests OK, `check_work_queue` "30 work items: ownership, contract registration and task cards consistent.") |

Axiom output, exactly the three standard logical axioms for all three:

```
'NSFormalization.Section4.B02.lowFrequencyIntegrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.B02.lowFrequencyIntegral'   depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.B02.fourierSupBound'        depends on axioms: [propext, Classical.choice, Quot.sound]
```

Elaboration cost: `time lake env lean …/LowFrequency.lean` → **3.6 s wall**, under
default heartbeats, no `set_option` anywhere.

## 2. Spec conformance — exact

Whitespace-normalised textual diff of each `HomogeneousApproxAPI` field type
against the corresponding `example` in `research/B02/axioms_u34.lean`:

```
lowFrequencyIntegrable  MATCH: True
lowFrequencyIntegral    MATCH: True
fourierSupBound         MATCH: True
```

All three are string-identical, not merely defeq. Each `example` is discharged
with a bare `:=` by the theorem, with **no extra hypotheses** and no argument
massaging:

* `lowFrequencyIntegrable (s : ℝ) (hs : -3 / 2 < s)` ↔ `∀ s : ℝ, -3 / 2 < s → …`
* `lowFrequencyIntegral` — no hypotheses on either side
* `fourierSupBound (k : Space → Space) (hk : MemLp k 1 volume) (ξ : Space)` ↔
  `∀ k : SpatialField, MemLp k 1 volume → ∀ ξ : Space, …`

The `SpatialField` / `Space → Space` gap is the declared one and is sound:
`verification/Contracts/V1/Data.lean:99` is `abbrev SpatialField := Space → Space`
(a reducible abbrev, hence the bare `:=` works), and the module docstring
(`LowFrequency.lean:40-43`) states this explicitly with the correct line
citation. `angularFourier` is not redefined in `Contracts.V1.Data` — that file
only does `open NSFormalization.Source (angularFourier)` (`Data.lean:89`), so the
constant in the spec and the constant in the theorem are literally the same one.

## 3. Constants against the paper — correct

**The `(2π)^{-3/2}` amplitude.** `paper/sections/01-introduction.tex:91` is
exactly `\widehat z(\xi)=(2\pi)^{-3/2}\int_{\R^3}e^{-ix\cdot\xi}z(x)\dd x`.
`NSFormalization.Source.angularFourier` (`Source/FourierConvention.lean:23`) is
`frequencyUnit ^ (-3/2 : ℝ) • 𝓕 f (frequencyUnit⁻¹ • ξ)` with
`frequencyUnit := 2 * Real.pi` (`:15`), and `angularFourier_eq_integral` (`:27`)
proves it equals `(2π)^{-3/2} • ∫ e^{-i⟪x,ξ⟫} • f x` — the manuscript's display
character for character. So `(2 * Real.pi) ^ (-(3:ℝ)/2)` is the right constant,
and the proof's `hfreq` (`LowFrequency.lean:191`) is the honest bridge, not a
reinterpretation. Both citations `FourierConvention.lean:23,27` are accurate.

**The vector form.** `01-introduction.tex:103` is "For vectors and tensors we sum
the squared component norms", so the manuscript's `|\widehat k(\xi)|` for a
vector field *is* `(Σ_i|ẑ_i(ξ)|²)^{1/2}`. The statement therefore matches the
paper, and the proof earns it honestly: it applies
`norm_integral_le_integral_norm` to an `EuclideanSpace ℂ (Fin 3)`-valued
integrand (`LowFrequency.lean:136-190`) rather than bounding componentwise, so
the constant is the manuscript's `C` with **no factor 3**. Squaring gives
`C = (2π)^{-3}`, which is what `Spec.lean:231` `lowHighConstant` uses.

**The `4π`.** `04-whole-space.tex:246` is
`\le C\norm{k}_1^2\int_{|\xi|<1}|\xi|^{-2}\dd\xi+\norm{k}_2^2`, so the factor to
evaluate is indeed `∫_{|ξ|<1}‖ξ‖^{-2}dξ` over ℝ³, and `:249` is "The integral at
the origin is finite in dimension three" — both citations exact. In polar
coordinates `∫₀¹ r^{-2}·4πr² dr = 4π·∫₀¹ dr = 4π`. The Lean proof realises
precisely that: `integral_fun_norm_addHaar` (verified present at
`Mathlib/MeasureTheory/Constructions/HaarToSphere.lean:296`, as cited) gives

```
∫ x, f ‖x‖ = finrank ℝ E • μ.real (ball 0 1) • ∫ y in Ioi 0, y ^ (finrank ℝ E - 1) • f y
```

and the proof supplies `finrank = 3`, `volume.real (ball 0 1) = π*4/3` (from
`EuclideanSpace.volume_ball_fin_three`, checked: `ofReal r ^ 3 * ofReal (π*4/3)`),
and inner integral `∫_{Ioo 0 1} y²·y^{-2} = ∫_{Ioo 0 1} 1 = 1`, so
`3 • (π*4/3) • 1 = 4π`. Arithmetic consistency with the spec docstring also
holds: `C' = (2π)^{-3}·4π = 4π/(8π³) = 1/(2π²)`, as `Spec.lean:229-232` claims.

## 4. Honesty spot-checks on `research/B02/ATTEMPTS.md`

Three of the six snags reproduced directly against this toolchain, plus the
source citation:

1. **Snag 1 (`positivity` on `frequencyUnit`) — CONFIRMED.**
   `example : (0:ℝ) ≤ frequencyUnit ^ (-3/2 : ℝ) := by positivity` →
   `error: failed to prove positivity/nonnegativity/nonzeroness`. The stated fix
   `Real.rpow_nonneg frequencyUnit_pos.le _` compiles, and the log's parenthetical
   is also right: `by positivity` *does* close `0 ≤ (2 * Real.pi) ^ (-(3:ℝ)/2)`.
2. **Snag 2 (no `aestronglyMeasurable_pi_iff`) — CONFIRMED.**
   `#check @aestronglyMeasurable_pi_iff` → `Unknown identifier`.
3. **Snag 5 (`Set.indicator_of_not_mem` renamed) — CONFIRMED.**
   `#check @Set.indicator_of_notMem` resolves; the old spelling does not.
4. **Citation `Paper3/SobolevWeights.lean:54` — CONFIRMED.** Line 54 is
   `theorem homogeneous_low_frequency_integrable {s C : ℝ} (hs : -3 / 2 < s)
   {φ : Space → ℂ} (hφ : Measurable φ) (hC : 0 ≤ C) (hbound : ∀ ξ, ‖φ ξ‖ ≤ C) :
   IntegrableOn (fun ξ => ‖ξ‖ ^ (2 * s) * ‖φ ξ‖ ^ 2) (Metric.ball 0 1)`, which is
   exactly what `LowFrequency.lean:59-61` instantiates at `φ ≡ (1:ℂ)`, `C = 1`.
   The COMPARISON row 3 plan ("`SW:54` at `φ ≡ 1`, `C = 1`") was followed as
   written.

Snag 3 (the heartbeat restructure) is recorded as **partially verified** — see
note 3 below.

---

## Findings

### 1. NOTE (informational, no action this lane) — the module is outside the default build graph

`grep -rn 'Section4.B02' --include='*.lean'` over `formalization/`,
`verification/` and `research/` shows the only importer of
`NSFormalization.Section4.B02.LowFrequency` is `research/B02/axioms_u34.lean`.
Every *other* `Section4/*` module is pulled into the build by a
`verification/Bindings/*.lean` file; B02's is not, and
`formalization/lakefile.toml`'s `[[lean_lib]] name = "NSFormalization"` declares
no globs, so `lake build`'s default target does not reach it either.

This is **not** a defect here: CI compiles it anyway on this PR via
`experiments/build_changed_lean.py`, whose own docstring is "Compile changed Lean
modules even if no acceptance test imports them yet", and whose dry run confirms

```
$ python3 experiments/build_changed_lean.py --base-ref origin/erenup/integration --dry-run
Changed Lean modules: NSFormalization.Section4.B02.LowFrequency
```

Permanent wiring is COMPARISON unit 9's job ("promote to
`verification/Contracts/V1/HomogeneousApprox.lean` with a typed `Bindings` entry").
**Fix (for unit 9, not now):** once unit 9 lands, make sure the Bindings entry
imports this module, otherwise later PRs that do not touch the file will never
recompile it.

### 2. NOTE (informational, no action this lane) — `axioms_u34.lean` is a manual gate, not a CI gate

`experiments/build_changed_lean.py::targets` only maps paths under
`verification/`, `formalization/` and `vendor/NavierStokesAndEuler/`; anything
under `research/` is skipped. So `research/B02/axioms_u34.lean` — the file that
carries the spec-conformance `example`s and the `#print axioms` calls — is never
run by CI. It is also the only `research/*/axioms*.lean` in the tree, i.e. a new
interim device rather than an established pattern. I ran it by hand (section 1
above) and it passes.
**Fix (for unit 9, not now):** replace it with the project's standard gate —
`Bindings` + `contracts.json` + a `Tests/*.lean` with the `#print axioms` check,
which is what produces the `Contract …: checked; standard logical axioms only`
lines in `make test`.

### 3. NIT (honesty) — ATTEMPTS.md snag 3's failure claim is not reproducible from the log as written

Snag 3 claims an "`isDefEq` timeout (≥1M heartbeats) when composing through
`EuclideanSpace.equiv.symm`" with a `Prod.mk`ed argument. The *outcome* claim is
fully verified: the delivered proof carries no `set_option maxHeartbeats`, and the
file elaborates in 3.6 s. But my closest reconstruction of the described failing
shape — `F x = equiv.symm (fun i => e • ↑(k x i))` with a.e.-strong-measurability
via `Continuous.comp_aestronglyMeasurable` on an `AEStronglyMeasurable.prodMk`
pair — compiled in 4.2 s at `maxHeartbeats 1000000` rather than timing out.
That is a *neutral* result, not a contradiction: I annotated the `ℂ × (Fin 3 → ℂ)`
continuous map explicitly, which is close to what the log says the fix was. No
action; recording it so the log entry is not later read as a reproducible recipe.

### 4. OBSERVATION (about `Spec.lean`, untouched by this lane)

`lowFrequencyIntegrable`'s docstring says the weight is integrable on the unit
ball "exactly when `2s > -3`", but the field states only the sufficient
direction (`-3/2 < s → IntegrableOn …`). The lane proved the field as written,
which is the correct thing to do; flagging only so that nobody later reads the
field as an iff. No change wanted in `Spec.lean` from this lane.

---

## Summary of commands run

```
cd <WT> && bash scripts/lean-install.sh                                  # == OK
. <WT>/scripts/lean-env.sh ; export LEAN_NUM_THREADS=6
cd <WT>/verification
lake build NSFormalization.Section4.B02.LowFrequency                     # exit 0, 8777 jobs
lake env lean ../formalization/NSFormalization/Section4/B02/LowFrequency.lean
                                                                         # exit 0, zero messages, 3.6 s
lake env lean ../research/B02/axioms_u34.lean                            # exit 0, 3x standard axioms
cd <WT> && make check                                                    # exit 0
python3 experiments/build_changed_lean.py --base-ref origin/erenup/integration --dry-run
                                                                         # NSFormalization.Section4.B02.LowFrequency
```

Snag reproductions were run as scratch files in `/tmp` via
`lake env lean /tmp/<file>.lean` from `<WT>/verification`; nothing was written
inside the worktree except this review file.
