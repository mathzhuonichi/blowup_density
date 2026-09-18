REJECT

## What the lane claims

The worker report says the r1 revision proves the full U1 arbitrary-
spacetime existential bridge and its all-
`z` `ℝ≥0∞`/`⨆` corollary (`research/T17/REPORT_369.md:9-19`), exporting four
theorems including the old ball form and two new `_shift` declarations
(`research/T17/REPORT_369.md:21-28`). The brief/status target, however, names
the arbitrary-`z` theorem `latticeLift_iteratedFDeriv_eq` and asks for that
existential statement plus a `k = 0` specialization
(`research/T17/T17_SPLIT.md:64-70`). The report's opening summary is also stale
and contradicts its r1 section: it says the general existential is absent
(`research/T17/REPORT_369.md:3-7`) while later claiming it is present
(`research/T17/REPORT_369.md:11-25`).

## What is in Lean

The proof content is mathematically on target. The declaration named
`latticeLift_iteratedFDeriv_eq` is only the `k = 0` ball theorem: it requires
`x ∈ ball x₀ r` and returns an unshifted right-hand side
(`formalization/NSFormalization/Section3/T17/LatticeDeriv.lean:9-15`). This
matches T16's `latticeLift_eq_of_ball` hypotheses and conclusion
(`formalization/NSFormalization/Section3/T16/LatticeLift.lean:139-166`), and
the neighborhood/derivative route is valid (`formalization/NSFormalization/Section3/T17/LatticeDeriv.lean:16-24`; `vendor/NavierStokesAndEuler/NavierStokes/PeriodicLocalization.lean:250-258`).

The requested arbitrary-`z`, shifted equality does exist, but under the
different name `latticeLift_iteratedFDeriv_eq_shift`
(`formalization/NSFormalization/Section3/T17/LatticeDeriv.lean:52-59`). Its
copy-present branch uses T16 periodicity and local ball equality
(`formalization/NSFormalization/Section3/T17/LatticeDeriv.lean:60-84`), and its
no-copy branch uses the honest strict separation `ρ < r` to obtain a zero
neighborhood (`formalization/NSFormalization/Section3/T17/LatticeDeriv.lean:85-138`).
The all-`z` ENNReal supremum corollary is likewise present under
`latticeLift_iteratedFDeriv_norm_le_iSup'`
(`formalization/NSFormalization/Section3/T17/LatticeDeriv.lean:139-155`). The
paper's derivative target is the global-in-time/space estimate at
`paper/sections/03-torus.tex:225-230`; the local derivative transport itself
is sound, and the Lean `CorrectionAPI` field has the directional norm shape
shown at `research/T17/Spec.lean:878-884`.

The concrete probe is non-vacuous: it constructs the bump and checks an
off-cube lattice copy, the general corollary, and the fundamental-ball form
(`research/T17/probes/lattice_deriv_closes.lean:10-82`). The required negative
mutations are substantive: widening `r + ρ ≤ 1` fails in
`research/T17/probes/rev369_negative_widened_ball.lean:13`, and weakening
`ρ < r` fails in `research/T17/probes/rev369r1_negative_lt.lean:21`.

## Gaps

1. **Blocking public-statement/API mismatch.** Applying the exact name
   required by the brief to the requested arbitrary-`z` type does not typecheck.
   The scratch probe `research/T17/probes/rev369_api_name.lean:20` produces:

   ```text
   ../research/T17/probes/rev369_api_name.lean:20:53: error: Application type mismatch: The argument
     z
   has type
     SpaceTime
   but is expected to have type
     ℕ
   in the application
     latticeLift_iteratedFDeriv_eq hslice hρr ?m.65 z
   ../research/T17/probes/rev369_api_name.lean:20:49: error: Application type mismatch: The argument
     hlt
   has type
     ρ < r
   but is expected to have type
     ?m.64 ∈ ball x₀ r
   in the application
     latticeLift_iteratedFDeriv_eq hslice hρr hlt
   ```

   Rename the current ball theorem to a `..._of_ball`/`..._k0` name and export
   the existential theorem under the required `latticeLift_iteratedFDeriv_eq`
   name, updating the dependent probes and axiom audit. The current `_eq_shift`
   declaration is a correct proof but does not satisfy the specified public
   theorem contract.

2. **Record honesty.** Remove or rewrite the stale opening summary of
   `REPORT_369.md:3-7` so it no longer says the general theorem is absent. The
   status line `research/T17/T17_SPLIT.md:245` also says U5/U6 “now transport”
   the bounds, but no U5/U6 Lean modules are present in this lane; qualify that
   as a downstream plan or remove it.

The whole Section4 tree contains no declaration with either the requested or
delivered lattice-derivative bridge name (`rg` exit 1), so there is no existing
Section4 lemma that resolves the API gap.

## Commands and results

All Lean commands used `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, and ran
`lake` from `verification/`. The module build succeeded; its own file was
silent, with only replayed pre-existing warnings from unrelated modules and the
exact final line:

```text
Build completed successfully (9359 jobs).
```

The direct typechecks were all exit 0 and produced no output:

```text
lake env lean ../formalization/NSFormalization/Section3/T17/LatticeDeriv.lean
lake env lean ../research/T17/probes/lattice_deriv_closes.lean
lake env lean ../research/T17/axioms_u1.lean
lake env lean ../research/T17/probes/rev369_nonvacuity.lean
```

The axioms file printed exactly (all four declarations):

```text
'NSFormalization.Section3.T17.latticeLift_iteratedFDeriv_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.latticeLift_iteratedFDeriv_norm_le_iSup' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.latticeLift_iteratedFDeriv_eq_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.latticeLift_iteratedFDeriv_norm_le_iSup'' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The negative probes exited 1 with the expected type errors. The widened-ball
probe reports `hr : r + ρ ≤ 2` where `r + ρ ≤ 1` is expected; the strictness
probe reports `hle : ρ ≤ r` where `ρ < r` is expected. The non-vacuity probe
exited 0.

`make check` from the repository root exited 0. Its exact relevant tail was:

```text
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.046s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The same run reported the repository baseline diagnostics
`"source_hashes_match": false`, `Explicit axiom/admission tokens, all copied
sources: 11`, and `"base_compatibility_checked": false`; these are unrelated
pre-existing architecture checks, not tokens in this lane's module/probes.
`git diff --check` exited 0; the diff has no modified existing `.lean` module,
and the code/probe scan found no `sorry`, `admit`, `axiom`, `native_decide`, or
`maxHeartbeats`. `scripts/gates.sh` and the base-ref contract gate were not
applicable because `verification/` is untouched by this lane.

Verdict: REJECT

---

## Fix note (lane 369 r2, 2026-09-18) — API name + record honesty

Per the lead ruling (the general existential theorem is the U1 target and must be
exported under the brief's name), the earlier "keep names" choice is reverted:

1. **API name mismatch (blocking) fixed.** The public names are now:
   - `latticeLift_iteratedFDeriv_eq` — the general **arbitrary-`z`** `∃ k`
     shifted-copy equality `‖iteratedFDeriv ℝ n (latticeLift w) z u‖ =
     ‖iteratedFDeriv ℝ n w (z - (0, latticeVector k)) u‖`, with the no-copy/zero
     case (`k = 0`, both sides `0`).
   - `latticeLift_iteratedFDeriv_norm_le_iSup` — its all-`z` `ℝ≥0∞`/`⨆` corollary.
   - `latticeLift_iteratedFDeriv_eq_ballZero` /
     `latticeLift_iteratedFDeriv_norm_le_iSup_ballZero` — the `k = 0`
     fundamental-ball specializations (the former bare names).
   The reviewer probe `research/T17/probes/rev369_api_name.lean` — which applies the
   exact name `latticeLift_iteratedFDeriv_eq` to the general existential type — now
   compiles (exit 0), i.e. the previously reported type mismatch is gone.

2. **Record honesty fixed.** The stale opening summary of `REPORT_369.md` (which
   said the general theorem was absent) is removed; `## completion (lane 369 r1)`
   plus a `## r2` note are the authoritative summary.  `T17_SPLIT.md` U1 status no
   longer claims U5/U6 transport the bounds "now" — it states U5/U6 are **separate
   lanes, not started here**, and that they will consume
   `latticeLift_iteratedFDeriv_eq`.

Probe reference adjustments (so every probe compiles / behaves as designed):
`lattice_deriv_closes.lean`, `rev369_nonvacuity.lean`,
`rev369_negative_widened_ball.lean` now reference the `_ballZero` names;
`rev369r1_negative_lt.lean` and `rev369_api_name.lean` reference the bare
`latticeLift_iteratedFDeriv_eq`.  No reviewer probe is superseded — all are kept
and compile (positives exit 0; the two negatives still exit 1 with the intended
type mismatches on `_ballZero` / the general theorem).

Gates re-run (from `verification/`, `LEAN_NUM_THREADS=6`, after `. scripts/lean-env.sh`):
`lake build NSFormalization.Section3.T17.LatticeDeriv` exit 0; `lake env lean` on the
module, `lattice_deriv_closes.lean`, `rev369_nonvacuity.lean`, `rev369_api_name.lean`,
`axioms_u1.lean` all exit 0; `rev369_negative_widened_ball.lean` and
`rev369r1_negative_lt.lean` exit 1 (intended); `make check` exit 0.  `axioms_u1.lean`
prints all four declarations depending only on `[propext, Classical.choice, Quot.sound]`.
