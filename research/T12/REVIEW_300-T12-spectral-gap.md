ACCEPT

## 1. What the lane claims

The worker report claims the exact `spectralGap` and
`homogeneous_le_sobolev` statements at
`research/T12/REPORT_300.md:8-17`, the explicit constant and positivity theorem
at `research/T12/REPORT_300.md:23-26`, and six reusable reweighting exports at
`research/T12/REPORT_300.md:29-33`.  Every claimed declaration exists:

- `gapConst` and `gapConst_pos` are at
  `formalization/NSFormalization/Section3/T12/SpectralGap.lean:23-30`.
- The two public weight comparisons are at
  `formalization/NSFormalization/Section3/T12/SpectralGap.lean:76-122`.
- `reweightDatum`, its application formula, norm bound, and reality-preservation
  theorem are at
  `formalization/NSFormalization/Section3/T12/SpectralGap.lean:127-189`.
- `homogeneous_le_sobolev` is exactly the reported statement at
  `formalization/NSFormalization/Section3/T12/SpectralGap.lean:293-296`.
- `spectralGap` is exactly the reported statement at
  `formalization/NSFormalization/Section3/T12/SpectralGap.lean:331-335`.

The statements are byte-for-byte the two canonical API field shapes after
substituting `Cgap := gapConst`: compare
`research/T12/probes/api_on_canonical.lean:206-222` with the conformance
examples at `research/T12/probes/spectral_gap_closes.lean:23-39`.  The latter
typechecks silently.

The mathematics matches the cited manuscript.  The paper says that homogeneous
and inhomogeneous norms are equivalent on mean-zero periodic fields at
`paper/sections/02-preliminaries.tex:50-54`.  Its precise nonzero-mode weight
comparison is at `paper/sections/appendix-b-embeddings.tex:85-90`.  With the
paper's norm convention at `paper/sections/01-introduction.tex:83-107`, taking
the square root of the displayed squared-weight inequality gives exactly

```text
(1 + (2π)⁻²)^(s/2) = (1 + 1/(4π²))^(s/2) = gapConst s.
```

The converse constant is exactly one because the homogeneous weight is bounded
by the inhomogeneous weight at nonnegative order; this is the reconciled ruling
in `research/T12/RECONCILIATION.md:5-6` and is implemented at
`formalization/NSFormalization/Section3/T12/SpectralGap.lean:76-86`.

## 2. What is in Lean

The proof has the requested content, not only the requested outer types.

- The canonical inhomogeneous datum includes periodicity, Haar integrability,
  and the weighted coefficient equation at
  `formalization/NSFormalization/Section3/T10/PeriodicData.lean:96-112`.
  The homogeneous datum includes the same integrability conjunct and physical
  zero mean at
  `formalization/NSFormalization/Section3/T10/PeriodicData.lean:162-174`.
  This is precisely lead amendment 1 at
  `research/T10/RECONCILIATION.md:28-61`.
- `MemPeriodicHomogeneous` contains periodicity, physical `L²`, physical zero
  mean, and a finite homogeneous norm at
  `formalization/NSFormalization/Section3/T12/MeanZeroCalculus.lean:57-62`.
  Thus the right side of `spectralGap` is not an empty-infimum `⊤` case.
- The first theorem transports every inhomogeneous datum by the ratio bounded
  by one and carries its integrability and the hypothesis's mean-zero fact into
  the homogeneous datum at
  `formalization/NSFormalization/Section3/T12/SpectralGap.lean:297-327`.
  If there is no inhomogeneous datum, `le_iInf` correctly leaves the right side
  as `⊤`; no `.toReal` conversion is used.
- The spectral-gap theorem extracts a real homogeneous witness from the finite
  norm hypothesis at
  `formalization/NSFormalization/Section3/T12/SpectralGap.lean:281-289`, builds
  the inverse reweighting at lines 337-342, and handles the zero coefficient
  via the physical mean at lines 343-366.  The cited tree lemma really is
  `periodicFourierCoeff_zero_eq_mean_component` at
  `formalization/NSFormalization/Section3/T10/DatumBasics.lean:100-114`.
- The infimum comparison and identification with the unique homogeneous datum
  are at `formalization/NSFormalization/Section3/T12/SpectralGap.lean:261-279`
  and `:367-374`.

No hypothesis makes either main theorem vacuous.  The main `hs` proof is used
in the multiplier bounds at
`formalization/NSFormalization/Section3/T12/SpectralGap.lean:303,339-340`; the
main `hv` supplies zero mean at line 307 and an actual datum at line 337.
`gapConst_pos` names its guard `_hs` because the explicit constant is in fact
positive for every real `s`; retaining the guard is the exact API requirement
at `research/T12/probes/api_on_canonical.lean:112-117`, not an extra premise.
There are no interval hypotheses or `.toReal` uses.  The full guard is
satisfiable at every order by the zero field, proved at
`research/T12/probes/spectral_gap_closes.lean:41-65` and checked by Lean.

The substantive reviewer mutation is
`research/T12/probes/rev300_smaller_gap_constant.lean:19-27`: it changes
`4π²` to `8π²`, hence strictly shrinks the positive-order factor and is false
on a first nonzero Fourier mode.  Reusing the lane proof fails at the changed
conclusion with the expected type mismatch; the exact error appears in part 4.

Hygiene is clean.  The ten public declarations listed at
`research/T12/axioms_spectral_gap.lean:12-21` each print exactly
`[propext, Classical.choice, Quot.sound]`.  The changed Lean files contain no
`sorry`, `admit`, `axiom` declaration, or `native_decide`, and there is no
`maxHeartbeats` override.  The base diff contains only five additions and no
modified tracked file; in particular no existing module was modified.

## 3. Gaps

There is no proof or statement gap.  I found no exact-line fix to request.

The worker explicitly declares no residual hypothesis or proof gap at
`research/T12/REPORT_300.md:51-56` and
`research/T12/ATTEMPTS_SPECTRAL_GAP.md:71-75`.  Neither file claims that any
lemma is absent or “not in the tree.”  Therefore the requested whole-Section4
`grep -rn` validation has no missing-lemma claim to query; the applicability
check and its exact output are recorded below.

The branch is behind the integration tip, but every lane path is still absent
from the current `origin/erenup/integration-section3`, so this creates no
same-path overwrite.  This is informational and does not change the verdict.

`verification/` is not touched.  Consequently the brief's conditional
`scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration-section3` gates are
not applicable.  The unconditional `make check` nevertheless ran the ordinary
architecture contract check successfully.

## 4. Commands and results

All Lean commands were run from `verification/` after sourcing
`scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`.

### Module build

Command:

```sh
cd verification && . ../scripts/lean-env.sh && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T12.SpectralGap
```

Exit 0. Exact output:

```text
⚠ [8778/9174] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [h]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:39:23: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [insert, coord]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [9322/9360] Replayed NSFormalization.Source.RealSobolev
warning: NSFormalization/Source/RealSobolev.lean:90:30: This simp argument is unused:
  Complex.smul_re

Hint: Omit it from the simp argument list.
  [apply] simp [Complex.smul_im]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/RealSobolev.lean:90:47: This simp argument is unused:
  Complex.smul_im

Hint: Omit it from the simp argument list.
  [apply] simp [Complex.smul_re]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/RealSobolev.lean:90:64: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9326/9360] Replayed NSFormalization.Paper3.SpatiallyCompactTime
warning: NSFormalization/Paper3/SpatiallyCompactTime.lean:88:19: `ContinuousLinearMap.sub_apply` has been deprecated: Use `sub_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sub_apply` to `sub_apply x`).
⚠ [9333/9360] Replayed NSFormalization.Paper3.RealPositiveDensity
warning: NSFormalization/Paper3/RealPositiveDensity.lean:67:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:76:63: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:88:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:100:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9336/9360] Replayed NSFormalization.Paper3.RealVectorPositiveDensity
warning: NSFormalization/Paper3/RealVectorPositiveDensity.lean:29:5: Variable name `hc` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hc

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9346/9360] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [9349/9360] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  [apply] simp [viscosityVelocity, dilateField, viscosityHomeomorph, Prod.map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Build completed successfully (9360 jobs).
```

All warnings are replayed from pre-existing dependencies; there is no output
from the lane module itself.

### Direct elaboration and conformance probe

Commands:

```sh
cd verification && . ../scripts/lean-env.sh && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T12/SpectralGap.lean
cd verification && . ../scripts/lean-env.sh && LEAN_NUM_THREADS=6 lake env lean ../research/T12/probes/spectral_gap_closes.lean
```

Both exited 0. Exact output for each was empty.

### Axiom audit

Command:

```sh
cd verification && . ../scripts/lean-env.sh && LEAN_NUM_THREADS=6 lake env lean ../research/T12/axioms_spectral_gap.lean
```

Exit 0. Exact output:

```text
'NSFormalization.Section3.T12.gapConst' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.gapConst_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.homogeneousDatumWeight_le_periodicFrequencyWeight_rpow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T12.periodicFrequencyWeight_rpow_le_gap_mul_homogeneous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T12.reweightDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.reweightDatum_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.reweightDatum_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.reweightDatum_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.homogeneous_le_sobolev' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.spectralGap' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `make check`

Command:

```sh
. scripts/lean-env.sh && LEAN_NUM_THREADS=6 make check
```

Exit 0. The raw output is 43,331 lines / 1,785,268 bytes, SHA-256
`22eb774326e70d3cb24e9b168342ac8ecc9542a06a81b1cec09b43e7d848f992`.
Following the repository review-log rule, here are the exact first and last 25
lines rather than pasting the 1.8 MB contract closure:

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 558,
    "vendor/NavierStokesAndEuler": 2486,
    "vendor/HeliCorgi": 129
  },
  "source_manifest_entries": 2975,
  "missing_copied_imports": [],
  "citation_interfaces_reachable": [],
  "tokens_in_copied_umbrella_closure": [
    {
      "module": "NSFormalization.Paper1.BoundaryCorollary",
      "path": "formalization/NSFormalization/Paper1/BoundaryCorollary.lean",
      "line": 90,
      "token": "sorry"
    }
  ],
  "tracked_cache_free": true,
  "source_hashes_match": false
}
Explicit axiom/admission tokens, all copied sources: 11
python3 experiments/check_contracts.py
{
```

```text
      "NavierStokes.VolterraRegularity",
      "NavierStokes.WaveEdgeExtension",
      "NavierStokes.WaveEnvelopeTransport",
      "NavierStokes.WaveInteractionBounds",
      "NavierStokes.WaveStateRegularity",
      "NavierStokes.WeightedClasses",
      "NavierStokes.WeightedODEJets",
      "NavierStokes.WeightedQuotients",
      "NavierStokes.WeightedRadialPrimitive",
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.TorusData"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.048s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The existing copied-source token and `source_hashes_match: false` are
informational output from the repository-wide checker; the command exits 0.

### Negative mutation

Command:

```sh
cd verification && . ../scripts/lean-env.sh && LEAN_NUM_THREADS=6 lake env lean ../research/T12/probes/rev300_smaller_gap_constant.lean
```

Expected exit 1. Exact output:

```text
../research/T12/probes/rev300_smaller_gap_constant.lean:27:2: error: Type mismatch
  spectralGap
has type
  ∀ (s : ℝ),
    0 ≤ s →
      ∀ (v : SpatialField),
        MemPeriodicHomogeneous s v →
          periodicSobolevENorm s v ≤ ENNReal.ofReal (gapConst s) * periodicHomogeneousENorm s v
but is expected to have type
  ∀ (s : ℝ),
    0 ≤ s →
      ∀ (v : SpatialField),
        MemPeriodicHomogeneous s v →
          periodicSobolevENorm s v ≤ ENNReal.ofReal (rev300SmallerGapConst s) * periodicHomogeneousENorm s v
```

### Hygiene and conditional-gate applicability

Commands and exact outputs:

```text
$ rg forbidden declaration/tactic patterns over the lane and reviewer Lean files
NO_FORBIDDEN_DECLARATIONS_OR_TACTICS

$ rg maxHeartbeats over the lane and reviewer Lean files
NO_MAX_HEARTBEATS_OVERRIDES

$ git diff --name-status origin/erenup/integration-section3...HEAD
A formalization/NSFormalization/Section3/T12/SpectralGap.lean
A research/T12/ATTEMPTS_SPECTRAL_GAP.md
A research/T12/REPORT_300.md
A research/T12/axioms_spectral_gap.lean
A research/T12/probes/spectral_gap_closes.lean

$ git diff --diff-filter=M --name-only origin/erenup/integration-section3...HEAD
NO_EXISTING_TRACKED_FILE_MODIFIED

$ git diff --name-only origin/erenup/integration-section3...HEAD | rg '^verification/'
VERIFICATION_NOT_TOUCHED

$ git diff --check origin/erenup/integration-section3...HEAD
(no output; exit 0)

$ grep -rnE 'not in (the )?tree|missing lemma|absent from (the )?tree' research/T12/REPORT_300.md research/T12/ATTEMPTS_SPECTRAL_GAP.md
(no matches)
NO_NOT_IN_TREE_CLAIM_TO_VALIDATE
```

Because `verification/` is absent from the diff, `scripts/gates.sh` and the
base-ref contract check were not run, exactly as required by their conditional
gate.
