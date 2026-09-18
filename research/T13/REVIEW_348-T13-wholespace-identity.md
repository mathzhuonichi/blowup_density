ACCEPT-WITH-NOTES

## What the lane claims

The worker report claims that lane 348 proves the `LocalizationAPI.wholeSpace_identity`
field verbatim (`research/T13/REPORT_348.md:8-27`), namely

```lean
∀ (s : ℝ), 0 < s → s < 1 → ∀ f : SpatialField,
  ContDiff ℝ ∞ f → HasCompactSupport f →
    IReal s f < ⊤ ∧ IReal s f = cFrac s * dotHomogeneousENorm s f ^ (2 : ℕ)
```

This is exactly the canonical field (`research/T13/probes/api_on_canonical.lean:47-51`)
and matches the cited paper calculation: positivity/finiteness of `c_s` and the
whole-space Plancherel/Tonelli identity are at `paper/sections/03-torus.tex:35-51`.
The definitions used by the field are the concrete `fractionalRadialKernel`, `cFrac`,
and `IReal` at `formalization/NSFormalization/Section3/T13/Localization.lean:47-57,70-74`;
the registered infimum norm is token-for-token at
`formalization/NSFormalization/Section4/D01/HomogeneousNorm.lean:21-28`.

## What is in Lean

The shipped theorem has the exact target and no additional hypotheses at
`formalization/NSFormalization/Section3/T13/WholeSpaceIdentity.lean:509-525`.
The proof genuinely bridges the datum infimum using the compact witness theorem
(`WholeSpaceIdentity.lean:42-50`, consuming
`Section4/D01/HomogeneousWitness.lean:517-528`, whose uniqueness/norm lemmas are at
`:416-444`), proves finiteness at `:53-58`, and expands the square at `:62-72`.
The angular Plancherel statement is explicit at `:93-107`, the translation phase and
subtraction at `:111-154`, and the componentwise Schwartz/Plancherel step at
`:158-210`.  The rotation+dilation kernel identity has the claimed constant and
`ξ ≠ 0` guard at `:239-317`; the null-set fact used in the Tonelli assembly is the
tree lemma `Section4/D01/HomogeneousWitness.lean:169-176`.  The final component/Tonelli
assembly is at `:359-441`, `:443-488`, and `:490-504`.

The closure probe is exact (`research/T13/probes/wholespace_identity_closes.lean:38-43`)
and includes an explicit nonzero smooth compactly supported `ContDiffBump` field at
`:47-79`, so the theorem is not being accepted only through an empty or zero-only
instance.

## Gaps

There is no mathematical or statement-fidelity gap.  The assumptions are exactly the
API assumptions, and the `0 < s < 1` hypotheses are used only to derive the D01 order
guard and the finite `cFrac` factor (`WholeSpaceIdentity.lean:514-524`).  The substantive
mutation probe changes the final constant to `2 * cFrac s`; Lean rejects the attempted
proof at `research/T13/probes/rev348_mutation.lean:20` with:

```text
error: Type mismatch
  wholeSpace_identity s hs0 hs1 f hzs hzc
has type
  IReal s f < ∞ ∧ IReal s f = cFrac s * dotHomogeneousENorm s f ^ 2
but is expected to have type
  IReal s f < ∞ ∧ IReal s f = 2 * cFrac s * dotHomogeneousENorm s f ^ 2
```

One conformance-record fix is required.  `WholeSpaceIdentity.lean` contains 26
public theorem declarations (the helper declarations at `:128-142`, `:320-333`, and
the other theorem heads through `:509` are not private), but
`research/T13/axioms_wholespace_identity.lean:15-30` prints only 16 of them, while
`research/T13/REPORT_348.md:50-51` calls those 16 “all public declarations”.  The ten
omitted names are `measurable_phase`, `norm_phase_le`, `integrable_phase_mul`,
`contDiff_translate`, `hasCompactSupport_translate`, `contDiff_diff`,
`hasCompactSupport_diff`, `measurable_kernel`, `continuous_phase`, and
`measurable_weightedSq`.  The reviewer audit probe
`research/T13/probes/rev348_axioms_all.lean` prints each omitted declaration as
exactly `[propext, Classical.choice, Quot.sound]`; therefore this is a mechanical
conformance omission, not an illicit axiom or proof defect.  Fix by adding one
`#print axioms` line for each of those ten names and changing the report’s count to
26.

No “not in the tree” gap is asserted by the report.  The cited D01 witness, norm,
uniqueness, and `ae_ne_zero` declarations were nevertheless searched in the whole
`formalization/NSFormalization/Section4` tree and found at the lines cited above.
There are no `sorry`, `admit`, `axiom`, or `native_decide` tokens in the production
module or closure probe; the sole heartbeat override is the commented, declaration-
local `set_option maxHeartbeats 400000 in` at `WholeSpaceIdentity.lean:490-495`.
The triple-dot diff against `origin/erenup/integration-section3` has no modified
formalization module (only added modules; the lane commit itself adds
`WholeSpaceIdentity.lean`), and no `verification/` path is touched.

## Commands and results

All Lean commands were run after `. scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`,
and `lake` only from `verification/`, one process at a time.

* `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T13.WholeSpaceIdentity` — exit 0.  Exact final output was:

  ```text
  warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
    Function.comp_def
  Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
  Build completed successfully (9358 jobs).
  ```

  The only diagnostics are replayed dependency warnings; `grep WholeSpaceIdentity`
  on the build log returned 0.
* `cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T13/WholeSpaceIdentity.lean` — exit 0, 0 bytes.
* `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T13/probes/wholespace_identity_closes.lean` — exit 0, 0 bytes.
* `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T13/axioms_wholespace_identity.lean` — exit 0.  Exact output (Lean wraps three entries across lines):

  ```text
  'NSFormalization.Section3.T13.dotHomogeneousENorm_eq_homogeneousFourierENorm' depends on axioms: [propext,
   Classical.choice,
   Quot.sound]
  'NSFormalization.Section3.T13.homogeneousFourierENorm_lt_top' depends on axioms: [propext, Classical.choice, Quot.sound]
  'NSFormalization.Section3.T13.homogeneousFourierENorm_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
  'NSFormalization.Section3.T13.schwartz_lintegral_normSq' depends on axioms: [propext, Classical.choice, Quot.sound]
  'NSFormalization.Section3.T13.lintegral_angularFourier_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
  'NSFormalization.Section3.T13.angularFourier_translate' depends on axioms: [propext, Classical.choice, Quot.sound]
  'NSFormalization.Section3.T13.angularFourier_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
  'NSFormalization.Section3.T13.angularFourier_diff' depends on axioms: [propext, Classical.choice, Quot.sound]
  'NSFormalization.Section3.T13.per_h_component' depends on axioms: [propext, Classical.choice, Quot.sound]
  'NSFormalization.Section3.T13.lintegral_kernel_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
  'NSFormalization.Section3.T13.ofReal_normSq_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
  'NSFormalization.Section3.T13.continuous_angularFourier_component' depends on axioms: [propext,
   Classical.choice,
   Quot.sound]
  'NSFormalization.Section3.T13.component_integral_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
  'NSFormalization.Section3.T13.IReal_decomp' depends on axioms: [propext, Classical.choice, Quot.sound]
  'NSFormalization.Section3.T13.IReal_eq_cFrac_mul_homogeneousFourierENorm_sq' depends on axioms: [propext,
   Classical.choice,
   Quot.sound]
  'NSFormalization.Section3.T13.wholeSpace_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
  ```

  The ten omitted helpers independently print the same list in
  `rev348_axioms_all.lean`.
* `make check` — exit 0.  Exact final output:

  ```text
  python3 experiments/test_contract_policy.py
  .............
  ----------------------------------------------------------------------
  Ran 13 tests in 0.046s

  OK
  python3 experiments/check_work_queue.py
  45 work items: ownership, contract registration and task cards consistent.
  ```

* The conditional broader command was also attempted as
  `BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 scripts/gates.sh NSFormalization.Section3.T13.WholeSpaceIdentity`.
  Build and `make test-mutations` passed (`extra_axiom: rejected as required`,
  `weakened_hypothesis: rejected as required`, `Mutation suite passed`), but the
  final base-compatibility check fails before lane code is considered:

  ```text
  AssertionError: Removed stable specification: verification/Contracts/V1/PacketImport.lean
  ```

  This conditional gate is not owed because `verification/` is absent from the lane
  diff; the same repository-baseline issue is not a defect in lane 348.
