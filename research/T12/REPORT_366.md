# Lane 366-T12-U1 report

The API bridge and the supported-in-cube scalar/vector `L^p` transfer are proved.
The periodic Haar/cube theorem is reduced for finite nonzero `p` to one explicit
lintegral identity, matching the fundamental-domain argument in T13.

Lean now contains `HaarCube.lean`, with the p=3 and p=6 API probes.

The remaining gap is the general measurable ENNReal density identity (including
the endpoint cases); no placeholder or axiom was added.

Validation: module source and probe checked with `lake env lean`; full build and
`make check` remain to be run by the integrator after this partial lane result.

## completion (lane 366 r1)

Addresses the codex REJECT (`research/T12/REVIEW_366-T12-U1-haar-cube.md`).

**What was proved.** The actual all-`p` Haar↔cube transfer for periodic fields,
for every `p : ℝ≥0∞` including `p = 0` and `p = ⊤`:
`eLpNorm (torusLift v) p periodicTorusMeasure = eLpNorm v p (volume.restrict fundamentalCube)`
(`eLpNorm_torusLift_eq_restrict`), plus the smooth corollary, the scalar and the
gradient-tensor (carrier `WithLp 2 (Fin 3 → Space)`) specializations, the
`periodicLpENorm` bridges, and the supported-in-cube transfer in both
`Function.support` and `tsupport` spellings (scalar + gradient-tensor carriers).

**What exists in Lean now.** `formalization/NSFormalization/Section3/T12/HaarCube.lean`
with 11 public theorems, all auditing to `[propext, Classical.choice, Quot.sound]`.
The proof no longer routes through a hypothesised lintegral identity: instead a
single measure identity `map_torusChart` (the fundamental-domain chart
`torusChart z = toSpace ((measurableEquivPiIoc 0 z).val)` pushes Haar measure to
`volume.restrict fundamentalCube`) is combined with Mathlib's measurable-embedding
change of variables `MeasurableEmbedding.eLpNorm_map_measure`, which itself covers
finite exponents by `∫⁻ ‖·‖ₑ^p.toReal` and the endpoint `p = ⊤` by `essSup`.  The
review's three module warnings are gone (no deprecated lemma, `_hv` silences the
unused-hypothesis linter).

**Gap.** None for U1: the theorem is unconditional in the exponent and holds for
every field (the periodicity hypothesis is the paper's "unit-periodic `v`"
interface, kept for statement fidelity and downstream U4/U5 but unused in the
proof — like the smoothness hypotheses in `T15/HaarBridge.lean`).  No `sorry`,
`axiom`, or `native_decide`.

**Commands / results.**
- `lake build NSFormalization.Section3.T12.HaarCube` → success (0 errors).
- `lake env lean` on the module → empty output (0 warnings; the three
  review-flagged warnings removed).
- `lake env lean research/T12/axioms_haar_cube.lean` → all 11 declarations print
  exactly `[propext, Classical.choice, Quot.sound]`.
- `lake env lean research/T12/probes/haar_cube_closes.lean` → clean (genuine
  `p = 3`, `p = 6`, `p = ⊤` transfer + `periodicLpENorm` bridge on the two-mode
  field `scalarOfCoeff probeCoeff`).
- reviewer probes: `rev366_required_name`, `rev366_nonvacuity`,
  `rev366_vector_axioms` clean; `rev366_mutation` fails as intended (wrong `+1`
  RHS).
- `make check` → OK (contract policy, work queue consistent).
