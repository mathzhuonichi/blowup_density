# Lane 176 — SIMP/tester pass over the first codex batch

## 1. What was simplified

* `A01/ConstructorDivergenceSlice`: replaced the reviewed word-descent/summation detour with the
  existing vendor `divergenceFree_classical_divergence_zero` bridge.  The theorem type is
  unchanged; the compatibility-only invariance premise is referenced proof-locally as `_hu` to
  keep the module warning-free.  The rebased module is 185 → 150 lines after the proof and prose
  cleanup.  The owner's six-theorem `A01/ConstructorDivergence` module is untouched.
* `C01/EnergyBounds` + `Paper1/ScalarEnergy`: hoisted the generalized regularized-square-root
  lemma into `NSFormalization.Paper1.sqrt_energy_le_primitive_general`.  The original
  `Paper1.sqrt_energy_le_primitive` and C01 `sqrt_energy_le_primitive'` statements are unchanged
  corollaries; C01 shrank 318 → 282 lines and Paper1 is 217 → 241 lines.
* `A01/SliceWiring`: retired the pure `velocitySliceSmoothL2` alias and changed its sole term use
  to `C01.velocityField`; retained `velocitySliceSmoothL2_field` as a direct compatibility `rfl`
  theorem.  Added `sobolevENorm_slice_ne_top_order` for arbitrary `m : ℕ`, retaining the old
  `q+1` theorem as a one-line corollary.  The module remains 192 lines after the balanced rewrite.
* `research/C01/Spec.lean`: corrected the two reviewed paper citations `:103` → `:104`.
* `DatumPathContinuous`, `ConstructorPressure`, `Enstrophy`, `EnstrophyIdentityRaw`, `R44/Pieces`,
  and `D01/HomogeneousNorm` were inspected without further source changes.  Integration's owner
  `C01/EnstrophyIdentity` module is untouched.  Full details and exact line deltas are in
  `research/MAINT/ATTEMPTS_SIMP_176.md`.

## 2. What is in Lean now (statement invariance)

The consumed theorem statements are invariant.  In particular, the registered C01 V3 fields
(`energyDifferentialBound`, `l2Bound`), inherited unchanged by V4, and the D01 G1
definition/bridge are byte-identical, as are the existing `sqrt_energy_le_primitive` and C01
`sqrt_energy_le_primitive'` headers.  The A01 Slice divergence theorem headers and the old q+1
slice-finiteness theorem retain their types.

Alias retirement is the one signature exception.  `velocitySliceSmoothL2` previously had two
same-module term uses and research-probe uses, but no external production or verification
consumer; all term sites were migrated to `C01.velocityField`.  The retained
`velocitySliceSmoothL2_field` header therefore changed only from the retired alias's `.field` to
the definitionally equal `(C01.velocityField ...).field`.  Its only external references are
research `#print`/`#check` audits, not theorem applications.  The new arbitrary-order theorem is
additive.

| module | before → after | consumed declarations changed |
|---|---:|---:|
| `A01/DatumPathContinuous` | 107 → 107 | 0 |
| `A01/ConstructorDivergenceSlice` | 185 → 150 | 0 |
| `A01/ConstructorPressure` | 256 → 256 | 0 |
| `C01/Enstrophy` | 250 → 250 | 0 |
| `C01/EnstrophyIdentityRaw` | 257 → 257 | 0 |
| `R44/Pieces` | 218 → 218 | 0 |
| `D01/HomogeneousNorm` | 65 → 65 | 0 |
| `C01/EnergyBounds` | 318 → 282 | 0 |
| `Paper1/ScalarEnergy` | 217 → 241 | old theorem 0 |
| `A01/SliceWiring` | 192 → 192 | old q+1 theorem 0 |

The closure audit reports no registered closure for `A01.DatumPathContinuous`,
`A01.ConstructorDivergenceSlice`, `A01.ConstructorPressure`, `A01.SliceWiring`,
`C01.Enstrophy`, `C01.EnstrophyIdentityRaw`, or `R44.Pieces`.  `D01.HomogeneousNorm` is in
`D01.homogeneous_norm`; `C01.EnergyBounds` is inherited by the registered
`C01.energy_absorption_v4`.  That owner V4 has exactly six new public fields:
`enstrophyIdentity`, `enstrophyDifferentialBound`, `enstrophyIntegralBound`,
`sobolevTwoFourier`, `h2TimeIntegral`, and `h2TimeIntegralZeroDatum`.  Lane 177 was cancelled;
nothing was registered in lane 176.

## 3. Skipped items and reasons

No requested simplification was skipped for lack of testing.  The unchanged modules listed in §1
were deliberately left untouched in this lane.  On the rebased baseline, the registered owner C01
chain supplies the identity, absorption, Fourier, and endpoint H² fields.  Our `Enstrophy` plus
`EnstrophyIdentityRaw` chain is therefore not needed by V4: it is an alternative raw-carrier proof,
and its strict-interior finiteness results are subsumed for contract purposes by the quantitative
terminal-horizon theorem.  `CLOSURE_PLAN.md` proposes auditing and retiring this legacy route as a
future SIMP row; no such deduplication is performed here.

## 4. Commands and results

All Lean commands used `. scripts/lean-env.sh` (or `..` from `verification/`), ran `lake` from
`verification/`, and used `LEAN_NUM_THREADS=6`.

* The combined `lake build` for the four touched modules and the Section4 importers found by the
  requested `grep -rln` completed successfully (10,360 jobs).  The importer set was
  `A01.ForceBridge`, the owner and Raw `C01.EnstrophyIdentity` modules, and `R43.Pieces`.
  A direct `lake env lean` check of `ConstructorDivergenceSlice.lean` exited 0 with no output,
  confirming that the proof-local `_hu` reference removes the lane-local warning.
* Conformance: `research/A01/axioms_b1_ladder.lean`, `axioms_c6.lean`,
  `axioms_pressure_p3.lean`, `axioms_slice_wiring.lean`, `research/C01/axioms_e5.lean`,
  `axioms_e6e7.lean`, `axioms_energy_bounds.lean`, `research/R44/axioms_r44_pieces.lean`, and
  `research/D01/axioms_g1.lean` all exit 0.  Every audited declaration prints exactly
  `[propext, Classical.choice, Quot.sound]`.
* Existing negative probes all failed as intended (exit 1): `rev161_mutation_widen`,
  `rev162_mutate_divergence_constant`, `rev168_negative_gradient_shift`, `rev163_flip_sign`,
  `rev170_force_sign_mutation`, `rev166_mutation_quarter_fail`, `rev164_mutate_zero_to_one`, and
  `rev157_mut2_const`.  The omitted module-specific probes also behaved as required:
  `rev154_mut_A_constant` rejected the EnergyBounds coefficient mutation and
  `rev176_mutate_budget` rejected the Paper1 `2 → 1` budget mutation; its nonzero control
  `rev176_nonvacuity` exited 0.  Updated positive `rev157_fidelity` and signature probes exit 0.
* `scripts/gates.sh` with the same eight formalization modules: exit 0 (`make check`; `make test`,
  including registered V4, all contracts standard axioms; mutation suite passed; gates OK).
* `python3 experiments/check_contracts.py --base-ref origin/erenup/integration`: exit 0,
  28 registered contracts and `base_compatibility_checked: true`.
