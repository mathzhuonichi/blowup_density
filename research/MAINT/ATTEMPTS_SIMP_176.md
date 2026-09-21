# SIMP/tester pass — lane 176

The original simplification was measured against `393e3a7`; this follow-up is rebased onto
`9825a35` (`origin/erenup/integration` at final rebase time).  Integration renamed the lane-162 module
to `ConstructorDivergenceSlice.lean` and the lane-170 module to
`EnstrophyIdentityRaw.lean`; the owner modules at the unsuffixed paths are untouched.

No theorem statement consumed by a registered contract changed.  The registered consumers touched
here (`C01.EnergyBounds`, inherited by `C01.energy_absorption_v4`, and
`D01.HomogeneousNorm`) retain their consumed statements byte-for-byte.

## Simplification ledger

| item | files | lines before → after | removed / added | consumers rebuilt |
|---|---|---:|---:|---|
| A01 datum path | `Section4/A01/DatumPathContinuous.lean` | 107 → 107 | 0 / 0; reviewed, no safe dead code found | `research/A01/axioms_b1_ladder.lean` |
| A01 c6 divergence | `Section4/A01/ConstructorDivergenceSlice.lean` | 185 → 150 | original proof simplification: 36 removed / 4 added; the follow-up adds the proof-local `hu` reference and rewrites stale prose | Slice importers and `research/A01/axioms_c6.lean`; direct vendor bridge replaces the redundant word-descent assembly |
| A01 c9 pressure | `Section4/A01/ConstructorPressure.lean` | 256 → 256 | 0 / 0; only the reviewed redundant `hprojected` note was already fixed at HEAD | `research/A01/axioms_pressure_p3.lean` |
| C01 E5 | `Section4/C01/Enstrophy.lean` | 250 → 250 | 0 / 0; legacy alternative route retained unchanged | `research/C01/axioms_e5.lean` |
| C01 E6/E7 | `Section4/C01/EnstrophyIdentityRaw.lean` | 257 → 257 | 0 / 0; renamed legacy route retained unchanged | `research/C01/axioms_e6e7.lean` |
| R44 pieces | `Section4/R44/Pieces.lean` | 218 → 218 | 0 / 0; shared R43 lemmas already imported | `research/R44/axioms_r44_pieces.lean` |
| D01 homogeneous norm | `Section4/D01/HomogeneousNorm.lean` | 65 → 65 | 0 / 0; existing canonical definition/lemmas retained | `research/D01/axioms_g1.lean`, registered `D01.homogeneous_norm` closure |
| C01 energy scalar | `Section4/C01/EnergyBounds.lean` | 318 → 282 | 38 removed / 2 added; generalized proof hoisted to Paper1 | `research/C01/axioms_energy_bounds.lean`, registered C01 V3/V4 closure |
| Paper1 scalar owner | `Paper1/ScalarEnergy.lean` | 217 → 241 | 40 added / 16 removed; added `sqrt_energy_le_primitive_general`, old theorem is its corollary | `research/C01/axioms_energy_bounds.lean` |
| A01 slice wiring | `Section4/A01/SliceWiring.lean` | 192 → 192 | 17 removed / 17 added; retired pure alias, added arbitrary-order lemma and q+1 corollary | `research/A01/axioms_slice_wiring.lean` plus updated existing 157 probes |
| C01 citation cleanup | `research/C01/Spec.lean` | — | two `:103` → `:104` citations | C01 conformance remains green |

The alias retirement has one deliberate signature exception.  Before the lane,
`velocitySliceSmoothL2` was used by two proofs in its own module and by research probes, but had no
external production or verification consumer.  Those term sites now use `C01.velocityField`, and
the retired name has no term-level use.  Consequently `velocitySliceSmoothL2_field` is not
byte-identical: its left side changed from the retired alias's `.field` to the definitionally equal
`(C01.velocityField ...).field`.  Its only external Lean references are research `#print`/`#check`
audits, not theorem applications.  `sobolevENorm_slice_ne_top_order` is the generalized owner; the
old q+1 theorem remains a one-line corollary.

## Tester pass

The conformance files audit the touched and inspected modules, with every declaration printing
exactly `[propext, Classical.choice, Quot.sound]`: `axioms_b1_ladder`, `axioms_c6`,
`axioms_pressure_p3`, `axioms_slice_wiring`, `axioms_e5`, `axioms_e6e7`,
`axioms_energy_bounds`, `axioms_r44_pieces`, and `axioms_g1`.  The c6 and E6/E7 probes now import
the renamed Slice/Raw paths.

The selected negative probes fail for their intended mutations: `rev161_mutation_widen`,
`rev162_mutate_divergence_constant`, `rev168_negative_gradient_shift`, `rev163_flip_sign`,
`rev170_force_sign_mutation`, `rev166_mutation_quarter_fail`, `rev164_mutate_zero_to_one`, and
`rev157_mut2_const`.  Two previously omitted module-specific tests are also recorded:
`research/C01/probes/rev154_mut_A_constant.lean` rejects the `EnergyBounds` pairing coefficient
mutation, and `research/MAINT/probes/rev176_mutate_budget.lean` rejects the Paper1 generalized
budget constant `2 → 1`; its nonzero control `rev176_nonvacuity.lean` succeeds.

## Skipped / unchanged items

* `DatumPathContinuous`, `ConstructorPressure`, `Enstrophy`, `EnstrophyIdentityRaw`, `R44/Pieces`,
  and `D01/HomogeneousNorm` had no additional safe simplification in the original pass.  They were
  rebuilt and tested.
* The owner's six-field `C01.energy_absorption_v4` is now registered.  `Enstrophy` and
  `EnstrophyIdentityRaw` form an unregistered alternative proof route whose identity and
  strict-interior finiteness results are duplicated or subsumed by the owner chain.  Their possible
  retirement is proposed as a future SIMP row in `CLOSURE_PLAN.md`; no deduplication is done here.
* No contract was registered in lane 176.  The remaining future closure plan is A01 V2.
* `research/C01/Spec.lean` is a documentation-only citation correction; no Lean statement changed.
