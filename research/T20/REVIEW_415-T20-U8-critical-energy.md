ACCEPT

## what the lane claims

The report claims that `criticalEnergy` closes the `CriticalRegularityTAPI.criticalEnergy` field with the exact quantifier order and inequality, using `criticalTrilinearConst), and that the zero-force/zero-solution probe is non-vacuous. The paper display is `paper/sections/03-torus.tex:420-440`; the displayed conclusion is at lines 437-440. The canonical field is `formalization/NSFormalization/Section3/T20/CriticalRegularity.lean:286-299), including `0 < ν`, `g ∈ forceClassT`, `t ∈ Ioo 0 T`, and an existential derivative witness.

## what is in Lean

The implementation is present at [CriticalEnergy.lean](/data_8T/ping/blowup_density/.claude/worktrees/415-T20-U8-critical-energy/formalization/NSFormalization/Section3/T20/CriticalEnergy.lean:518), and the final assembly uses the derivative, transport, force, and trilinear estimates through lines 721-748. The probe checks the field type by `exact` and supplies the sanctioned zero instance ([critical_energy_closes.lean](/data_8T/ping/blowup_density/.claude/worktrees/415-T20-U8-critical-energy/research/T20/probes/critical_energy_closes.lean)). No forbidden token occurs in the implementation. The mutation probe changed the main constant to `criticalTrilinearConst + 1`; Lean rejected `exact criticalEnergy` with the expected type mismatch, proving the statement is load-bearing.

## gaps

No U8 gap is declared, and a whole-tree grep found no missing `criticalEnergy` or matching Section 4 lemma that contradicts that claim. The report's caveats about only having the zero-force non-vacuity witness and fixing `C₀` for U13 are accurate. The branch diff contains the new U8 module and records/probes; no pre-existing formalization module is modified.

## commands and results

- `lake build NSFormalization.Section3.T20.CriticalEnergy`: `Build completed successfully (10648 jobs).`
- `lake env lean ../formalization/NSFormalization/Section3/T20/CriticalEnergy.lean`: exit 0, no output.
- `lake env lean ../research/T20/probes/critical_energy_closes.lean`: exit 0, no output.
- `lake env lean ../research/T20/axioms_u8.lean`: exit 0; all 21 declarations report exactly `[propext, Classical.choice, Quot.sound]`.
- Root `make check`: `python3 experiments/check_formalization_plan.py --check` completed successfully.
- `experiments/check_contracts.py --base-ref origin/erenup/integration-section3`: completed with `"base_compatibility_checked": true`.
- `scripts/gates.sh NSFormalization.Section3.T20.CriticalEnergy`: the gate ran the build/test/mutation sequence; its architecture scan reports the repository's pre-existing copied-source hash/admission findings, unrelated to this lane. No lane-specific Lean error was reported.
- Negative mutation: `rev415_mutation.lean` fails because the expected type contains `(criticalTrilinearConst + 1)) while `criticalEnergy` has `criticalTrilinearConst`; this is the expected substantive break.

