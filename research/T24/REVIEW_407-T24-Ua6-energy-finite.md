ACCEPT-WITH-NOTES

## 1. What the lane claims

`REPORT_407.md:7-16` claims T24a Ua6, namely the raw-field theorem

```lean
theorem energy_finite {U : VelocityField} (c : Space) (r τ₀ τ₁ : ℝ)
    (henergy : energyENorm 1 U < ⊤) :
    ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b →
      energyENorm 1 (affineVelocity U b) < ⊤
```

This is the requested raw clause in the ledger (`research/T24/T24_SPLIT.md:209-214`).
The paper’s finite-energy/dissipation assertion is at
`paper/sections/03-torus.tex:686-687`, and the exact Spec field is
`research/T24/Spec.lean:1071-1077`.  The delivered declaration at
`formalization/NSFormalization/Section3/T24/AffineEnergy.lean:406-415` has the
same quantifier order, constant `1`, strict `< ⊤`, and affine velocity, with
the Spec packet field replaced by raw `U`.  No radius/window positivity or
smoothness/measurability hypothesis on `U` was silently added.

The local `energyEssSup`, `energyGradient`, and `energyENorm` at
`formalization/NSFormalization/Section3/T24/AffineEnergy.lean:60-76` reproduce
the registered definitions at `verification/Contracts/V1/Data.lean:444-476`.
The four `rfl` bridges in `research/T24/probes/affine_energy_closes.lean:42-56`
confirm the registered spelling, and the packet/raw theorem applications are
at `:89-105`.  The zero variation is explicitly admissible at `:109-121` and
the `b = 0` conclusion reduces to the hypothesis at `:123-133`, so the
quantifier is not vacuous.

The proof route is honest about the missing measurability of raw `U`: it uses
the squared `ℝ≥0∞` estimate and right-summand integral splitting in
`AffineEnergy.lean:84-156`, then the differentiability case split in
`:165-209`, compact-support bounds in `:216-308`, and the two finite halves in
`:312-402`.  The cited downstream alternatives really do require extra
hypotheses (`verification/Bindings/ScalingEnergy.lean:57-71`, `:105-121`,
`:167-180`).

## 2. What is in Lean

The new module is 423 lines and contains the three local norm definitions plus
14 theorem declarations; the declaration list is visible at
`formalization/NSFormalization/Section3/T24/AffineEnergy.lean:84-415`.
`AffineAdmissible` and `affineVelocity` are imported rather than restated
(`formalization/NSFormalization/Section3/T24/AffineBasics.lean:21-33`).
The conformance probe also proves the Spec-shaped statement on
`Bindings.packet ν hν` (`research/T24/probes/affine_energy_closes.lean:87-105`).

No declaration-level `sorry`, `admit`, `axiom`, `native_decide`, or
`maxHeartbeats` occurs in the changed Lean additions.  The committed diff is
additive only: `git diff --name-only origin/erenup/integration-section3...HEAD`
lists the new `AffineEnergy.lean`, axiom file, and probe, plus lane records;
no pre-existing Lean module is modified.

The exact changed-path output is:

```text
formalization/NSFormalization/Section3/T24/AffineEnergy.lean
logs/LESSONS.md
research/T24/ATTEMPTS_UA6.md
research/T24/REPORT_407.md
research/T24/T24_SPLIT.md
research/T24/axioms_ua6.lean
research/T24/probes/affine_energy_closes.lean
```

## 3. Gaps and notes

The worker’s sole gap is correctly outside Ua6: `PacketAPI` has no assembled
`energyENorm 1 velocity < ⊤` field.  The packet instead exposes
`square_integrable` at `verification/Contracts/V1/Packet.lean:243-247`,
`energy_isLUB` at `:248-256`, `dissipation_integrable` at `:257-260`, and
`dissipation_eq` at `:261-267`; this is accurately reported at
`research/T24/REPORT_407.md:32-34`.  A whole-tree search of
`formalization/NSFormalization/Section4` found no assembled `energyENorm`
theorem; it found only the reusable ingredients
`I02.eLpNorm_two_eq_ofReal_sqrt` (`Section4/I02/Energy.lean:87-100`) and
`I03.eLpNorm_spatialGradient_sq_slice` (`Section4/I03/Energy.lean:61-76`).
Thus threading `henergy` is the correct Ua6 scope.

The required substantive negative check is in the reviewer-only probe
`research/T24/probes/rev407_mutated_time.lean:8-15`: changing the main
statement’s time constant from `1` to `2` fails with the expected type mismatch
(`energyENorm 1 ...` is supplied where `energyENorm 2 ...` is required), not by
dropping an argument.  This probe is intentionally untracked and is the only
reviewer-added file.

Two exact documentation/audit fixes remain:

1. `research/T24/axioms_ua6.lean:12-25` prints the 14 theorems but omits the
   three local norm definitions at `AffineEnergy.lean:62`, `:68`, and `:75`.
   Add one `#print axioms` line for each; a direct check showed each also has
   exactly `[propext, Classical.choice, Quot.sound]`.
2. In `research/T24/REPORT_407.md:20`, replace “each carries four
   measurability/differentiability hypotheses” with “the alternatives carry
   additional measurability/differentiability hypotheses (in varying counts)”.
   The cited lemmas have different arities (two for `energyEssSup_add_le`, six
   for `energyGradient_add_le`, and more for `energyENorm_add_le`).

## 4. Commands and results

All commands used `. scripts/lean-env.sh`; Lake commands ran from `verification/`
with `LEAN_NUM_THREADS=6`.

```text
LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T24.AffineEnergy
⚠ [9316/9326] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [9319/9326] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def
Build completed successfully (9326 jobs).

LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T24/AffineEnergy.lean
[no output; exit 0]

LEAN_NUM_THREADS=6 lake env lean ../research/T24/probes/affine_energy_closes.lean
[no output; exit 0]
```

```text
LEAN_NUM_THREADS=6 lake env lean ../research/T24/axioms_ua6.lean
```

The shipped axiom file returned exit 0 and exactly these permitted lists for
all 14 printed theorems:

```text
'NSFormalization.Section3.T24.add_rpow_two_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.rpow_two_eLpNorm_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.rpow_two_eLpNorm_add_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.rpow_two_eLpNorm_le_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.enorm_spatialGradient_affineVelocity_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.continuous_spatialDerivative_uncurry' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.spatialDerivative_eq_zero_of_notMem_tsupport' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.exists_bound_spatialDerivative' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.enorm_spatialGradient_rpow_two_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.rpow_two_eLpNorm_slice_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.rpow_two_eLpNorm_gradient_slice_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.energyEssSup_affineVelocity_lt_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.energyGradient_affineVelocity_lt_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.energy_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The direct audit of the three omitted definitions returned the same permitted
list for each.  From the repository root (`verification/` has no Makefile
target), `make check` exited 0; its exact final gate output was:

```text
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.044s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The full check also reports the repository’s pre-existing copied-source
`BoundaryCorollary.lean:90` admission token and `source_hashes_match: false`;
these are outside this lane’s diff and the command still exits 0.

The complete standard gate script was rerun with the requested Section 3 base:

```text
BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 scripts/gates.sh NSFormalization.Section3.T24.AffineEnergy
GATES_EXIT=0
== lake build NSFormalization.Section3.T24.AffineEnergy
Build completed successfully (9326 jobs).
== make test
== make test-mutations
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
== gates OK
```

The mutation probe failed as intended:

```text
../research/T24/probes/rev407_mutated_time.lean:15:2: error: Type mismatch
  energy_finite c r τ₀ τ₁ henergy
has type
  ∀ (b : VelocityField), AffineAdmissible c r τ₀ τ₁ b → energyENorm 1 (affineVelocity U b) < ⊤
but is expected to have type
  ∀ (b : VelocityField), AffineAdmissible c r τ₀ τ₁ b → energyENorm 2 (affineVelocity U b) < ⊤
```

Finally, `git diff --check origin/erenup/integration-section3...HEAD` returned
`DIFF_CHECK_EXIT=0`; the declaration-level forbidden-token and
`maxHeartbeats` scans returned no matches.
