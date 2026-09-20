# Lane 355-T14-packet-contract report

## 1. What is registered

`T01.packet_import` version 1 is registered in `verification/contracts.json`
under parent task `T01`.  The contract asserts the whole-space source packet
used before T15 placement and periodization, reusing the registered
`I01.packet` witness and adding exactly the two `eq:packetenergy` relations.
The registry scope records the factors `2ν` and `2`, the `Ioo 0 t` accumulated
force integral, the `CompactEnergy`/`sqrt_energy_le_primitive` proof
provenance, and the fact that periodization is outside T14.

The contract has five top-level declarations: `accumulatedForce`, the two-field
`PacketEnergyAPI`, `PacketImportAPI`, `packetImportStatement`, and
`PacketImportFamily`.  `PacketEnergyAPI` has two fields:
`energy_le_work` and `work_eq_square`.

## 2. Lean files and binding

- [PacketImport.lean](/data_8T/ping/blowup_density/.claude/worktrees/355-T14-packet-contract/verification/Contracts/V1/PacketImport.lean)
  is the namespace-adjusted reconciliation and imports only
  `Contracts.V1.Packet`.
- [PacketImport.lean](/data_8T/ping/blowup_density/.claude/worktrees/355-T14-packet-contract/verification/Bindings/PacketImport.lean)
  provides the `accumulatedForce_eq` bridge and the concrete family built from
  `Bindings.packet ν hν` and the two Section 3 T14 theorems.
- [PacketImport.lean](/data_8T/ping/blowup_density/.claude/worktrees/355-T14-packet-contract/verification/Tests/PacketImport.lean)
  checks the statement, both energy fields, the selected-packet velocity
  equality, and the transitive axiom boundary.
- [axioms_contract.lean](/data_8T/ping/blowup_density/.claude/worktrees/355-T14-packet-contract/research/T14/axioms_contract.lean)
  is the standalone conformance/axiom audit.

The ledger now lists `T01.packet_import` under T14, and the rendered task files
were regenerated.  `research/T14/ATTEMPTS_CONTRACT.md` records the route and
checks; `COMPARISON.md` has a new Registered section.

## 3. Gaps and boundaries

No T14 proof gap remains.  The packet is an actual selected `PacketAPI` and the
energy fields are actual terms from `energy_le_work_of_packet` and
`work_eq_square_of_packet`; no hypothesis is substituted for the registered
declaration.  There are no `sorry`, `admit`, `axiom`, placeholder `Prop`
fields, periodic proxy, or formalization changes.  T10 Fourier data and T15
placement/periodization remain downstream and are intentionally not asserted.

## 4. Commands and results

The claim was recorded first with `python3 experiments/tasks.py claim T14 erenup`
and rendered with `python3 experiments/tasks.py render`; the claim is commit
`a5e6c319`.  The contract modules were built from `verification/` with
`. scripts/lean-env.sh` and `LEAN_NUM_THREADS=6`; the direct build passed.

The final gates were run with
`BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 scripts/gates.sh`:

- `make check`: passed; the work queue reported `45 work items` and the policy
  suite reported `OK`.
- `make test`: passed; `Tests.PacketImport.lean` reported
  `checked; standard logical axioms only`.
- `make test-mutations`: passed (`Mutation suite passed`).
- `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`:
  exit 0, `registered_contracts: 40`, and
  `base_compatibility_checked: true`.
- `lake env lean ../research/T14/axioms_contract.lean`: passed; every printed
  declaration has exactly `[propext, Classical.choice, Quot.sound]`.
- `git diff --stat verification/contracts.json`: `11` additions and no
  deletions.

The contract commit is separate from the ledger claim commit `a5e6c319`.  The
worktree is clean after both commits.
