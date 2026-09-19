# Lane 443 continuation (fix) — add the canonical `energyRate` with the explicit nonnegativity premises (lead ruling, same as lane 435)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker continuing lane 443 in `/data_8T/ping/blowup_density/.claude/worktrees/443-T18-U9-U10-energy-mixed-rates` (branch `erenup/443-T18-U9-U10-energy-mixed-rates`;
commit `64872e8b` has `Section3/T18/EnergyRate.lean` with `energyRate_separateConstants` and `Section3/T18/MixedRate.lean` with the four U10 fields; the Spec-form `energyRate` is closed in
`research/T18/probes/u9_u10_closes.lean` from `PacketImportAPI.energy_isLUB`/`dissipation_eq`). Read `research/T18/REPORT_443.md` §3 and `ATTEMPTS_U9_U10.md`.

**Lead ruling** (same pattern as lane 435's `velocityDifference_support`): `InsertionData` does not retain the raw packet clauses giving `0 ≤ M`, `0 ≤ D` (in the raw packet `M = Real.sqrt …`, `D = Real.sqrt …`).
Do not modify `InsertionData`. Add to `EnergyRate.lean` the canonical theorem with the two raw clauses as explicit premises:
```
theorem energyRate (data : InsertionData) (hM : 0 ≤ data.energyBound) (hD : 0 ≤ data.dissipationBound) :
    ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
      energyENormT data.place.T (fun z => velocity data ε z - data.reference.velocity z) ≤
        ENNReal.ofReal ((data.energyBound + data.dissipationBound) * ε ^ ((1 : ℝ) / 2) +
          data.correction.energyConst * ε ^ ((3 : ℝ) / 2))
```
(conclusion token-identical to the Spec field under the `InsertionData` projections), derived from `energyRate_separateConstants` by `ENNReal.ofReal_add` (nonnegativity of each summand: `hM`, `hD`,
`energyConst_nonneg`, `ε > 0`). Make the probe close the Spec field through this theorem (discharging `hM`/`hD` from the packet's `M = √…`/`D = √…` clauses or `energy_isLUB`/`dissipation_eq` as you already do).
Document the ruling in `ATTEMPTS_U9_U10.md`/`REPORT_443.md` ("explicit raw premises; U12 discharges them from the packet clauses; a later MAINT may add them to `InsertionData`") and update the U9 status line.

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; no edits to existing modules other than this lane's own `EnergyRate.lean` and research files. Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`.

## Gates
`lake build NSFormalization.Section3.T18.EnergyRate NSFormalization.Section3.T18.MixedRate` (0 errors), `lake env lean` on both modules (0 output), the probe (0 output), `research/T18/axioms_u9_u10.lean` (add `energyRate`), `make check`.

## Report
Commit `[443-T18] U9: canonical energyRate with the explicit nonnegativity premises (lead ruling)`; end with four parts; append them to `research/T18/REPORT_443.md`.
