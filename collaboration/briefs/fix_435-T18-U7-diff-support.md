# Lane 435 continuation (fix) — close `velocityDifference_support` with the raw packet support clause as an explicit premise (lead ruling)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker continuing lane 435 in `/data_8T/ping/blowup_density/.claude/worktrees/435-T18-U7-diff-support` (branch `erenup/435-T18-U7-diff-support`; commit
`f5a1ca5d` has `Section3/T18/Support.lean` with `diffSupportRadius`, `diffSupportRadius_pos`, `correction_slice_support`, `diffSupport_in_chart` and the probe `research/T18/probes/u7_closes.lean` proving
the full target *given* the clause `∀ s ∈ Ico 0 1, tsupport (fun y ↦ data.packetVelocity (s, y)) ⊆ data.place.Kstar`). Read `research/T18/REPORT_435.md` §3, `ATTEMPTS_U7.md`, the probe, and
`Section3/T18/Insertion.lean` (`InsertionData` — it carries `place`, `scaling`, `correction`, `reference` but **no raw packet support clause**; that is a U1 design omission recorded by the lead).

**Lead ruling.** Do not modify `InsertionData` (lanes 443/445 are building on it). Instead, state the canonical theorem with the raw clause as an explicit premise — exactly the pattern of T24's raw
clauses and T17's G1 `hv`:
```
theorem velocityDifference_support (data : InsertionData)
    (hsupp : ∀ s ∈ Ico (0 : ℝ) 1, tsupport (fun y : Space ↦ data.packetVelocity (s, y)) ⊆ data.carrier) :
    ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data), ∀ t ∈ Ico (0 : ℝ) data.place.T,
      tsupport (fun x : Space ↦ velocity data ε (t, x) - data.reference.velocity (t, x)) ⊆
        periodicSet (Metric.ball data.place.x₀ (ε * diffSupportRadius data))
```
(use `data.carrier` = the packet carrier `K` if that is the clause the T15 placement theorems consume — `carrier_subset : K ⊆ Kstar` then gives the `Kstar` form; pick whichever the probe's proof
needs and say why). The conclusion must stay token-identical to the Spec field under the `InsertionData` projections. In the probe, discharge `hsupp` from the Spec's `PacketImportAPI.velocity_support`
(the registered `Contracts/V1/PacketImport.lean` field — read its exact text; the probe may import `Contracts.*`), so that the Spec-form field `velocityDifference_support` is closed from the canonical
theorem with no residual. Document the ruling in `ATTEMPTS_U7.md`/`REPORT_435.md` ("explicit raw premise; U12 assembly discharges it from `PacketImportAPI.velocity_support`; a later MAINT may add the
clause to `InsertionData`") and update the U7 status line in `T18_SPLIT.md`.

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; no edits to existing modules other than `Section3/T18/Support.lean` (your own lane's file) and the lane's research files. Every declaration prints exactly
  `[propext, Classical.choice, Quot.sound]`.

## Gates
`lake build NSFormalization.Section3.T18.Support` (0 errors), `lake env lean` on the module (0 output), `research/T18/probes/u7_closes.lean` (0 output, all four Spec fields closed), `research/T18/axioms_u7.lean`, `make check`.

## Report
Commit `[435-T18] U7: velocityDifference_support with the explicit raw support premise (lead ruling)`; end with four parts; append them to `research/T18/REPORT_435.md`.
