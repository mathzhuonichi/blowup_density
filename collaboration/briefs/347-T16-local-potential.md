# Lane 347-T16-local-potential — T16 `lem:potential`: prove `localPotentialStatement` (cutoffs, radial vector potential, divergence-free periodic correction, `eq:bgzero`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/347-T16-local-potential` (git branch `erenup/347-T16-local-potential`,
based on `origin/erenup/integration-section3`; canonical T10 modules `formalization/NSFormalization/Section3/T10/{PeriodicData,PhysicalBridge,DatumBasics,...}.lean`).
Read `CLAUDE.md` (hard rules; "结构体例外"), **`research/T16/Spec.lean` (the reconciled statement — the target is `localPotentialStatement`,
`Spec.lean:320-338`, over `CutoffData` `:96` and `LocalPotentialAPI` `:145-318`), `research/T16/RECONCILIATION.md`, `research/T16/COMPARISON.md`**,
`paper/sections/03-torus.tex:163-215` (`lem:potential` and its proof), and the top 40 lines of `logs/LESSONS.md` (**name every instance
explicitly**; no anonymous `local instance`).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented.
  No edits to existing modules; new files only (a `Section3/T16/` directory of several modules is fine).
- **No placeholders, no aliases, no goal repackaging.** At most ONE exactly-stated named input is allowed for the whole lane, and only if
  it is a concrete analytic lemma (state it as a `theorem`-shaped hypothesis with its own docstring and the exact reason it is open);
  a `def X : Prop := <goal>` or a hypothesis equal to a target field is a stub and will be discarded without review. An honest partial
  (some fields closed, the rest as concrete lemma statements with error text) is acceptable; a repackaged goal is not.
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Section4/I02/{Reference,Prescribed,Support}.lean`
  (`exists_local_truncation`, `timePotential_contDiffOn`, `spatialCurl_timePotential_on`, `exists_prescribed_cutoff` — the ℝ³ proof of the
  same lemma, which `RECONCILIATION.md` says is reusable verbatim for the local part), `Section4/I02/*.lean`, `Section3/T10/*.lean`, and
  `vendor/NavierStokesAndEuler/NavierStokes/PeriodicLocalization.lean`. Before citing a paper line, `sed -n` it.
  Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.

## Goal
`localPotentialStatement` verbatim (`Spec.lean:328-336`): for `v U : SpaceTimeField`, compact `K`, `x₀`, `0 < r < 1/2`, `0 < T`, `0 < δ`,
`v` periodic on `univ`, smooth and divergence-free on `Ioo 0 (T+δ) ×ˢ ball x₀ r`, `U` spatially supported in `K` for `t ∈ Ioo 0 1`:
`∃ D : CutoffData, LocalPotentialAPI v U K x₀ r T δ D`. Every field of `LocalPotentialAPI` is quoted in the Spec with its paper line;
the mathematics is `03-torus.tex:176-192`: Urysohn cutoffs `θ` (space, `= 1` on an open plateau ⊇ `K`, support in `ball 0 θRadius`) and
`η` (time, `= 1` on `[-1,1]`, support in `(-2,2)`), the threshold `ε₀` making `2ε² < min T δ` and `ε·θRadius < r`, the radial vector
potential `A` with `∇×A = v` on the chart cylinder (`potential_formula`/`potential_curl` — the ℝ³ construction of I02 `Reference.lean`),
the correction `w_ε = −∇×(η_ε θ_ε A)` rescaled and placed at `x₀` (`correction_formula`), which is smooth, periodic, divergence-free
(curl of a smooth compactly supported field), supported in the `ε`-cylinder / in `ball x₀ r` (`correction_support*`), and cancels the
background on the packet's support (`correction_cancels` = `eq:bgzero`). Periodicity: the correction has support inside one chart ball of
radius `r < 1/2` — check how the Spec spells `correction_periodic` (a periodized field via `periodicSet`/`latticeVector`, or plain
`IsPeriodicOn` of the field extended by zero) and prove exactly that spelling.

## Deliverables
1. Canonical module(s) `formalization/NSFormalization/Section3/T16/LocalPotential.lean` (+ optionally `Cutoffs.lean`; namespace
   `NSFormalization.Section3.T16`): the Spec's definitions (`latticeVector`, `periodicSet`, `periodicScaledPacket`, `correctedBackground`,
   `CutoffData`, `LocalPotentialAPI`) restated over the **canonical T10 vocabulary** (`Section3/T10/PeriodicData.lean`: `SpaceTimeField`,
   `SpatialField`, `IsPeriodicOn`, … — do not copy T10 definitions; import them; if the Spec's local copy differs textually, prove `rfl`
   equality in the probe), then `theorem localPotential : localPotentialStatement` (or the fieldwise constructor it needs).
2. Probe `research/T16/probes/api_on_canonical.lean` (`cd verification && lake env lean ../research/T16/probes/api_on_canonical.lean`):
   restates the Spec's definitions/structures **token-for-token** (namespace only), proves every restated `def` equals the module's by `rfl`,
   gives the fieldwise conversion `LocalPotentialAPI (Spec copy) ↔ (module)` for the structures (structure exception), and closes the
   Spec's `localPotentialStatement` from the module. Include a non-vacuity `example` (concrete `v = 0`, `U = 0`, `K = {0}` instance).
3. Records: `research/T16/ATTEMPTS.md`, conformance `research/T16/axioms_local_potential.lean`, update `research/T16/COMPARISON.md`
   (status), report `research/T16/REPORT_347.md`; if you find a Spec clause that is false or unprovable as stated, do not change the Spec —
   write the counterexample/obstruction in `research/T16/SPEC_ISSUES.md` and deliver the rest.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T16.LocalPotential` (0 errors), `lake env lean` on each module
(0 output), on the probe (only its `#print axioms` lines), on the axioms file; `make check` from the worktree root.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with exact error text / commands run and
results). Also write it to `research/T16/REPORT_347.md`.
