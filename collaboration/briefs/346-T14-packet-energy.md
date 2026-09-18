# Lane 346-T14-packet-energy — T14 `lem:packetenergy`: prove `packetImportStatement` and build `PacketImportFamily` from the registered ℝ³ packet

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/346-T14-packet-energy` (git branch `erenup/346-T14-packet-energy`,
based on `origin/erenup/integration-section3`). Read `CLAUDE.md` (hard rules; "合同 import 规则"; "结构体例外"),
**`research/T14/Spec.lean` (the reconciled statement — every target below is quoted from it), `research/T14/RECONCILIATION.md`,
`research/T14/COMPARISON.md`**, and the top 40 lines of `logs/LESSONS.md` first.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented.
  No edits to existing modules, `Contracts/V*`, `Tests/*`, `contracts.json`; new files only.
- **No placeholders, no aliases, no named inputs.** A `def Foo : Prop := <the goal>` or `theorem foo (h : <the goal>) : <the goal>`
  is a stub and will be discarded without review. Every theorem must be closed from Mathlib, the vendor packages and the
  tree. If something cannot be closed, deliver the rest and state the residual as a concrete lemma statement with the exact
  error text in `ATTEMPTS.md` — an honest partial is fine, a repackaged goal is not.
- Before claiming a lemma is "not in the tree", `grep -rn` `vendor/NavierStokesAndEuler/NavierStokes/R3/CompactEnergy.lean`,
  `formalization/NSFormalization/Section4/{I01,I02,C01}`, `formalization/NSFormalization/Paper1/ScalarEnergy.lean`.
  Before citing a paper line, `sed -n` it (`paper/sections/02-preliminaries.tex:127-153`, `01-introduction.tex:15-29`).
  Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.

## Goal (the two fields of `PacketEnergyAPI`, `research/T14/Spec.lean:62-99`, then the packaging `:101-134`)
For the registered packet `P : Contracts.V1.PacketAPI ν` (`verification/Contracts/V1/Packet.lean:171-320`; the witness is
`BlowupDensity.Bindings.packet ν hν`, `verification/Bindings/Packet.lean:104`, whose `l2Sq`/`dissipation` are `rfl`-equal to
`NavierStokesR3.CompactEnergy.l2Sq`/`dissipation`, `Bindings/Packet.lean:85-90`):
- `energy_le_work : ∀ t ∈ Ico 0 1, l2Sq P.velocity t + 2ν ∫_{Ioo 0 t} dissipation P.velocity ≤ 2 ∫_{Ioo 0 t} √(l2Sq P.force s) · accumulatedForce P.force s`
- `work_eq_square : ∀ t ∈ Ico 0 1, 2 ∫_{Ioo 0 t} √(l2Sq P.force s) · accumulatedForce P.force s = (accumulatedForce P.force t)^2`
with `accumulatedForce F t := ∫ s in Ioo 0 t, √(l2Sq F s)` (`Spec.lean:52`), and then `packetImportStatement : ∀ ν, 0 < ν → Nonempty (PacketImportAPI ν)`
plus a term of `PacketImportFamily`.

Route (all pieces exist): the energy balance on the packet's compact support —
`NavierStokesR3.CompactEnergy.energy_balance` / `hasDerivAt_energy_balance` / `l2Sq_continuousOn` / `uniform_finite_energy`
(`vendor/NavierStokesAndEuler/NavierStokes/R3/CompactEnergy.lean:202-360`; check their exact hypotheses against the `PacketAPI`
clauses `velocity_smooth`, `velocity_support`/`carrier_compact`, `navier_stokes`, `divergence_free`, `force_smooth`) gives
`d/ds l2Sq u s = −2ν·dissipation u s + 2⟪f(s),u(s)⟫` on `(0,1)`; `l2Sq u 0 = 0` (`zero_initial_velocity`); Cauchy–Schwarz
`⟪f,u⟫ ≤ √l2Sq f · √l2Sq u`; and `√(l2Sq u s) ≤ accumulatedForce f s` from `Paper1/ScalarEnergy.lean:77`
`sqrt_energy_le_primitive` (the `E' ≤ 2 b √E ⇒ √E ≤ N` lemma; `N' = b = √(l2Sq f ·)` is continuous because `f` is smooth with
compact space-time support — `CompactEnergy.l2Sq_continuousOn`). Integrate over `[0,t]` (`intervalIntegral` ↔ `∫ in Ioo 0 t`:
`intervalIntegral.integral_of_le` + `integral_Ioc_eq_integral_Ioo`). `work_eq_square` is the FTC for `N²` with `N(0)=0`
(`intervalIntegral.integral_eq_sub_of_hasDerivAt` on `fun s => N s ^ 2`, derivative `2 N' N`).

## Deliverables
1. New module `formalization/NSFormalization/Section3/T14/PacketEnergy.lean` (namespace `NSFormalization.Section3.T14`).
   `formalization/` must NOT import `Contracts.*`, so state everything over the raw packet fields
   (`u f : VelocityField`, `p : PressureField`, `ν`, and hypotheses that are **verbatim** the `PacketAPI` clauses you use — nothing
   stronger), using the vendor's `NavierStokesR3.CompactEnergy.l2Sq`/`dissipation`; `def accumulatedForce` verbatim from the Spec;
   theorems `energy_le_work_of_packet` and `work_eq_square_of_packet` with exactly the two conclusions above.
2. Probe `research/T14/probes/api_on_canonical.lean` (checked with `cd verification && lake env lean ../research/T14/probes/api_on_canonical.lean`):
   imports `Contracts.V1.Packet`, `Bindings.Packet` and your module; restates `accumulatedForce`, `PacketEnergyAPI`, `PacketImportAPI`,
   `packetImportStatement`, `PacketImportFamily` **token-for-token from `research/T14/Spec.lean`** (only the namespace changes), proves
   `accumulatedForce = <your module's>` by `rfl`, and closes `theorem packetImport : packetImportStatement` and
   `def packetImportFamily : PacketImportFamily` via `BlowupDensity.Bindings.packet ν hν` + your theorems. Include a non-vacuity
   `example` (e.g. that `(packetImportFamily.select ν hν).velocity` is the bound packet's velocity by `rfl`).
3. Records: `research/T14/ATTEMPTS.md` (routes tried, exact residuals if any), conformance `research/T14/axioms_packet_energy.lean`
   (`#print axioms` of every new declaration), update `research/T14/COMPARISON.md` (status section), report `research/T14/REPORT_346.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T14.PacketEnergy` (0 errors), `lake env lean` on the module
(0 output), on the probe (only its `#print axioms` lines), on the axioms file; `make check` from the worktree root.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with exact error text / commands run and
results). Also write it to `research/T14/REPORT_346.md`.
