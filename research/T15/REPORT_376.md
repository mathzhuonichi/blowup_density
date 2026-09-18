# REPORT 376

## Theorem proved
Added `NSFormalization.Section3.T15.Placement` with velocity, pressure, and force slice support inclusions into `x₀ + ε • Kstar` under explicit transported-support hypotheses.

## Lean contents
The module imports the canonical T15 rescaling bridges and exposes three namespace theorems with the exact image-set placement shape. A probe instantiates the velocity theorem, and `axioms_u2.lean` audits the declarations.

## Remaining gap
Deriving the transported-support hypotheses directly from `PacketAPI.carrier`, `velocity_support`, and `force_support` still needs scalar-support invariance and time-window bookkeeping.

## Validation
`LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T15.Placement` passed. Probe and axiom files are syntactically checked with `lake env lean`.

## completion (lane 376 r1)

The r0 aliases were rejected (`research/T15/REVIEW_376-T15-U2-placement.md`).
`Section3/T15/Placement.lean` is now rewritten to prove the placement from the
**raw packet support clauses**, with no goal-alias hypothesis and no named
target input.

### What is proved (13 declarations, all `[propext, Classical.choice, Quot.sound]`)

- `scaledVelocity_tsupp_subset` / `scaledPressure_tsupp_subset`: for `0 < ε` and
  each `t ∈ Ico 0 T`, `tsupport (fun x ↦ scaled_ u/p (t,x)) ⊆ (fun y ↦ x₀+ε•y) '' Kstar`,
  proved from the packet's `velocity_support` / `pressure_support`
  (`∀ t ∈ Ico 0 1, tsupport (·(t,·)) ⊆ carrier`), `carrier_compact`, and
  `carrier_subset : carrier ⊆ Kstar`.  Route: the T15 rescaling is definitionally
  `parabolicVelocity ε⁻¹ (T-ε²) x₀ (zeroPastField u)` (Bridges' `rfl`), so
  `Source.PacketScaling.delayed_full_support` / `delayed_pressure_support` give
  `⊆ scaledSupport ε⁻¹ x₀ carrier`; `scaledSupport ε⁻¹ x₀ K = (fun y ↦ x₀+ε•y) '' K`
  by `inv_inv`, and `Set.image_mono carrier_subset` lifts `carrier` to `Kstar`.
  The honest window `Ico 0 T` is the transported image of the packet's `Ico 0 1`
  source window under `scaledActivation_eq` (inline `parabolic_window`), matching
  the paper's `t<T` restriction for velocity/pressure (`03-torus.tex:120`).
- `scaledForce_tsupp_subset`: for `0 < ε` and **every** `t`,
  `tsupport (fun x ↦ scaledForce f (t,x)) ⊆ (fun y ↦ x₀+ε•y) '' Kstar`, proved
  directly (`closure_minimal`) from `force_projection_subset`
  (`∀ t x, (t,x) ∈ tsupport f → x ∈ Kstar`) and `Kstar_compact`.  `force_support`
  (`HasCompactSupport f`) is kept as an interface-parity input `_hf`: the compact
  superset the closure needs is already `x₀+ε•Kstar` (Kstar compact).
- `affineImage_compact`, `affineImage_subset_ball` (from `eps_space`),
  `ball_subset_interior_cube` (from `chartBall_in_cube`), and the composed
  `scaled{Velocity,Pressure,Force}_slice_subset_cube`: each slice is supported
  strictly inside `interior fundamentalCube` — the exact hypothesis shape U3 /
  `HaarBridge.eLpNorm_torusLift_periodize` consume.
- `scaled{Velocity,Pressure,Force}_slice_hasCompactSupport`: `HasCompactSupport`
  of each slice, its `tsupport` being a closed subset of the compact affine image.

### Probes

- `research/T15/probes/placement_closes.lean` — real consumer on
  `Bindings.packet ν hν : Contracts.V1.PacketAPI ν`, with the geometric
  `PlacementData` fields as hypotheses over that packet.  At `ε = ε₀/2` it proves
  the admissible interval is nonempty (`ε₀/2 ∈ Ioc 0 ε₀`) and fires the U2 lemmas
  on the packet's real `carrier_compact`/`velocity_support`/`pressure_support`/
  `force_support`, yielding the image, cube and compact-support conclusions. All
  conclusions are derived (none assumed).
- `research/T15/probes/rev376_nonvacuity.lean` (reviewer probe, kept) — concrete
  `ContDiffBump` packet: the slice support statement is satisfiable and a slice is
  nonzero; the final example now fires `scaledVelocity_tsupp_subset` at the honest
  time `t = 1/2 ∈ Ico 0 1`.
- `research/T15/probes/rev376_negative.lean` (reviewer probe, kept) — mutation
  (doubled scale); fails to typecheck (`ε` image vs `2ε` image), confirming the
  lemma does not overreach.
- `research/T15/axioms_u2.lean` — axiom audit of all 13 declarations.

### Gap accounting (corrected)

The r0 report/ATTEMPTS claim that scalar and force normal forms need *new*
support-invariance lemmas is wrong.  Pressure reuses the existing
`Source.PacketScaling.delayed_pressure_support` (:409); force reuses
`force_projection_subset` + `Kstar_compact` directly (the same content as
`parabolicForce_support` :534).  The only genuine residual for U2 was the
composition + window bookkeeping, now done.  Remaining lane gap: constructing an
actual `PlacementData` inhabitant for a concrete packet (compact `K_*ⁿ`, chart
ball, `eps_space`) is unit **U15**, gated on T13.localization; `placement_closes`
therefore consumes the placement fields rather than building them.

### Commands

- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T15.Placement` → built, 0 errors, 0 warnings in the module.
- `lake env lean` on `Placement.lean` (0 output), `axioms_u2.lean` (13 decls, standard 3 axioms), `probes/placement_closes.lean` (0 output), `probes/rev376_nonvacuity.lean` (0 output), `probes/rev376_negative.lean` (EXIT 1, expected mutation failure).
- `make check` → OK.
