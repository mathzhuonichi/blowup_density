# REPORT 376 — T15 U2 scaled-support placement (r2)

Lane `376-T15-U2-placement`. Module
`formalization/NSFormalization/Section3/T15/Placement.lean`
(namespace `NSFormalization.Section3.T15`), 16 declarations, all
`[propext, Classical.choice, Quot.sound]`. This report supersedes the r0/r1
drafts.

## 1. What was proved

`prop:scaling` placement, `paper/sections/03-torus.tex:101-120`: the rescaled
packet velocity, pressure and force each have their spatial slices supported in
the single copy `x₀ + ε·K_* ⊆ B ⊆ interior Q`, with compact slice support —
proved from the **raw `PacketAPI` support clauses**, over the exact time domains
of the U3 consumers.

## 2. What is in Lean (exact final statements)

Shared implicit data: `u : VelocityField`, `p : PressureField`,
`f : VelocityField`, `x₀ chartCenter : Space`, `T ε ε₀ chartRadius : ℝ`,
`carrier Kstar : Set Space`.

- `scaledVelocity_tsupp_subset (hε : 0 < ε) (hcarrier_compact : IsCompact carrier)`
  `(hvel : ∀ t ∈ Ico 0 1, tsupport (fun x => u (t,x)) ⊆ carrier)`
  `(hcarrier_subset : carrier ⊆ Kstar) {t} (ht : t < T) :`
  `tsupport (fun x => scaledVelocity u x₀ T ε (t,x)) ⊆ (fun y => x₀ + ε • y) '' Kstar`.
  Domain **`t < T`**, matching `velocity_singleCopy` (`research/T15/Spec.lean:704-710`).
- `scaledPressure_tsupp_subset` — identical shape with `hpre` (pressure_support)
  and `scaledPressure`; domain **`t < T`**, matching `pressure_singleCopy`
  (`research/T15/Spec.lean:715-718`).
- `scaledForce_tsupp_subset (hε : 0 < ε) (hKstar_compact : IsCompact Kstar)`
  `(hf : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)`
  `(hforce_proj : ∀ t x, (t,x) ∈ tsupport f → x ∈ Kstar) (t : ℝ) :`
  `tsupport (fun x => scaledForce f x₀ T ε (t,x)) ⊆ (fun y => x₀ + ε • y) '' Kstar`.
  Domain **every `t`**, matching `force_singleCopy` (`research/T15/Spec.lean:726-731`).
  The hypothesis is the **verbatim** packet clause `CompactPositiveTimeSupport f`,
  used honestly through `Source.PacketScaling.parabolicForce_support hf.1`.
- `scaledVelocity_slice_eq_zero` / `scaledPressure_slice_eq_zero` (`t ≤ T-ε²`):
  the pre-activation slice is identically zero
  (`Source.PacketScaling.zeroPast_dilate_early`).
- `tsupport_subset_of_slice_zero` — an identically-zero slice has empty `tsupport`.
- `affineImage_compact`, `affineImage_subset_ball` (from `eps_space`),
  `ball_subset_interior_cube` (from `chartBall_in_cube`).
- `scaled{Velocity,Pressure}_slice_hasCompactSupport` (`t < T`),
  `scaledForce_slice_hasCompactSupport` (every `t`): `HasCompactSupport` of each slice.
- `scaled{Velocity,Pressure}_slice_subset_cube` (`t < T`),
  `scaledForce_slice_subset_cube` (every `t`): slice `⊆ interior fundamentalCube`.

Route for velocity/pressure: for `t ≤ T-ε²` the source time is nonpositive and
the zero-past extension makes the slice zero; for `T-ε² < t < T` the source time
lies in `(0,1)`, so `Source.PacketScaling.parabolic_support` / `dilate_support`
transport the support to `scaledSupport ε⁻¹ x₀ carrier = (fun y => x₀+ε•y) ''
carrier` (via `inv_inv`), and `Set.image_mono carrier_subset` lifts to `K_*`. No
`eps_time` hypothesis is needed for this range: `(ε⁻¹)²·ε² = 1` gives the source
time `< 1` directly.

### Probes

- `research/T15/probes/placement_closes.lean` — explicit geometric instance
  (permitted fallback): nonzero `ContDiffBump` velocity/pressure with spatial
  support `closedBall 0 (1/4) = Kstar = carrier`, centre `x₀ = chartCenter =
  (1/2,1/2,1/2)`, chart radius `3/8`, `ε₀ = 1`, `T = 1`. It proves the geometry
  (`pc_chartBall_in_cube`, `pc_eps_space`), fires the velocity cube and compact-support
  lemmas and the pressure cube lemma at the **active** time `t = 7/8` (`t_ε = 3/4 <
  7/8`), and exhibits a genuinely nonzero velocity slice there.
- `research/T15/probes/rev376_contract_shape.lean` (reviewer) — passes the
  verbatim `CompactPositiveTimeSupport f` clause to `scaledForce_tsupp_subset`;
  now typechecks (was the reviewer's reproducing error).
- `research/T15/probes/rev376_honest_nonvacuity.lean` (reviewer) — concrete bump,
  nonzero velocity slice at `t = 7/8`, lane theorem applied there.
- `research/T15/probes/rev376_nonvacuity.lean` (reviewer, r1) — same bump; final
  example is the pre-activation zero-slice case (`t = 1/2 < 3/4`).
- `research/T15/probes/rev376_negative.lean` (reviewer) — doubled-scale mutation;
  fails (`ε` vs `2ε` image).
- `research/T15/axioms_u2.lean` — audits all 16 declarations.

## 3. Gap

Force `HasCompactSupport` is genuinely used (through `parabolicForce_support`),
so no dead binder remains. The one thing not done here: constructing a
`PlacementData` inhabitant for the abstract selected packet `Bindings.packet ν
hν` (choosing `K_*`, chart ball, `ε₀` covering that packet's carrier) is unit
**U15**, gated on T13.localization; `placement_closes` uses an explicit concrete
packet with explicit numbers instead. `PlacementData` itself
(`BlowupDensity.T15.Draft.PlacementData`, `research/T15/Spec.lean`) lives in a
research spec file that `formalization/` and probes cannot import, so the module
lemmas restate its geometric fields as hypotheses verbatim.

## 4. Commands and results

All after `. scripts/lean-env.sh`; every `lake` from `verification/` with
`LEAN_NUM_THREADS=6`.

- `lake build NSFormalization.Section3.T15.Placement` → built, 0 errors, 0
  warnings in the module.
- `lake env lean` on `Placement.lean` → 0 output.
- `lake env lean ../research/T15/axioms_u2.lean` → 16 declarations, each exactly
  `[propext, Classical.choice, Quot.sound]`.
- `lake env lean` on `probes/placement_closes.lean`,
  `probes/rev376_contract_shape.lean`, `probes/rev376_honest_nonvacuity.lean`,
  `probes/rev376_nonvacuity.lean` → 0 output (EXIT 0); on
  `probes/rev376_negative.lean` → EXIT 1 (expected `ε` vs `2ε` mutation mismatch).
- `make check` → OK (contract policy 13 tests, work queue consistent).
