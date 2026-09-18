# Lane 387 — T22 · U-A4 — order-0 vector Plancherel isometry

## 1. What was proved (theorems, exact statements)

New module `formalization/NSFormalization/Section3/T22/OrderZeroIsometry.lean`
(namespace `NSFormalization.Section3.T22`), all with commented `set_option maxHeartbeats 400000 in`:

- **Target (U-A4):**
  `theorem norm_orderZeroDatum_eq {z : Space → Space} (hz : MemLp z 2 volume) :`
  `    ‖orderZeroDatum hz‖ₑ = eLpNorm z 2 volume`
  (`orderZeroDatum` and `eLpNorm` are the exact `D01`/Mathlib spellings). This is the identity
  `Section4/D01/OrderZeroDatum.lean` explicitly leaves open ("the norm identity is NOT proved here").

- **Vector isometry (the piece the brief asked to deliver):**
  `theorem cyclesToAngularRealVector_zero_norm (v : RealVectorSobolev (0 : ℝ)) :`
  `    ‖cyclesToAngularRealVector 0 v‖ = ‖v‖`

- **Supporting lemmas:**
  `cyclesToAngularReal_zero_norm (h : RealSobolevHilbert (0:ℝ)) : ‖cyclesToAngularReal 0 h‖ = ‖h‖`
  `cyclesToAngular_zero_norm (g : SobolevHilbert (0:ℝ)) : ‖cyclesToAngular 0 g‖ = ‖g‖`
  `norm_coe_realSobolev (h : RealSobolevHilbert (0:ℝ)) : ‖h‖ = ‖(h : FourierData)‖`  (`rfl`)
  `coe_cyclesToAngularReal_zero (h : RealSobolevHilbert (0:ℝ)) :`
  `    (cyclesToAngularReal 0 h : FourierData) = cyclesToAngular 0 (h : FourierData)`  (`rfl`)

All six declarations print exactly `[propext, Classical.choice, Quot.sound]`. No `sorry`/`admit`/`axiom`/
`native_decide`, no named inputs, no placeholder/alias definitions, no goal repackaging.

Mathematical route (all at `s = 0`, where `frequencyUnit ^ |0| = 1`): the pipeline
`orderZeroDatum hz = cyclesToAngularRealVector 0 (WithLp.toLp 2 (i ↦ realProjectionTo 0 (𝓕 (componentLp hz i))))`
is an isometry — vector transport is norm-preserving (`cyclesToAngularRealVector_zero_norm`), each
`𝓕 (componentLp hz i)` is conjugate-symmetric so `realProjectionTo 0` is the identity
(`realProjection_eq_self` + `D01.fourier_componentLp_mem`), and `Lp.norm_fourier_eq` (Plancherel) gives
`‖𝓕 (componentLp hz i)‖ = ‖componentLp hz i‖`; the Euclidean Pythagoras identity
`D01.norm_toLp_component_sq_sum` reassembles `∑ᵢ ‖componentLp hz i‖²` into `‖hz.toLp‖²`, and
`Lp.enorm_toLp` identifies `‖hz.toLp‖ₑ` with `eLpNorm z 2 volume`.

## 2. What exists in Lean now (files)

- `formalization/NSFormalization/Section3/T22/OrderZeroIsometry.lean` — the module (builds clean).
- `research/T22/probes/orderzero_isometry_closes.lean` — non-vacuity: a nonzero `ContDiffBump` field
  `z : Space → Space` (bump × `coordinateVector 0`), smooth + compact support ⇒ `MemLp z 2 volume`,
  nonzero at the centre; `probe_closes` gives the identity with both sides `< ⊤`.
- `research/T22/axioms_ua4.lean` — `#print axioms` audit of all six declarations.
- `research/T22/ATTEMPTS_UA4.md` — positive/negative examples (below), heartbeat findings.
- `research/T22/T22_SPLIT.md` — U-A4 marked DONE.

Reused unchanged (no edits to existing modules): `Section4/D01/FiniteOrderNorm.lean`
(`norm_toLp_component_sq_sum`, `eLpNorm_component_sq_sum`, `norm_orderZeroDatum_le`),
`Paper3` (`cyclesToAngular_norm_le`/`_symm_norm_le`, `cyclesToAngularRealVector_apply`,
`realProjectionTo`), `Source.RealSobolev` (`realProjection_eq_self`), Mathlib
(`Lp.norm_fourier_eq`, `Lp.enorm_toLp`, `ofReal_norm`, `PiLp.norm_sq_eq_of_L2`,
`ContinuousLinearEquiv.ofSubmodules_apply`).

## 3. Gaps

None for U-A4 itself: `norm_orderZeroDatum_eq` is proved verbatim and is the D01-open identity.

Downstream (out of this lane's scope): U-A4 is consumed by **U-A5** (`orderZero`,
`Section3/T22/OrderZero.lean`), which additionally needs the `L²(Ω)` quotient/restriction identity and the
`⊤ = ⊤` off-`L²(Ω)` edge (see `T22_SPLIT.md`). Those are not this deliverable.

One process note recorded for the reviewer: the closed-subspace `cyclesToAngularReal` `symm` bound
overflows even the 400000 per-declaration cap; the module deliberately routes through the plain-`Lp`
`cyclesToAngular` and two `rfl` coercion bridges to stay inside 400000 (details in ATTEMPTS_UA4.md).

## 4. Commands run and results

All from the worktree with `. scripts/lean-env.sh`, `lake` from `verification/`, `LEAN_NUM_THREADS=6`:

- `lake build NSFormalization.Section3.T22.OrderZeroIsometry`
  → `✔ Built NSFormalization.Section3.T22.OrderZeroIsometry`; `Build completed successfully (9928 jobs).`
- `lake env lean ../research/T22/axioms_ua4.lean`
  → each of the six declarations: `depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `lake env lean ../research/T22/probes/orderzero_isometry_closes.lean` → no errors;
  `T22Probe.probe_closes` also `depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `make check` → contract policy 13 tests `OK`; architecture checks pass;
  `45 work items: ownership, contract registration and task cards consistent.`

### Heartbeat measurements (why the route is what it is)
- forward subspace bound alone: passes at 400000.
- reverse (`symm`) subspace bound alone: `(deterministic) timeout at whnf/isDefEq` at 400000 — FAILS.
- plain-`Lp` isometry (`cyclesToAngular_zero_norm`) + the two `rfl` bridges: each passes at 400000.
- composed scalar/vector isometry + main theorem: all pass at 400000.
