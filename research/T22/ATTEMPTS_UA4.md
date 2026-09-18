# T22 · U-A4 — `norm_orderZeroDatum_eq` — attempts / negative examples

Target: `‖D01.orderZeroDatum hz‖ₑ = eLpNorm z 2 volume` for `hz : MemLp z 2 volume`
(the order-0 Plancherel norm identity that `OrderZeroDatum.lean` leaves open).
Module: `formalization/NSFormalization/Section3/T22/OrderZeroIsometry.lean`.

## What worked

The pipeline `orderZeroDatum hz = cyclesToAngularRealVector 0 (WithLp.toLp 2 (i ↦ realProjectionTo 0 (𝓕 (componentLp hz i))))`
is an isometry chain at `s = 0`. Reused, unchanged:
- `Section4/D01/FiniteOrderNorm.lean`: `norm_toLp_component_sq_sum` (Euclidean Pythagoras
  `‖hz.toLp‖² = ∑ᵢ ‖componentLp hz i‖²`), `eLpNorm_component_sq_sum`, and the `≤`-half
  `norm_orderZeroDatum_le` (structure model).
- `Paper3.cyclesToAngular_norm_le` / `cyclesToAngular_symm_norm_le` (at `s=0`, `frequencyUnit^|0|=1`).
- `Source.RealSobolev.realProjection_eq_self` (identity on the real subspace) + `D01.fourier_componentLp_mem`.
- `MeasureTheory.Lp.norm_fourier_eq` (Plancherel), `Lp.enorm_toLp`, `ofReal_norm`, `PiLp.norm_sq_eq_of_L2`.

Everything is done in real norms then lifted to `ℝ≥0∞` at the last step (`hz : MemLp` makes both sides finite).

## Negative examples / what failed and why

1. **Direct subspace isometry with `symm` overflows 400000 heartbeats.**
   `cyclesToAngularReal_zero_norm` proved by `le_antisymm` where the reverse direction uses
   `cyclesToAngularReal_symm_norm_le 0 (cyclesToAngularReal 0 h)` + `ContinuousLinearEquiv.symm_apply_apply`.
   Measured: the FORWARD bound alone fits in 400000; the REVERSE (`symm`) bound on the closed real
   subspace `RealSobolevHilbert 0` times out — `(deterministic) timeout at whnf` / `isDefEq` at 400000.
   Root cause: `cyclesToAngularReal = ((cyclesToAngular s).restrictScalars ℝ).ofSubmodules …`; the
   `symm` unfolds the `ofSubmodules`/`restrictScalars` construction plus the subspace
   `NormedAddCommGroup`/`InnerProductSpace` instance diamond (the same heaviness
   `AngularRealVectorBochner.lean` handles by running the whole module at 800000, which is over the
   400000 per-declaration cap this lane is held to).

2. **`show`-ing the goal at the plain-`Lp` level also overflows.**
   `show ‖cyclesToAngular 0 (h : FourierData)‖ = ‖(h : FourierData)‖` on the subspace goal forces the
   same heavy `isDefEq` as (1) — a `show`/`change` re-checks defeq eagerly, so it is not lighter.

3. **Passing `PiLp.norm_sq_eq_of_L2 (β) (cyclesToAngularRealVector 0 v)` with explicit `x` overflows.**
   Supplying the applied term `cyclesToAngularRealVector 0 v` explicitly forces eager elaboration of the
   `PiLp`/`ofSubmodules` type. The existing `cyclesToAngularRealVector_norm_le` avoids this by
   `rw [PiLp.norm_sq_eq_of_L2]` (unification) + `change`; mirroring that form fixed it.

## The fix (fits 400000 per declaration)

Route the isometry through the plain-`Lp` transport, paying each heavy `isDefEq` once as an opaque lemma:
- `cyclesToAngular_zero_norm : ‖cyclesToAngular 0 g‖ = ‖g‖` — Lp-level (no subspace diamond), reverse `symm` is light here.
- `norm_coe_realSobolev : ‖h‖ = ‖(h:FourierData)‖` (`rfl`) and
  `coe_cyclesToAngularReal_zero : (cyclesToAngularReal 0 h : FourierData) = cyclesToAngular 0 (h:FourierData)`
  (`rfl`, via `ContinuousLinearEquiv.ofSubmodules_apply`) — each `rfl` checked once.
- `cyclesToAngularReal_zero_norm` then composes these three by `rw` (syntactic, cheap).
- `cyclesToAngularRealVector_zero_norm` lifts componentwise via `PiLp.norm_sq_eq_of_L2` (+ `change`).
Each declaration carries a commented `set_option maxHeartbeats 400000 in`.

## Non-vacuity

`research/T22/probes/orderzero_isometry_closes.lean`: a `ContDiffBump` centred at `0` (`rIn=1, rOut=2`)
times `coordinateVector 0`, smooth with compact support ⇒ `MemLp _ 2 volume`, nonzero at the centre;
`probe_closes` gives `‖orderZeroDatum _‖ₑ = eLpNorm z 2 volume` with both sides `< ⊤`.
All declarations, including the probe, print `[propext, Classical.choice, Quot.sound]`.
