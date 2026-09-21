# P21 / P6 Route B split

Status: **P6 remains Partial.**  This file tracks the preferred smooth-data,
fixed-force Route B from `ASSESSMENT.md` §3.  Closing B0 supplies norm and force
bridges; it does not prove H¹-uniform restart or either endpoint target.

| Unit | Exit condition | Size / model | Status |
|---|---|---|---|
| B0 | Reconcile H¹/H² Fourier norms with derivative energy and state shifted-force cap | M / sol | **Closed — lane 503.** Exact identities and finite caps on both domains; targets type-checked in `Targets.lean`. |
| B1 | General (no critical smallness) enstrophy interpolation/Young inequality on R³ | L / astra | Pending |
| B2 | Periodic version including mean and ordinary L² energy | L / astra | Pending |
| B3 | Uniform ODE barrier, integrated dissipation, endpoint monotone limit | M–L / astra | Pending |
| B4 | Maximal-lifespan contradiction, smooth common-interval restriction, regularity and pressure adapters | M / sol | Pending |
| B5 | Uniform restartBeyond and registration/audits | M / sol | Pending |

## B0 output

- `Section4/A04/H1Bridges.lean`: exact whole-space H¹/H² identities and the
  finite compact-window force cap.
- `Section3/T11/H1Bridges.lean`: exact periodic H¹/H² identities, the finite
  cap, and the smooth/periodic package for shifted forces.
- `Targets.lean`: `h1RestartR`, `h1RestartT`, `h1UniformEndpointR`, and
  `h1UniformEndpointT` as unproved `Prop` definitions in registered vocabulary.

## Remaining acceptance risks

- B1/B2 must prove the general cubic enstrophy inequality without importing
  the critical-smallness absorption from T20.
- B3 must choose the barrier time before restart time and datum, retain the
  inhomogeneous low modes, and justify endpoint integrability by monotone
  limits.
- B4 must argue through the already constructed smooth maximal solution; it
  must not infer a lower bound for the selected high-order local horizon.
- On the torus, B3/B4 may use B0's shifted smoothness, periodicity, and common
  `L²` cap, but not shifted membership in `forceClassT`.
- B5 remains responsible for the actual H¹ restart/endpoint theorems and any
  ensuing contract, binding, test, graph, guide, or registry decision.

**B0 note (review 503):** B0 proves compact-core R³ identities with κ=1; B1 consumption still needs support-free/carrier adapters and specialization of `enstrophy_differential_of_norm_bridges` at κ=1, not its fixed (2π)⁻² wrapper (done by lane 507, `H1BridgesSmooth.lean`).
