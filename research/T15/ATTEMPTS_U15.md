# T15 U15 — assembly attempts

## Successful construction

The equation probe's cube centre `(1/2,1/2,1/2)` and radius `3/8`
work unchanged. For compact `Kstar = K ∪ Prod.snd '' tsupport f`, choose
`R > 0` bounding every spatial norm and set
`ε₀ = min (min (1/2) (T/4)) (1/(8*(R+1)))`.
Then `2*ε² ≤ ε ≤ T/4 < T`, and the spatial displacement is less than
`3/8`. Both canonical and contract placement preserve `T` by `rfl`.

The 21-field assembly uses the union of 16 raw clauses:

1. Past-zero velocity smoothness on `Iio 1 ×ˢ univ`.
2. Compact velocity/pressure carrier.
3. Velocity slice support on `Ico 0 1`.
4. Square integrability of velocity slices on `Ico 0 1`.
5. Zero initial velocity.
6. Exact energy `IsLUB`.
7. Integrable dissipation on `Ioo 0 1`.
8. Exact dissipation constant as the square root of its integral.
9. Pressure slice support on `Ico 0 1`.
10. Past-zero pressure smoothness on `Iio 1 ×ˢ univ`.
11. Global force smoothness.
12. `CompactPositiveTimeSupport` of force.
13. Force vanishing at nonpositive times.
14. Extended momentum equation for every `t < 1`.
15. Extended incompressibility for every `t < 1`.
16. `SpeedUnboundedAtOne`.

Clauses 1–8 are carried by the already proved I03 `PacketData` record.
`scalingStatement_holds` accepts the unchanged canonical full hypothesis
list and builds that subrecord. The registered statement quantifies every
`PacketImportFamily`, positive viscosity and existing placement, with no
additional premises. The probe explicitly restates the raw clauses at the
registered I01 packet. Full `q=1,2` convergence uses `ConvergenceTwo`.

## Resolved elaboration errors

- Initial geometry generalization gave `Unknown identifier hK.union`:
  theorem section variables used only in the proof need `include hK hf`.
  The positivity theorem likewise explicitly includes `hT`.
- Importing both `Bindings.PacketImport` and `Bindings.Scaling` failed with
  `environment already contains BlowupDensity.Bindings.navierStokesResidual_eq`.
  Those existing bindings independently declare that name. Removed the
  unnecessary Euclidean binding import and built the eight-field energy
  subrecord directly from the packet. No existing module was edited.
- A non-vacuity `rw` could not match the horizon projection against `T`
  across the packet-indexed placement. An explicit `change` to the
  definitionally equal horizon in the norm hypothesis fixes the match.

## Final validation

All resolved; no mathematical gap, extra assumption, omitted field, or
nonstandard axiom. See REPORT_459.md for gate output and all 68 axiom lines.
