# Lane 392 — T24 Uc1 + Ua1 report

## 1. What was proved

Uc1 is closed verbatim: every positive-viscosity canonical periodic classical
solution from rest, forced by the negative gradient of a globally smooth
unit-periodic potential, has zero velocity at every `(t,x)` with `t∈[0,T)`.

Ua1's five fields are closed over raw whole-space packet fields: positive
radius, the strict window `0<τ₀<τ₁<1`, zero initial affine velocity, agreement
with the packet after `τ₁`, and injectivity of `b ↦ U+b`.

## 2. What Lean contains now

- `Section3/T24/Conservative.lean`: the canonical definitions
  `PeriodicPotentialT`, `conservativeForceT`, and theorem `zero_from_rest`,
  proved via `Paper1.ConservativeForce.zero_of_negative_gradient_on_Ico`.
- `Section3/T24/AffineBasics.lean`: canonical raw-field affine vocabulary and
  the five Ua1 theorems `radius_pos`, `window`, `zero_initial`,
  `late_agreement`, and `distinct`.
- `probes/uc1_ua1_closes.lean`: registered-spelling closure, including the
  contract/canonical `ClassicalSolutionT` conversion and
  `Bindings.packet ν hν` for the whole-space raw fields.
- `axioms_uc1_ua1.lean`: every new declaration prints exactly
  `[propext, Classical.choice, Quot.sound]`.

## 3. Remaining gap

This lane proves exactly Uc1 and Ua1.  T24c still needs Uc2
`potential_pairing` before its API can be assembled.  T24a still needs Ua2-Ua8
(divergence, momentum expansion, force smoothness/support, blow-up transfer,
energy finiteness, infinite dimensionality, and non-isolation) before its
13-field API and existence statement can be assembled.  No placeholder or
named assumption was added for those later fields.

## 4. Commands and results

All commands were run after `. scripts/lean-env.sh`, with Lake only from
`verification/`:

- `LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T24.Conservative NSFormalization.Section3.T24.AffineBasics`
  — success, 0 errors.
- `lake env lean` on both modules, the probe, and the axiom audit — success;
  the probe has 0 warnings after its final cleanup.
- `make check` — success.
- forbidden-token scan — no `sorry`, `admit`, `axiom`, or `native_decide` in
  the delivered Lean modules/probe.
