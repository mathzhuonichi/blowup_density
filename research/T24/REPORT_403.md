# Lane 403 — T24a Ua5 report

## 1. Theorem with exact statement

The new canonical raw-field theorem is:

```lean
theorem speed_unbounded {U : VelocityField} (c : Space) (r τ₀ τ₁ : ℝ)
    (hτ₁ : τ₁ < 1) (hspeed : SpeedUnboundedAtOne U) :
    ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b →
      SpeedUnboundedAtOne (affineVelocity U b)
```

The conclusion is the `AffineVariationAPI.speed_unbounded` field with
`P.velocity` replaced by the raw `U`.  `AffineAdmissible` does not carry
`τ₁ < 1`: it contains only global smoothness, compact support, cylinder support,
and pointwise zero divergence.  The extra geometric hypothesis `hτ₁` is
therefore necessary.  The only packet clause assumed is the raw
`SpeedUnboundedAtOne U`.

The proof calls `hspeed` with `min δ (1 - τ₁)`.  The resulting witness lies
past `τ₁`, so Ua1's `late_agreement` rewrites the affine velocity to `U` at that
point while retaining the requested `1 - δ < t` inequality.

## 2. Files

- `formalization/NSFormalization/Section3/T24/AffineSpeed.lean` — canonical
  Ua5 theorem, importing `AffineBasics` and reusing `late_agreement`.
- `research/T24/probes/affine_speed_closes.lean` — exact registered-spelling
  field closure on `BlowupDensity.Bindings.packet ν hν`, plus a concrete
  `b = 0` admissibility-and-blowup example.
- `research/T24/axioms_ua5.lean` — axiom audit; the theorem prints exactly
  `[propext, Classical.choice, Quot.sound]`.
- `research/T24/ATTEMPTS_UA5.md` — source quantifiers, necessity of `hτ₁`, proof
  route, and probe iteration.
- `research/T24/T24_SPLIT.md` — Ua5 and W3 status updated to lane 403 done.
- `research/T24/REPORT_403.md` — this four-part report.

## 3. Gaps and error text

There is no remaining Ua5 gap and no named input was introduced.  Ua4 and Ua6
remain separate units and are outside this lane.

One transient probe import error was resolved without changing the canonical
proof:

```text
error: unknown namespace `NSFormalization.Section4.A02`
```

The registered `SpaceTimeField` spelling lives in `Contracts.V1.Data` for this
probe's import closure; importing that module made the raw/contract bridge
definitionally exact.  All final gate invocations have zero errors.

## 4. Commands and results

All Lean commands ran after `. scripts/lean-env.sh`; Lake ran only from
`verification/`, with `LEAN_NUM_THREADS=6`.

- `lake build NSFormalization.Section3.T24.AffineSpeed` — success, 3007 jobs,
  0 errors.
- `lake env lean ../formalization/NSFormalization/Section3/T24/AffineSpeed.lean`
  — success, 0 output.
- `lake env lean ../research/T24/probes/affine_speed_closes.lean` — success,
  0 output.
- `lake env lean ../research/T24/axioms_ua5.lean` — success; output exactly
  `'NSFormalization.Section3.T24.speed_unbounded' depends on axioms:
  [propext, Classical.choice, Quot.sound]`.
- `make check` — success: formalization plan check completed, 42 registered
  contracts passed architecture checks, 13 contract-policy tests passed, and
  45 work items were consistent.
- `git diff --check` — success, 0 output.

