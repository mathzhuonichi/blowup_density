# Lane 402 — T24 Ua2 divergence-free report

## 1. Theorem with exact statement

The canonical raw-field theorem is:

```lean
theorem divergence_free {U : VelocityField} (c : Space) (r τ₀ τ₁ : ℝ)
    (hvelocity_smooth : ContDiffOn ℝ ∞ U preSingularDomain)
    (hdivergence : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space,
      spatialDivergence U t x = 0) :
    ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b →
      ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space,
        spatialDivergence (affineVelocity U b) t x = 0
```

The divergence hypothesis is token-identical to the raw packet clause, and
the conclusion is token-identical to `Spec.lean:1038-1040` after replacing
`P.velocity` by raw `U`.  The smoothness premise is necessary for the vendor
additivity lemma's pointwise differentiability hypothesis.

## 2. Files

- `formalization/NSFormalization/Section3/T24/AffineDivergence.lean` proves Ua2
  using `ResidualCalculus.spatialDivergence_add` and the two raw solenoidal
  clauses.
- `research/T24/probes/affine_divergence_closes.lean` checks the reconciled
  registered spelling on `Bindings.packet nu hnu`, including the three `rfl`
  vocabulary bridges and a `b = 0` non-vacuity example.
- `research/T24/axioms_ua2.lean` audits the new theorem.
- `research/T24/ATTEMPTS_UA2.md` records why raw packet smoothness remains an
  input.
- `research/T24/T24_SPLIT.md` marks Ua2 done.

## 3. Gaps

No Ua2 proof gap remains and no named input was introduced.  This lane does
not assemble the full 13-field `AffineVariationAPI`; Ua3-Ua8 and the Ua9
assembly remain separate units.

## 4. Commands and results

All commands were run after `. scripts/lean-env.sh`, with Lake only from
`verification/` and build parallelism set to `LEAN_NUM_THREADS=6`:

- `lake build NSFormalization.Section3.T24.AffineDivergence` — success, 0 errors.
- `lake env lean` on the module — success, 0 output.
- `lake env lean` on the probe — success, 0 output.
- `lake env lean` on the axiom audit — success; exactly
  `[propext, Classical.choice, Quot.sound]`.
- `make check` — success (exit 0).  Its informational formalization-plan
  output retains the pre-existing copied-source `BoundaryCorollary.lean`
  admission notice and `source_hashes_match: false`; this lane neither imports
  nor modifies that module.
