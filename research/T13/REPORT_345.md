# REPORT 345 — T13 `torus_identity`

## 1. What was proved

`03-torus.tex:53-72` (the second display of the proof of `lem:localization`):
for `0 < s < 1` and every smooth unit-periodic vector field `f : R³ → R³`,

```
ITorus s f < ⊤  ∧  ITorus s f = cFrac s * periodicHomogeneousENorm s (meanZeroPartT f) ^ 2
```

i.e. `∫_Q ∫_Q |f(x)-f(y)|² K_s(x-y) = c_s ‖f - f̂(0)‖²_{Ḣ^s(T³)}` with the
paper's explicit constant `c_s = ∫_{R³} |e^{ih₁}-1|² |h|^{-3-2s} dh` and the
T10 weight `|2πk|^{2s}`.  This is the `torus_identity` field of the reconciled
`LocalizationAPI` (`research/T13/probes/api_on_canonical.lean`), copied
verbatim; nothing was weakened and no named input was introduced.

## 2. What is in Lean now

New module `formalization/NSFormalization/Section3/T13/TorusIdentity.lean`
(83 declarations, no `sorry`/`axiom`), in namespace
`NSFormalization.Section3.T13`.  The consumer-facing results are

- `torus_identity` — the API field, and `torus_identity_smooth` — the equality
  alone (no `s < 1` needed);
- `cFrac_lt_top` — `0 < s < 1 ⟹ c_s < ⊤` (the finiteness half of
  `constant_pos_finite`);
- `kernelIntegral_eq` — `∫_{R³} |e^{i⟨ξ,h⟩}-1|² K_s(h) dh = |ξ|^{2s} c_s`
  (the rotation/dilation identity), with `kernel_rotation`
  (= `kernelIntegral_isometry`) and `kernel_scaling` (= `kernelIntegral_smul`)
  as the two reusable halves;
- `periodicKernel_unfold` (= `lintegral_cube_periodicKernel`), plus the
  underlying tiling `lintegral_eq_tsum_halfOpenCube`,
  `fundamentalCube_ae_eq_halfOpenCube`, `lintegral_fundamentalCube_ofReal`;
- `periodicFourierCoeff_shift` — the Fourier translation rule;
- `exists_homogeneous_datum`, `homogeneousDatum_unique`,
  `periodicHomogeneousENorm_sq_smooth`,
  `periodicHomogeneousENorm_lt_top` — the T10 homogeneous datum of a smooth
  periodic mean-zero field and its norm, which T10 does not expose.

Probe `research/T13/probes/torus_identity_closes.lean` closes the API field by
`example` and adds the non-vacuity examples.  Conformance file
`research/T13/axioms_torus_identity.lean` prints the axioms of all 83
declarations.

## 3. Gaps

- The explicit numerical value of `ITorus` on the single mode
  `x ↦ cos(2π x₁) e₁` is not computed (see
  `research/T13/ATTEMPTS_TORUS_IDENTITY.md`, "Residual gap"); the probe
  instead evaluates both sides of the per-frequency identity at `k = e₁` and
  instantiates the theorem at that nonconstant mode.
- `0 < cFrac s` (the other half of `constant_pos_finite`) is **not** proved
  here; lane 344 owns that field.  Nothing in `torus_identity` needs it.
- The other five `LocalizationAPI` fields are untouched.

## 4. Commands and results

```
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T13.TorusIdentity
  → Build completed successfully, 0 errors
cd verification && lake env lean ../formalization/NSFormalization/Section3/T13/TorusIdentity.lean
  → no output (0 errors, 0 warnings)
cd verification && lake env lean ../research/T13/probes/torus_identity_closes.lean
  → no output
cd verification && lake env lean ../research/T13/axioms_torus_identity.lean
  → 83 lines, every one `[propext, Classical.choice, Quot.sound]`
make check (worktree root)
  → architecture checks OK; 13 contract-policy tests OK;
    45 work items consistent
make test (worktree root)
  → all registered contracts replayed, standard logical axioms only
```
