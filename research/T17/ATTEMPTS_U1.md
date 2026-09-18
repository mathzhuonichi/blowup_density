# U1 attempts

The closed proof uses `latticeLift_eq_of_ball` on the preimage of an open spatial ball under `ContinuousAt.snd`, then `EventuallyEq.iteratedFDerivWithin` on `univ`. The public theorem is the `k = 0` fundamental-ball form; the ENNReal supremum corollary is proved pointwise. A general existential translated-copy statement remains a follow-up extension.

## r1 (after codex REJECT, 2026-09-18) — general `∃ k` form delivered

Kept the two `k = 0` theorems verbatim (the reviewer probes reference them) and
**added** the missing general theorems, so nothing existing is renamed/restated:

- `latticeLift_iteratedFDeriv_eq_shift` — arbitrary `z`, `∃ k`, shifted RHS
  `z - (0, latticeVector k)`, and the no-copy/zero case (`k = 0`, both sides `0`).
- `latticeLift_iteratedFDeriv_norm_le_iSup'` — the all-`z` `ℝ≥0∞`/`⨆` corollary.

Design choice: `latticeLift_iteratedFDeriv_eq` already existed with the `k = 0`
ball statement and is referenced by the reviewer probes; renaming it would violate
"do not change existing declaration names/statements" and break those probes, so
the general theorem is a new sibling `…_eq_shift`, and the old one is exactly its
`k = 0` fundamental-ball specialization.

### Key steps that worked
- Case split `by_cases hcase : ∃ k, z.2 - latticeVector k ∈ ball x₀ r`.
- Copy present: `latticeLift w =ᶠ[𝓝 z] (· - (0, latticeVector k)) ∘ w` from
  `isPeriodicOn_sub_latticeVector (latticeLift_periodic w)` + `latticeLift_eq_of_ball`
  on the open preimage `{z' | z'.2 - latticeVector k ∈ ball x₀ r}`; then
  `Filter.EventuallyEq.iteratedFDeriv` and translation invariance
  `iteratedFDeriv_comp_sub`.
- No copy: on `ball z.2 (r-ρ)` (needs `hlt : ρ < r`) every lattice term
  `w (z'.1, z'.2 - latticeVector k)` vanishes (triangle inequality vs `hcase k`),
  so `latticeLift w =ᶠ 0` and (via `k = 0`) `w =ᶠ 0`; both derivatives are `0`.
  No smoothness assumption used anywhere.

### Failed/rejected approaches
- Detecting the copy via the support ball `ball x₀ ρ` instead of `ball x₀ r`:
  `latticeLift_eq_of_ball` only fires on `ball x₀ r` (needs `r + ρ ≤ 1`), so the
  copy region must be the `r`-ball; the zero region then needs `closedBall x₀ ρ ⊆
  ball x₀ r`, i.e. the strict `hlt : ρ < r` (added; false without it — see the
  negative probe).
- Reusing `latticeLift_sliceSupport` for the zero case: it gives only a fixed-`t`
  spatial slice support, not the spacetime neighbourhood the iterated derivative
  needs; replaced by the direct `ball z.2 (r-ρ)` term-by-term vanishing argument.

### Gates (all from `verification/`, `LEAN_NUM_THREADS=6`, after `. scripts/lean-env.sh`)
- `lake build NSFormalization.Section3.T17.LatticeDeriv` → exit 0,
  `Built NSFormalization.Section3.T17.LatticeDeriv`, `Build completed successfully (9359 jobs).`
  (no warnings from the module after replacing deprecated `push_neg` → `rw [not_exists]`
  and `ContinuousMultilinearMap.zero_apply` → `simp`).
- `lake env lean ../formalization/NSFormalization/Section3/T17/LatticeDeriv.lean` → exit 0, no output.
- `lake env lean ../research/T17/probes/lattice_deriv_closes.lean` → exit 0, no output
  (concrete, non-vacuous: the reviewer bump, `∃ k` exercised off-cube at
  `z = (0, latticeVector k₁)`, `k₁ = (1,0,0)`; `lift_nonzero_offcube` proves the
  lift is nonzero there; the `⨆` corollary and the `k = 0` form also close).
- `lake env lean ../research/T17/axioms_u1.lean` → exit 0; all four declarations
  `depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `make check` → exit 0 (`13` policy tests OK; `45 work items … consistent`).

### Negative-check evidence
- `research/T17/probes/rev369_negative_widened_ball.lean` (reviewer, r0) → exit 1:
  widening `r + ρ ≤ 1` to `≤ 2` is a type mismatch on `latticeLift_iteratedFDeriv_eq`.
- `research/T17/probes/rev369r1_negative_lt.lean` (r1) → exit 1: weakening the new
  `hlt : ρ < r` to `ρ ≤ r` is a type mismatch on `latticeLift_iteratedFDeriv_eq_shift`
  (`argument hle has type ρ ≤ r but is expected to have type ρ < r`).
- `research/T17/probes/rev369_nonvacuity.lean` (reviewer, r0) → exit 0 (still valid,
  references the unchanged `k = 0` theorem).
