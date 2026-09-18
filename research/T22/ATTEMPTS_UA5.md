# T22 · U-A5 — `orderZero` — attempts log (lane 393)

Target: `BoundedDomainNormAPI.orderZero` verbatim
(`Section3/T22/Domain.lean:59-62`, `research/T22/Spec.lean:125-128`):
`∀ Ω, IsOpen Ω → ∀ z, ContDiffOn ℝ ∞ z Ω →
   domainSobolevENorm Ω 0 (restrictField Ω z) = eLpNorm z 2 (volume.restrict Ω)`.

Delivered module: `formalization/NSFormalization/Section3/T22/OrderZero.lean`. All declarations
print `[propext, Classical.choice, Quot.sound]`.

## What closed, and how

### `≤` (positive)
`domainSobolevENorm ≤ sobolevENorm 0 (E₀z)` (lane 383 `domainSobolevENorm_le_sobolevENorm`) →
`= eLpNorm (E₀z) 2 volume` (order-0 field norm identity `sobolevENorm_zero_eq_eLpNorm`, proved
here from `sobolevENorm_le_of_isSobolevDatum` + `isSobolevDatum_unique` + lane 387
`norm_orderZeroDatum_eq`) → `= eLpNorm z 2 (volume.restrict Ω)`
(`eLpNorm_indicator_eq_eLpNorm_restrict`, `zeroExtension = Ω.indicator`). Needs `MemLp (E₀z) 2`,
supplied by `memLp_indicator_iff_restrict` from `MemLp z 2 (restrict Ω)`; the latter from
`ContDiffOn.continuousOn.aestronglyMeasurable` + the finiteness case split. The `⊤` case is
`le_top`.

### `≥` (positive) — the two genuinely new facts
1. **Order-0 realization surjectivity** `orderZeroDatum_surjective`:
   `∀ A : RealVectorSobolev 0, ∃ w hw, orderZeroDatum hw = A`. Route: `v := (cyclesToAngularRealVector 0).symm A`;
   `g i := 𝓕⁻ (v i)`; the field is `fieldOf g x := WithLp.toLp 2 (fun i => ((g i) x).re)`.
   The key missing bridge (nothing of this form existed in the tree — confirmed by a full search)
   is `conjugation_fourierInv_of_mem`: `h ∈ realSubspace 0 → conjugation (𝓕⁻ h) = 𝓕⁻ h`
   (proved by applying `𝓕`, `fourier_conjugation`, `mem_realSubspace_iff`, `𝓕`-injectivity). This
   makes `g i` a.e. real, so `componentLp (memLp_fieldOf g) i = g i`, `𝓕 (componentLp ..) = v i`,
   `realProjectionTo 0 (v i) = v i` (`realProjectionTo_inclusion`), hence
   `orderZeroDatum (memLp_fieldOf g) = cyclesToAngularRealVector 0 v = A`
   (`apply_symm_apply`). Then `‖A‖ₑ = eLpNorm w 2 volume` is lane 387's identity for free.
2. **du Bois-Reymond bridge** `restrictField_eq_ae`: `restrictField Ω w = restrictField Ω z →
   w =ᵐ[restrict Ω] z`, from Mathlib
   `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` applied per component to `w·i - z·i`,
   with a ℂ-Schwartz test built from the real test `g` via `HasCompactSupport.toSchwartzMap`.
   The general datum-restriction bridge `restrictDatum_eq_restrictField_of_datum` (interior tests
   vanish off `Ω`) turns `IsSobolevDatum 0 w A` + `restrictDatum Ω 0 A = restrictField Ω z` into
   `restrictField Ω w = restrictField Ω z`. Then
   `eLpNorm z 2 (restrict Ω) = eLpNorm w 2 (restrict Ω) ≤ eLpNorm w 2 volume = ‖A‖ₑ`
   (`eLpNorm_congr_ae`, `eLpNorm_mono_measure Measure.restrict_le_self`). No `MemLp`-or-not split
   is needed: the `⊤` edge is handled uniformly because `‖A‖ₑ` is always finite (a Hilbert norm),
   so the constraint family is empty exactly when `z ∉ L²(Ω)`.

## Negative examples / pitfalls (recorded for the reviewer)

- **`rw`/`conv` closing the equiv `apply_symm_apply` by `rfl` is heartbeat-nondeterministic.**
  `cyclesToAngularRealVector 0 (e.symm A)` is *definitionally* `A`, so a trailing `rfl` inside
  `rw`/`conv` sometimes closes the goal and sometimes `(deterministic) timeout at isDefEq`
  (the lane-387 heavy unification). This made `rw [hkey]; exact e.apply_symm_apply A` fail with
  either "No goals" or "unsolved goals" depending on the remaining budget. **Fix:**
  `simp only [hkey, ContinuousLinearEquiv.apply_symm_apply]` (deterministic), inside a
  commented `set_option maxHeartbeats 400000`.
- **`WithLp.toLp_ofLp` is `rfl`**, so `WithLp.toLp 2 (fun i => v i) = v` self-closes under `rw`;
  a following `exact WithLp.toLp_ofLp v` then errors "No goals". Drop the redundant `exact`.
- `MemLp.integrable` needs `[IsFiniteMeasure μ]`, false for `volume` on ℝ³. Use
  `memLp_one_iff_integrable.mp (hwi.mul' hg2)` (Hölder `2·2→1`) instead.
- `MemLp.locallyIntegrable` takes the `1 ≤ p` argument explicitly (`hwi.locallyIntegrable one_le_two`).
- `PiLp.continuous_apply`'s implicit `β` would not infer through dot-projection; `by fun_prop`
  discharges the component continuity cleanly.
- Vector-field coordinates display as `(w x).ofLp i`; `w x i` is defeq, `memLp_piLp_iff` and
  `WithLp.ofLp_injective (p := 2)` are the working spellings.
- `EuclideanSpace.proj i` introduced a topology-instance diamond in `comp_continuousOn`; avoided
  via `by fun_prop`.

## Heartbeats
- `orderZeroDatum_surjective`: needs `set_option maxHeartbeats 400000` (the `cyclesToAngularRealVector`
  `.apply_symm_apply` / subspace defeq, same source lane 387 flagged). All other declarations pass
  at the default 200000.
