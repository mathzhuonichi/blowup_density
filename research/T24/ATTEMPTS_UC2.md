# T24c Uc2 — `potential_pairing` — attempts log (lane 395)

Target verbatim (`research/T24/Spec.lean:1391-1406`): for every `ν : ℝ`, `T : ℝ`
with `0 < T`, every `φ` with `PeriodicPotentialT φ`, every
`S : ClassicalSolutionT ν 0 (conservativeForceT φ) T` and every `t ∈ Ico 0 T`,
`∫ y, torusLift (fun x ↦ inner ℝ (conservativeForceT φ (t,x)) (S.velocity (t,x))) y ∂periodicTorusMeasure = 0`.

Module: `formalization/NSFormalization/Section3/T24/PotentialPairing.lean`.

## What worked (final route)

The whole analytic content is a single already-formalized vendor lemma:

- `NavierStokes.PeriodicUniqueness.cubeIntegral_pressure_energy_zero`
  (`vendor/NavierStokesAndEuler/NavierStokes/PeriodicUniqueness.lean:435`):
  `∫_{cube} ⟪u(t), ∇p(t)⟫ = 0` for `ContDiff` spatial slices `u(t), p(t)`,
  `UnitPeriods` of both, and `∀ x, spatialDivergence u t x = 0`.

Proof skeleton:
1. `rw [NSFormalization.Paper1.integral_torusLift]` — Haar integral over
   `PeriodicTorus` becomes `cubeIntegral` over the fundamental cube
   (`Paper1/TorusCube.lean:40`).
2. Feed the vendor lemma with:
   - `hw : ContDiff ℝ ∞ (fun x ↦ S.velocity (t,x))` from
     `S.velocity_smooth.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun x ↦ ⟨ht, mem_univ x⟩)`
     (the `ClassicalSolutionT` slab regularity restricted to the time slice — the
     same incantation as `Section3/T11/EnergyIdentity.lean:482`);
   - `hφx : ContDiff ℝ ∞ (fun x ↦ φ (t,x))` from `hφ.1.comp (contDiff_const.prodMk contDiff_id)`;
   - `hpw`/`hpφ : UnitPeriods …` directly from `S.velocity_periodic t ht` and `hφ.2 t (mem_univ t)`
     (`IsPeriodicOn` unfolds field-for-field to `UnitPeriods` at a fixed time);
   - `hdiv : ∀ x, spatialDivergence S.velocity t x = 0` from `S.divergence t ht`.
3. Rewrite the integrand `inner ℝ (conservativeForceT φ (t,x)) (S.velocity (t,x))`.
   `conservativeForceT φ (t,x) = -pressureGradient φ t x` is `rfl`; then
   `inner_neg_left` and `real_inner_comm` give `= -(inner ℝ (S.velocity (t,x)) (pressureGradient φ t x))`.
4. `cubeIntegral_neg` + the vendor lemma value + `neg_zero`.

## Key positive findings

- **No `t = 0` case split.** The brief's route split `t = 0` (from `S.initial`)
  and `t ∈ Ioo 0 T` (IBP). This is unnecessary: `ContDiffOn.comp_contDiff`
  produces a *global* spatial `ContDiff` slice at *every* `t ∈ Ico 0 T`
  (including the left endpoint `t = 0`), and `S.divergence`/`S.velocity_periodic`
  also hold on all of `Ico 0 T`. So `cubeIntegral_pressure_energy_zero` applies
  uniformly and the proof is one branch.
- **`0 < ν` is never used.** The Spec field quantifies `∀ ν : ℝ` with no
  positivity — correctly, since this is pure integration by parts, independent
  of the viscosity. (Contrast `zero_from_rest`/Uc1, which genuinely needs
  `0 < ν` via classical uniqueness.) So the `zero_of_conservative_residual`
  scaffold at `ConservativeForce.lean:23` (which needs `0<ν`) is NOT reused
  directly; its *sibling* pairing lemma `cubeIntegral_pressure_energy_zero` — the
  ingredient it and the energy balance are built from — is what closes Uc2.
- `PeriodicPotentialT`/`conservativeForceT` restated verbatim from
  `Spec.lean:1367-1372` because lane 392's `Section3/T24/Conservative.lean` was
  not on the base; Uc3 assembly should dedupe.

## Negative attempts / dead ends considered

- **Reusing `zero_of_conservative_residual` (`ConservativeForce.lean:23`) directly.**
  Rejected: it concludes `u ≡ 0` on the slab, but requires `0 < ν` (via
  `PeriodicUniqueness.classical_uniqueness_on_Icc`). `potential_pairing` has no
  `0<ν`, so this cannot discharge the general-`ν` statement. It would only prove
  a strictly weaker specialization. Its underlying cube pairing lemma is the
  right granularity to mine instead.
- **`rw [integral_torusLift]` with the bare name.** Failed: `integral_torusLift`
  lives in `NSFormalization.Paper1` and is not in scope via the `open`s; the T10
  canonical `torusLift`/`periodicTorusMeasure` are reducible abbrevs of the
  Paper1 originals, so `rw [NSFormalization.Paper1.integral_torusLift]` unifies
  through them. (Error was `Unknown identifier 'integral_torusLift'`.)
- **Probe periodicity of `cos(2πx₁)` via `fin_cases i` + `rw [hc]`.** Failed:
  `fin_cases` leaves the index as a beta-redex `(fun i ↦ i) ⟨0,_⟩`, so
  `rw [(coordinateVector 0) 0 = 1]` cannot find its literal pattern, and the
  `if (0:Fin 3) = ⟨0,_⟩` is not decided by `simp only`. Replaced with a single
  `by_cases`/`split_ifs` on `(0 : Fin 3) = i`, computing the shifted coordinate
  with `EuclideanSpace.single_apply`.

## Commands

- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T24.PotentialPairing` → `Build completed successfully`.
- `cd verification && lake env lean ../research/T24/axioms_uc2.lean` → `[propext, Classical.choice, Quot.sound]`.
- `cd verification && lake env lean ../research/T24/probes/potential_pairing_closes.lean` → clean (0 errors/warnings).
- `make check` → OK (architecture + contract-policy + work-queue).
