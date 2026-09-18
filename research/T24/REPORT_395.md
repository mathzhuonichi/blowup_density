# Lane 395 — T24c Uc2 `potential_pairing` — report

## 1. What was proved (theorem, exact statement)

`formalization/NSFormalization/Section3/T24/PotentialPairing.lean`, namespace
`NSFormalization.Section3.T24`:

```
theorem potential_pairing :
    ∀ (ν : ℝ) (T : ℝ), 0 < T → ∀ φ : SpaceTimeScalar, PeriodicPotentialT φ →
      ∀ S : ClassicalSolutionT ν (0 : SpatialField) (conservativeForceT φ) T,
        ∀ t ∈ Ico (0 : ℝ) T,
          ∫ y : PeriodicTorus,
              torusLift (fun x : Space ↦
                (inner ℝ (conservativeForceT φ (t, x)) (S.velocity (t, x)) : ℝ))
                y ∂periodicTorusMeasure = 0
```

This is the first field of `ConservativeForcingAPI`
(`research/T24/Spec.lean:1391-1406`; `paper/sections/03-torus.tex:729-731`),
verbatim over the canonical T10/T11 vocabulary: the Haar (unit-torus) pairing of
the conservative force `-∇φ` with the divergence-free periodic velocity vanishes
at every time of the classical lifespan `[0,T)`.

Two supporting definitions restated verbatim from `Spec.lean:1367-1372` (lane
392's canonical `Section3/T24/Conservative.lean` was not on this base; dedupe in
Uc3):
```
def PeriodicPotentialT (φ : SpaceTimeScalar) : Prop := ContDiff ℝ ∞ φ ∧ IsPeriodicOn univ φ
def conservativeForceT (φ : SpaceTimeScalar) : SpaceTimeField := fun z ↦ -pressureGradient φ z.1 z.2
```

Axiom audit (`research/T24/axioms_uc2.lean`):
`'NSFormalization.Section3.T24.potential_pairing' depends on axioms:
[propext, Classical.choice, Quot.sound]` — exactly the three allowed.

## 2. What exists in Lean now

- Module `Section3/T24/PotentialPairing.lean` — builds under `lake`, 0 sorry /
  axiom / native_decide, warning-free.
- Probe `research/T24/probes/potential_pairing_closes.lean` — 0 errors/warnings:
  * Part 1: the field statement over canonical vocabulary closed by
    `exact potential_pairing` (statement fidelity).
  * Part 2: `φ = cos(2πx₁)` (`probePotential`) proved to satisfy
    `PeriodicPotentialT` (`probePotential_isPeriodicPotential`) and to be
    genuinely nonconstant (`probePotential_nonconstant`: `φ(0)=1`, half-period
    value `-1`), so the hypothesis class is non-degenerate (`-∇φ ≠ 0`).
  * Part 3: the conclusion evaluated at that potential and the from-rest
    (zero) velocity is a real `∫ = 0` identity.
- `research/T24/axioms_uc2.lean`, `research/T24/ATTEMPTS_UC2.md`.
- Status recorded in `research/T24/T24_SPLIT.md` (Uc2 marked DONE with the
  landed route); one-line lesson prepended to `logs/LESSONS.md`.

The analytic engine reused (not reproved): the already-formalized torus
integration-by-parts lemma
`NavierStokes.PeriodicUniqueness.cubeIntegral_pressure_energy_zero`
(`vendor/NavierStokesAndEuler/NavierStokes/PeriodicUniqueness.lean:435`), plus
`NSFormalization.Paper1.integral_torusLift` (`Paper1/TorusCube.lean:40`) and
`cubeIntegral_neg` (`PeriodicIntegration.lean:71`). Slab→slice smoothness is
`ContDiffOn.comp_contDiff` (as in `Section3/T11/EnergyIdentity.lean:482`).

## 3. Gap

None for the Uc2 target: the field is proved unconditionally with the standard
three axioms. Scope boundaries worth flagging for Uc3 assembly:

- `PeriodicPotentialT`/`conservativeForceT` are a **local restatement**; Uc3 must
  dedupe against lane 392's `Section3/T24/Conservative.lean` once it lands (same
  names/namespace, byte-identical to `Spec.lean:1367-1372`).
- Full non-vacuity by an actual constructed `ClassicalSolutionT` inhabitant (the
  rest solution `u≡0`, `p = -φ` normalized) is **not** built here: it requires
  the heavy `sobolev` field (a Fourier-datum path for `u≡0`) and is Uc3's
  registration job (the split assigns the `φ=0` rest-solution non-vacuity to
  Uc3, `T24_SPLIT.md:80-85`). The probe instead witnesses non-vacuity by (i) a
  genuine nonconstant `φ` in the hypothesis class and (ii) the conclusion
  computing to `0` at the from-rest velocity.

## 4. Commands run and results

```
. scripts/lean-env.sh
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T24.PotentialPairing
  → Build completed successfully (9353 jobs).
cd verification && lake env lean ../formalization/NSFormalization/Section3/T24/PotentialPairing.lean
  → (clean: 0 errors, 0 warnings)
cd verification && lake env lean ../research/T24/probes/potential_pairing_closes.lean
  → (clean: 0 errors, 0 warnings)
cd verification && lake env lean ../research/T24/axioms_uc2.lean
  → [propext, Classical.choice, Quot.sound]
make check
  → contract_policy 13 tests OK; check_work_queue 45 items consistent; architecture checks pass.
```
