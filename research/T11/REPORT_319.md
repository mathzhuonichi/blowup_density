# 319-T11 — Persistence (conditional delivery)

## 1. Theorems / exact statements

**Not an unconditional analytic closure of U9d1.** The half-order ladder and
common-horizon assembly are proved from exactly one explicit input.

```lean
theorem torusForcedMildOn_persistence (H : TorusHalfStepInput)
    (ν : ℝ) (hν : 0 < ν) (C : TorusTwoSpaceContract ν)
    (a : SpatialField) (g : SpaceTimeField) (T : ℝ)
    (ha : a ∈ initialClassT) (hg : ContDiff ℝ ∞ g) (hp : IsPeriodicOn univ g)
    (hT : 0 < T) (A : PeriodicSobolev 3) (F P u : ℝ → PeriodicSobolev 3)
    (hA : IsPeriodicDatum 3 a A) (hF : IsPeriodicSobolevPath 3 g F)
    (hP : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    (hu : TorusForcedMildOn C A P T u) :
    ∀ m : ℕ, ∃ u_m : ℝ → PeriodicSobolev m,
      (∀ t ∈ Ico 0 T, IsPeriodicReweight 3 (m : ℝ) (u t) (u_m t)) ∧
      ContinuousOn u_m (Ico 0 T) ∧
      (∀ K : Set ℝ, IsCompact K → K ⊆ Ico 0 T →
        ∃ B : ℝ, ∀ t ∈ K, ‖u_m t‖ ≤ B)
```

`persistence_halfOrder_ladder` gives continuous realizations at 3+n/2,
for every n, on the same Ico 0 T. `persistenceDown` is an actual continuous
linear reweighting from s to r≤s. Composition of reweights, transport in both
directions between representing data and reweights, and compact-subset bounds
are unconditional. In particular the conclusion includes t=0.

`persistence_constant_mild` proves, for every supplied C and 0≤T:

```lean
TorusForcedMildOn C (torusConstantDatum 3 c) (fun _ ↦ torusConstantDatum 3 c) T
  (fun t ↦ (1 + t) • torusConstantDatum 3 c)
```

The probe takes c=e₁ and an inhabited contract from lane 317: force and initial
solution are nonzero, and all half-step realizations are independently constructed.
All **17** module declarations have guarded exact axiom output
`[propext, Classical.choice, Quot.sound]`.

## 2. Files

* `formalization/NSFormalization/Section3/T11/Persistence.lean` — new module.
* `research/T11/probes/persistence_closes.lean` — conditional physical statement,
  literal requested statement with full original hypotheses, and non-vacuity.
* `research/T11/axioms_persistence.lean` — every module declaration audited.
* `research/T11/ATTEMPTS_PERSISTENCE.md` — search, routes, exact residual input,
  exact conditional conclusion, resolved errors and limitations.
* `research/T11/EXISTENCE_ROUTE.md` — appended U9d1 status and full input.
* `research/T11/T11_SPLIT.md` — appended unit status within §1.
* This report. No existing Lean module or contract was modified.

## 3. Gaps / errors

ONE unresolved input: `TorusHalfStepInput`, reproduced verbatim in the attempts
and route documents. It assumes a single half-order gain from an already
continuous order-r realization. It still includes real-order convolution,
fractional heat smoothing and endpoint Duhamel continuity. The analytic
follow-up is named U9d1-analytic, with no allocated lane number. This report
does not pretend to discharge that input with the existing sigma=1 estimate.
A whole-order step would have the nonintegrable kernel (t-s)^(-1).

**Statement defect:** `.1 i k` stores weighted, not physical Fourier
coefficients. Thus the brief's literal equality is true for `u_m := u` solely
by phantom-index erasure. `persistence_literal_target` records this fact as a
diagnostic; it is NOT counted as persistence. The additional physical theorem
uses canonical `IsPeriodicReweight`; no existing target/contract was changed
and no approval of a replacement is assumed. `PeriodicLocalRegularity`'s
ContDiffOn/pressure/projected fields are not proved by this delivery.

This checkout has no PhysicalRecovery.lean, ForcePaths.lean or the referenced
lane-318 status paragraph. No dependencies were pulled from another worktree.

Resolved Lean errors included `not a positivity goal`, the zero-rung cast
`IsPeriodicReweight 3 (3 + ↑0 / 2) ...` type mismatch, and `simp made no
progress` on a Duhamel integral; full error text and fixes are in the attempts.
**No remaining Lean errors.**

## 4. Commands / results

Every Lean invocation sourced `. scripts/lean-env.sh`, ran Lake only from
`verification/`, with `LEAN_NUM_THREADS=6`.

| Command | Result |
| --- | --- |
| `lake build NSFormalization.Section3.T11.Persistence` | PASS, 9973 jobs; module no errors/warnings (dependencies replay existing warnings) |
| `lake env lean ../formalization/NSFormalization/Section3/T11/Persistence.lean` | PASS, no output |
| `lake env lean ../research/T11/probes/persistence_closes.lean` | PASS, no output |
| `lake env lean ../research/T11/axioms_persistence.lean` | PASS, all 17 exact guards |
| `make check` from root | PASS, 13 tests and 45 work items consistent |
| `make test` from root | PASS, registered contract tests |
| `make test-mutations` from root | PASS, refactor accepted; admitted proof, extra axiom and weakened hypothesis rejected |
| `git diff --check` | PASS |

No proof placeholders, extra axioms, native evaluation, heartbeat overrides,
or anonymous instances were introduced. No push, merge or rebase.
