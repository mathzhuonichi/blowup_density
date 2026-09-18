# Lane 347 — T16 `lem:potential` (`localPotentialStatement`) — report

Honest partial.  No `sorry`/`admit`/`axiom`/`native_decide`, no placeholder or
alias definitions, no goal repackaging.  Every declaration prints
`[propext, Classical.choice, Quot.sound]`.

## 1. What was proved (theorems with exact statements)

Module `NSFormalization.Section3.T16` in
`formalization/NSFormalization/Section3/T16/LocalPotential.lean`, over the
canonical T10/Section 4 vocabulary (imports T10 `PeriodicData`, I02
`Reference`/`Prescribed`/`Support`, `Source` `ParabolicScaling`/`PacketScaling`):

* All 6 Spec objects restated: `latticeVector`, `periodicSet`,
  `periodicScaledPacket`, `correctedBackground`, `structure CutoffData`,
  `structure LocalPotentialAPI`, and `def localPotentialStatement`.
* `exists_originCutoff {K} (hK : IsCompact K) : ∃ R θ O, 0 < R ∧ ContDiff ℝ ∞ θ ∧
  HasCompactSupport θ ∧ tsupport θ ⊆ ball 0 R ∧ IsOpen O ∧ K ⊆ O ∧
  EqOn θ (fun _ => 1) O ∧ ∀ x, θ x ∈ Icc 0 1`.
* `exists_timeCutoff : ∃ η, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
  (∀ t, η t ∈ Icc 0 1) ∧ EqOn η (fun _ => 1) (Icc (-1) 1) ∧
  tsupport η ⊆ Ioo (-2) 2`.
* `exists_threshold {θRadius r T δ} (hθR : 0<θRadius)(hr:0<r)(hT:0<T)(hδ:0<δ) :
  ∃ ε₀, 0<ε₀ ∧ (∀ ε ∈ Ioc 0 ε₀, 2*ε^2 < min T δ) ∧ (∀ ε ∈ Ioc 0 ε₀, ε*θRadius < r)`.
* `localPotential_zero (U K x₀ r T δ) (hr hr2 hT hδ hK hU) :
  ∃ D : CutoffData, LocalPotentialAPI (fun _ => 0) U K x₀ r T δ D` — the **full**
  reconciled API for the zero reference `v = 0`, discharging every one of the 26
  fields with the actual Urysohn cutoffs and threshold and the zero
  potential/correction.  Supporting facts `cross_zero_left`, `curl_const_zero`,
  `spatialDivergence_const_zero`, `tsupport_zero_field`, `tsupport_zero_slice`.

Probe `research/T16/probes/api_on_canonical.lean` (copies `research/T16/Spec.lean`
token-for-token and checks it against the module):

* `latticeVector_eq`, `periodicSet_eq`, `periodicScaledPacket_eq`,
  `correctedBackground_eq` — each Spec `def` (using the `Contracts.V1` operators)
  equals the module's by `rfl`.
* `toModuleData`/`ofModuleData` with `rfl` roundtrips (`CutoffData` structure
  exception); `api_toModule`/`api_ofModule` convert `LocalPotentialAPI` fieldwise
  both directions (all 26 fields hold by defeq).
* `specStatement_of_module : localPotentialStatement (module) →
  localPotentialStatement (Spec)`.
* A non-vacuity `example` closing
  `∃ D, BlowupDensity.T16.Spec.LocalPotentialAPI (fun _=>0) (fun _=>0) {0} x₀ r T δ D`.

This proves the reconciliation faithful: `Contracts.V1.{curl, cross,
scaledSpatialCutoff, scaledTemporalCutoff, scaledPacket, spatialDivergence}` are
definitionally the canonical `NavierStokes`/`Paper1`/`Source` notions.

## 2. What exists in Lean now (files)

* `formalization/NSFormalization/Section3/T16/LocalPotential.lean` — the module
  (builds; `lake env lean` gives zero output).
* `research/T16/probes/api_on_canonical.lean` — the probe (only its `#print
  axioms` lines are output).
* `research/T16/axioms_local_potential.lean` — axiom audit of the module.
* `research/T16/ATTEMPTS.md`, `research/T16/SPEC_ISSUES.md`, updated
  `research/T16/COMPARISON.md`.

## 3. Gap (with exact error text)

The general `localPotential : localPotentialStatement` is **not** delivered.  Two
genuine, coupled gaps (full residual lemma statements in `ATTEMPTS.md`,
owner-facing analysis in `SPEC_ISSUES.md`):

* **Radial potential on the ball.**  `potential_smooth`, `potential_curl` are
  stated on `Ioo 0 (T+δ) ×ˢ Metric.ball x₀ r`, and T16 gives `v` smooth /
  divergence-free only there, but the I02 lemmas require `I ×ˢ univ`.  Exact
  error when feeding the ball hypothesis to `spatialCurl_timePotential_on`:

  ```
  error: Application type mismatch: The argument
    hv
  has type
    ContDiffOn ℝ ∞ v (Ioo 0 (T + δ) ×ˢ Metric.ball x₀ r)
  but is expected to have type
    ContDiffOn ℝ ∞ v (Ioo 0 (T + δ) ×ˢ univ)
  ```

  Bridging needs a spatial-truncation lemma (spatial analogue of I02
  `Reference.lean`'s time truncation) — new mathematics, not in the tree.

* **Periodic correction.**  `correction_periodic : IsPeriodicOn univ` and
  `correction_support_ball ⊆ periodicSet (ball x₀ r)` force `D.correction ε` to be
  the lattice lift `∑' k, physicalCorrection(·, · - latticeVector k)`.  All eight
  `correction_*` fields are coupled to that lift; the local-finiteness /
  smoothness / periodicity / support / cancellation of the lift, and the two T10
  physical-bridge lattice lemmas they need, are not registered yet.

## 4. Commands run and results

* `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T16.LocalPotential`
  → `Build completed successfully (9357 jobs)`.
* `lake env lean ../formalization/NSFormalization/Section3/T16/LocalPotential.lean`
  → no output (0 warnings/errors).
* `lake env lean ../research/T16/probes/api_on_canonical.lean` → only the 6
  `#print axioms` lines, each `[propext, Classical.choice, Quot.sound]`.
* `lake env lean ../research/T16/axioms_local_potential.lean` → 9 lines, each
  `[propext, Classical.choice, Quot.sound]`.
* `make check` (worktree root) → exit 0 (contract policy, work-queue, architecture
  checks pass).
* Gap probe (deleted scratch) reproducing the `univ` vs `ball x₀ r` type error —
  text quoted in §3 and `ATTEMPTS.md`.
