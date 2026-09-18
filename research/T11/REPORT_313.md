# Report 313 — LocalExistence (U9b)

Route R2. Delivered the full two-space constructor **conditionally on one
projected-convolution boundedness input**, and the forced prescribed-window
fixed point, ball uniqueness, restriction and explicit H³ time estimate.
The H¹ input is defined verbatim and its lifespan consequence is derived
conditionally; it is not proved by this lane.

## 1. Theorems with exact statements

All declarations below are in `NSFormalization.Section3.T11`. The amended
`PeriodicQuantitativeLocalInput'` is byte-for-byte the definition in
`LEAD_AMENDMENTS.md`.

```lean
theorem quantitative_lifespan_lower_bound' (H : PeriodicQuantitativeLocalInput') :
    ∀ ν : ℝ, 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ →
      ∀ M : ℕ → ℝ≥0∞, (∀ m, M m ≠ ⊤) → ∃ δ : ℝ, 0 < δ ∧
      ∀ a : SpatialField, a ∈ initialClassT → periodicSobolevENorm 1 a ≤ K →
        ∀ g : SpaceTimeField, ContDiff ℝ ∞ g → IsPeriodicOn univ g →
          (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ M m) →
            ENNReal.ofReal δ ≤ maximalLifespanT ν a g
```

```lean
theorem torusConvolution_summable (A B : PeriodicSobolev 3) (i j : Fin 3)
    (k : PeriodicFrequency) :
    Summable (fun l : PeriodicFrequency ↦
      ‖(((periodicFrequencyWeight l) ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) * A.1 j l *
        (((periodicFrequencyWeight (k-l)) ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) * B.1 i (k-l)‖)
```

```lean
theorem torusTwoSpaceContract_nonempty (H : TorusConvolutionInput) (ν : ℝ) (hν : 0 < ν) :
    Nonempty (TorusTwoSpaceContract ν)
```

```lean
theorem torusForcedPicard_exists {ν : ℝ} (C : TorusTwoSpaceContract ν)
    (A : PeriodicSobolev 3) (F : ℝ → PeriodicSobolev 3) (T R b : ℝ)
    (P : TorusPicardConstants C T R b) (hF : ContinuousOn F (Icc 0 T))
    (hb : ∀ t, ∀ ht : t ∈ Icc (0 : ℝ) T,
      ‖C.analytic.linearEvolution ⟨t, ht.1⟩ A +
        ∫ s in (0 : ℝ)..t,
          C.analytic.linearEvolution (Real.toNNReal (t-s)) (F s)‖ ≤ b) :
    ∃ u : ℝ → PeriodicSobolev 3,
      TorusForcedMildOn C A F T u ∧ ∀ t ∈ Icc (0 : ℝ) T, ‖u t‖ ≤ R
```

```lean
theorem torusForcedMildOn_unique {ν T R b : ℝ} (C : TorusTwoSpaceContract ν)
    (P : TorusPicardConstants C T R b) {A : PeriodicSobolev 3}
    {F u v : ℝ → PeriodicSobolev 3}
    (hu : TorusForcedMildOn C A F T u) (hv : TorusForcedMildOn C A F T v)
    (hub : ∀ t ∈ Icc (0 : ℝ) T, ‖u t‖ ≤ R)
    (hvb : ∀ t ∈ Icc (0 : ℝ) T, ‖v t‖ ≤ R) :
    ∀ t ∈ Icc (0 : ℝ) T, u t = v t
```

```lean
theorem TorusForcedMildOn.restrict {ν T S : ℝ} {C : TorusTwoSpaceContract ν}
    {A : PeriodicSobolev 3} {F u : ℝ → PeriodicSobolev 3}
    (hu : TorusForcedMildOn C A F T u) (hS : 0 ≤ S) (hST : S ≤ T) :
    TorusForcedMildOn C A F S u
```

```lean
theorem TorusPicardConstants.restrict {ν T S R b : ℝ} {C : TorusTwoSpaceContract ν}
    (P : TorusPicardConstants C T R b) (hS : 0 < S) (hST : S ≤ T) :
    TorusPicardConstants C S R b
```

```lean
theorem torusPicardConstants_explicit {ν b : ℝ} (hν : 0 < ν) (C : TorusTwoSpaceContract ν)
    (hb : 0 ≤ b) :
    TorusPicardConstants C (torusKernelTime ν (torusPicardThreshold ‖C.analytic.bilinear‖ b)) (b+1) b
```

```lean
theorem torusForcedPicard_quantitative {ν : ℝ} (hν : 0 < ν) (C : TorusTwoSpaceContract ν)
    (A : PeriodicSobolev 3) (F : ℝ → PeriodicSobolev 3) (B : ℝ) (hB : 0 ≤ B)
    (hF : ContinuousOn F (Icc 0 1)) (hFB : ∀ t ∈ Icc (0 : ℝ) 1, ‖F t‖ ≤ B) :
    let b := ‖A‖ + B
    let T := torusKernelTime ν (torusPicardThreshold ‖C.analytic.bilinear‖ b)
    0 < T ∧ T ≤ 1 ∧ ∃ u : ℝ → PeriodicSobolev 3,
      TorusForcedMildOn C A F T u ∧ (∀ t ∈ Icc (0 : ℝ) T, ‖u t‖ ≤ b+1) ∧
      ∀ v : ℝ → PeriodicSobolev 3, TorusForcedMildOn C A F T v →
        (∀ t ∈ Icc (0 : ℝ) T, ‖v t‖ ≤ b+1) → ∀ t ∈ Icc (0 : ℝ) T, v t = u t
```

The constructor additionally discharges real-submodule closedness/completeness,
heat/smoothing CLMs with exact weights, joint strong heat continuity at zero,
and local kernel integrability. The bounded continuous-path affine map has a
Banach fixed point (`torusAffinePicard_exists_unique`); the force integral is
proved continuous and interval-integrable, and the nonlinear integral carries
its actual integrability certificate.

The explicit quantities used above are exactly:

```lean
def torusKernelTime (ν η : ℝ) : ℝ :=
  min 1 ((η / (1 + 2 * (Real.sqrt ν)⁻¹)) ^ 2)

def torusPicardThreshold (q b : ℝ) : ℝ :=
  min (1 / (q * (b+1)^2 + 1)) (1 / (2 * (q * (2*(b+1)) + 1)))
```

For `b = ‖A‖+B`, the solution exists on exactly this explicit positive time,
with radius `b+1`, for continuous coefficient force bounded by B on `[0,1]`.
This is an H³ estimate with a coefficient-force supremum bound, not the
H¹/order-wise-L¹ estimate needed in U9e.

## 2. Files

* `formalization/NSFormalization/Section3/T11/LocalExistence.lean` — new module,
  665 lines, 39 named declarations including explicitly named instances.
* `research/T11/probes/existence_u9b.lean` — zero datum, nonzero constant
  Fourier mode `e₁`, nonzero constant coefficient force, absolute convergence,
  projected-symbol vanishing on constant modes, and the unconditional primed
  nonzero physical witness.
* `research/T11/axioms_existence_u9b.lean` — 39 guarded checks, each requiring
  exactly `[propext, Classical.choice, Quot.sound]` (whitespace ignored only).
* `research/T11/EXISTENCE_ROUTE.md` — append-only `U9b status` with exact
  residual and U9c–e handoff.
* `research/T11/ATTEMPTS_EXISTENCE_U9B.md` — routes, actual diagnostics and fixes.
* `research/T11/REPORT_313.md` — this report.

Only the explicitly requested append modifies a pre-existing file. No existing
Lean module, registered contract, work-queue file, or global option is changed.

## 3. Gaps and error text

The one construction residue, assigned to U9c, is exactly:

```lean
def TorusConvolutionInput : Prop :=
  ∃ Q : PeriodicSobolev 3 →L[ℝ] PeriodicSobolev 3 →L[ℝ] PeriodicSobolev 2,
    ∀ A B i k, (Q A B).1 i k = torusProjectedConvectionSymbol A B i k
```

Absolute convergence of each coefficient convolution is proved. Its weighted
H³×H³→H² bounded real bilinear realization is not proved. All other contract
fields and the entire forced fixed-point target are proved. The primed input
is the required eventual target and is never an assumption of the coefficient
solver. U9d still owes common-horizon all-order bootstrap, physical velocity
and normalized pressure recovery; U9e still owes the amended H¹-uniform input.
Their exact statements are in the appended route status.

There are **no remaining Lean errors**. An actual development diagnostic was:

```text
error: Tactic `simp` failed with a nested error:
(deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached
```

It was resolved by targeted `change`/`rw`/`exact`, with no heartbeat increase.
The guarded audit initially reported:

```text
error: Unknown option `pp.width`
```

It now uses whitespace-insensitive message guards. More exact diagnostics are in the attempts record. The
mathematical residual is not presented as a compiler failure.

## 4. Commands and results

Every Lean command sourced `. scripts/lean-env.sh`, ran from `verification/`,
and set `LEAN_NUM_THREADS=6`.

| Command | Result |
| --- | --- |
| `lake build NSFormalization.Section3.T11.LocalExistence` | PASS, exit 0; 9906 build jobs, final module built |
| `lake env lean ../formalization/NSFormalization/Section3/T11/LocalExistence.lean` | PASS, exit 0; no output/errors/warnings |
| `lake env lean ../research/T11/probes/existence_u9b.lean` | PASS, exit 0; no output/errors/warnings |
| `lake env lean ../research/T11/axioms_existence_u9b.lean` | PASS, exit 0; all 39 exact axiom guards pass |
| `make check` from worktree root | PASS, exit 0; 13 contract-policy tests and 45-item work-queue consistency pass |
| Verbatim amendment / append-only route / forbidden-token checks | PASS |

The root architecture check prints existing copied-source diagnostics (including
`source_hashes_match: false`); these do not fail its gate and are outside this
lane's new module. No forbidden proof tokens occur in the new module, and it
uses no `maxHeartbeats` override. Local run logs are under `tmp/u9b/` and are not
part of the commit.

Commit message: `[313-T11] LocalExistence (U9b)`.
No push, merge, or rebase was performed.
