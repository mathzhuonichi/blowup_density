# REPORT 179 — A01 Grönwall endpoint (P9b)

## 1. Theorems with exact statements

Namespace `NSFormalization.Section4.A01`. The following is the exact shared
binder block (opens/imports are in the module), followed by the three theorem
statements. `include` retains all assumptions in each exported theorem.

```lean
variable {ν T R : ℝ} {a : SpatialField} {f : SpaceTimeField} {q : ℕ}
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f)
    (w : ClassicalSolutionR ν a f T) (hpath : HasSmoothSobolevPath T w.velocity)
    (hT : 0 < T)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t)) (hq : 4 ≤ q)
    (hslice : ∀ t : Icc (0 : ℝ) T,
      (fun x : Space => w.velocity (↑t, x)) =ᵐ[volume] ⇑(U t))
    (hR : ‖u‖ ≤ R)

include hν ha hf hpath hT hu hU hq hslice hR

theorem highOrder_bddAbove_of_kbnd_Ico_full {m : ℕ} (hm : 3 ≤ m) :
    ∀ t ∈ Ico (0 : ℝ) T,
      sobolevNormAt (m : ℝ) w.velocity t ≤
        (sobolevNormAt (m : ℝ) w.velocity 0 + (A04.forceSobolevENormL1 (m : ℝ) f).toReal)
          * Real.exp (A04.Cgron m ν * (256 * R ^ 2 * T))

theorem highOrder_bddAbove_all_orders_Ico_full :
    ∀ m : ℕ, 3 ≤ m →
      BddAbove (range (fun t : Ico (0 : ℝ) T => sobolevNormAt (m : ℝ) w.velocity t))

theorem hOne_uniform_Ico_full :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ t ∈ Ico (0 : ℝ) T,
      sobolevENorm 1 (fun x : Space => w.velocity (t, x)) ≤ K
```

The proof uses the original half-open Grönwall theorem at `T₀ := T`, fed the
closed cap restricted to `Ico 0 T`. Its exponential uses `256 * R^2 * T` once
for the full horizon. The H¹ witness is
`K = ENNReal.ofReal (‖D01.lowerVectorL 3 1 (by norm_num)‖ * B₃)`, where `B₃`
is the first theorem's right-hand side at `m = 3`.

## 2. Files

* `formalization/NSFormalization/Section4/A01/GronwallEndpoint.lean`: three proved theorems.
* `research/A01/axioms_gronwall_endpoint.lean`: all three axiom audits and a concrete
  `example` exercising the assembled theorem on `A04.zeroSol 1 1`, positive
  horizon, zero paths, `q = 4`, and `R = 0`.
* `research/A01/ATTEMPTS_GRONWALL_ENDPOINT.md`: route, resolved diagnostics,
  tree audit, endpoint interpretation and remaining supply obligations.
* `research/A01/A3_SPLIT.md`: appended row (iii-b) status correction.
* `research/A01/REPORT_179.md`: this report. No existing Lean module changed.

## 3. Gaps and error text

No unresolved Lean errors. Every new theorem prints exactly
`[propext, Classical.choice, Quot.sound]`; there are no added proof placeholders
or heartbeat overrides.

Resolved diagnostics include ``Unknown identifier `isSobolevDatum_lower` ``
(namespace `D01.Leray`), `Ambiguous term forceSobolevENormL1` (qualified A04),
and ``Tactic `rewrite` failed: Did not find an occurrence of the pattern
sobolevENorm ↑3 ...`` (normalize the natural cast). Full context and fixes are
in the attempts record.

Mathematical residual: this is the conditional full-half-open bound, not an
extension theorem or a value assertion at `T`. It retains `‖u‖ ≤ R`, the
closed-cylinder slice matching and smooth Sobolev path as premises. Thus
`Kbnd(R)` still cannot establish `HasAprioriBound`'s independently chosen `R`.
A02 uniform restart, constructor/path supply, and force bounds with the same
finite `K` remain separate. The mandatory full-tree grep found no implemented
A04 `restartBeyond`/`extendsBeyond` in this checkout; the handoff matches the
velocity-bound premise in `research/A04/Spec.lean` exactly.

## 4. Commands and results

All Lean commands sourced `. scripts/lean-env.sh`, set `LEAN_NUM_THREADS=6`,
and ran Lake from `verification/`.

* `lake build NSFormalization.Section4.A01.GronwallEndpoint`: PASS (9982 jobs);
  existing dependency warnings/info are replayed, no new-module diagnostics.
* `lake --quiet --log-level=error build NSFormalization.Section4.A01.GronwallEndpoint`:
  PASS, zero output (silent presentation of the same successful build).
* `lake env lean ../formalization/NSFormalization/Section4/A01/GronwallEndpoint.lean`:
  PASS, zero output.
* `lake env lean ../research/A01/axioms_gronwall_endpoint.lean`: PASS; exactly
  the required axiom sets for all three declarations; non-vacuity example passes.
* `make check` from the worktree root: PASS.
* `make test` from the worktree root: PASS.
* `make test-mutations` from the worktree root: PASS; all three mutations rejected.

Build/gate transcripts are in the ignored `tmp/179_*.log` files. No push,
merge or rebase was performed.
