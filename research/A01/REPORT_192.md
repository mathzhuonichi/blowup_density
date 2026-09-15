# REPORT 192 — combined constructor inputs from all-order bounds

## 1. Theorems with exact statements

All production declarations are in namespace `NSFormalization.Section4.A01`, with
`{f : A02.SpaceTimeField} {S : ℝ}`. The primary theorem remains:

```lean
theorem cylinderPair_of_bounds (hf : D01.MemForceR f) (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (R : ℕ → ℝ)
    (hb : ∀ q (hq : 6 ≤ q), HasAprioriBound hq hν a
      (C01.forcePath (S := S) hf)
      (C01.forcePath_jetLp_continuous (S := S) hf) (R q)) :
    ∃ U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2),
      U ⟨0, le_rfl, hS.le⟩ = a.toLp ∧
      (∀ q (hq : 6 ≤ q),
        ∃ u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)),
          (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
          (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
          (∀ (θ : AddCircle (1 : ℝ)) t,
            sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) ∧
          ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
            (coefficients 1 hq
              (sobolevPath (C01.forcePath (S := S) hf)
                (C01.forcePath_jetLp_continuous (S := S) hf) q))
            (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) ∧
      (∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
        ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
        ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1))
```

`cylinderPair_of_boundsInv` has the identical conclusion and replaces every
`HasAprioriBound` premise with `HasAprioriBoundInv`.

The constructor-facing export is one combined witness with every requested fact on that same
`U,u` pair:

```lean
theorem constructorInputs_of_bounds {q : ℕ} (hq : 6 ≤ q) (hf : D01.MemForceR f)
    (hν : 0 < ν) (hS : 0 < S) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0) (R : ℕ → ℝ)
    (hb : ∀ p (hp : 6 ≤ p), HasAprioriBound hp hν a
      (C01.forcePath (S := S) hf)
      (C01.forcePath_jetLp_continuous (S := S) hf) (R p)) :
    ∃ (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
      (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))),
      U ⟨0, le_rfl, hS.le⟩ = a.toLp ∧
      (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
      (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
      (∀ (θ : AddCircle (1 : ℝ)) t,
        sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) ∧
      (∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
        (coefficients 1 hq
          (sobolevPath (C01.forcePath (S := S) hf)
            (C01.forcePath_jetLp_continuous (S := S) hf) q))
        (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) ∧
      (∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
        ContDiffOn ℝ 0 G (Icc (0 : ℝ) S) ∧
        ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1)) ∧
      ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
        ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
        ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1)
```

`constructorInputs_of_boundsInv` has the same conclusion with an
`HasAprioriBoundInv` family. Both are derived by destructing the corresponding
`cylinderPair_of_bounds` theorem once, so `hU`, `hdiv`, angular invariance, the exact canonical
Duhamel equation, and every datum path refer to the same `U,u`. The retained `j = 0` constructor
projection is `hsob 0`, derived from the all-`j` family returned in the following conjunct. The six
old split projection declarations remain deleted; their API permitted unrelated existential
carriers.

The audit additionally proves the concrete producer:

```lean
theorem zero_all_order_bound (ν S : ℝ) (hν : 0 < ν) :
    ∀ q (hq : 6 ≤ q), HasAprioriBound hq hν
      (SmoothL2Field.zeroField : SmoothL2Field Space)
      (C01.forcePath (S := S) A04.memForceR_zero)
      (C01.forcePath_jetLp_continuous (S := S) A04.memForceR_zero) 0
```

For `T > 0`, `quadratic_mild_unique` identifies every zero-data/zero-force solution with the zero
path; `T = 0` is proved directly. Hence its norm is zero, and the main theorem is instantiated
with `R := fun _ => 0` without assuming `hb`.

All five audited declarations depend exactly on `[propext, Classical.choice, Quot.sound]`.

## 2. Files

* `formalization/NSFormalization/Section4/A01/CylinderWiring.lean`: the two all-order wiring
  theorems and two combined constructor exports.
* `research/A01/axioms_wiring_hsob.lean`: axiom audit, proved zero-radius bound family, and the
  resulting concrete instantiation of `cylinderPair_of_bounds`.
* `research/A01/probes/rev192_constructor_positive.lean`: consumes every combined output, feeds
  the all-`j` family to lane 190's exact `exists_joint_smooth_representative` hypothesis shape,
  and feeds its representative plus all cylinder clauses to the lane-180-shaped constructor.
* `research/A01/probes/rev192_combined_full_fail.lean`: converted from the re-review reproducer
  into positive exact-type regression checks for both complete combined exports.
* `research/A01/probes/rev192_named_exports_fail.lean`: retained as the negative record of the
  deleted split interface.
* `research/A01/ATTEMPTS_WIRING_HSOB.md`: proof route and corrected non-circular Grönwall plan.
* `research/A01/A3_SPLIT.md` and `research/A01/B1_LADDER.md`: existing lane status updates.

No pre-existing Lean module was modified.

## 3. Gaps and error text

There are no unresolved Lean errors, proof placeholders, extra axioms, or heartbeat overrides.
The remaining analytic input for nonzero data, besides lane 190's `hc3` and lane 189's `hpg`, is
the all-order `HasAprioriBound` family (or its invariant form).

The re-review's blocking interface gap is closed: neither combined proof discards `hinv` or
`hduh`, and neither truncates `hsob` to order `j = 0`. The full-shape reproducer now passes, while
the constructor probe verifies that the same all-`j` family has exactly lane 190's `hpaths` type.

The non-circular proposed route is now precise: choose the order-six local horizon and radius
first; lower any higher-order mild solution to order six and use lane 188 uniqueness; use that
base-order radius to cap the `H²` integral; then use Grönwall to choose each higher-order `R q`.
Using the higher-order radius in its own integral cap would be circular. Routing through this
lane's all-order constructor would also be circular because its premise is already `hb`.

The negative named-export probe now fails earlier, as intended, because the defective split API no
longer exists (elaboration stops at the first deleted name):

```text
Unknown identifier `hsob_of_bounds`
```

The independent order mutation remains a negative check: an order-`q+1` path cannot inhabit the
requested order-`q+2` type.

## 4. Commands and results

All Lean commands sourced `. scripts/lean-env.sh`; Lake ran from `verification/`, with
`LEAN_NUM_THREADS=6` for the module build.

* `lake --quiet --log-level=error build NSFormalization.Section4.A01.CylinderWiring`: PASS,
  zero output.
* `lake env lean ../formalization/NSFormalization/Section4/A01/CylinderWiring.lean`: PASS,
  zero output.
* `lake env lean ../research/A01/axioms_wiring_hsob.lean`: PASS; five exact standard-axiom lines,
  and the genuine non-vacuity construction checks.
* `lake env lean ../research/A01/probes/rev192_constructor_positive.lean`: PASS, zero output.
* `lake env lean ../research/A01/probes/rev192_combined_full_fail.lean`: PASS, zero output; retained
  under its reviewer-supplied filename as the fixed-defect regression.
* `lake env lean ../research/A01/probes/rev192_zero_nonvacuity.lean`: PASS, zero output.
* `lake env lean ../research/A01/probes/rev192_named_exports_fail.lean`: expected FAIL on the
  deleted split names.
* `lake env lean ../research/A01/probes/rev192_mutation_fail.lean`: expected FAIL on the
  `q+1`/`q+2` mismatch.
* `make check`: PASS.
