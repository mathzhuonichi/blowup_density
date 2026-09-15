# Lane 190-A01-b1-r4-joint-smooth report

## 1. Theorems, exact statements, and named inputs

The scalar finite-order engine is:

```lean
theorem scalarJointRepresentative_contDiffOn (n : ℕ) (s S : ℝ) (hS : 0 < S)
    (horder : (n : ℝ) + 2 ≤ s) (G : ℝ → FourierData)
    (hG : ContDiffOn ℝ n G (Icc (0 : ℝ) S)) :
    ContDiffOn ℝ n (scalarJointRepresentative s (by linarith) G)
      (Icc (0 : ℝ) S ×ˢ (univ : Set Space))
```

It includes the time endpoints: the induction uses `derivWithin` on `Icc 0 S`
and the new closed-set lemma `boundedEvaluation_hasFDerivWithinAt`.  Spatial
differentiation is the continuous-linear map `angularRepresentativeGradient`,
whose formula is first proved on angular Schwartz data and then closed by
uniform convergence.

The fixed field and its two principal properties are:

```lean
def jointRepresentative {S : ℝ}
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hpaths : ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1)) :
    SpaceTimeField

theorem jointRepresentative_slice {S : ℝ}
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hpaths : ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1))
    (t : Icc (0 : ℝ) S) :
    (fun x => jointRepresentative U hpaths (↑t, x)) =ᵐ[volume] ⇑(U t)

theorem jointRepresentative_contDiffOn {S : ℝ} (hS : 0 < S)
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hpaths : ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1)) :
    ContDiffOn ℝ ∞ (jointRepresentative U hpaths)
      (Icc (0 : ℝ) S ×ˢ (univ : Set Space))
```

`jointRepresentative` is the canonical bounded representative of the chosen
order-two path.  For each finite `n`, the order-`n+2` path proves `C^n` joint
regularity.  Its continuous representative and the fixed order-two
representative are both a.e. equal to `⇑(U t)`, hence equal everywhere.  This
is the cross-order compatibility required to transfer all finite orders to
one field.

The requested packaged theorem is exactly:

```lean
theorem exists_joint_smooth_representative {S : ℝ} (hS : 0 < S)
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hpaths : ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1)) :
    ∃ u : SpaceTimeField,
      (∀ t : Icc (0 : ℝ) S,
        (fun x => u (↑t, x)) =ᵐ[volume] ⇑(U t)) ∧
      ContDiffOn ℝ ∞ u (Ico (0 : ℝ) S ×ˢ (univ : Set Space))
```

The theorem is stated on the consumer's `Ico` slab, while
`jointRepresentative_contDiffOn` records the stronger closed-slab result.

The lane-178 composition is:

```lean
theorem exists_joint_smooth_representative_of_hall {ν S : ℝ}
    (hν : 0 < ν) (hS : 0 < S)
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hall : ∀ (q : ℕ) (hq : 6 ≤ q),
      ∃ (u₀ : SobolevSpace 1 (q + 1))
        (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
        (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))),
        ContDiffOn ℝ ∞ (extendPath S hS.le f) (Icc (0 : ℝ) S) ∧
        (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
        (∀ (θ : AddCircle (1 : ℝ)) t,
          sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) ∧
        ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
          (coefficients 1 hq f) u₀ u t) :
    ∃ u : SpaceTimeField,
      (∀ t : Icc (0 : ℝ) S,
        (fun x => u (↑t, x)) =ᵐ[volume] ⇑(U t)) ∧
      ContDiffOn ℝ ∞ u (Ico (0 : ℝ) S ×ˢ (univ : Set Space))
```

It is the direct composition of `exists_joint_smooth_representative` with
`datumPath_contDiffOn_all_orders hν hS U hall`.

Satisfiability of every final named input is explicit.  `hν` and `hS` are the
standard positive-viscosity and positive-horizon restrictions.  `U` is the
ordinary solution restricted to the common interval.  `hpaths` is the
standard all-order `C^j_t H^m_x` property of a smooth nonzero solution,
restricted to `[0,S]`.  `hall` is the standard compatible all-order smooth
cylinder realization of that same solution on the common horizon.  No
clamped-carrier or zero-only premise was introduced.  An explicit `U := 0`
example in the conformance file proves non-vacuity.

## 2. Files

- `formalization/NSFormalization/Section4/A01/JointRepresentative.lean` — new
  closed-set bounded evaluation, scalar and vector representative machinery,
  cross-order compatibility, fixed representative, closed-slab smoothness,
  packaged R4 theorem, and lane-178 composition.
- `research/A01/axioms_b1_r4.lean` — all 26 named declarations audited; every
  one prints exactly `[propext, Classical.choice, Quot.sound]`; also contains
  the explicit `U := 0` non-vacuity example.
- `research/A01/ATTEMPTS_B1_R4.md` — successful route, rejected alternatives,
  satisfiability account, source checks, and the corrected timeout.
- `research/A01/B1_LADDER.md` — R4 marked DONE conditionally on the honest
  all-order `hall` supply; stronger closed-slab conclusion recorded.
- `research/A01/REPORT_190.md` — this report.

No pre-existing Lean module was edited.

## 3. Gaps and error text

There is no remaining Lean error and no R4 representative/mixed-derivative
gap.  The result deliberately retains lane 178's honest supply input `hpaths`,
or equivalently `hall` in the composed theorem.  Constructing `hall` from the
final constructor premises is a separate upstream supply-side obligation; R4
does not strengthen it or replace it with a property special to zero.

During development, a cross-order equality was initially passed to
`ContDiffOn.congr` in the wrong direction.  The exact symptom was:

```text
error: (deterministic) timeout at `whnf`, maximum number of heartbeats
(400000) has been reached
```

Reversing the equality fixed the elaboration.  The delivered module contains
no `set_option maxHeartbeats` and none of `sorry`, `admit`, `axiom`, or
`native_decide`.

The only non-clean gate output is pre-existing repository output.  Lake
replays warnings from imported dependencies, while the new target emits no
warning.  `make check` reports:

```text
formalization/NSFormalization/Paper1/BoundaryCorollary.lean:90: token "sorry"
source_hashes_match: false
```

These are architecture notices already present in lane 178's report;
`make check` exits 0.

## 4. Commands and results

All Lake commands were run from `verification/` after sourcing
`scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`.

- `lake build NSFormalization.Section4.A01.JointRepresentative` — exit 0;
  `Built ... JointRepresentative`.  Lake replayed only pre-existing dependency
  warnings.
- `lake env lean ../formalization/NSFormalization/Section4/A01/JointRepresentative.lean`
  — exit 0, exactly zero output.
- `lake env lean ../research/A01/axioms_b1_r4.lean` — exit 0; all 26
  declarations printed exactly `[propext, Classical.choice, Quot.sound]`.
- `make check` from the worktree root — exit 0; all invoked checks completed
  successfully, with the two pre-existing notices quoted above.
- `git diff --check` — exit 0.
