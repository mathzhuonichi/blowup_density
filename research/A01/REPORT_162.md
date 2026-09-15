# Lane 162 report — A01 constructor row c6

## 1. Theorems proved

### `NSFormalization.Section4.A01.divergence_ae_of_cylinder`

```lean
theorem divergence_ae_of_cylinder {q : ℕ}
    (u : SobolevSpace 1 (q + 1))
    (U : EulerMeanSolenoidal.L2)
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (hU : ordinaryLift U = value 1 u)
    (hdiv : value 1 u ∈ divergenceFreeSpace 1 1 0)
    (Z : SmoothL2Field Space)
    (hZ : Z.field =ᵐ[volume] ⇑U) :
    ∀ᵐ x ∂(volume : Measure Space),
      ∑ i : Fin 3, (fderiv ℝ Z.field x (coordinateVector i)) i = 0
```

It descends the three length-one spatial words with `word_descent_ae_top`, identifies them with the
three classical derivatives using `word_descent_ae_full`, and sums their diagonal components.  The
source's weak cylinder constraint is converted by the existing vendor theorem
`EulerClassicalDivergence.divergenceFree_classical_divergence_zero`.

### `NSFormalization.Section4.A01.divergence_of_cylinder_pointwise_of_contDiff`

```lean
theorem divergence_of_cylinder_pointwise_of_contDiff {q : ℕ} {T : ℝ}
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2))
    (hu : ∀ (t : Icc (0 : ℝ) T) (θ : AddCircle (1 : ℝ)),
      sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (hdiv : ∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0)
    (Z : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hZ : ∀ t, (Z t).field =ᵐ[volume] ⇑(U t))
    (velocity : SpaceTimeField)
    (hslice : ∀ t : Icc (0 : ℝ) T,
      (fun x : Space => velocity (↑t, x)) =ᵐ[volume] ⇑(U t))
    (hslice_contDiff : ∀ t ∈ Ico (0 : ℝ) T,
      ContDiff ℝ ∞ (fun x : Space => velocity (t, x))) :
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, spatialDivergence velocity t x = 0
```

This is the exact `ClassicalSolutionR.divergence` field shape.  It upgrades the first theorem by
continuity and identifies the candidate slice with `Z t` everywhere from their common a.e. carrier
`U t`.

## 2. What is in Lean now

`formalization/NSFormalization/Section4/A01/ConstructorDivergence.lean` contains the two-layer c6
proof.  The source audit records that the Horizon clause uses
`EulerLiftedGradientSpace.divergenceFreeSpace`, defined as the orthogonal complement of the closed
lifted-gradient space.  The cited HeliCorgi theorem is the analogous result for a separate frequency
carrier, not the Horizon carrier.

`research/A01/axioms_c6.lean` prints the axiom dependencies of both declarations and checks two
inhabited zero-cylinder examples (`u := 0`, `U := 0`), including the all-time pointwise theorem.
Both declarations print exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The proof route, source distinction, full-tree negative search, and failed elaboration probes are
recorded in `research/A01/ATTEMPTS_C6.md`.  Since `research/A01/CONSTRUCTOR_SPLIT.md` is absent in
this worktree, the requested lane-162 status note was appended to `research/A01/A3_SPLIT.md`.

## 3. Gaps

There is no remaining analytic gap in row c6 under the stated carrier hypotheses.

The full mild-to-classical constructor must still provide the family
`Z : Icc 0 T → SmoothL2Field Space` with `Z t =ᵐ ⇑(U t)` and the candidate-slice equality
`hslice`.  The pointwise conclusion also deliberately retains the c3 hypothesis
`hslice_contDiff`.  Those are constructor/c3 inputs, not assumptions of divergence itself.

No Lean goal failed to close, so there is no residual error text.

## 4. Commands and results

All commands were run after sourcing `scripts/lean-env.sh`; all `lake` commands were run from
`verification/`.

```text
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.ConstructorDivergence
Build completed successfully (9987 jobs).
```

Exit 0.  Lake replayed warnings from pre-existing imported modules; the new target emitted no
warning or error.

```text
$ lake env lean ../formalization/NSFormalization/Section4/A01/ConstructorDivergence.lean
```

Exit 0, zero output.

```text
$ lake env lean ../research/A01/axioms_c6.lean
'NSFormalization.Section4.A01.divergence_ae_of_cylinder' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.divergence_of_cylinder_pointwise_of_contDiff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Exit 0.

```text
$ make check
python3 experiments/check_formalization_plan.py --check
...
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.048s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

Exit 0.  The architecture checker retained the repository's existing
`source_hashes_match: false` diagnostic and existing copied-source admission count; neither is a
failure of `make check` and this lane changes no copied or frozen source.
