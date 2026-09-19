# Lane 460 continuation / T17 U13

## 1. Theorem and exact statement

Proved `NSFormalization.Section3.T17.correctionStatementSlab'_holds`:

```lean
def correctionStatementSlab' : Prop :=
  ∀ (ν : ℝ) (u : VelocityField) (p : PressureField) (f : VelocityField)
    (K : Set Space) (place : PlacementData u p f K)
    (v : SpaceTimeField) (r δ : ℝ),
    0 < ν → 0 < r → r < 1 / 2 → 0 < δ → IsPeriodicOn univ v →
    ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (place.T + δ) ×ˢ (univ : Set Space)) →
    (∀ t ∈ Ioo (0 : ℝ) (place.T + δ), ∀ x ∈ ball place.x₀ r,
      spatialDivergence v t x = 0) →
    (∀ t ∈ Ioo (0 : ℝ) 1, tsupport (fun x : Space ↦ u (t, x)) ⊆ K) →
    ball place.x₀ r ⊆ ball place.chartCenter place.chartRadius →
    ∃ D : CutoffData, LocalPotentialAPI v u place.Kstar place.x₀ r place.T δ D ∧
      Nonempty (CorrectionAPI ν place v r δ D)

theorem correctionStatementSlab'_holds : correctionStatementSlab'
```

Global periodicity is retained; global reference smoothness is dropped.
The returned `D` is `correctionData v …` for the original reference.
The successful classical probe defines exactly
`v_ext z := if z.1 ∈ Ico 0 (place.T + δ) then reference.velocity z else 0`,
proves its global periodicity, open-slab smoothness, and divergence clause,
and obtains the requested existential by `exact correctionStatementSlab'_holds …`.
The original `not_correctionStatementSlab` is preserved unchanged.

## 2. Files and field audit

- New `formalization/NSFormalization/Section3/T17/SlabBridge2.lean`:
  exact statement, smooth time extension, four global locality/transfer
  lemmas, two time-window lemmas, rescaled-reference equality on the fixed
  cylinder, and the completed theorem (all 45 fields).
- Updated `research/T17/probes/slab_from_classical.lean`: successful call
  from the canonical `T10.ClassicalSolutionT`, original negative regressions,
  and silent guarded axiom audits of its five named declarations.
- Updated `research/T17/axioms_u13.lean`, `ATTEMPTS_U13.md`, and
  `T17_SPLIT_U13.md`; new `research/T17/REPORT_460b.md`.

No existing canonical module, contract, binding, or test is modified.
The original report remains a historical record. The two pre-existing
untracked brief files are excluded from the commit.

The cutoff has inner radius `m/2`, outer radius `3m/4`, `m = min T δ`.
The threshold is chosen using `T/2, δ/2` and shrunk by `place.ε₀`, so
`2ε² < m/2`, which puts every admissible window inside the plateau.
T16's existing `contDiff_cutoffSmul_of_ballSmooth` proves global smoothness.
Spatial periodicity and divergence are preserved by the time-only scalar.
Both potentials are obtained from the existing `localPotentialAPI` with
the same cutoff parameters; the original one uses cylinder `ContDiffOn`.

Field audit:

| Fields | Discharge |
| --- | --- |
| `potential` | Direct canonical T16 construction for original `v`; includes the unrestricted `potential_formula : ∀ t x, …`. Neither its potential nor the entire cutoff record is transferred. |
| `reference_periodic` | Original global hypothesis. This is the field that prevented the first statement. |
| `localization`, `viscosity_pos`, `radius_pos`, `ball_in_chart`, `eps_le_placement` | Copied from the auxiliary API; independent of reference values and identical cutoff parameters. |
| `correctionProfileConst`, `forceProfileConst`, `spatialVolumeConst`, `correctionDerivConst`, `forceDerivConst`, `energyConst`, `mixedConst`, `sobolevConst`, and their seven `_nonneg` / one `_pos` fields | Copied with all original quantifiers. These data and sign properties do not read `v`. |
| Three correction-profile estimate fields, three force-profile estimate fields, and both profile identities | Global profile equalities, plus correction/force equality for identities; fixed cylinders agree by `rfl`. |
| `force_smooth`, `force_periodic`, `force_support`, `force_spatial_volume`, `force_time_length`, `force_derivative_bound`, `force_spatial_memLp`, `force_mixed_bound`, `forceSobolev_memLp`, `force_sobolev_bound` | Global equality of force functions at each admissible scale. This also transfers all global derivatives, torus lifts, supports, and norms. |
| `correction_derivative_bound`, `correction_slice_memLp`, `correction_gradient_memLp`, `correction_energy_bound` | Global equality of correction functions at each admissible scale. |

There are **no `CorrectionAPI` fields quantifying over unguarded ε**.
All 22 scale-dependent fields use `ε ∈ Ioc 0 D.ε₀`. Their global spatial/time
quantifiers cause no difficulty because the equalities are global functions,
not just equalities on the cylinder. Off the time window the entire correction
slice and its spatial derivative vanish, killing both reference-dependent
force terms. The same argument handles force profiles off `Icc (-2) 2`.
The 23 remaining fields are exactly the first four rows above.

## 3. Gaps and error text

No residual mathematical or Lean obligation remains. No new axiom,
placeholder, global smoothness hypothesis, or API amendment is introduced.
The canonical T16 theorem already takes local smoothness; no generalized
T16 theorem is needed.

One correction to the proposed route was necessary: `2ε² < m` alone does
not put a window inside the radius-`m/2` plateau. The stronger threshold above
fixes that without changing the statement.

Resolved elaboration failures (full exact diagnostics in `ATTEMPTS_U13.md`):

```text
error: don't know how to synthesize implicit argument `x`
error: 'change' tactic failed, pattern
  ↑χ t * spatialDivergence v t x = 0
is not definitionally equal to target
  ∑ i, ((fderiv ℝ (fun y => ↑χ t • v (t, y)) x) (coordinateVector i)).ofLp i = 0
error: unsolved goals
⊢ fderiv ℝ (fun x => 0) z.2 = 0
```

These were fixed by explicitly evaluating differentiability at `x`, using a
separate spatial-derivative identity, and simplifying the lambda constant.
The assembly also required explicit `rfl` equalities of the fixed cylinders
and support radii rather than relying on simplifier unfolding. Deprecated
`if_pos`/`if_neg` in the first probe were replaced by `ite_eq_left`/`ite_eq_right`.

The checkout's `SPEC_ISSUES.md` still lacks the referenced G5 addendum;
the user's continuation supplies that ruling. This has no proof impact.

## 4. Commands and results

All Lean commands source `scripts/lean-env.sh`, run from `verification/`,
and use `LEAN_NUM_THREADS=6`. The mutation script invokes Lake there too.

- `lake build NSFormalization.Section3.T17.Assembly`: exit 0, 10032 jobs.
- `lake build NSFormalization.Section3.T17.SlabBridge NSFormalization.Section3.T17.SlabBridge2`:
  exit 0, 10034 jobs; only pre-existing dependency warnings replayed.
- `lake env lean ../formalization/NSFormalization/Section3/T17/SlabBridge.lean`:
  exit 0, zero output.
- `lake env lean ../formalization/NSFormalization/Section3/T17/SlabBridge2.lean`:
  exit 0, zero output.
- `lake env lean ../research/T17/probes/slab_from_classical.lean`:
  exit 0, zero output, including all five guarded axiom audits.
- `lake env lean ../research/T17/axioms_u13.lean`: exit 0;
  all 17 audited canonical declarations (7 original, 10 new), including
  `correctionStatementSlab'_holds`, print exactly
  `[propext, Classical.choice, Quot.sound]`.
- `lake test`: exit 0 (10949 jobs).
- `make check`: exit 0; 48 registered contracts, 13 policy tests pass,
  45 work items consistent. Existing informational manifest/copy diagnostics remain.
- `python3 experiments/test_contract_mutations.py`: exit 0;
  `Mutation suite passed. This is an infrastructure check, not a PDE proof.`
- `git diff --check`: exit 0.
