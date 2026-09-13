# A02 unit U1a — attempts, positive and negative

Lane 033, branch `erenup/033-A02-energy-u1a`, base `erenup/integration` at
`2554554`.  Unit **U1a** of `research/A02/COMPARISON.md:163` (unit table `:161-173`): from a
`ClassicalSolutionR ν a f T` produce
`UniformFiniteEnergy (Icc 0 b) u.velocity` for every `0 ≤ b < T`.

Deliverables: `formalization/NSFormalization/Section4/A02/Energy.lean` and the
shared restatement `formalization/NSFormalization/Section4/A02/SolutionClass.lean`
(byte-identical to §0 of lane 032's `Restrict.lean`; see §3 item 1).

---

## 1. What the target actually needs

`NavierStokesR3.ProblemStatement.UniformFiniteEnergy`
(`vendor/NavierStokesAndEuler/NavierStokes/R3/ProblemStatement.lean:81-83`) is

```lean
def UniformFiniteEnergy (times : Set ℝ) (u : VelocityField) : Prop :=
  ∃ E : ℝ, 0 ≤ E ∧ ∀ t ∈ times, SquareIntegrableAtTime u t ∧ kineticEnergy u t ≤ E
```

with `SquareIntegrableAtTime u t := Integrable (fun x => ‖u (t,x)‖ ^ 2) volume`
(`:71`) and `kineticEnergy u t := (1/2) * ∫ x, ‖u (t,x)‖ ^ 2` (`:76`).  So two
things are needed at every `t` of the compact, and — this is the part that makes
the unit non-trivial — **one** `E` for all of them.

`ClassicalSolutionR` (`verification/Contracts/V1/Data.lean:624-648`) supplies

```lean
velocity_smooth : ContDiffOn ℝ ∞ velocity (Ico (0:ℝ) T ×ˢ (univ : Set Space))
sobolev : ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
  ContinuousOn G (Ico (0:ℝ) T) ∧
    ∀ t ∈ Ico (0:ℝ) T, IsSobolevDatum (m : ℝ) (fun x => velocity (t, x)) (G t)
```

Nothing else is used: not `momentum`, not `divergence`, not `initial`, not
`pressure_smooth`, not `pressure_gradient`, not `horizon_pos`.

### Which clause of `sobolev` was needed, and did it suffice

**It sufficed, exactly.**  The two clauses play different roles and both are
load-bearing:

* the **datum clause** `IsSobolevDatum (m:ℝ) (velocity (t,·)) (G t)` at the
  single order `m = 0` gives square integrability *at each fixed `t`*;
* the **`ContinuousOn G (Ico 0 T)` clause** is what upgrades a pointwise family
  of finite energies into one bound.  `Icc 0 b` is compact and, for `b < T`, is
  contained in `Ico 0 T`, so `IsCompact.exists_bound_of_continuousOn` gives one
  `C` with `‖G t‖ ≤ C` on it.  This is the whole reason U1a is an **M** and not
  an **L**.

Had `sobolev` carried only measurability of the datum path (the weaker reading
considered in the task brief), the conclusion would have had to degrade to
`∀ t ∈ Icc 0 b, SquareIntegrableAtTime u t` plus a separate `BddAbove`
hypothesis.  That degradation was **not** needed and is not in the delivered
file.  `ClassicalSolutionR` was not weakened and no axiom was added.

Order `m = 0` is enough.  Nothing here needs `m = 2`, `m = 3`, or the
`L^∞`-embedding — those are U1b/U9's problem.

---

## 2. The route that worked

`IsSobolevDatum` is stated in the manuscript's **angular** normalization
(`Paper3.angularRealization`, `Data.lean:160`), and its right-hand side is a
*totalized* Bochner integral, so the predicate alone says nothing about a slice
that pairs integrably with no Schwartz test at all (the caveat of
`Data.lean:147-154` and `research/D01/REVIEW_RECONCILIATION.md:94`).  Continuity
of the slice — from `velocity_smooth` — is what removes that degeneracy.  The
chain is:

| step | declaration |
|---|---|
| slice is continuous | `NavierStokesR3.Comparison.continuous_slice_of_continuousOn` (`vendor/…/R3/ComparisonFiniteEnergy.lean:31`) applied to `velocity_smooth.continuousOn` |
| angular ⟶ cycles datum | `Paper3.angularRealization_eq_cycles` (`Paper3/AngularTameProduct.lean:30`), with `Paper3.cyclesToAngular_symm_norm_le` (`:20`) whose constant `frequencyUnit ^ ❘0❘` is `1` |
| datum pairs like the field on compact tests | `Source.FourierPhysicalJets.CompactRep` (`Source/FourierPhysicalJets.lean:14`) |
| **order-0 datum ⟹ `L²` slice** | `Source.FourierPhysicalJets.physicalLp_ae` (`:28`), which is Mathlib's `ae_eq_of_integral_contDiff_smul_eq` (`Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean:195`) applied to the `L²` class `physicalLp 0 le_rfl` (`:19`) and the continuous slice |
| three components ⟶ one `Lp Space 2` | `Source.FourierPhysicalJets.vectorLpReassembly` / `_ae` (`:119,123`) |
| `L²` norm ⟶ `∫ ‖·‖²` | `NavierStokesR3.LpNormTools.lpNorm_two_sq_eq_l2Sq` (`vendor/…/R3/LpNormTools.lean:63`) |
| `MemLp` ⟶ `SquareIntegrableAtTime` | `NavierStokesR3.Comparison.squareIntegrableAtTime_iff_memLp` (`vendor/…/R3/ComparisonFiniteEnergy.lean:24`) |
| one bound on the compact | `IsCompact.exists_bound_of_continuousOn` (`Mathlib/Analysis/Normed/Group/Bounded.lean:96`) |

The constant is `sliceConst = ‖vectorLpReassembly‖ * ‖physicalLp 0 le_rfl‖`, a
product of two operator norms.  It is deliberately **not** sharp: the
`∃ E` of `UniformFiniteEnergy` hides it entirely.  Chasing the sharp constant
would need the angular Plancherel identity, which does not exist in tree as a
single declaration (see §4).

---

## 3. Negative results and paths not taken

1. **`Contracts.V1.Data.ClassicalSolutionR` cannot be *imported* from
   `formalization/`; it has to be restated.**  The `NSFormalization` package is a
   *dependency* of the `Contracts` library (`verification/lakefile.toml`), and on
   this branch there is no local restatement of the structure
   (`grep -rn ClassicalSolutionR formalization/` finds only two docstring
   mentions in `Section4/D01/SmoothDatum.lean`).

   *First attempt, abandoned:* deliver only
   `uniformFiniteEnergy_of_sobolev`, whose two hypotheses are the two fields
   verbatim, and leave the structure version to a binding module.  Writing a
   private copy of the structure here was rejected because lane 032
   (`erenup/032-A02-restrict-order`, units U4/U6) restates the same objects in
   the **same namespace** `NSFormalization.Section4.A02`; two restatements would
   collide at merge.

   *Resolution (lead's instruction, mid-lane):* §0 of lane 032's
   `Section4/A02/Restrict.lean` (its lines 78-164) was extracted **byte-identical**
   into a separate module `Section4/A02/SolutionClass.lean` in this lane, with the
   same namespace, the same five imports and the same `open`s.  `Energy.lean`
   imports it, so the target statement is now literal:
   `ClassicalSolutionR.uniformFiniteEnergy` (`Section4/A02/Energy.lean:252`).
   At merge the lead dedupes: 032's `Restrict.lean` drops its §0 and imports
   `SolutionClass.lean`.  Verified with
   `diff <(sed -n '78,164p' <032>/Restrict.lean) <(sed -n '47,133p' SolutionClass.lean)`
   — empty.

   Consequence: `IsSobolevDatum` is taken from `SolutionClass.lean` (032's copy),
   **not** from `Section4/D01/SmoothDatum.lean:237`, and the import of
   `D01.SmoothDatum` was dropped.  The two predicates are definitionally equal;
   the copy is build hygiene, as 032's docstring records.  Nothing else in this
   module came from `D01.SmoothDatum`.

2. **The `m = 0` order is the cast `((0 : ℕ) : ℝ)`, not `(0 : ℝ)`.**  Rewriting
   `Nat.cast_zero` inside the hypothesis is a dependent rewrite (the datum type
   `RealVectorSobolev s` mentions `s`).  It happens to be harmless because
   `Source.RealSobolev.realSubspace` ignores its order argument, but relying on
   that is brittle.  Taken instead: the worker lemma
   `uniformFiniteEnergy_of_sobolevDatumPath` carries `{s : ℝ}` with `hs : s = 0`
   and opens with `subst hs`, so the `m = 0` instance applies with
   `Nat.cast_zero` as the proof and no transport at all.

3. **Not routed through `Source.SmoothLifespan.Flow`.**  `Flow` has an `energy`
   field (`Source/SmoothLifespan.lean:33`) of exactly the required shape, so
   `ClassicalSolutionR → Flow` would give U1a for free — but that implication
   *is* U1, of which U1a is the first half, so the route is circular.  Recorded
   because it is the first thing one tries.

4. **D01 unit L1 (datum uniqueness) is *not* needed**, although the unit table
   (`research/A02/COMPARISON.md:163`) lists it as a dependency of U1a.  The proof
   never needs *the* datum, only *a* datum together with its norm: the bound is
   `‖sliceLp (G t)‖ ≤ sliceConst * ‖G t‖` for the `G` that `sobolev` hands over,
   and `IsSobolevDatum` fixes the realized distribution, hence the slice, up to a
   null set — which is all `SquareIntegrableAtTime` and `kineticEnergy` see.  L1
   would only be needed to turn `sobolevENorm` (`Data.lean:189`) into an honest
   norm, and `sobolevENorm` does not appear in U1a.  **Positive finding: U1a's
   dependency list can be shortened.**

5. **`NavierStokesR3.CompactComparisonBounds.uniformFiniteEnergy_of_compact_slab`
   and `Comparison.uniformFiniteEnergy_sub_of_continuousOn`** (used at
   `Source/SmoothLifespan.lean:148-160`) produce `UniformFiniteEnergy` but only
   for *compactly supported* or *difference* fields.  A `ClassicalSolutionR`
   velocity has no compact support, so neither applies.

6. **No sharp-constant version.**  `‖sliceLp A‖ = ‖A‖` is true (both
   `Paper3.angularFrequencyDilation` and the `L²` Fourier transform are
   isometries, and `frequencyUnit ^ ❘0❘ = 1`), but proving it needs the angular
   Plancherel identity assembled from `Lp.fourierTransformₗᵢ`
   (`Mathlib/Analysis/Fourier/LpSpace.lean:49`) and
   `Paper3.angularFrequencyDilation`, plus the fact that
   `Source.PhysicalIntegerSobolev.sobolevOrderLowering 0 0` is the identity.
   That is a D01 unit **L1**-shaped job (datum uniqueness / honest norm) and not
   needed by U1a, so it was skipped on purpose.

---

## 4. Overlap with D01 unit `DatumToJets` — read before review

`Section4/D01/DatumToJets.lean` **does not exist on this branch** (base
`2554554`), but it was merged into `erenup/integration` while this lane was
running (`git cat-file -e erenup/integration:formalization/NSFormalization/Section4/D01/DatumToJets.lean`
succeeds; head `aba1a2e`).  It was read read-only from
`.claude/worktrees/025-D01-datum-to-jets/` and **not copied**.

It already contains, at general order, the order-0 step this module had to
re-derive locally:

| this module | `Section4.D01.DatumToJets` (integration) |
|---|---|
| `A02.cyclesComponent` | `D01.cyclesComponentOfAngular` (`:140`) |
| `A02.norm_cyclesComponent_le` | `D01.norm_cyclesComponentOfAngular_le` (`:153`) |
| `A02.compactRep_of_isSobolevDatum` | `D01.compactRep_cyclesComponentOfAngular` (`:161`) |
| `A02.componentLp` / `A02.sliceLp` / `A02.sliceLp_ae` | `D01.jetOfDatum` / `D01.jetOfDatum_ae` (`:196,202`) at `j = 0` |
| `A02.memLp_of_isSobolevDatum` | `D01.memLp_of_isSobolevDatum` (`:267`) — its docstring names this very unit |
| `A02.l2Sq_le_of_isSobolevDatum` | `D01.eLpNorm_le_of_isSobolevDatum` (`:276`), `ℝ≥0∞`-valued |
| slice smoothness | `D01.contDiff_slice` (`:366`) |

**Recommended action at rebase** (not done here, because the module would then
not compile on this branch and the build evidence below would be unverifiable):
after rebasing onto `erenup/integration`, delete sections 1 and 2 of
`Section4/A02/Energy.lean`, import `NSFormalization.Section4.D01.DatumToJets`,
and replace in `uniformFiniteEnergy_of_sobolevDatumPath`

* `memLp_of_isSobolevDatum hslice hdt` by `D01.memLp_of_isSobolevDatum hcontdiff hdt`,
* `l2Sq_le_of_isSobolevDatum hslice hdt` by the `ENNReal.toReal` of
  `D01.eLpNorm_le_of_isSobolevDatum hcontdiff hdt` together with
  `LpNormTools.lpNorm_two_sq_eq_l2Sq`,

where `hcontdiff` is `D01.contDiff_slice` instead of the present `hslice`.
`D01`'s lemmas are stated with `D01.IsSobolevDatum` while this module now uses
`A02.IsSobolevDatum` (from `SolutionClass.lean`); the two are definitionally
equal, so `exact` moves a hypothesis across without a transport.
Section 3 — the compactness argument and the assembly, which is the actual
content of U1a — is unaffected.  One difference worth keeping in mind: the local
version needs only `Continuous` of the slice, D01's needs `ContDiff ℝ ∞`; both
are available from `velocity_smooth`.

---

## 5. Commands run, in order, with results

Every `lake` invocation was from `WT/verification`.  `WT/formalization/.lake`
contains only `build/`; no `lake` was ever run from `WT/formalization`, so no
second Mathlib clone exists (`ls formalization/.lake` → `build`).

| # | command | result |
|---|---|---|
| 1 | `bash scripts/lean-install.sh` | exit 0, `== OK`; its `lake test` reported `checked; standard logical axioms only` for every registered contract |
| 2 | `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.D01.SmoothDatum NSFormalization.Source.FourierPhysicalJets NSFormalization.Paper3.AngularTameProduct` | **killed** — see the race below |
| 3 | `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A02.Energy` | **exit 1**, `Some required targets logged failures: - Euler.MeanSpatialDerivative`, `error: no such file or directory … Euler/MeanSpatialDerivative.olean` |
| 4 | same command again, nothing else running | **exit 1**, one real error: `NSFormalization/Section4/A02/Energy.lean:222:25: failed to prove positivity/nonnegativity/nonzeroness` |
| 5 | same command after the fix | **exit 0**, `✔ [9877/9877] Built NSFormalization.Section4.A02.Energy (4.5s)`, no warning from the new file |
| 6 | same command after rewiring to `SolutionClass.lean` | **exit 0**, `✔ Built NSFormalization.Section4.A02.SolutionClass (2.7s)`, `✔ Built NSFormalization.Section4.A02.Energy (3.3s)`, no warning from either new file |
| 7 | `cd verification && lake env lean ../research/A02/axioms_u1a.lean` | all six declarations: `depends on axioms: [propext, Classical.choice, Quot.sound]` |

### Two build failures worth recording

* **Concurrent `lake` in one worktree corrupts the shared `vendor/.lake/build`.**
  Runs 2 and 3 overlapped with each other *and* with the `lake test` that
  `scripts/lean-install.sh` runs at its end; the result was
  `error: no such file or directory … vendor/NavierStokesAndEuler/.lake/build/lib/lean/Euler/MeanSpatialDerivative.olean`
  on a module neither invocation had touched.  Lake's package lock did not
  prevent it.  **Rule: one `lake` per worktree at a time**, and in particular do
  not start a build while `lean-install.sh` is still running.  Rerunning with
  nothing else active rebuilt the module in 1.6 s and the error vanished.
* **`positivity` cannot see through an opaque constant.**  `sliceConst` is a
  `def` whose body is a product of two operator norms, so
  `positivity` fails on `0 ≤ sliceConst * ‖G t‖`.  Replaced by
  `mul_nonneg sliceConst_nonneg (norm_nonneg _)`.  (`positivity` still handles
  `0 ≤ (1/2) * (sliceConst * C) ^ 2`, but that one is written out explicitly too,
  so that the `0 ≤ b` hypothesis is genuinely used.)

Two further name/API points, found by reading rather than by failing: Mathlib's
`pow_le_pow_left` is now `pow_le_pow_left₀`
(`Mathlib/Algebra/Order/GroupWithZero/Basic.lean:507`), and
`MeasureTheory.Lp.norm_def` is `rfl`, so `comparisonLpNorm 2 z = ‖sliceLp A‖`
needs no rewriting beyond `eLpNorm_congr_ae`.
