# REVIEW — lane 143-C01-e3-e4-momentum (rows Ep / E3 / E4 + `energyIdentity` on carrier B)

Reviewer run 2026-09-14, worktree `.claude/worktrees/143-C01-e3-e4-momentum`
(branch `erenup/143-C01-e3-e4-momentum`, HEAD `e6d5ee8` on top of
`origin/erenup/integration`).  Read-only: no Lean edited, no git state touched.
Probes kept (not `/tmp`, per `logs/LESSONS.md`): `research/C01/probes/rev143_*.lean`.

## Verdict: **ACCEPT-WITH-NOTES**

Nothing blocks the merge.  All 12 declarations of
`formalization/NSFormalization/Section4/C01/MomentumCarrierB.lean` compile silently with
the standard three axioms; every cited source lemma exists at the cited line and says what
the lane says it says; the two vendor-field bridges are genuine; the `hmom` shape is
token-for-token the one `energyIdentity_of_carrierB` consumes; and the explicit `hd` of
`energyIdentity_classical` is **not** an escape hatch (finding 4, probe).  Three notes are
documentation-level one-liners; finding 6 **downgrades** the lane's own E4 blocker estimate
and recommends the opposite route from the brief's route (b).

---

## 1. Build / axioms / hygiene — PASS

```
$ cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.C01.MomentumCarrierB
Build completed successfully (10190 jobs).
[exited with code 0]
```
`grep -c 'MomentumCarrierB' <build log>` = **0** — the module contributes no warning or
info line of its own (every `⚠` in the log is a replayed `Source.*` / `Paper3.*` /
`Formal.*` module already on integration).

```
$ grep -nE 'sorry|admit|axiom|native_decide|maxHeartbeats|set_option' \
    formalization/NSFormalization/Section4/C01/MomentumCarrierB.lean
(no output)
```
No `sorry`/`admit`/`native_decide`, no declared `axiom`, and **no `set_option` at all** —
so the "`maxHeartbeats` only per-declaration ≤400000 with a comment" clause is vacuous here.
(The only `axiom` hits in the lane are the `#print axioms` lines of the audit file.)

```
$ cd verification && lake env lean ../research/C01/axioms_e3e4.lean
'…C01.velocitySliceField' depends on axioms: [propext, Classical.choice, Quot.sound]
'…C01.pressureGradientField' depends on axioms: [propext, Classical.choice, Quot.sound]
'…C01.temporalSliceField' depends on axioms: [propext, Classical.choice, Quot.sound]
'…C01.forceSliceField' depends on axioms: [propext, Classical.choice, Quot.sound]
'…C01.pressureGradientField_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'…C01.pressureGradientField_eq_gradient' depends on axioms: [propext, Classical.choice, Quot.sound]
'…C01.contDiff_pressureSlice' depends on axioms: [propext, Classical.choice, Quot.sound]
'…C01.velocitySliceField_divergence' depends on axioms: [propext, Classical.choice, Quot.sound]
'…C01.advectionField_velocitySlice_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'…C01.laplacianField_velocitySlice_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'…C01.momentum_split_toLp' depends on axioms: [propext, Classical.choice, Quot.sound]
'…C01.energyIdentity_classical' depends on axioms: [propext, Classical.choice, Quot.sound]
[exited with code 0]
```
12/12 exactly the standard three.  (LESSONS-109 warns that an *ambiguous* name makes
`#print axioms` print both readings and so cannot be used as evidence of non-ambiguity —
finding 2 settles that separately.)

```
$ make check          # worktree root
… python3 experiments/test_contract_policy.py → Ran 13 tests … OK
… python3 experiments/check_work_queue.py → 30 work items: ownership, contract
   registration and task cards consistent.
[exited with code 0]
```
`verification/contracts.json` and `Contracts/V1/*` are **untouched** — the diff is exactly
4 files (one `formalization/` module + three `research/C01/` records), so hard rule 3's
"no placeholder `Prop` field in a contract" is not even in scope here (finding 4).

CI closure: `python3 experiments/build_changed_lean.py --base-ref origin/erenup/integration`
prints `Changed Lean modules: NSFormalization.Section4.C01.MomentumCarrierB` — the module is
inside the closure CI compiles.

## 2. Row Ep — sources are the tree's D01 P2 lemmas; `gradient` is Mathlib's — PASS

Structure match.  `EulerLpTranslation.SmoothL2Field`
(`vendor/NavierStokesAndEuler/Euler/LpSmoothField.lean:31`) is
`⟨field, smooth : ContDiff ℝ ∞ field, integrable : ∀ n, MemLp (iteratedFDeriv ℝ n field) 2 volume⟩`
and `D01.SmoothSquareIntegrableJets`
(`formalization/NSFormalization/Section4/D01/DatumToJets.lean:118`) is the plain `And`
`ContDiff ℝ ∞ v ∧ ∀ n : ℕ, MemLp (iteratedFDeriv ℝ n v) 2 volume`, so the `.1`/`.2`
projections fill the structure on the nose.

| packaging | source, opened at the cited line | time guard |
|---|---|---|
| `velocitySliceField` (`:91`) | `C01.velocity_slice_smoothL2` (`Section4/C01/VelocityJets.lean:85`, `A05.SmoothL2`) | `Ico 0 T` ✅ |
| `pressureGradientField` (`:105`) — **row Ep proper** | `D01.pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR` (`Section4/D01/PressureJets.lean:126`, "**P2 (eq:Rpressure) — unconditional**") | `Ioo 0 T` ✅ |
| `temporalSliceField` (`:117`) | `D01.temporalDerivative_slice_smoothSquareIntegrableJets_of_memForceR` (`Section4/D01/PressureJets.lean:147`) | `Ioo 0 T` ✅ |
| `forceSliceField` (`:129`) | `D01.forceSlice_smoothL2_of_memForceR` (`Section4/D01/Pressure.lean:304`) | `0 ≤ t` ✅ |

All four `_field` lemmas are literally `:= rfl` (`:99`, `:113`, `:125`, `:135`).

**`gradient` — no alias ambiguity (LESSONS-109).**  Probe
`research/C01/probes/rev143_gradient_alias.lean` reproduces the module's *exact* `open`
list (including the selective `open NavierStokes.ProblemStatement (…)` of `:76-78`) and
elaborates, EXIT 0:

```
@gradient : {𝕜 : Type u_1} → {F : Type u_2} → [inst : RCLike 𝕜] → [inst_1 : NormedAddCommGroup F] →
  [InnerProductSpace 𝕜 F] → [CompleteSpace F] → (F → 𝕜) → F → F
divergence : (Space → Space) → Space → ℝ
```
with `example : @gradient = @_root_.gradient := rfl` accepted.  So `gradient` is Mathlib's
`_root_.gradient`, not a vendor homonym; `divergence` is `EulerSmoothLimit.divergence`.  The
same probe prints the consumers, which display the *same* constants:

```
@energyIdentity_of_carrierB : ∀ {ν d : ℝ} (u f Gt P : SmoothL2Field Space) (p : Space → ℝ),
  ContDiff ℝ ∞ p → (∀ (x : Space), P.field x = gradient p x) →
    (∀ (x : Space), divergence u.field x = 0) → …
gradient_pairing_zero : ∀ (A U : SmoothL2Field Space) (p : Space → ℝ), ContDiff ℝ ∞ p →
  (∀ (x : Space), A.field x = gradient p x) → (∀ (x : Space), divergence U.field x = 0) →
  ⟪A.toLp, U.toLp⟫ = 0
EulerMeanHarmonic.gradient_coordinate : ∀ (f : Space → ℝ) (x : Space) (i : Fin 3),
  (gradient f x).ofLp i = EulerVectorCalculus.partialDerivative f i x
```

`pressureGradientField_eq_gradient` (`:149`) is therefore the genuine `hgrad`; its proof is
`PiLp.ext` + `D01.pressureGradient_apply` (`Section4/D01/MomentumSlice.lean:127`) +
`EulerMeanHarmonic.gradient_coordinate` + `rfl` — sound, since
`pressureGradient p t x = ∑ᵢ (fderiv ℝ (p(t,·)) x (coordinateVector i)) • coordinateVector i`
(`vendor/…/NavierStokes/ProblemStatement.lean:71-73`) and `coordinateVector i =
EuclideanSpace.single i 1` (`:39`).

`contDiff_pressureSlice` (`:140`) = `D01.contDiff_slice_scalar w.pressure_smooth` ✅.
`velocitySliceField_divergence` (`:161`) uses `EulerSmoothLimit.divergence_eq_coordinate_sum`
(`vendor/…/Euler/EulerProof.lean:5219`, `= ∑ᵢ (fderiv ℝ f x (single i 1)) i`), which is
term-for-term `spatialDivergence` (`ProblemStatement.lean:67-68`) ✅.

## 3. Row E3 — `hmom` matches token for token; both bridges genuine; interior only — PASS

**`hmom` shape.**  From the `#check` above, `energyIdentity_of_carrierB`'s last hypothesis is

```
Gt.toLp = ν • (laplacianField u).toLp - (advectionField u u).toLp - P.toLp + f.toLp
```

and `momentum_split_toLp` (`:197-204`) concludes exactly that with
`Gt := temporalSliceField`, `u := velocitySliceField`, `P := pressureGradientField`,
`f := forceSliceField`.  `energyIdentity_classical` (`:260-270`) passes it straight into
that slot, so the match is checked by the kernel, not by eye.

**`advectionField_velocitySlice_field` (`:172`) is genuine.**
`advectionField_field` (`vendor/…/Euler/OrdinaryFieldAlgebra.lean:121-122`, a proved
`@[simp]` lemma, not a definitional unfolding) gives
`(advectionField A B).field x = fderiv ℝ B.field x (A.field x)`; the manuscript
`advection u t x = spatialDerivative u t x (u (t,x)) = fderiv ℝ (fun y => u (t,y)) x (u (t,x))`
(`ProblemStatement.lean:59-64`).  With `A = B = velocitySliceField` these are the same term,
so the closing `rfl` is honest.

**`laplacianField_velocitySlice_field` (`:183`) is genuine, and `vector_laplacian_eq_sum`
is a real theorem.**  `laplacianField_field`
(`formalization/NSFormalization/Source/OrdinaryViscousStability.lean:16-17`) gives
`= Laplacian.laplacian W.field`; `EulerMeanVectorIdentities.vector_laplacian_eq_sum`
(`vendor/…/Euler/MeanVectorIdentities.lean:36-37`) is
`Δ f = fun x => ∑ i : Fin 3, vectorPartial (vectorPartial f i) i x`, proved at `:38-48` from
`laplacian_eq_iteratedFDeriv_orthonormalBasis` — not an axiom, not `sorry`.  With
`vectorPartial f i x = fderiv ℝ f x (EuclideanSpace.single i 1)` (`:14-15`) this is
term-for-term `spatialLaplacian u t x = ∑ᵢ fderiv ℝ (fun y => spatialDerivative u t y (eᵢ)) x (eᵢ)`
(`ProblemStatement.lean:76-79`), so the closing `rfl` is honest.

**Interior times only.**  `momentum_split_toLp` takes `ht : t ∈ Ioo (0:ℝ) T` and its only
use of the equation is `D01.temporalDerivative_slice_eq w ht x`
(`Section4/D01/Pressure.lean:196-203`), whose own hypothesis is `ht : t ∈ Ioo (0:ℝ) T` and
whose proof is `have h := u.momentum t ht x` — i.e. `ClassicalSolutionR.momentum` is invoked
**only** at interior times ✅.  The `Ioo_subset_Ico_self ht` / `le_of_lt ht.1` coercions are
used only for the velocity (valid on `Ico 0 T`) and force (valid for `0 ≤ t`) slots.

## 4. `energyIdentity_classical` — honest hypothesis, and *not* a weakening — PASS

**Docstring honesty.**  `:235-251` says it plainly, three times: the title is
"**eq:RL2's asserted derivative value for a classical solution, modulo row E4**"; the body
says "*given the row-E4 derivative-value fact* `hd : d = 2⟪u(t,·), ∂ₜu(t,·)⟫_{L²}`"; and the
last paragraph says "Row E4 … is the **single remaining input** and is **not** closed in
tree; see the module footer for the precise blocker".  The module header repeats it at
`:55-68` in bold, and explicitly **corrects** the old `ENERGY_SPLIT.md` E4 note.  This is an
honest explicit hypothesis documented as an open row, not a hidden placeholder.  Hard rule 3
(no placeholder `Prop` field in a **contract**) is not engaged: this is a `formalization/`
theorem and no contract file changed.

**`hd` is not an escape hatch** — probe `research/C01/probes/rev143_hd_not_escape.lean`,
EXIT 0, standard three axioms.  Because `hd` is satisfiable by `rfl` for every `w`, the
theorem is *equivalent* to the hypothesis-free identity, which the probe discharges as
`energyIdentity_classical w hf ht rfl`:

```lean
example … (w : ClassicalSolutionR ν a f T) (hf : MemForceR f) (ht : t ∈ Ioo (0:ℝ) T) :
    2 * ⟪(velocitySliceField w _).toLp, (temporalSliceField w hf ht).toLp⟫
      = -2 * ν * (∫ x, ∑ i : Fin 3, ‖fderiv ℝ (velocitySliceField w _).field x (axis i)‖ ^ 2)
          + 2 * (∫ x, ⟪(velocitySliceField w _).field x, (forceSliceField hf _).field x⟫) :=
  energyIdentity_classical w hf ht rfl
```

So the lane has proved a genuine **unconditional** theorem about `ClassicalSolutionR`; E4 is
only the step that converts the *value* `2⟪u,∂ₜu⟫` into a *derivative of the energy*.  That
is a materially stronger deliverable than "modulo a hypothesis" suggests, and is worth saying
in the merge note.

**Against the spec's asserted value** (`research/C01/Spec.lean:344-350`,
`-2 * ν * gradientSq (slice w.velocity t) + 2 * pairing (slice w.velocity t) (slice f t)`):

* `(velocitySliceField w ht).field = fun x => w.velocity (t,x) = slice w.velocity t` and
  `(forceSliceField hf ht).field = slice f t`, both `rfl` ✅.
* `2 * (∫ x, ⟪u x, f x⟫)` **is** `2 * pairing (slice u t) (slice f t)` definitionally —
  `pairing w z := ∫ x, (inner ℝ (w x) (z x) : ℝ)` (`Spec.lean:196`) and the scoped `⟪·,·⟫` is
  `inner ℝ` ✅.  (`REVIEW_E2.md` §2 already verified this `rfl` in the `verification` context.)
* `gradientSq` is **NOT** definitional — see Note 1.  The missing glue is exactly one
  verification-side line, already prototyped by 136's reviewer (`REVIEW_E2.md` §2):
  ```lean
  theorem gradientSq_eq_fderivSum (z : SpatialField) :
      gradientSq z = ∫ x : Space, ∑ i : Fin 3, ‖fderiv ℝ z x (axis i)‖ ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall fun _ => PiLp.norm_sq_eq_of_L2 _ _)
  ```
  (`coordinateVector = axis`, `spatialDerivative (lift z) 0 x = fderiv ℝ z x` and
  `gradientTensor = spatialGradient ∘ lift` are absorbed by defeq.)
* Still missing for the full spec field, beyond E4: the `HasDerivAt` wrapper and E2a applied
  on a *neighbourhood* of `t` (`ENERGY_SPLIT.md` finding 7's `HasDerivAt.congr_of_eventuallyEq`).

## 5. Paper citations — opened and checked

```
$ grep -n 'label{eq:RL2}' paper/sections/*.tex
paper/sections/04-whole-space.tex:118:\begin{equation}\label{eq:RL2}
$ awk 'NR>=117 && NR<=120' paper/sections/04-whole-space.tex
117: This controls the gradient … The separate ordinary energy identity, with regularized norm division, supplies
118: \begin{equation}\label{eq:RL2}
119:  \norm{u(t)}_2\le\norm{a}_2+\int_0^t\norm{f(s)}_2\dd s=:K(t).
120: \end{equation}
```
`:117` is indeed where "The separate ordinary energy identity" appears — the same anchor
`Spec.lean:331` uses for the `energyIdentity` field.  See Note 2 on the `eq:RL2` wording.
`ENERGY_SPLIT.md`'s `**energyIdentity** (:344)` matches `Spec.lean:344` ✅.

## 6. E4 obstruction audit — the blocker is real; **route (b) is the more expensive one**

### (a) the hypothesis package — CONFIRMED verbatim

`vendor/NavierStokesAndEuler/Euler/OrdinaryWordTime.lean:69-75` is a `variable` block,
pulled into `:87` by `include hA hB hd in` at `:86`:

```lean
variable (T : ℝ) (hT : 0 ≤ T)
  (A B : Icc (0 : ℝ) T → SmoothL2Field Space)
  (hA : ∀ n, Continuous (fun t => (A t).jetLp n))
  (hB : ∀ n, Continuous (fun t => (B t).jetLp n))
  (hd : ∀ t (ht : t ∈ Ioo 0 T) x,
    HasDerivAt (fun r => (A (projIcc 0 T hT r)).field x) ((B ⟨t,ht.1.le,ht.2.le⟩).field x) t)
include hA hB hd in
theorem wordEnergy_hasDerivWithinAt (s : ℕ) (t : Icc (0 : ℝ) T) : …
```
Exactly as `ATTEMPTS_E3E4.md` §3 quotes it.  ✅

### (b) nothing in tree already gives the time-continuity — CONFIRMED

Sweep: `grep -rn 'Continuous\|ContinuousOn' formalization/NSFormalization/Section4/ |
grep -iE 'pressure|temporal|momentumResidual|jetLp'` (all hits inspected):

* `Section4/C01/Evolution.lean:164` `velocityField_jetLp_continuous` — this is the `hA`, for
  the **velocity only**; its own docstring `:162-163` already says "the pressure jets (and,
  through them, the time-derivative field) remain".
* `Section4/D01/PressureJets.lean:126` (P2) and `:147` (the `∂ₜu` corollary) — both
  `{t : ℝ} (ht : t ∈ Ioo 0 T)`, i.e. **pointwise in `t`**; nothing about `t`-continuity.
  The worker's correction of the old `ENERGY_SPLIT.md` E4 note is right.
* `Section4/A01/DatumPathContinuity.lean` — `continuous_orderZeroDatum` (`:127`),
  `continuousOn_datumPath` (`:144`) are **generic order-0** tools for an `L²`-continuous
  path; no `∇p` statement.
* `Section4/A01/Continuation.lean:99,121,173,213,251` and
  `Section4/A01/ContinuationInvariant.lean:71,158,215,283` — all take
  `hF : ∀ n, Continuous fun t => (F t).jetLp n` for a **force** path as a *hypothesis*.
* `Section4/A02/Energy.lean` — only `uniformFiniteEnergy*` (bounds, no continuity).
* `Section4/A04/*` — pointwise datum work only; no hit for pressure/temporal continuity.

### (c) route comparison — **recommend route (a), not route (b)**

**Route (b) (uniqueness transport) is currently strictly dominated**, for two independent
reasons:

1. *No source object.*  `A02.velocity_unique` (`Section4/A02/Uniqueness.lean:120-127`)
   identifies **two `ClassicalSolutionR`s**, but the tree contains **no theorem that
   constructs one**.  Every `∃ w : ClassicalSolutionR` / `Nonempty (ClassicalSolutionR …)`
   in `Section4/` takes a solution as input: `A02/Restrict.lean:83,90,208,217,271`,
   `A02/Maximal.lean:89,95,101`, `A02/Patch.lean:92,134`, `R42/FullHorizon.lean:147`,
   `R42/SolutionOnShorter.lean:90`.  A01 is still open — `Section4/A01/CarrierBridge.lean`
   proves only the **order-0** C1b row (`isSobolevDatum_zero_ordinaryL2`, `:98`), and there is
   **no `HeliCorgiPort.lean`** in `Section4/A01/` (files there: `CarrierBridge`,
   `ContinuationInvariant`, `Continuation`, `ConvectionDivergence`, `DatumPathContinuity`,
   `ForceCap`, `PressureGauge`, `ProjectedEquation`, `Propagation`, `RadialPotential`).  So
   route (b) presupposes the whole blocked A01 chain (C1b/C1c + A3/B1).
2. *The vendor does not prove `hB` for its own solutions either — it **assumes** it.*
   `Euler/SmoothEulerEvolution.lean:47` `rhs_jet_continuous` takes
   `hG : ∀ n, Continuous (fun t => (G t).jetLp n)` for the **pressure-force path** as a
   hypothesis; `Euler/OrdinaryEulerDifference.lean:21-27` bundles `pressure_continuous` as a
   *field* of its `Evolution` structure; and all three call sites of
   `wordEnergy_hasDerivWithinAt` (`Euler/OrdinaryRegularizedEnergy.lean:65`,
   `Euler/OrdinaryEulerHigherEnergy.lean:51`, `Euler/OrdinaryEulerDifference.lean:129`)
   instantiate `A := U.velocity`, `B := U.derivative` of such a structure.  So even with A01
   landed, `hB` would still have to be built.  There is **no** vendor theorem giving
   `hA`/`hB`/`hd` unconditionally for a constructed local solution.

**Route (a) (the time-regular P2 unit) is cheaper than `ATTEMPTS_E3E4.md` §3 estimates,**
because four of its five pieces already exist.  Exact missing declarations:

| # | needed declaration | status | size |
|---|---|---|---|
| 1 | `forceField_jetLp_continuous` — `∀ n, Continuous (fun s => (forceSliceField … s).jetLp n)` | **missing**, but a verbatim mirror of `Evolution.velocityField_jetLp_continuous` (`C01/Evolution.lean:164`): `MemForceR` (`A02/SolutionClass.lean:100-106`) gives per order `m` a datum path with **`ContDiffOn ℝ ∞ G futureTimes`** — *stronger* than the velocity's `ContinuousOn` — and `jetOfDatum_continuous` (`C01/Evolution.lean:147`) + `D01.jetOfDatum_ae` apply unchanged | **S** |
| 2 | `laplacianField` / `ν •` jet continuity | assemble from vendor: `SmoothL2Field.continuous_jetLp_directionalField` (`Euler/LpSmoothFieldAlgebra.lean:147`) twice, `continuous_jetLp_addField` (`:128`) over `Finset.univ (Fin 3)` (`laplacianField` is `sumField`, `Euler/OrdinaryFieldAlgebra.lean:18`; `Fin.sum_univ_three` or a 3-line induction), `continuous_jetLp_mapField` (`:119`) or `continuous_jetLp_scaleField` (`Euler/SmoothL2ScalingContinuity.lean:47`) for `ν •` | **S** |
| 3 | `(u·∇)u` jet continuity | **already exists**: `EulerSmoothEulerEvolution.advection_jet_continuous` (`Euler/SmoothEulerEvolution.lean:29-32`), from `hU` alone; `advection_field` (`:23-27`) matches `advectionField_field` | **none** |
| 4 | a **continuous-in-time order-`m` datum path** for the momentum residual `h(s,·) = f − (u·∇)u + νΔu` — the `s`-continuous upgrade of `A04.momentum_datum` / `D01.smoothL2_momentumResidual_slice` | **missing; this is the whole cost.**  Needs continuity of the tame product in its datum argument (`Section4/A03/OuterTameProduct.lean`) | **M–L** |
| 5 | push through the Leray complement | **already a CLM**: `D01.Leray.lerayComplement (s : ℝ) : RealVectorSobolev s →L[ℝ] RealVectorSobolev s` (`Section4/D01/LerayDatum.lean:255`, `mkContinuous 1`), and `D01.pin_pressureGradient_datum` (`PressureJets.lean:112`) already pins `∇p`'s datum to `lerayComplement m Am` | **none** |

So `ATTEMPTS_E3E4.md` §3's "pushing it through `Leray.lerayComplement` as a continuous
composition — a genuine new analysis obligation" **overstates the blocker**: the
`lerayComplement` leg is a continuous linear map already in tree, and steps 1–3 and 5 are
free or small.  Only step 4 is new mathematics.

**Recommendation:** open route (a) as two lanes — a small one for rows 1+2 (both **S**,
immediately doable, and reusable by E5's enstrophy row), and one **M–L** lane for row 4, the
continuous-in-time momentum-residual datum path.  Do **not** pursue route (b) until A01
lands, and note that even then it does not avoid building `hB`.

(Checked and rejected as a shortcut: proving `energyDifferentialBound` (`Spec.lean:353-362`)
first does not dodge E4 — its `∀ E', HasDerivAt … E' t → …` still needs a derivative to pin
`E'` against, via `HasDerivAt.unique` against E4.)

## 7. Negative check — PASS (two substantive statement mutations)

Probe `research/C01/probes/rev143_mutation.lean`, `set_option autoImplicit false` (so a
changed statement cannot be silently rescued by implicit re-binding, LESSONS 077), each
mutation carrying the lane's **verbatim** proof script.  EXIT 1, both fail at `abel`:

**M1 — flip the sign of the `∇p` term** (`- P.toLp` ⇝ `+ P.toLp`):
```
../research/C01/probes/rev143_mutation.lean:34:57: error: unsolved goals
⊢ f (t, x) + (-1 • advection w.velocity t x + (ν • spatialLaplacian w.velocity t x
      + -1 • pressureGradient w.pressure t x)) =
  f (t, x) + (-1 • advection w.velocity t x + (ν • spatialLaplacian w.velocity t x
      + pressureGradient w.pressure t x))
```

**M2 — drop the viscosity** (`ν • Δu` ⇝ `Δu`):
```
../research/C01/probes/rev143_mutation.lean:71:57: error: unsolved goals
⊢ f (t, x) + (-1 • advection w.velocity t x + (ν • spatialLaplacian w.velocity t x
      + -1 • pressureGradient w.pressure t x)) =
  f (t, x) + (-1 • advection w.velocity t x + (-1 • pressureGradient w.pressure t x
      + spatialLaplacian w.velocity t x))
```
Both residual goals display exactly the mutated summand, so the `∇p` sign and the `ν`
coefficient are load-bearing — neither is a dropped argument.

## 8. Honesty of ATTEMPTS / ENERGY_SPLIT — PASS

Every declaration and line number cited in `ATTEMPTS_E3E4.md` was opened; all are correct:
`LpSmoothField.lean:31`, `OrdinaryFieldAlgebra.lean:132` (the `@[simp] advectionField_field`
body is at `:122`, the lemma header at `:121` — the file-local drift is one line, harmless),
`Source/OrdinaryViscousStability.lean:19` (`laplacianField_field` at `:16-17`, again one line),
`OrdinaryWordTime.lean:87`, `PressureJets.lean:150` (the `∂ₜu` corollary is at `:147`),
`MeanHarmonicLaplacian.lean:13`.  The three recorded errors (§4.1 ambiguous `Space`,
§4.2 unqualified `gradient_coordinate`, §4.3 the `Pi.add_apply`/`Pi.sub_apply` interleaving)
are all consistent with what I reproduced in the mutation probe, where the same `rw` chain is
needed.  §4.4's claim that plain `rfl` closes the Laplacian bridge is confirmed by finding 3.

---

## Notes (one-line fixes; none blocks the merge)

**Note 1 (docstring precision).**  `MomentumCarrierB.lean:52-53` ("raw-integral form,
definitionally the spec quantities") and `:243-244` ("definitionally the spec's
`gradientSq`/`pairing` on the carrier's `.field`") are accurate for `pairing` but **not** for
`gradientSq`, which needs the `PiLp.norm_sq_eq_of_L2` one-liner (`REVIEW_E2.md` §2 recorded
the `rfl` failure).  Suggested wording: "definitionally the spec's `pairing`; `gradientSq`
after the one-line `PiLp.norm_sq_eq_of_L2` binding (see `Vocabulary.lean`'s header)".
Inherited phrasing from `Vocabulary.lean:41-44`, whose own parenthetical carries the caveat,
so this is not a lane regression.

**Note 2 (paper citation).**  `MomentumCarrierB.lean:11` writes "the ordinary energy identity
eq:RL2 (`paper/sections/04-whole-space.tex:117`)".  `:117` is the right anchor for the phrase
"The separate ordinary energy identity", but `\label{eq:RL2}` is at `:118` and labels the
*L² bound* `‖u(t)‖₂ ≤ ‖a‖₂+∫₀ᵗ‖f(s)‖₂` at `:119` — a different display.  The identity itself
carries no label in the tex.  Copied verbatim from the merged `Vocabulary.lean:11-12`, so
again not a lane regression; fix both together in the next SIMP lane if at all
(per LESSONS: re-`grep` the label rather than inheriting a line number).

**Note 3 (`ENERGY_SPLIT.md` E4 row).**  The row now reads "a new time-regularity unit, ≈L".
Finding 6(c) argues **M–L concentrated in one unit**, with three of the five pieces already
in tree/vendor and `Leray.lerayComplement` already a `→L[ℝ]`.  Worth amending the row (and
the same sentence in `ATTEMPTS_E3E4.md` §3) so the next planner does not over-budget it.

**Note 4 (non-vacuity, informational).**  `research/C01/axioms_e3e4.lean:6-12` says a full
non-vacuity witness for `ClassicalSolutionR` is deliberately not built.  That is not just a
cost decision — finding 6(c)(1) shows the tree *cannot* build one yet (no construction
theorem exists).  Honest as written; worth linking to the A01 blocker in the record.

---

## Commands run (worktree `.claude/worktrees/143-C01-e3-e4-momentum`, `. scripts/lean-env.sh`)

| command | result |
|---|---|
| `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.C01.MomentumCarrierB` | exit 0, `Build completed successfully (10190 jobs)`, 0 lines mentioning the module |
| `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/C01/axioms_e3e4.lean` | exit 0, 12/12 `[propext, Classical.choice, Quot.sound]` |
| `cd verification && lake env lean ../research/C01/probes/rev143_gradient_alias.lean` | exit 0 — `gradient = _root_.gradient` by `rfl`; consumers print the same constant |
| `cd verification && lake env lean ../research/C01/probes/rev143_hd_not_escape.lean` | exit 0 — hypothesis-free identity discharged by `… ht rfl`; standard three axioms |
| `cd verification && lake env lean ../research/C01/probes/rev143_mutation.lean` | **exit 1** (intended): both mutations `unsolved goals` at `abel` |
| `make check` | exit 0 (13 contract-policy tests OK; 30 work items consistent) |
| `python3 experiments/build_changed_lean.py --base-ref origin/erenup/integration` | `Changed Lean modules: NSFormalization.Section4.C01.MomentumCarrierB` |
| `grep -nE 'sorry\|admit\|axiom\|native_decide\|maxHeartbeats\|set_option' …/MomentumCarrierB.lean` | no output |
