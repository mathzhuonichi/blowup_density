# REVIEW — lane 153 (`153-A01-l2-descent`): the `L²`-level descent, piece (d) of the carrier bridge

Reviewer: opus, read-only, worktree `.claude/worktrees/153-A01-l2-descent`, branch
`erenup/153-A01-l2-descent`, HEAD `b251d28`. No edits to lane files, no git state changes. New files
written by the reviewer: this report and `research/A01/probes/rev153_{fidelity,consumer,subsumes,mut1_slice,mut2_noinv,mut3_body}.lean`.

## Verdict: **ACCEPT-WITH-NOTES**

The mathematics is correct, the four statements are what they claim to be, `exists_ordinaryLift_of_invariant`
is token-identical to the target `DescentL2`, and `hword_jet_full` genuinely discharges lane 149's
named hypothesis for **all** `n ≤ q+1` (verified by a probe that applies it). All six notes below are
record-file / follow-up level; **none** requires a change to `L2Descent.lean`.

---

## 1. What the lane claims

Piece **(d)** of row (i)'s four-part carrier bridge (`research/A01/REVIEW_APRIORI_ROWS.md` §2,
`research/A01/ATTEMPTS_APRIORI_ROWS.md:132-160`): every angle-invariant `L²` cylinder field is the
`ordinaryLift` of a `θ`-independent ordinary `L²` field on `ℝ³`, **with no jet/regularity
hypothesis** — so the 3-order jet loss of `EulerPairing.exists_descend`
(`EulerPairing.lean:296-299`, `hnq : n + 3 ≤ q`) disappears and the top three orders
`n ∈ {q−1, q, q+1}` of `hword_jet` are covered. Route claimed: `θ`-averaging + Fubini for null sets,
**not** the `AddCircle` Fourier route the lane-151 review recommended.

## 2. What is in Lean now

New file `formalization/NSFormalization/Section4/A01/L2Descent.lean` (231 lines, 4 theorems, zero
`sorry/admit/axiom/native_decide/maxHeartbeats/set_option`, all four `#print axioms` standard three).

### 2.1 `exists_ordinaryLift_of_invariant` (`L2Descent.lean:63-133`) — statement fidelity ✅

```
theorem exists_ordinaryLift_of_invariant (g : LiftL2 1)
    (hginv : ∀ θ : AddCircle (1 : ℝ), translation 1 ((0 : Vector3), θ) g = g) :
    ∃ G : EulerMeanSolenoidal.L2, ordinaryLift G = g
```
versus the target `DescentL2` (`research/A01/probes/probe151_descent_L2.lean:28-30`)

```
∀ g : LiftL2 1, (∀ θ : AddCircle (1 : ℝ), translation 1 ((0 : Vector3), θ) g = g) →
  ∃ G : EulerMeanSolenoidal.L2, ordinaryLift G = g
```

Token-identical. I did **not** take this on inspection: `research/A01/probes/rev153_fidelity.lean`
restates `DescentL2` verbatim in probe-151's *own* `open` environment — which deliberately does not
`open EulerLpTranslation`, while the lane module does — and discharges it by
`theorem descentL2_holds : DescentL2 := exists_ordinaryLift_of_invariant`. It typechecks
(3-axiom), so `translation` / `ordinaryLift` / `LiftL2` / `EulerMeanSolenoidal.L2` / the local
`Fact (0 < (1:ℝ))` instance all resolve to the same constants in both environments (LESSONS
2026-09-14 0839Z/152: a selective `open` can silently resolve a bare name to a vendor homonym; this
probe rules that out). `#check` in the same probe prints

```
NSFormalization.Section4.A01.exists_ordinaryLift_of_invariant : ∀ (g : ↥(LiftL2 1)),
  (∀ (θ : AddCircle 1), (translation 1 (0, θ)) g = g) → ∃ G, ordinaryLift G = g
```

**No weakening anywhere**: `hginv` is for *every* `θ` as an equality of `Lp` classes (not a.e., not
one `θ`); the conclusion is an honest equality in `LiftL2 1`; no `MemLp`, `ContDiff`, jet or
finiteness side condition is attached.

**Fidelity trap checked and clean.** `EulerMeanSolenoidal.L2` is `Lp Space 2 volume`
(`vendor/NavierStokesAndEuler/Euler/MeanSolenoidalSpace.lean:22`) — despite the namespace it carries
**no** solenoidal or mean constraint, so `∃ G : EulerMeanSolenoidal.L2` is *not* a divergence-free
claim. The module docstring (`L2Descent.lean:24`) says this explicitly. `Space` and `Vector3` are both
`EuclideanSpace ℝ (Fin 3)` (`ProblemStatement.lean:30`, `EulerProof.lean:1083`), which is why the
two `Lp` types are comparable at all.

### 2.2 The three points the brief asked me to check in the proof

**(a) The uncountable family of null sets — handled correctly.** `hginv θ` is an `Lp`-class equality;
`translation_ae` (`vendor/NavierStokesAndEuler/Euler/EulerProof.lean:1227-1229`) turns it into
`⇑g =ᵐ[liftMeasure 1] fun x => ⇑g (x + (0,θ))`, whose null set depends on `θ`. Two things are done
right at `L2Descent.lean:67-94`:

* the a.e. datum is first transported onto a **strongly measurable representative** `g₀` (`:67-71`,
  `(Lp.aestronglyMeasurable g).mk`), on *both* sides — the translated side through
  `(measurePreserving_translation 1 (0,θ)).quasiMeasurePreserving.ae hg₀ae` (`:80-82`), which is the
  step you cannot skip (`hg₀ae` alone does not apply at the translated point);
* the swap is `Measure.ae_ae_comm` at `:92-94` with `α := AddCircle 1`, `β := LiftDomain 1`,
  `μ := volume`, `ν := liftMeasure 1`, `p θ pt := (g₀ pt = g₀ (pt + (0,θ)))`, fed
  `ae_of_all _ hinv0` (weakening `∀ θ` to `∀ᵐ θ`). The measurability side condition is exactly
  `{z : AddCircle 1 × LiftDomain 1 | g₀ z.2 = g₀ (z.2 + ((0:Vector3), z.1))}` (`:86-91`), i.e.
  `{x | p x.1 x.2}` in the lemma's own indexing — I checked the index order against the printed
  signature (`probe153_sigs.lean` output, reproduced in §5), and it matches. Measurability is
  `measurableSet_eq_fun` applied to `g₀ ∘ snd` and `g₀ ∘ (fun z => z.2 + (0,z.1))`, the latter built
  explicitly as `measurable_snd.add (measurable_const.prodMk measurable_fst)`;
  `MeasurableEq Space` comes from the second-countable + T2 instance at
  `Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean:620`
  (`instance [SecondCountableTopology α] [T2Space α] : MeasurableEq α`) — the ATTEMPTS citation is
  correct to the line. `SFinite` on both sides is automatic (`liftMeasure` is a product of
  σ-finite measures). **This is the legitimate Fubini-for-null-sets move, and the reason the
  strongly-measurable representative had to be taken first.**

**(b) `AddCircle 1` carries the probability Haar measure.**
`AddCircle.measure_univ : volume (univ : Set (AddCircle T)) = ENNReal.ofReal T`
(`Mathlib/MeasureTheory/Integral/IntervalIntegral/Periodic.lean:69`), so at `T = 1` the total mass is
`1`; the local instance at `L2Descent.lean:56-59` proves exactly that, and it is `local` so it does
not leak. Left-invariance for `integral_add_left_eq_self` comes from
`instance : IsAddHaarMeasure (volume : Measure (AddCircle T))` (same file, `:74`). Both require
`[Fact (0 < T)]`, supplied at `:54`. ✅

**(c) `translation 1 ((0:Vector3), θ)` really acts as `pt ↦ pt + (0,θ)`.**
`translation period a := Lp.compMeasurePreservingₗᵢ ℝ (fun x => x + a) (measurePreserving_translation period a)`
(`EulerProof.lean:1223-1225`), with `measurePreserving_translation` at `:1216-1221` for the map
`fun x : LiftDomain period => x + a`, and `translation_ae` at `:1227-1229`. With
`LiftDomain 1 = Vector3 × AddCircle 1` (`:1085`) and
`liftMeasure 1 = (volume : Measure Vector3).prod (volume : Measure (AddCircle 1))` (`:1092-1093`),
`pt + ((0:Vector3), θ) = (pt.1, pt.2 + θ)` (`Prod.add_def` + `add_zero`, used at `L2Descent.lean:104-107`).
So the hypothesis really is "invariance under rotating the angle only", which is what the proof
consumes. ✅

**The slice-constancy chain (`:99-110`) is unconditional in integrability** — I re-ran it as a
standalone positive control in `rev153_mut1_slice.lean` and it closes:
`g₀ pt = ∫ g₀ pt` (`integral_const` + probability), `= ∫ g₀ (pt+(0,θ))` (`integral_congr_ae hpt`,
no integrability needed — both sides are Bochner integrals of a.e.-equal integrands),
`= ∫ g₀ (pt.1, pt.2+θ)`, `= ∫ g₀ (pt.1,θ)` (`integral_add_left_eq_self`, proved from a
measure-preserving change of variables, also integrability-free), `= G₀ pt.1`. No hidden
`Integrable` obligation, no `⊤`/junk-value hazard.

**The `L²` step (`:113-124`)** is `memLp_map_measure_iff` through
`ordinaryProjection_measurePreserving.map_eq : map Prod.fst (liftMeasure 1) = volume`
(`vendor/…/MeanOrdinaryLift.lean:19-21`), with `AEStronglyMeasurable.integral_prod_right'` giving
measurability of the average; the `MemLp` on the product side is `(Lp.memLp g).ae_eq hgfst`.
**Assembly (`:126-133`)** is `Lp.ext` on `ordinaryLift_ae` (`MeanOrdinaryLift.lean:27-29`) +
`MemLp.coeFn_toLp` pushed through `ordinaryProjection_measurePreserving.quasiMeasurePreserving.ae`.
All correct.

### 2.3 `word_descent_ae_top` (`:142-149`) — no order bound sneaks in ✅

`hn : n ≤ q + 1` is used **only** to form the array index `⟨⟨n, Nat.lt_succ_of_le hn⟩, …⟩`, which is
literally the definition of `word` (`vendor/…/CylinderSobolevSpace.lean:66-67`). The invariance of
the word is the same `congrArg (fun v => v.val ⟨…⟩) (hu θ)` that `exists_descend`'s `hinv` uses
(`EulerPairing.lean:305`); it typechecks because `liftOperator_apply` is `rfl`
(`vendor/…/CylinderSobolevOperators.lean:85-89`), so `(sobolevTranslation 1 (q+1) a u).val w` is
*definitionally* `translation 1 a (u.val w)` and `sobolevTranslation` is `liftOperator` of
`translation` (`:117-118`). Nothing else in the proof is order-sensitive.

### 2.4 `word_descent_ae_full` (`:156-189`) — the `n+3 ≤ q+1` restriction really only came from `exists_descend` ✅

Side-by-side against `CarrierWords.word_descent_ae` (`CarrierWords.lean:242-276`): the two proofs
are line-for-line identical except that `obtain ⟨Zw', hZw'⟩ := exists_descend u hu (…) (by omega) (by omega)`
(`:278-279`) becomes `obtain ⟨Zw', hZw'⟩ := word_descent_ae_top u hu n hn' (Fin.tail w)`
(`L2Descent.lean:178`), and `hn' : n + 3 ≤ q + 1` becomes `hn' : n ≤ q + 1`. The two other
ingredients of the induction step carry **no** order bound, which I checked at the source:

* `descent_step_ae` (`CarrierWords.lean:183-189`) quantifies over arbitrary `Zw Zc : EulerMeanSolenoidal.L2`
  and a `HasDerivAt` hypothesis — no `n`, no `q` at all;
* `word_hasDerivAt` (`vendor/…/CylinderSobolevSpace.lean:70-77`) needs only `hn : n < q`, here
  `hlt : n < q + 1`, which follows from `hn : n + 1 ≤ q + 1` by `omega`.

The base case is unchanged (`ordinaryLift.injective` on the empty word). So the generalisation is
sound and the docstring's claim ("the induction closes verbatim") is accurate.

### 2.5 `hword_jet_full` (`:199-229`) — it does discharge `AprioriRows`' named hypothesis ✅

`AprioriRows.sobolevSpace_norm_le_sobolevENorm` (`AprioriRows.lean:287-291`) asks for
```
hword_jet : ∀ (n : ℕ) (hn : n ≤ q + 1) (w : Fin n → Fin 4),
    ‖word 1 u hn w‖ ≤ (eLpNorm (iteratedFDeriv ℝ n z) 2 volume).toReal
```
and `hword_jet_full`'s conclusion is that statement with `z := Z.field`, character for character.
I did not eyeball this either — `research/A01/probes/rev153_consumer.lean` closes the loop:

```
theorem converse_no_hword_jet {q : ℕ} (u : SobolevSpace 1 (q + 1))
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (U : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u)
    (Z : SmoothL2Field Space) (hUz : (⇑U) =ᵐ[volume] Z.field)
    (hfin : sobolevENorm ((q + 1 : ℕ) : ℝ) Z.field ≠ ⊤) :
    ‖u‖ ≤ jetSobolevConst (q + 1) * (sobolevENorm ((q + 1 : ℕ) : ℝ) Z.field).toReal :=
  sobolevSpace_norm_le_sobolevENorm u Z.smooth hfin (hword_jet_full u hu U hU Z hUz)
```

typechecks, 3-axiom. `hz` is free (`Z.smooth`); `hfin` is **not** free from `SmoothL2Field`
(`Z.integrable n` bounds each `eLpNorm (iteratedFDeriv ℝ n Z.field)`, which is a different quantity
from `sobolevENorm`) and is carried as a hypothesis — downstream it comes from
`ClassicalSolutionR.sobolev`, exactly as `AprioriRows.lean:59-61` says. The `.toReal` direction is
safe: the RHS is finite by `Z.integrable n` (`L2Descent.lean:220`), so this is not a `⊤.toReal = 0`
artefact (LESSONS 09-14 0707Z/149 hazard checked, and it points the other way here).

The `.toReal` monotonicity, the `ordinaryLift.norm_map` / `Lp.norm_def` / `eLpNorm_congr_ae` chain
and the angular-word case split are lifted unchanged from `hword_jet_of_descent`
(`CarrierWords.lean:311-339`); the only difference is `hn : n ≤ q + 1` in place of `n + 3 ≤ q + 1`.

**Strictly stronger, verified**: `research/A01/probes/rev153_subsumes.lean` derives lane 151's
`hword_jet_of_descent` and `word_descent_ae` from the lane-153 versions, and instantiates
`hword_jet_full` at the top order `n = q + 1` (which 151 could not reach). All three typecheck.

### 2.6 Non-vacuity

`research/A01/axioms_l2_descent.lean:17-27` gives `g = 0` and `g = ordinaryLift G₀` for arbitrary
`G₀`. My probe `rev153_mut2_noinv.lean` proves the **converse**,
`invariance_necessary : (∃ G, ordinaryLift G = g) → ∀ θ, translation 1 (0,θ) g = g`
(`ordinaryLift_translation`, `MeanOrdinaryLift.lean:31-42`), so together with the lane's theorem

> `range ordinaryLift = {g : LiftL2 1 | ∀ θ, translation 1 ((0:Vector3),θ) g = g}`

i.e. the hypothesis is not merely sufficient, it is *exactly* the image characterisation. That makes
witness 2 the general case, and it makes the theorem a genuine equality of two sets rather than a
one-sided existence statement. See note N7 for the one thing this does not formally rule out.

---

## 3. Gaps — what row (i) still owes, ranked by cost

With (a)(b)(c) (lane 151) and (d) (this lane), **the carrier-bridge lemma of row (i) is complete and
`hword_jet` is discharged for every `n ≤ q+1`.** What remains between here and `HasAprioriBound`
(`Horizon.lean:106`), cheapest first:

| # | Obligation | Exact statement | Cost |
|---|---|---|---|
| 1 | **Wire `Z` to the real velocity slice** | From a `ClassicalSolutionR ν a f T` with velocity `v`, produce `Z : SmoothL2Field Space` with `Z.field = fun x => v (t,x)`: `D01.exists_smoothL2Field_of_memHInfty (hz : ContDiff ℝ ∞ z) (hA : ∀ m, ∃ A : RealVectorSobolev (m:ℝ), IsSobolevDatum (m:ℝ) z A) : ∃ B : SmoothL2Field Space, B.field = z` (`D01/DatumToJets.lean:306-309`); `hz` from `DatumToJets.contDiff_slice`, `hA` from `ClassicalSolutionR.sobolev` | **S** — both inputs exist; pure plumbing, one short lemma |
| 2 | **`hfin` for the slice** | `sobolevENorm ((q+1:ℕ):ℝ) (fun x => v (t,x)) ≠ ⊤` for every `t : Icc 0 T` | **S** — same `ClassicalSolutionR.sobolev` datum; likely falls out of #1 |
| 3 | **`hslice` + horizon matching (row (i), the residue)** | `∀ t : Icc 0 T, (fun x => v (↑t,x)) =ᵐ[volume] ⇑(U t)` from the cylinder pair `(u,U)` of `Horizon.exists_local_shape_of_aprioriBound`, **plus** matching the `ClassicalSolutionR` horizon `T` to the cylinder path's index `Icc 0 T` (the `∃ T` of `exists_local` is chosen by the local theory, not by the caller) | **M–L** — the a.e. identification is the genuinely new content; the horizon match is bookkeeping but needs a decision about which `T` is primary |
| 4 | **(iv) `hinv`** | `∀ θ (t : Icc 0 T), sobolevTranslation 1 (q+1) (0,θ) (u t) = u t` for the `u` that `HasAprioriBound` quantifies over — `HasAprioriBound` constrains `u` only by the Duhamel equation (`Horizon.lean:106-115`), and *both* the forward route and (ii)'s `hword_jet` need it (review note N2 of lane 149: the angular words of `Fin 4` vanish only under invariance). Once in hand `U` is free via `Continuation.forced_ordinary_descent` | **L** — unit A2b; unchanged by this lane, now the single largest blocker of row (i)'s consumer |
| 5 | **(v) `F ↔ f` datum/forcing bridge** | From `(a : SmoothL2Field Space, F : Icc 0 S → SmoothL2Field Space)` produce `(a' ∈ initialClassR, f : SpaceTimeField)` with `MemForceR f`, `MemL1Hm f`, and a `ClassicalSolutionR ν a' f T` whose velocity is the cylinder path's carrier. No A01 module connects the two vocabularies today | **M–L** |
| 6 | **`t = T` Grönwall endpoint (row iii-b)** | The Grönwall *output* at the closed endpoint. The *cap* at `T₀ = T` exists (`kbnd_of_sup_bound_Icc_endpoint`), and the cylinder-level `‖u‖ ≤ R` on `Icc 0 T` is free (`u` is a `ContinuousMap`); what is missing is `highContinuationIntegral` at `t = T`, which needs the energy identity *at* `T`, not interval bookkeeping | **L** — the genuine eq:criterion endpoint, deliberately untouched |

So the cheapest genuinely-next lane is **#1+#2 together** (a single small module turning a
`ClassicalSolutionR` velocity slice into the `Z : SmoothL2Field Space` + `hfin` that
`sobolevSpace_norm_le_sobolevENorm` and `hword_jet_full` both consume), after which row (i) reduces
to #3, and the A01 chain's real blocker is #4.

---

## 4. Numbered findings

All **notes**. None blocks the merge; none touches `L2Descent.lean`.

**N1 (record, cosmetic, one-line fix).** `research/A01/A3_SPLIT.md` — the lane-153 block is inserted
at line 270, *above* the lane-151 block at line 271, while the file's other updates run oldest →
newest (147 @263, 149 @265, 149-post-review @267). Worse, the now-stale lane-151 sentence
"**Only (d) OPEN (L)** …" is what a reader hits at the end of the file.
*Fix: move the added lines 269-270 to the end of the file, after the lane-151 paragraph.*

**N2 (record, honesty, one-line fix).** `research/A01/ATTEMPTS_L2_DESCENT.md:88-96` heads a list
"Mathlib lemmas **used**" that includes `Measure.ae_ae_of_ae_prod` and
`StronglyMeasurable.integral_prod_right`; neither occurs in `L2Descent.lean`
(`grep -c ae_ae_of_ae_prod` → `0`; the module uses `Measure.ae_ae_comm` and the
`AEStronglyMeasurable.integral_prod_right'` variant). They are only `#check`ed in
`probe153_sigs.lean`.
*Fix: change the heading to "…lemmas used, plus candidates `#check`ed in `probe153_sigs.lean`", or
drop the two names.*

**N3 (follow-up, simplifier lane, not blocking).** `hword_jet_full` and `word_descent_ae_full` now
strictly subsume `CarrierWords.hword_jet_of_descent` (`:311`), `word_descent_ae` (`:242`) and
`word_descent_ae_partial` (`:284`) — proved in `research/A01/probes/rev153_subsumes.lean`. Having
two `hword_jet` suppliers with different order hypotheses is exactly the kind of duplication that
later lanes cite wrongly. *Fix in the next `NNN-SIMP-A01` lane: restate the three 151 theorems as
one-line corollaries of the 153 ones, or delete them; do not do it in this lane (never mix
simplification with new mathematics).*

**N4 (CI coverage).** `NSFormalization.Section4.A01.L2Descent` is inside **no** registered contract
closure (`grep -rl Section4.A01 verification/` hits only `Bindings/RegularityPartial.lean` and
`Contracts/V1/RegularityPartial.lean`). It *is* compiled on this PR —
`experiments/build_changed_lean.py --base-ref origin/erenup/integration --dry-run` prints
`Changed Lean modules: NSFormalization.Section4.A01.L2Descent` — but nothing keeps it compiling after
the merge. *Fix: add it (with `CarrierWords`, `AprioriRows`) to the next A01 contract bundle;
tracked, not blocking.*

**N5 (lead action before merge, not a lane defect).** The lane branched at `0077b7e`; integration has
since merged lane 152's `verification/Contracts/V2/EnergyAbsorptionPartial.lean`. So on this branch
`python3 experiments/check_contracts.py --base-ref origin/erenup/integration` fails with
`AssertionError: Removed stable specification: verification/Contracts/V2/EnergyAbsorptionPartial.lean`.
That is stale-base noise, not a change made by this lane (the lane touches no contract file);
`make check` (which runs `check_contracts.py` without `--base-ref`) is green, and the assertion
disappears after a rebase onto `origin/erenup/integration`. *Fix: rebase, then re-run
`scripts/gates.sh`.* (Also worth flagging for the lead: LESSONS 2026-09-14/123 — after rebasing,
`lake build` the lane's module again before merging.)

**N6 (informational, no action).** `make check` reports `"source_hashes_match": false` and one
`sorry` token in the copied-umbrella closure (`Paper1/BoundaryCorollary.lean:90`). Both are
pre-existing and unrelated to this lane (which adds no copied source); `make check` exits 0.

**N7 (honesty about non-vacuity, no action now).** The formal record contains no element of
`LiftL2 1` that *violates* `hginv`. Combined with N-section 2.6's converse, the formalisation
therefore does not by itself exclude the (mathematically false, but unformalised) reading in which
every `g : LiftL2 1` is angle-invariant and the theorem is the triviality "`ordinaryLift` is
surjective". My probe `rev153_mut2_noinv.lean` states this precisely:
`drop_hginv_collapses : (∀ g, ∃ G, ordinaryLift G = g) → ∀ g θ, translation 1 (0,θ) g = g`.
Constructing a genuine non-invariant witness (e.g. `(B ×ˢ A).indicator c` with
`memLp_indicator_const`, `B` a ball in `ℝ³` and `A` an arc, then an `AddCircle` arc-measure
computation) is ~60-100 lines. *Suggested for the A01 tester lane, not for this one.* The content of
the theorem is unaffected either way.

---

## 5. Commands and results

Environment: `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, `lake` run only from `verification/`.

### 5.1 Build and typecheck — silent

```
$ cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.L2Descent
Build completed successfully (9983 jobs).
EXIT=0
$ grep -n "L2Descent" <build log>          # warnings attributable to the new module
(empty)
$ cd verification && lake env lean ../formalization/NSFormalization/Section4/A01/L2Descent.lean
EXIT=0        (no output)
```
(The build log's ~30 warnings are all *replayed* upstream modules — `Source/FiniteHilbertBochner`,
`Source/RealSobolev`, `Paper3/*`, `vendor/HeliCorgi/*`; none from `L2Descent.lean`.)

### 5.2 Axioms and non-vacuity — all standard three

```
$ cd verification && lake env lean ../research/A01/axioms_l2_descent.lean
'NSFormalization.Section4.A01.exists_ordinaryLift_of_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.word_descent_ae_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.word_descent_ae_full' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.hword_jet_full' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.exists_ordinaryLift_of_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXIT=0
```
Both non-vacuity `example`s (`g = 0`; `g = ordinaryLift G₀`) elaborate — they are in the same file
and the exit code is 0.

### 5.3 The lane's own probes

```
$ cd verification && lake env lean ../research/A01/probes/probe153_sigs.lean
@Measure.ae_ae_comm : … MeasurableSet {x | p x.1 x.2} →
  ((∀ᵐ (x : α) ∂μ, ∀ᵐ (y : β) ∂ν, p x y) ↔ ∀ᵐ (y : β) ∂ν, ∀ᵐ (x : α) ∂μ, p x y)
@integral_add_left_eq_self : … [μ.IsAddLeftInvariant] (f : G → E) (g : G),
  ∫ (x : G), f (g + x) ∂μ = ∫ (x : G), f x ∂μ
@memLp_map_measure_iff : … AEStronglyMeasurable g (Measure.map f μ) → AEMeasurable f μ →
  (MemLp g p (Measure.map f μ) ↔ MemLp (g ∘ f) p μ)
@measurableSet_eq_fun : … [MeasurableEq β] {f g : α → β}, Measurable f → Measurable g →
  MeasurableSet {x | f x = g x}
ordinaryProjection_measurePreserving : MeasurePreserving Prod.fst (liftMeasure 1) volume
…
EXIT=0
$ cd verification && lake env lean ../research/A01/probes/probe153_micro.lean
EXIT=0        (no output)
```

### 5.4 Reviewer probes (new)

```
$ cd verification && lake env lean ../research/A01/probes/rev153_fidelity.lean
'Rev153Fidelity.descentL2_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
translation : (period : ℝ) → [inst : Fact (0 < period)] → LiftDomain period → ↥(LiftL2 period) →ₗᵢ[ℝ] ↥(LiftL2 period)
NSFormalization.Section4.A01.exists_ordinaryLift_of_invariant : ∀ (g : ↥(LiftL2 1)),
  (∀ (θ : AddCircle 1), (translation 1 (0, θ)) g = g) → ∃ G, ordinaryLift G = g
EXIT=0

$ cd verification && lake env lean ../research/A01/probes/rev153_consumer.lean
'Rev153Consumer.converse_no_hword_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT=0

$ cd verification && lake env lean ../research/A01/probes/rev153_subsumes.lean
EXIT=0        (three `example`s: 151's hword_jet_of_descent, 151's word_descent_ae, and n = q+1)

$ cd verification && lake env lean ../research/A01/probes/rev153_mut2_noinv.lean
'Rev153Mut2.invariance_necessary' depends on axioms: [propext, Classical.choice, Quot.sound]
'Rev153Mut2.drop_hginv_collapses' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT=0
```

### 5.5 Negative checks (mutations)

**Mutation 1 — replace the `θ`-average by the `θ = 0` slice** (`rev153_mut1_slice.lean`). The file
contains two *positive controls* that compile (the module's own averaging chain, and
`Filter.Eventually.exists` giving *some* angle depending on `pt`) and one mutant. Only the mutant
errors:

```
$ cd verification && lake env lean ../research/A01/probes/rev153_mut1_slice.lean
../research/A01/probes/rev153_mut1_slice.lean:56:57: error: Function expected at
  hpt
but this term has type
  ∀ᵐ (θ : AddCircle 1), g₀ pt = g₀ (pt + (0, θ))

Note: Expected a function because this term is being applied to the argument
  (-pt.2)
EXIT=1
```
This is exactly the mathematical obstruction, not a syntactic accident: reaching a **fixed** slice
needs the invariance at the single angle `θ = -pt.2`, and the datum is only `∀ᵐ θ` — `{-pt.2}` is
`volume`-null in the atomless `AddCircle 1`. The average needs only the a.e. statement
(`integral_congr_ae`), which is why it works. **The `θ`-average is load-bearing.**

**Mutation 2 — is `hginv` load-bearing?** Two checks, neither of them the forbidden
"omit-the-argument-and-re-apply" (LESSONS 2026-09-14/113):

* *statement level* (`rev153_mut2_noinv.lean`, compiles): `invariance_necessary` proves the converse,
  so the `hginv`-free mutant is equivalent to `∀ g θ, translation 1 (0,θ) g = g`
  (`drop_hginv_collapses`) — the cylinder `L²` space would not see the `AddCircle 1` factor of
  `liftMeasure 1 = volume.prod volume` at all. See N7 for what this does and does not formally
  settle.
* *proof level* (`rev153_mut3_body.lean`): the module's body re-run verbatim with `hginv` deleted,
  under `set_option autoImplicit false` so the deleted binder cannot be silently re-bound as an
  implicit (LESSONS 2026-09-14/077):
```
$ cd verification && lake env lean ../research/A01/probes/rev153_mut3_body.lean
../research/A01/probes/rev153_mut3_body.lean:44:10: error(lean.unknownIdentifier): Unknown identifier `hginv`
EXIT=1
```
  Line 44 is `rw [hginv θ] at h` inside `hinv0` — i.e. the *only* place the hypothesis enters, and it
  enters at the first step. Everything after `hinv0` is hypothesis-free plumbing.

### 5.6 Hygiene

```
$ grep -nE "sorry|admit|(^|[^_a-zA-Z])axiom|native_decide|maxHeartbeats|set_option" \
    formalization/NSFormalization/Section4/A01/L2Descent.lean
38:`#print axioms` is the standard three for every declaration (…)      ← docstring prose only
```
No `sorry`, `admit`, declared `axiom`, `native_decide`, `maxHeartbeats` or any `set_option` in the
module. Same grep over `research/A01/axioms_l2_descent.lean`, `probe153_sigs.lean`,
`probe153_micro.lean`: clean.

### 5.7 `make check`

```
$ make check
python3 experiments/check_formalization_plan.py --check      → OK (30 tasks; pre-existing
                                                               "source_hashes_match": false, N6)
python3 experiments/check_contracts.py                       → OK (24 registered contracts)
python3 experiments/test_contract_policy.py                  → Ran 13 tests … OK
python3 experiments/check_work_queue.py                       → 30 work items: ownership, contract
                                                                registration and task cards consistent.
EXIT=0
```

### 5.8 Citations spot-checked at the cited lines

| Cited in | Claim | Verified |
|---|---|---|
| `ATTEMPTS_L2_DESCENT.md:60` | `MeasurableEq` instance at `BorelSpace/Basic.lean:620` | ✅ `instance [SecondCountableTopology α] [T2Space α] : MeasurableEq α` is line 620 |
| `L2Descent.lean:26` | `liftMeasure 1 = volume.prod volume` | ✅ `EulerProof.lean:1092-1093` |
| `L2Descent.lean:24` | `EulerMeanSolenoidal.L2` has no solenoidal constraint | ✅ `MeanSolenoidalSpace.lean:22`, `abbrev L2 := Lp Space 2 volume` |
| `L2Descent.lean:28` | `AddCircle 1` has total mass one | ✅ `IntervalIntegral/Periodic.lean:69` (`= ENNReal.ofReal T`), Haar instance `:74` |
| `L2Descent.lean:140` | `sobolevTranslation` acts by `translation` on each coordinate, `liftOperator_apply` | ✅ `CylinderSobolevOperators.lean:85-89`, proved by `rfl`; `sobolevTranslation` at `:117-118` |
| `L2Descent.lean:154` | `word_hasDerivAt` needs only `n < q + 1` | ✅ `CylinderSobolevSpace.lean:70` (`hn : n < q`) |
| `ATTEMPTS_L2_DESCENT.md:88-96` | the "lemmas used" list | ⚠️ see **N2** (two entries are `#check`ed, not used) |
