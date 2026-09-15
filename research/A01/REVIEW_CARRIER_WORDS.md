# REVIEW — lane 151 (A01 carrier-bridge words), `Section4/A01/CarrierWords.lean`

Reviewer: opus, read-only. Worktree `.claude/worktrees/151-A01-carrier-words`, branch
`erenup/151-A01-carrier-words`, HEAD `ab13588`. No lane file edited, no git state changed; one
probe added (`research/A01/probes/rev151_descent_a_proved.lean`) and this report.

**Verdict: ACCEPT-WITH-NOTES.** All four declarations compile, `lake env lean` on the module is
silent, the four `#print axioms` are the standard three, `make check` passes, the two statements
that the lane ports from `REVIEW_APRIORI_ROWS.md` §2 are token-identical, the assembly's named
hypothesis is honest (∀-form over the descent witness, not a vacuous ∃), and two substantive
mutations break as predicted.

**One finding is substantive and must be fixed before the records propagate further (N1): the
lane's central negative claim — that piece (a) is an L-level open problem blocked by a
"signature mismatch … not in the tree" — is false.** The bridge it says is missing
(`complex Schwartz → real compact support`) is already a tree theorem,
`A03.ae_eq_of_schwartz_pairing` (`Section4/A03/ScalarTameProduct.lean:136`), whose test functions
are *complex Schwartz* with exactly the `∫ ψ x * f x` pairing shape the descent produces. **I proved
(a) in full**, ~120 lines, tree lemmas only, standard 3 axioms
(`research/A01/probes/rev151_descent_a_proved.lean`, §3 below). This is the LESSONS-line-3 failure
mode again ("审稿判「树里没有」之前先 grep 同名引理的所有命名空间"): the worker grepped for
`ae_eq_of_integral_contDiff_smul_eq` and stopped at Mathlib's signature.

---

## 1. What the lane claims

Pieces **(b)**, **(c)** and the assembly of the four-part carrier-bridge lemma of
`research/A01/REVIEW_APRIORI_ROWS.md` §2, which would discharge lane 149's single named hypothesis
`hword_jet` of `AprioriRows.sobolevSpace_norm_le_sobolevENorm` (`AprioriRows.lean:287-294`):

* (b) `eLpNorm_jet_component_le` — jet-component `L²` bound;
* (c) `word_angular_eq_zero` (port of the lane-149 reviewer probe) plus the generalization
  `word_eq_zero_of_mem_zero` (angular slot in *any* position), the piece the 149 review flagged as
  "not formalized here";
* `hword_jet_of_descent` — the assembly, giving `hword_jet` for all `w : Fin n → Fin 4` with
  `n + 3 ≤ q + 1`, **conditional** on a named hypothesis `hdescent` = piece (a);
* pieces (a) and (d) recorded as open with probes.

## 2. What is actually in Lean

### (b) `CarrierWords.lean:71-79` — genuine, and token-identical to the review

The statement is character-for-character `REVIEW_APRIORI_ROWS.md` §2 (b):

```lean
theorem eLpNorm_jet_component_le (n : ℕ) (z : Space → Space) (w : Fin n → Fin 3) :
    eLpNorm (fun x => iteratedFDeriv ℝ n z x (fun i => coordinateVector (w i))) 2 volume
      ≤ eLpNorm (iteratedFDeriv ℝ n z) 2 volume
```

Proof is exactly what the docstring says: `eLpNorm_mono` (`:74`) over the pointwise
`(iteratedFDeriv ℝ n z x).le_opNorm _` (`:77`), with `∏ i, ‖coordinateVector (w i)‖ = 1` closed by
`simp [coordinateVector]` (`:79`) — `coordinateVector i = EuclideanSpace.single i 1`
(`vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:39`), norm 1. No hidden hypothesis:
`z` is an arbitrary `Space → Space`, not even measurable, which is correct since `eLpNorm_mono` is
pointwise. Mutation M1 (§5) confirms the right-hand order `n` is load-bearing.

### (c) `:88-107` `word_angular_eq_zero` — genuine; direction `0` really is the angle

`standardDirection 0 = (0,1)` is `vendor/NavierStokesAndEuler/Euler/EulerProof.lean:6529`
(spatial component `0`, angular component `1`); the spatial directions are
`standardDirection i.succ = (EuclideanSpace.single i 1, 0)` (`:6535`). The definition lives in the
vendor `EulerCylinderSobolev` namespace, **not** in `Source/OrdinaryCylinderDescent.lean` as the
brief guessed; `OrdinaryCylinderDescent.lean:29 exists_ordinary_value` only *consumes* the angular
invariance. The lane's docstring (`:84-85`) cites the fact without a file, which is fine; the
`A3_SPLIT` note and the 149 review both carry the correct `EulerProof.lean:6529`.

The proof is the 149 probe verbatim (`research/A01/probes/rev149_angular_words.lean:20-38`):
`hword` (`:92-94`) projects the array-level invariance `hu` onto the single word coordinate;
`hpath` (`:95-98`) computes that the direction-`0` translation path is purely angular; `hfun`
(`:100-105`) therefore makes the orbit constant; `HasDerivAt.unique` against `hasDerivAt_const`
(`:107`). Mutation M2b (§5) shows `hpath` is exactly where a spatial direction dies.

### `:114-142` `word_eq_zero_of_mem_zero` — the induction really covers any position

`∀ n (hn : n ≤ q) (w : Fin n → Fin 4), (∃ k, w k = 0) → word 1 u hn w = 0`, by induction on `n`
after `intro n` (so the IH is quantified over `hn` and `w`, `:118`).

* `zero` (`:119`): the witness `k : Fin 0` is `k.elim0`. Vacuous, correctly.
* `succ`, leading slot angular (`hw0 : w 0 = 0`, `:123-128`): `word_angular_eq_zero` at
  `Fin.tail w`, then `Fin.cons_self_tail` rewrites `Fin.cons 0 (Fin.tail w)` back to `w`
  (rewriting the *hypothesis*, per the ATTEMPTS' recorded `rw` pitfall).
* `succ`, leading slot spatial (`:129-142`): the witness index is `k ≠ 0`, so `k = k'.succ`
  (`Fin.exists_succ_eq`), hence `Fin.tail w k' = 0`; the IH kills the **tail** word
  (`hzero`, `:133`); `word_hasDerivAt` at the (arbitrary, possibly spatial) direction `w 0` then
  differentiates the orbit of `0`, which is constant `0` by `map_zero` (`:138`), so the child word
  is `0` (`HasDerivAt.unique`, `:140`), and `Fin.cons_self_tail` identifies the child with `w`.

So an angular slot anywhere is handled, and the direction of the *prefix* letters is irrelevant —
correct, since `translation` is linear and kills `0`. `hn : n + 1 ≤ q` is used as `hlt : n < q`
definitionally (`:122`).

### Assembly `:161-197` `hword_jet_of_descent`

Exact signature (`:161-169`):

```lean
theorem hword_jet_of_descent {q : ℕ} (u : SobolevSpace 1 (q + 1))
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u)
    {z : Space → Space} (hz : ContDiff ℝ ∞ z) (hfin : sobolevENorm ((q + 1 : ℕ) : ℝ) z ≠ ⊤)
    (hdescent : ∀ (n : ℕ) (hn : n + 3 ≤ q + 1) (w : Fin n → Fin 3)
        (Zw : EulerMeanSolenoidal.L2),
        ordinaryLift Zw = word 1 u (by omega) (fun i => (w i).succ) →
        (⇑Zw) =ᵐ[volume] fun x => iteratedFDeriv ℝ n z x (fun i => coordinateVector (w i))) :
    ∀ (n : ℕ) (hn : n + 3 ≤ q + 1) (w : Fin n → Fin 4),
      ‖word 1 u (by omega) w‖ ≤ (eLpNorm (iteratedFDeriv ℝ n z) 2 volume).toReal
```

**Is `hdescent` exactly (a)?** Yes for the word data, with the hand-off context absorbed. Compared
with `REVIEW_APRIORI_ROWS.md` §2 (a), the conclusion and the four word binders
(`hn`, `w : Fin n → Fin 3`, `Zw`, `hZw`) are token-identical; what is dropped is the context
`(U) (hU : ordinaryLift U = value 1 u) (hUz : ⇑U =ᵐ z)`, which is what *supplies* (a) rather than
part of its per-word content (`hz` survives, in the assembly's own binder list). Dropping context
makes the named hypothesis **harder** to supply, i.e. weakens the theorem — it is not a
strengthening in the dangerous direction, and (a) + any `(U, hU, hUz)` discharges it.

**Is it vacuity-proof?** Yes, on both counts the brief asks about.
* It is the `∀ Zw, ordinaryLift Zw = word … → …` form, not `∃`. And since `ordinaryLift` is a
  linear isometry with `ordinaryLift.injective`, the `Zw` satisfying the equation is *unique*, so
  the ∀-form and "the `Zw` that `exists_descend` produces" are the same obligation.
* Instantiated at `n = 0` it forces the hand-off: my probe (script in §5, "n=0") derives
  `⇑U =ᵐ[volume] z` from `hdescent` alone, given `ordinaryLift U = value 1 u` — i.e. the hypothesis
  already contains the worker's `word_descent_ae_base`, not an empty statement.
* The lane's conformance file exercises the assembly with a genuine `hdescent` witness at
  `u = 0, z = 0` (`axioms_carrier_words.lean:50-72`), which elaborates.

**Proof.** `by_cases hex : ∃ k, w k = 0` (`:172`). Angular branch (`:173-174`):
`word_eq_zero_of_mem_zero` then `ENNReal.toReal_nonneg` — note this is where `hu` is consumed, as
review note N2 of lane 149 predicted. Spatial branch: `hne` built by hand rather than `push_neg`
(`:175`, deprecation recorded in ATTEMPTS), `w' i := (w i).pred`, `hw_eq` via `Fin.succ_pred`
(`:176-178`); `exists_descend u hu _ hnle hn` (`EulerPairing.lean:296`, whose two numeric
hypotheses at `q := q+1` are exactly `n ≤ q+1` and `n + 3 ≤ q + 1`) (`:179`); then the norm chain
`ordinaryLift.norm_map` → `Lp.norm_def` → `eLpNorm_congr_ae hae` → (b) (`:189-197`). The
`.toReal` monotonicity needs `≠ ⊤`, derived at `:181-188` by `Finset.single_le_sum` into
`jetSobolevENorm (q+1) z` and `jetSobolevENorm_le_sobolevENorm (q+1) hz` (`DatumToJets.lean:343`)
under `hfin` — this is the only use of `hz` and of `hfin`, both load-bearing.

**Coverage claim is honest.** `n + 3 ≤ q + 1` in the conclusion, not `n ≤ q + 1`: the consumer
(`AprioriRows.lean:289`) needs the latter, so the assembly does *not* yet discharge `hword_jet`;
the module docstring (`:158-160`) and the ATTEMPTS say exactly this.

### Consistency

Nothing here touches a registered contract; no restatement of a contract definition is introduced
(`word`, `value`, `SobolevSpace`, `standardDirection` are all used from vendor/upstream). The
module imports only `A01.AprioriRows` and `A01.EulerPairing`, both already in the tree.

## 3. The gap audit — (a) is NOT open (finding N1)

### What the lane says

`ATTEMPTS_CARRIER_WORDS.md:75-98`, `CarrierWords.lean:39-43` and
`probes/probe151_descent_a.lean:9-13,45-50`: the descent supplies a **complex-Schwartz** pairing
(`weakDeriv_pairing_of_lift_hasDerivAt`), "the only tree/Mathlib lemma" for uniqueness is
`ae_eq_of_integral_contDiff_smul_eq` which takes **real compactly supported** test functions,
therefore closing (a) "needs a bridge not in the tree" — complex→real, Schwartz→compact support,
classical IBP, `iteratedFDeriv_succ_apply_left`, vector reassembly, induction — "an L-level analytic
development". The `A3_SPLIT.md` update (lane-151 paragraph) propagates this.

### Both `#check`s in the probe are accurate; the conclusion drawn from them is not

The two signatures the probe prints are correct (§5). But the tree already contains the exact
bridge, in a namespace the worker did not grep:

```
NSFormalization.Section4.A03.ae_eq_of_schwartz_pairing   -- ScalarTameProduct.lean:136
  {f g : Space → ℂ} (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume)
  (h : ∀ ψ : SchwartzMap Space ℂ, ∫ x, ψ x * f x = ∫ x, ψ x * g x) :
  ∀ᵐ x ∂volume, f x = g x
```

i.e. *complex* Schwartz test functions, in the multiplicative pairing shape — the complex→real and
Schwartz→compact-support conversions are inside it (`HasCompactSupport.toSchwartzMap` +
`Complex.ofRealCLM`, `ScalarTameProduct.lean:140-145`). `Source/WeakClassicalDerivative.lean:12`
`ae_eq_classical_derivative` is a second, independent template for the same manoeuvre (and its
docstring says "No support premise is used").

The classical side needs no new IBP either: `D01.smoothField_weakDeriv_pairing`
(`FiniteOrderConstructor.lean:306`) already states, for a `SmoothL2Field Space`, the *same*
complex-Schwartz pairing between the field and its classical directional derivative — the exact
mirror of the descent's pairing. So the two pairings can be cancelled against each other and (a)'s
step is `ae_eq_of_schwartz_pairing` applied componentwise. Note that this route never performs IBP
against a non-compactly-supported test function, so LESSONS' 094 trap (smooth + `MemLp 2` is not
enough for termwise Schwartz IBP) is not entered.

### (a), proved

`research/A01/probes/rev151_descent_a_proved.lean` (compiles silently, three declarations, all
`[propext, Classical.choice, Quot.sound]`):

```lean
-- step (25 lines): the two tree pairings cancelled through A03.ae_eq_of_schwartz_pairing
theorem descent_step_ae (Z : SmoothL2Field Space) (j : Fin 3) (Zw Zc : EulerMeanSolenoidal.L2)
    (hZw : (⇑Zw) =ᵐ[volume] Z.field)
    (h : HasDerivAt (fun t : ℝ => EulerLiftedGradientSpace.translation 1
        (translationPath 1 (standardDirection j.succ) t) (ordinaryLift Zw)) (ordinaryLift Zc) 0) :
    (⇑Zc) =ᵐ[volume] (Z.directionalField (coordinateVector j)).field

-- the word field = the classical jet slice (iteratedFDeriv_succ_apply_left, 20 lines)
def wordField (Z : SmoothL2Field Space) : ∀ {n : ℕ}, (Fin n → Fin 3) → SmoothL2Field Space
theorem wordField_field (Z) : ∀ n w x,
    (wordField Z w).field x = iteratedFDeriv ℝ n Z.field x (fun i => coordinateVector (w i))

-- (a), the review's statement (30 lines: induction on the word length)
theorem word_descent_ae' {q : ℕ} (u : SobolevSpace 1 (q + 1))
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (U : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u)
    (Z : SmoothL2Field Space) (hUz : (⇑U) =ᵐ[volume] Z.field)
    (n : ℕ) (hn : n + 3 ≤ q + 1) (w : Fin n → Fin 3) (Zw : EulerMeanSolenoidal.L2)
    (hZw : ordinaryLift Zw = word 1 u (by omega) (fun i => (w i).succ)) :
    (⇑Zw) =ᵐ[volume] fun x => iteratedFDeriv ℝ n Z.field x (fun i => coordinateVector (w i))
```

Ingredients, all existing: `A01.weakDeriv_pairing_of_lift_hasDerivAt` (`EulerPairing.lean:265`),
`D01.smoothField_weakDeriv_pairing` (`FiniteOrderConstructor.lean:306`),
`A03.ae_eq_of_schwartz_pairing` (`ScalarTameProduct.lean:136`), `exists_descend`
(`EulerPairing.lean:296`), `word_hasDerivAt` (`vendor/…/Euler/CylinderSobolevSpace.lean:70`),
`ContDiff.differentiable_iteratedFDeriv`, `iteratedFDeriv_succ_apply_left`,
`SmoothL2Field.directionalField` (`vendor/…/Euler/LpSmoothFieldAlgebra.lean:94`),
`ContinuousMultilinearMap.apply`. The induction's base case is the worker's
`word_descent_ae_base` argument (`ordinaryLift.injective`, `iteratedFDeriv_zero_apply`).

**Difference from the review's (a):** the smooth field is given as
`Z : EulerLpTranslation.SmoothL2Field Space` (smooth + `MemLp` jets at *all* orders) rather than as
`(hz : ContDiff ℝ ∞ z)` alone, because `smoothField_weakDeriv_pairing` is stated on that carrier.
That is free downstream: `D01.exists_smoothL2Field_of_memHInfty` (`DatumToJets.lean:306`) builds it
from `ContDiff ℝ ∞ z` + an all-orders datum, which a `ClassicalSolutionR` velocity slice has
(`smoothSquareIntegrableJets_slice`, `DatumToJets.lean:396`). Size to land it as a lane module:
**S–M** (≈120 lines, already written), not L.

### Consequence for the plan

With (a) in hand, `hword_jet_of_descent` discharges `hword_jet` for **all** `n ≤ q − 2`
unconditionally, and the only remaining obstacle to lane 149's converse is (d), the top three
orders.

### (d) — the lane's reading is correct

* `EulerMeanSolenoidal.L2 = MeasureTheory.Lp Space 2 volume` (`abbrev`,
  `vendor/…/Euler/MeanSolenoidalSpace.lean:22`): **no** solenoidal or mean constraint at this level,
  so (d) really is only a disintegration statement, as the ATTEMPTS says (and as the 149 review
  left open, "I did not check whether the constraints obstruct").
* `LiftL2 1 = Lp Vector3 2 (liftMeasure 1)` (`EulerProof.lean:1100`) with
  `liftMeasure period = (volume : Measure Vector3).prod (volume : Measure (AddCircle period))`
  (`:1092`) — a genuine product measure on `ℝ³ × S¹`, so Fubini applies.
* `exists_ordinary_value` (`Source/OrdinaryCylinderDescent.lean:29-56`) does descend by the
  `θ = 0` slice of the continuous `H³` representative (`representative 1 v (x, 0)`, `:41`), and that
  is where `3 ≤ q` is spent. Accurate.

**What Mathlib gives**, for the record (the ATTEMPTS does not say): there is no ready-made
"a.e. invariant in the second factor ⇒ pulled back from the first". The usable route is the
`AddCircle` Fourier Hilbert basis — `fourierBasis : HilbertBasis ℤ ℂ (Lp ℂ 2 haarAddCircle)`
(`Mathlib/Analysis/Fourier/AddCircle.lean:411`, with `span_fourierLp_closure_eq_top` at `:261`):
invariance forces every nonzero-mode coefficient to vanish (`ĝ_k(x)·e^{2πikθ₀} = ĝ_k(x)` for all
`θ₀`), leaving the `k = 0` mode, which is `G ∘ Prod.fst`; `ordinaryLift_ae` and
`ordinaryProjection_measurePreserving` (both `#check`ed in the lane's probe) then close it. Fubini
for the slice-wise `MemLp` is standard. This is still an L-ish piece, but the ingredient list is
now concrete rather than "Fubini somehow". Mathlib's `Dynamics/Ergodic/AddCircleAdd.lean` is about
ergodicity of a *single* irrational rotation and is not the right tool (invariance here is under
the whole circle action, which is strictly easier).

## 4. Notes

* **N1 (records, blocking for the records; the Lean is fine).** `ATTEMPTS_CARRIER_WORDS.md:75-98`,
  `CarrierWords.lean:39-43`, `probes/probe151_descent_a.lean:9-13,45-50` and the lane-151 paragraph
  of `A3_SPLIT.md` must drop the "not in the tree / L-level" verdict on (a) and point at
  `A03.ae_eq_of_schwartz_pairing` + `D01.smoothField_weakDeriv_pairing` +
  `research/A01/probes/rev151_descent_a_proved.lean`. Suggested replacement sentence: *"(a) is
  provable from tree lemmas alone (`A03.ae_eq_of_schwartz_pairing` consumes the complex-Schwartz
  pairing directly; `D01.smoothField_weakDeriv_pairing` supplies the classical side); proved in
  `research/A01/probes/rev151_descent_a_proved.lean`, S–M to land as a module."*
* **N2 (follow-up lane, recommended next step on the critical chain).** Land
  `rev151_descent_a_proved.lean` as `Section4/A01/CarrierWords.lean` additions (or a sibling module
  `CarrierDescent.lean` importing `A03.ScalarTameProduct`), restate `hword_jet_of_descent` with the
  `SmoothL2Field` carrier, and the whole `n ≤ q − 2` half of `hword_jet` becomes unconditional.
  Note the import policy: this is `formalization/`, not `Contracts/`, so importing
  `Section4.A03.ScalarTameProduct` from `Section4.A01` is allowed; it compiles together today
  (checked, §5).
* **N3 (statement, cosmetic).** The assembly absorbs (a)'s `(U, hU, hUz)` context into `hdescent`.
  When (a) lands, either keep `hdescent` and discharge it at the call site, or thread
  `(U) (hU) (hUz)` through the assembly so the caller supplies only the hand-off. Prefer the
  latter — it keeps the *named-hypothesis-free* theorem one step away.
* **N4 (citation, cosmetic).** `ATTEMPTS_CARRIER_WORDS.md:83` cites
  `Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean:195` for
  `ae_eq_of_integral_contDiff_smul_eq`; the signature printed by the probe matches, and the file
  exists, but the line number is unverifiable from the worktree without the packages path —
  harmless, and the lemma name is what matters.
* **N5 (nothing to fix).** The lane's two recorded `Fin`/`push_neg`/`simp` pitfalls
  (`ATTEMPTS_CARRIER_WORDS.md:131-149`) are real and reproduced by reading the proofs; they are
  good LESSONS candidates only in the `push_neg` case (deprecated in this Lean, breaks
  `lake env lean` silence), which is already a general fact.

## 5. Commands and results

All from `.claude/worktrees/151-A01-carrier-words`, after `. scripts/lean-env.sh`,
`LEAN_NUM_THREADS=6`, lake from `verification/`.

```
$ lake build NSFormalization.Section4.A01.CarrierWords
Build completed successfully (9982 jobs).            # only vendor/replayed warnings
$ lake env lean ../formalization/NSFormalization/Section4/A01/CarrierWords.lean
                                                      # exit 0, 0 bytes of output
$ grep -n 'sorry|admit|native_decide|maxHeartbeats|set_option|axiom' <module, axioms file, both probes>
NONE FOUND
$ lake env lean ../research/A01/axioms_carrier_words.lean
'NSFormalization.Section4.A01.eLpNorm_jet_component_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.word_angular_eq_zero'     depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.word_eq_zero_of_mem_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.hword_jet_of_descent'     depends on axioms: [propext, Classical.choice, Quot.sound]
                                                      # and the four non-vacuity examples elaborate,
                                                      # including the genuine hdescent witness at u = 0, z = 0
$ lake env lean ../research/A01/probes/probe151_descent_a.lean      # exit 0, prints the three #checks
$ lake env lean ../research/A01/probes/probe151_descent_L2.lean     # exit 0, prints DescentL2 : Prop + four #checks
$ make check
python3 experiments/test_contract_policy.py  -> Ran 13 tests OK
python3 experiments/check_work_queue.py      -> 30 work items: ownership, contract registration and task cards consistent.
```

**Brief item 3 probe (`hdescent` at `n = 0`).** Compiles (exit 0):

```lean
example {q : ℕ} (u : SobolevSpace 1 (q + 1)) (z : Space → Space)
    (U : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u) (h3 : 3 ≤ q + 1)
    (hdescent : …) : (⇑U) =ᵐ[volume] z := by
  have hwemp : (fun i => ((Fin.elim0 : Fin 0 → Fin 3) i).succ) = (Fin.elim0 : Fin 0 → Fin 4) :=
    Subsingleton.elim _ _
  have h := hdescent 0 (by omega) Fin.elim0 U (by rw [hwemp, hU]; rfl)
  refine h.trans (Filter.EventuallyEq.of_eq ?_); funext x; rw [iteratedFDeriv_zero_apply]
```

**Brief item 4 probe (the missing bridge).** `lake env lean` on a file importing both
`Section4.A01.CarrierWords` and `Section4.A03.ScalarTameProduct` prints

```
@NSFormalization.Section4.A03.ae_eq_of_schwartz_pairing : ∀ {f g : Space → ℂ},
  LocallyIntegrable f volume → LocallyIntegrable g volume →
    (∀ (ψ : SchwartzMap Space ℂ), ∫ x, ψ x * f x = ∫ x, ψ x * g x) → ∀ᵐ x, f x = g x
```

and `research/A01/probes/rev151_descent_a_proved.lean` compiles silently with

```
'Rev151A.descent_step_ae'  depends on axioms: [propext, Classical.choice, Quot.sound]
'Rev151A.word_descent_ae'  depends on axioms: [propext, Classical.choice, Quot.sound]
'Rev151A.word_descent_ae'' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Negative checks (two substantive mutations, on copies of the module, never by dropping an
argument).**

*M1 — (b) with the right-hand side at order `n+1` instead of `n`* (`iteratedFDeriv ℝ (n+1) z`):

```
/tmp/rev151_mut1.lean:73:55: error: unsolved goals
⊢ ‖iteratedFDeriv ℝ n z x‖ ≤ ‖iteratedFDeriv ℝ (n + 1) z x‖
/tmp/rev151_mut1.lean:197:41: error: Application type mismatch: …
  eLpNorm (…) 2 volume ≤ eLpNorm (iteratedFDeriv ℝ (n + 1) z) 2 volume
but is expected to have type
  eLpNorm (…) 2 volume ≤ eLpNorm (iteratedFDeriv ℝ n z) 2 volume
```

i.e. the pointwise `le_opNorm` step and the assembly's last `calc` step both die — the order match
is load-bearing, and (b) is not a weaker statement dressed up.

*M2b — (c) with the leading direction `1` (spatial `e₀`) instead of `0` (angular), changed in the
statement **and** throughout the proof:*

```
/tmp/rev151_mut2b.lean:96:100: error: unsolved goals
hword : ∀ (θ : AddCircle 1), (translation 1 (0, θ)) (word 1 u ⋯ w) = word 1 u ⋯ w
⊢ (t = 0 ∨ (standardDirection 1).1 = 0) ∧ ↑(t * (standardDirection 1).2) = ↑t
```

The proof dies exactly at `hpath`: for a spatial direction the translation path has a nonzero
*spatial* component and a zero angular component, so the orbit is not constant and the angle
invariance `hword` is useless. (A shallower mutation that changes only the statement fails at the
final `exact` with `word 1 u ⋯ (Fin.cons 0 w) = 0 but is expected to have type … (Fin.cons 1 w) = 0`.)
Both confirm that `standardDirection 0 = (0,1)` — i.e. that slot `0` is the angle — is what the
theorem rests on.
