# REVIEW — lane 119 (`erenup/119-A01-c1b-split`), unit C1b split-and-start

Reviewer run 2026-09-13.  Scope = the single commit `3ae8457` on top of
merge-base `8f8a5a5` (9 files, +467, no deletions).  Probes in `/tmp/rev119/`;
every error/goal text quoted below was produced by the commands shown.

## Verdict: **ACCEPT-WITH-NOTES**

The Lean is correct, builds, is axiom-clean and non-vacuous; the four theorems
say what the table says they say.  The §0 `2π` analysis is **right** and I
re-derived it independently in Lean (finding 5).  The notes are in the *table*,
not the code: one wrong input citation and one overstated blocker on the single
**L** row (findings 8 and 9), one misleading boldface about constants
(finding 7), one missing row (finding 10), citation drift (finding 11), and a
wrong recorded *cause* in ATTEMPTS (finding 12).  None of these need a code
change; they should be fixed in `C1B_SPLIT.md` / `ATTEMPTS_C1B.md` before the
next C1b lane is briefed off this table.

---

## 1. Compiles / axioms / hygiene — **PASS**

```
$ . scripts/lean-env.sh; cd verification
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.CarrierBridge
Build completed successfully (9873 jobs).                       # EXIT=0
$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/A01/CarrierBridge.lean
                                                                # silent, EXIT=0
$ LEAN_NUM_THREADS=6 lake env lean ../research/A01/axioms_c1b.lean
'NSFormalization.Section4.A01.IsSobolevDatum.congr_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.isSobolevDatum_zero_ordinaryL2' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.exists_isSobolevDatum_zero_ordinaryL2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.isSobolevDatum_zero_initial' depends on axioms: [propext, Classical.choice, Quot.sound]
$ cd ..; make check                                             # EXIT=0
  ... Ran 13 tests ... OK
  30 work items: ownership, contract registration and task cards consistent.
$ make test                                                     # EXIT=0
  ... Contract BlowupDensity.Tests.checkedInsertionLifespanV2: checked; standard logical axioms only
```

Hygiene grep over the whole diff
(`grep -nE 'sorry|admit|axiom|native_decide|maxHeartbeats|set_option'`) hits only
the four `#print axioms` lines of `research/A01/axioms_c1b.lean`.  No
`set_option`, no raised heartbeats, no `sorry`.  `git status --porcelain` empty;
no `Contracts/V1/*` or `Tests/*` file touched.  A01 is already
`state: in-progress / owner: erenup` in `collaboration/work_items.json`, so the
absence of a claim commit is correct.  All four lane probes
(`research/A01/probes/c1b_*.lean`) typecheck under `lake env lean`.

## 2. Statement fidelity and non-vacuity — **PASS** (probe `/tmp/rev119/fidelity.lean`, silent)

```
@IsSobolevDatum.congr_field : ∀ {s : ℝ} {z z' : Space → Space} {A : RealVectorSobolev s},
  IsSobolevDatum s z A → z =ᵐ[volume] z' → IsSobolevDatum s z' A
isSobolevDatum_zero_ordinaryL2 : ∀ (U : ↥EulerMeanSolenoidal.L2), IsSobolevDatum 0 (↑↑U) (orderZeroDatum ⋯)
exists_isSobolevDatum_zero_ordinaryL2 : ∀ (U : ↥EulerMeanSolenoidal.L2), ∃ A, IsSobolevDatum 0 (↑↑U) A
isSobolevDatum_zero_initial : ∀ (a : EulerLpTranslation.SmoothL2Field Space) (U : ↥EulerMeanSolenoidal.L2),
  U = a.toLp → IsSobolevDatum 0 a.field (orderZeroDatum ⋯)
```

**(F1) Not a tautology.**  `Iff.rfl` shows the conclusion unfolds to the genuine
pairing
`angularRealization 0 (orderZeroDatum … i) ψ = ∫ x, ψ x * ((U x i : ℝ) : ℂ)`
— the left side is a Fourier-side distribution, the right side the Bochner
pairing with the **coercion to a function of the very same `L²` element** whose
datum is taken.  There is no `orderZeroDatum … = orderZeroDatum …`.

**(F2) Carrier identification is real but trivial** — both sides are `abbrev`s:
`EulerMeanSolenoidal.L2 = Lp Space 2 volume := rfl` and
`EulerSmoothLimit.Space = NavierStokes.ProblemStatement.Space := rfl` both close
by `rfl`.  This is the entire new content of rows C1b-0 / C1b-c5-0.

**(F3, severity LOW) Three of the four theorems are defeq re-exports.**
`isSobolevDatum_zero_ordinaryL2 U = isSobolevDatum_orderZeroDatum (Lp.memLp U)`
closes by `rfl`, and `exists_isSobolevDatum_zero_of_memLp (Lp.memLp U)` already
inhabits `exists_isSobolevDatum_zero_ordinaryL2`'s statement verbatim.  The table
labels row C1b-0 "bookkeeping (order-0 seed re-export)", so this is **honestly
declared**, not hidden — recorded only so the next lane does not read "3 of 4
theorems proved" as three units of progress.  The one theorem with content is
`IsSobolevDatum.congr_field` (all real orders, genuinely reusable — it is the
lemma that will carry every later row from `⇑(U t)` to the physical `velocity t`).

**(F4, severity LOW) `isSobolevDatum_zero_initial` is subsumed by D01.**
`smoothAngularDatum_isSobolevDatum 0 0 (by norm_num) a : IsSobolevDatum 0 a.field
(smoothAngularDatum 0 0 _ a)` needs no Euler input at all, and by
`isSobolevDatum_unique` the two data coincide:
`orderZeroDatum (Lp.memLp U) = smoothAngularDatum 0 0 _ a` (both proved in the
probe).  The lemma is still correctly *shaped* — its value is identifying the
**Euler-built** datum at `t = 0`, which is what a datum *path* needs — and it does
fit `exists_local`: probe `/tmp/rev119/exists_local_fit.lean` destructures
`OrdinaryForcedLocal.exists_local` and feeds clause 3
(`U ⟨0, le_rfl, hT.le⟩ = a.toLp`, `OrdinaryForcedLocal.lean:41`) straight into it,
silent.  So the docstring's claim to be about `exists_local`'s initial clause is
accurate.

**Non-vacuity.**  Instantiated on a concrete nonzero field
`Uc := indicatorConstLp 2 measurableSet_ball … (EuclideanSpace.single 0 1)`:
`IsSobolevDatum 0 (⇑Uc) (orderZeroDatum (Lp.memLp Uc))` typechecks and `Uc ≠ 0`
is proved (via `norm_indicatorConstLp` + `measure_ball_pos`).  The
`IsSobolevDatum` docstring's *totalization caveat* (junk `0` when the field pairs
integrably with no Schwartz test) is **not** reachable here: the probe proves
`Integrable (fun x => ψ x * ((U x i : ℝ) : ℂ))` for every `L²` field and Schwartz
`ψ` (`MemLp.integrable_mul`).  And `isSobolevDatum_unique` pins the datum: any
`A` satisfying the predicate equals `orderZeroDatum (Lp.memLp U)`.  So the
statement is non-vacuous in both senses.

### The `2π` claim — **verified independently, and it is right** (finding 5)

`/tmp/rev119/tau_symbol.lean` (silent, no `sorry`) proves, from the in-tree
pieces and not from the docstrings:

```lean
def mid (s : ℝ) (a ζ : Space) : ℂ :=
  angularWeightSymbol (s - 1) ζ * sobolevDirectionalSymbol a ζ * angularWeightSymbol (-s) ζ

theorem mid_eq (s : ℝ) (a ζ : Space) :          -- the cycles-variable symbol
    mid s a ζ = (2 * Real.pi * Complex.I) *
      ((inner ℝ ζ a : ℂ) * sobolevBesselWeight (-1) (frequencyUnit • ζ))

theorem mid_angular (s : ℝ) (a ξ : Space) :     -- THE CLAIM
    mid s a (frequencyUnit⁻¹ • ξ) =
      Complex.I * ((inner ℝ ξ a : ℂ) * sobolevBesselWeight (-1) ξ)
```

plus three `rfl` sanity checks (`sobolevDirectionalSymbol` really carries the
`2π`; `frequencyUnit = 2 * Real.pi`; `angularWeightSymbol s` really is the ratio
`(1+(2π)²‖ζ‖²)^{s/2}/(1+‖ζ‖²)^{s/2}`).  So the middle symbol of
`angularDirectionalDerivative`, read in the **angular** variable `ξ = 2π ζ`, is
exactly `i⟨ξ,a⟩(1+‖ξ‖²)^{-1/2}`: the `2π` of Mathlib's `𝓕(∂ⱼf) = 2πiζⱼ𝓕f` is
cancelled exactly by the `(2π)⁻¹` argument rescaling of `Source.angularFourier`
(`FourierConvention.lean:23`), and **nothing is left over**.  This matches the
multiplier `D01/DerivativeDatum.lean` claims in its header, so C1B_SPLIT §0's
"derivative rule … no `2π`" is correct, and its corroboration via
`isSobolevDatum_partialDeriv` is legitimate.

The order-0 constant is likewise right: `angularSobolevSq_eq_frequency_weight`
(`FourierConvention.lean:50`) is proved through
`hcoef : (frequencyUnit ^ (-3/2 : ℝ))^2 * frequencyUnit^3 = 1` (`:62-65`), i.e.
the `(2π)^3` Jacobian exactly cancels the amplitude, and
`sobolevRealization_zero` (`SobolevHilbertModel.lean:130`) is Mathlib's `𝓕⁻` with
no `L¹` hypothesis.  Order-0 constant **= 1**, as claimed.

**(F6, severity LOW) One imprecise sentence in §0(A).**  "`angularRealization s`
… at order 0 it is Mathlib's genuine `L²` inverse-Fourier embedding
(`sobolevRealization_zero`)" is not literally true:
`angularRealization s = angularCoordinateRealization s ∘ angularFrequencyDilation.symm`
(`AngularFourierDilation.lean:177`) and `cyclesToAngular s = angularWeightEquiv s
∘ angularFrequencyDilation` (`AngularTameProduct.lean:11`), so at `s = 0` the two
differ by the (unitary, non-identity) frequency dilation.  The correct statement
is the composite `angularRealization s ∘ cyclesToAngularReal s = sobolevRealization s`
(`AngularRealSobolev.lean:89`), which is exactly how `isSobolevDatum_orderZeroDatum`
is proved.  The **constant-1 conclusion is unaffected** (the dilation is unitary
and is carried inside the datum).  Fix the sentence, not the code.

**(F7, severity MEDIUM) The boldface "no scalar constant" at order `m ≥ 1` is
about the multiplier, not about norms — and the table should say so up front.**
The Euler `SobolevSpace 1 q` norm is the norm inherited from the *product*
`SobolevWord q → LiftL2 1`, i.e. the **sup** over derivative words
(`CylinderSobolevSpace.lean:49-53`; `‖u‖ = ‖u.val‖` by `rfl` and
`pi_norm_le_iff_of_nonneg` is what `ordinarySobolev_norm_le` uses).  So the Euler
order-`m` quantity is a sup over a word-indexed family of `L²` norms of
derivative tensors, while D01's order-`m` datum lives against the inhomogeneous
Bessel weight `(1+‖ξ‖²)^{m/2}`.  These are **equivalent, not equal**, with
`m`-dependent constants **in both directions** (the table says "constants
`1 ≤ c_m`", which names only one side).  The table does concede this two
sentences after the boldface, so §0 is self-consistent — but as written the
headline reads as "no constant anywhere at any order", which is wrong.
Recommended wording: *"the datum/multiplier identity is constant-free; the norm
comparison is an equivalence with two `m`-dependent constants, and A01 never
needs it because `ClassicalSolutionR.sobolev` (`Contracts/V1/Data.lean:643`) asks
for datum **existence** plus continuity, not a norm identity."*

## 3. The table — 10 rows, inputs re-`#check`ed

All cited declarations exist and typecheck (probes
`/tmp/rev119/fidelity.lean`, `/tmp/rev119/nextlane.lean`, and the lane's own four
probe files, all silent/clean).  Sizes and DONE/ready/gap statuses are plausible
as marked, with the two exceptions below.

**(F8, severity MEDIUM) Row C1b-m names an input that is not available at
`t > 0`.**  The row cites `ordinarySobolev_coordinate`
(`Euler/MeanOrbitSobolev.lean:79`) as the source of "the Euler `ordinarySobolev
(q+1)` derivative tensors".  But

```
EulerMeanSmoothRepresentative.ordinarySobolev : (q : ℕ) →
  (u : ↥EulerMeanSolenoidal.L2) → EulerMeanSmoothRepresentative.SmoothOrbit u → ↥(SobolevSpace 1 q)
```

requires `SmoothOrbit u = ContDiff ℝ ∞ (fun a : Space => translation a u)`, which
`exists_local` supplies **only at `t = 0`** (`a.translation_contDiff`).  At `t > 0`
`exists_local` hands over the *abstract* array `u t : SobolevSpace 1 (q+1)` plus
`ordinaryLift (U t) = value 1 (u t)` (clause 4, `OrdinaryForcedLocal.lean:42`) and
whole-array angle invariance (clause 7, `:47`).  The real inputs for C1b-m are
therefore `EulerCylinderSobolevSpace.word` / `word_hasDerivAt` / `word_has_jet` /
`ofJet` (`CylinderSobolevSpace.lean:66,70,91,78`) and
`OrdinaryCylinderDescent.exists_ordinary_value` (`:29`), all `#check`ed in
`/tmp/rev119/nextlane.lean`.

**(F9, severity MEDIUM) The B1/T1 dependence of C1b-m is overstated.**  The row
says C1b-m "needs `U t` to be a `SmoothL2Field` … shared with **B1/T1**", and §2
repeats that whoever proves joint smoothness "unblocks C1b-m at once".  That is
true of the *route the row picks*, but a **finite-order route needs no joint
smoothness at all**:

* `u t : SobolevSpace 1 (q+1)` is by construction a closed-graph array whose every
  edge is a genuine **strong `L²` translation derivative** (`word_hasDerivAt`) —
  that is already `H^{q+1}`-type information about the cylinder field, with no
  `ContDiff` anywhere;
* each derivative word is the `value` of a lower-order sub-array
  (`word_has_jet` + `ofJet`), and clause 7's angle invariance passes to it, so
  `exists_ordinary_value` (which needs only `3 ≤ order`) descends **each word** to
  an ordinary `EulerMeanSolenoidal.L2` field;
* hence `U t` has genuine strong `L²` derivatives up to order `q+1` at every
  fixed `t > 0`, with **no** `SmoothOrbit`, no `SmoothL2Field`, no B1, no T1.

What is actually missing is a **new D01 constructor**: "`MemLp z 2` + `L²`
derivatives up to order `m` ⟹ `∃ A : RealVectorSobolev m, IsSobolevDatum m z A`",
i.e. the order-`m` analogue of `orderZeroDatum`.  D01 currently jumps from order
0 (`orderZeroDatum`, bare `MemLp`) to all orders (`smoothAngularDatum`, needs
`SmoothL2Field`), and even `isSobolevDatum_partialDeriv` carries
`{Z : SmoothL2Field Space}` — so there is nothing in between.  That constructor is
where the homogeneous↔inhomogeneous comparison of finding 7 actually bites.  The
row should be re-labelled: **blocker = a missing D01 finite-order constructor**,
not B1/T1.

Separately, the *all-order* statement `ClassicalSolutionR.sobolev : ∀ m : ℕ, …`
(`Contracts/V1/Data.lean:643-645`) on one horizon `T` is gated by **A3**
(order-independent `T₀`, `A01_SPLIT.md:88`), because `exists_local`'s `T` depends
on `q`.  Neither B1 nor T1 fixes that.  B1 is needed for one thing only — to
replace `⇑(U t)` by the pointwise `velocity t` — and that step is *exactly* what
this lane's `IsSobolevDatum.congr_field` already discharges once B1 supplies
`velocity t =ᵐ[volume] ⇑(U t)`.

### Which rows actually feed `A01_SPLIT.md` §c rows c5/c6/c8 and §b row A1

| A01 obligation | fed by C1b rows | honest status |
|---|---|---|
| **c8** `∀ m, ∃ G, ContinuousOn G ∧ IsSobolevDatum m (velocity t) (G t)` | C1b-0 + C1b-c8-0 (m=0); C1b-m + C1b-c8-m (m≥1); C1b-cong (velocity ↔ `⇑(U t)`); C1b-unique (well-definedness of "the" datum) | the only obligation C1b really serves; additionally gated by **A3** for "∀ m on one T" |
| **c6** `spatialDivergence velocity = 0` | C1b-c6 only | gap, as marked |
| **c5** `initial : ∀ x, velocity (0,x) = a x` | **none** | c5 is a *pointwise field equality*; C1b-c5-0 / C1b-c5-all produce *datum* statements, which feed c8 at `t = 0`, not c5.  The pointwise half is B1's |
| **A1** tame product | **none** | A1 is A03's and needs a product estimate on the D01 carrier, not a carrier bridge.  The preamble's "(§b row `A1`)" is not supported by any row |

**(F10, severity LOW) Missing row: the B1 hand-off.**  Every row produces a datum
for `⇑(U t)`; every A01 obligation is about `velocity`.  The preamble promises
"transport of `U 0 = a.toLp` and of the divergence-free clause to
**pointwise**/datum statements", but no row owns the pointwise half.  Add a row,
e.g.

> **C1b-rep** — `velocity t =ᵐ[volume] ⇑(U t)` for `t ∈ Ico 0 T` (and
> `velocity (0,·) = a.field` pointwise) — size **L**, **owned by B1**, consumed
> here: given it, every datum row transfers by `IsSobolevDatum.congr_field`.

Making that explicit is what stops a future lane from reading C1b-c5-0 as
discharging c5.

**(F11, severity LOW) Citation drift.**  Every declaration exists and `#check`s;
only line numbers drift.  Wrong: `D01/DerivativeDatum.lean:246` → **245**
(`isSobolevDatum_partialDeriv`; also wrong in ATTEMPTS §"Convention question");
`Euler/MeanOrdinaryLift.lean:31` → **27** (`ordinaryLift_ae`);
`Euler/MeanSolenoidalSpace.lean:107,189` → **58** (`solenoidalSpace`) and **79**
(`mem_solenoidal_iff`, the actual weak-divergence test — `:107` is
`solenoidalProjection_mem`); `OrdinaryForcedLocal.lean` "clause 4 (`:44`)" → **42**
and "clause 5 (`:45`)" → **43** (the clause *numbering* is right);
`CarrierBridge.lean` docstring `OrderZeroDatum.lean:97` → **96**; probe comment
`SmoothDatum.lean:279 / :291` → **278 / 290**.
Correct as cited: `Contracts/V1/Data.lean:160`; `D01/SmoothDatum.lean:237,278,290`;
`D01/OrderZeroDatum.lean:72,96,103`; `D01/ForceClass.lean:286`;
`D01/DatumToJets.lean:267`; `Paper3/AngularFourierDilation.lean:177`;
`Paper3/SobolevHilbertModel.lean:130`; `Euler/LpSmoothField.lean:44`;
`Euler/MeanSolenoidalSpace.lean:22`; `Euler/MeanOrbitSobolev.lean:71,75`
(`:79` is the equation line of the decl at `:77`); `Euler/MeanOrdinaryLift.lean:24`;
`Source/OrdinaryCylinderDescent.lean:56,60`; `Source/FourierConvention.lean:15,23,50`;
`NavierStokes/ProblemStatement.lean:30`; `Euler/EulerProof.lean:5202`;
`Source/OrdinaryForcedLocal.lean:32,41`; `COMPARISON.md:194`.

One claim I checked and found **correct**: §0(B)'s `(iξ)^{⊗m}` has the right
**sign** — `EulerMeanSolenoidal.translation a u = u(· + a)`
(`MeanSolenoidalTranslation.lean:18-20`), so the orbit derivative is `+∂ⱼu`, not
`−∂ⱼu`.

## 4. Honesty of `ATTEMPTS_C1B.md` — failure reproduces; **recorded cause is wrong**

Reproduced verbatim (`/tmp/rev119/dotfail.lean`):

```
error(lean.invalidField): Invalid field `congr_field`: The environment does not contain
`Function.congr_field`, so it is not possible to project the field `congr_field` from an expression
  isSobolevDatum_zero_ordinaryL2 U
of type
  ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
    ((NSFormalization.Paper3.angularRealization 0) ↑((orderZeroDatum ⋯).ofLp i)) ψ =
      ∫ (x : Space), ψ x * ↑((↑↑U x).ofLp i)
```

**(F12, severity LOW, but it is lesson-shaped and would propagate)**  ATTEMPTS
records the cause as "`IsSobolevDatum … : Prop := ∀ …`, so a value of that type
reduces to a `∀` (a `Function`), and dot notation looked for
`Function.congr_field`", and draws the lesson "dot notation on a predicate whose
body is `∀`/`Prop` does not resolve the namespaced helper".  **That lesson is
false.**  `/tmp/rev119/dotfix.lean` declares the *same* lemma inside
`namespace NSFormalization.Section4.D01` (full name
`…D01.IsSobolevDatum.congr_field'`) and then

```lean
(isSobolevDatum_zero_ordinaryL2 U).congr_field' (by rw [hU]; exact a.toLp_ae)
```

**typechecks, silently.**  The real cause is a **namespace mismatch**: the helper
was declared under `NSFormalization.Section4.A01` while the predicate's head
constant is `NSFormalization.Section4.D01.IsSobolevDatum`; Lean looks for
`D01.IsSobolevDatum.congr_field`, fails, *then* unfolds the `def` to a pi type and
reports the `Function.congr_field` fallback.  Two consequences worth acting on:
(a) do **not** promote the recorded sentence to `logs/LESSONS.md`; the correct
one-liner is *"a `Foo.bar` helper only supports `h.bar` when it is declared in the
namespace of `Foo`'s head constant — the `Function.baz` message is the fallback,
not the cause"*; (b) the name
`NSFormalization.Section4.A01.IsSobolevDatum.congr_field` advertises dot notation
it cannot deliver.  Since the module is not a frozen contract, consider moving it
to the `D01` namespace (or renaming to `isSobolevDatum_congr_field`) in the next
touch — cosmetic, not blocking.

Everything else in ATTEMPTS checks out: the two probes really did typecheck (I
re-ran all four lane probe files), the scoping decision (order 0 first, because
D01 already ships the whole order-0 seed from a bare `MemLp`) is the right call,
and the three "not attempted" entries are correctly scoped out — in particular
C1b-c8-m's blocker (the vector order-`m` Plancherel isometry) really is absent
from the tree, as `OrderZeroDatum.lean:40-53` itself records.

---

## 5. Recommendation for the next C1b lane

Two candidates.  **Prefer (A)** — it is the only self-contained **M** left on the
row list, needs no new analysis and no upstream unit, and it is half of what c8
wants at order 0.

**(A) Row C1b-c8-0 — order-0 datum-path continuity.**  Exact statement:

```lean
theorem continuous_orderZeroDatum {X : Type*} [TopologicalSpace X]
    (U : X → EulerMeanSolenoidal.L2) (hU : Continuous U) :
    Continuous (fun t => orderZeroDatum (Lp.memLp (U t)))
```

Route (no new mathematics): re-express `componentLp` as a CLM of its `L²`
argument — `Lp.compLpₗ (Complex.ofRealCLM.comp (EuclideanSpace.proj i))`,
matching `memLp_component`'s `(Complex.ofRealCLM.comp (EuclideanSpace.proj i)).comp_memLp'`
(`OrderZeroDatum.lean:67-73`) — then compose the remaining factors, each already a
CLM/CLE: `𝓕 = Lp.fourierTransformₗᵢ`, `realProjectionTo 0`, `WithLp.toLp 2`,
`cyclesToAngularRealVector 0`.  The awkward step is that `orderZeroDatum` takes
the *proof* `hz : MemLp z 2 volume` as an argument, so the lane must first prove
`orderZeroDatum (Lp.memLp u) = Φ u` for an explicit CLM `Φ` and then transport
continuity through that equation.  No norm identity is needed (the module's own
docstring is explicit that the Plancherel identity is out of scope).

**(B) Row C1b-m, re-scoped to finite order — the real unblocking of C1b (see
findings 8/9).**  Split into two lanes, neither of which touches B1 or T1:

*B1-step (Euler side, size M, no D01):*

```lean
theorem exists_ordinary_word {q n : ℕ} (hq : n + 3 ≤ q) (u : SobolevSpace 1 q)
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 q (0, θ) u = u)
    (w : Fin n → Fin 4) :
    ∃ z : EulerMeanSolenoidal.L2, ordinaryLift z = word 1 u (by omega) w
```

Proof route: `word_has_jet 1 u (q - n) n _ w` + `ofJet` present `word 1 u _ w` as
the `value` of an order-`(q-n)` array; show that array inherits clause 7's angle
invariance (`sobolevTranslation` acts coordinatewise — check against
`translation_value` / `ordinarySobolev_angle`, `OrdinaryCylinderDescent.lean:71`);
then `exists_ordinary_value`.  This is where the lane should also record whether
`sobolevTranslation` really is coordinatewise — that is the one fact I did not
verify.

*B2-step (D01 side, size M–L, the actual analysis):* the missing finite-order
constructor,

```lean
theorem exists_isSobolevDatum_of_memLp_derivs {m : ℕ} {z : Space → Space}
    (hz : MemLp z 2 volume)
    (hd : /- the strong L² translation derivatives of z of order ≤ m exist -/) :
    ∃ A : RealVectorSobolev (m : ℝ), IsSobolevDatum (m : ℝ) z A
```

built as `cyclesToAngularRealVector m` of the Bessel-weighted componentwise
transform, exactly parallel to `orderZeroDatum` (`OrderZeroDatum.lean:96`), with
the one new analytic input being the homogeneous↔inhomogeneous comparison
`(1+‖ξ‖²)^m ≤ c_m (1 + ∑_{|α| = m} |ξ^α|²)` that puts the weighted transform in
`L²`.  This is the constructor D01 is missing between `orderZeroDatum` (order 0,
bare `MemLp`) and `smoothAngularDatum` (all orders, `SmoothL2Field`), and it is
the honest blocker of C1b-m.

Before either lane, fix `C1B_SPLIT.md` per findings 7–11 (input citations of row
C1b-m, the blocker attribution, the boldface about constants, the missing
C1b-rep row) and `ATTEMPTS_C1B.md` per finding 12, so the next worker is briefed
off a correct table.
