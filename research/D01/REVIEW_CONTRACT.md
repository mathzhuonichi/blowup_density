# Review — lane 034, contract `D01.datum_lemmas`

Reviewer pass over the registration of the four merged D01 lemma modules as one V1 contract
(`verification/Contracts/V1/DatumLemmas.lean`, `Bindings/DatumLemmas.lean`,
`Tests/DatumLemmas.lean`, the `D01.datum_lemmas` entry of `verification/contracts.json`).
Scope: run the gates, check that the contract states what the modules prove and only that.
No code was changed; this file is the lane's only addition by the reviewer.

## Verdict: **ACCEPT-WITH-NOTES**

All five gates pass. The binding proves nothing — 33 fields, zero `by` blocks, zero rewrites,
zero `le_antisymm`; every field is `:= Upstream.theorem` or a `fun … =>` argument permutation,
and the only glue is structural (one projection, one `.imp` conjunct-drop, one existential
introduction), each of which *weakens* and each of which is declared in the docstring it
belongs to. All 31 upstream `Section4/D01/*.lean:NNN` line citations are exact. The two
statements the brief singled out both survive scrutiny: `isHomogeneousSliceDatum_unique`
really is unconditional in `s` in the module, and `memHInfty_iff_smoothJets` really is the
same jet class the A05 and A03 contracts are built on.

The notes are all documentation-level: one mis-attributed `Data.lean` line range, five
line-number slips into the paper and into sibling contracts, one sentence in the module
docstring that overstates *why* a theorem was left out, and two bookkeeping items. None
changes a mathematical claim; none blocks the merge.

---

## Findings

### 1. LOW — `Conventions` attributes the `s < 3/2` **upper** bound to the **lower**-bound lines

**Field/location:** `verification/Contracts/V1/DatumLemmas.lean`, module docstring,
`## Conventions` → "The homogeneous range" bullet.

**What is wrong.** The bullet reads "The upper bound `s < 3/2` of the
`Data.IsHomogeneousDatum` docstring (`Data.lean:318-321`) is a *sufficient* Cauchy-Schwarz
route …". `Data.lean:318-321` is the **lower**-bound passage:

> 318 bound `-3/2 < s` is not a hypothesis of this definition: it is what the
> 319 manuscript needs for injectivity and the absence of polynomial ambiguity
> 320 (`02-preliminaries.tex:70`), and it appears as a hypothesis of unit L7, not
> 321 here.

The upper-bound Cauchy-Schwarz text is `Data.lean:307-317` ("whose right factor is finite at
the origin exactly when `2s < 3`" … "what is lost is surjectivity"); `REVIEW_HOMOGENEOUS.md`
ruling (a) cites `Data.lean:313-315` for the same passage. The same `318-321` cite is used
correctly two lines earlier in the module docstring (for unit L7) and correctly in the
`isHomogeneousSliceDatum_unique` field docstring, so only this one bullet is misaimed.

**Fix.** In that bullet cite `Data.lean:307-317` for the upper bound; leave `318-321` where it
refers to unit L7.

### 2. LOW — three manuscript line cites off by 1–4 lines

**Fields/locations:**

| cited | actual | where |
|---|---|---|
| `04-whole-space.tex:48` for the display `g_ε = g + H_ε + F_ε` | `:49` (the display block is 46–50) | module docstring `## Consumers` (B01/R42 bullet) and `memForceR_of_force_formula` docstring, twice |
| `04-whole-space.tex:33` for "there are `g_ε ∈ F_R`" | `:32` (line 33 is `\[`) | `memForceR_of_compact_difference` docstring |
| `04-whole-space.tex:198` for `cor:Rclasses` | `:194` | `memForceCompact_memForceR` docstring |

**What is wrong.** Off-by-small line numbers only; each cited *claim* is present and correct at
the nearby line. Everything else verified exact: `04-whole-space.tex` 8, 51, 53, 70, 185, 192,
219, 226, 249; `02-preliminaries.tex` 12, 17, 22, 58-69, 63, 70; `01-introduction.tex` 85-86,
91, 94, 103, 105; `appendix-a-local-theory.tex` 10, 12.

**Fix.** Bump the three numbers.

### 3. LOW — three cites into sibling contracts / `Data.lean` point at docstring lines

**Fields/locations:**

| cited | actual | where |
|---|---|---|
| `GradientL6.lean:104` for `SmoothSquareIntegrableJets` | `def` at `:106` | `Contracts/V1/DatumLemmas.lean` (unit-L2 field docstring) **and** `Bindings/DatumLemmas.lean:54-55` |
| `GradientL6.lean:88` for `partialDeriv` | `def` at `:83` | `Bindings/DatumLemmas.lean:75` and `memHInfty_partialDeriv` docstring |
| `Data.lean:654` for `ClassicalSolutionR.pressure_gradient` | field at `:647` (654 is prose inside the `maximalLifespanR` docstring) | module docstring "No pressure datum" bullet and `solution_slice_pressureGradient_contDiff` |

**Fix.** Bump the three numbers. Worth contrasting with the upstream cites, which are perfect:
all 31 `Section4/D01/{SmoothDatum,DatumToJets,ForceClass,HomogeneousWitness}.lean:NNN`
references land exactly on the named `theorem`/`def` line.

### 4. LOW — the module docstring gives the wrong reason for leaving out the conditional equality

**Field/location:** `verification/Contracts/V1/DatumLemmas.lean`, module docstring,
"`forceHomogeneousENorm` is still not known to be `< ⊤`" bullet: "… the conditional equality is
the two of them together and is deliberately not a field (**it cannot be stated without the
implementation's own path**, see `research/D01/ATTEMPTS_CONTRACT.md`)."

**What is wrong.** `ATTEMPTS_CONTRACT.md` §2.3 says the opposite, and §2.3 is right. What
cannot be *bound* as-is is the upstream theorem
`HomogeneousWitness.lean:692 forceHomogeneousENorm_eq_of_aestronglyMeasurable`, whose hypothesis
is `AEStronglyMeasurable (compactHomogeneousPath hs hf hc) forceTimeMeasure` and does name the
implementation's path. But the contract-vocabulary form
`(∃ G, IsHomogeneousPath s f G ∧ AEStronglyMeasurable G forceTimeMeasure) →
forceHomogeneousENorm q s f = eLpNorm (fun t => homogeneousFourierENorm s fun x => f (t,x)) q
forceTimeMeasure` *is* statable with no implementation name; what it would cost is a
`le_antisymm` / `iInf_le_of_le` assembly in the **binding**, i.e. mathematics in the adapter
layer, which the lane rules forbid. That is the honest reason, and it is the one §2.3 gives.

The underlying decision is correct either way, and the substitute is adequate: the two
registered fields `bochnerDatumENorm_eq_eLpNorm_slice` and
`eLpNorm_slice_le_forceHomogeneousENorm` give a consumer the equality in two lines once it has a
measurable path.

**Fix.** Replace the parenthetical with "the upstream theorem's hypothesis names the
implementation's own path, and the contract-vocabulary form would need a proof in the binding".

### 5. INFO — `ATTEMPTS_CONTRACT.md` miscounts the bridges once

**Location:** `research/D01/ATTEMPTS_CONTRACT.md` §3 item 7 — "The binding's 21 `rfl` bridges".
The actual count is **22** (verified by enumeration: `Bindings/DatumLemmas.lean` lines 45, 50,
56, 60, 65, 70, 77, 82, 85, 91, 95, 98, 102, 110, 114, 119, 123, 128, 133, 140, 144, 148), and
the same document's §3 item 9, its own header, and the contract module docstring all say 22.

**Fix.** One character.

### 6. INFO — `PLAN.md` has no row for lane 034

**Location:** `PLAN.md` §7 lane table. The diff correctly flips 024–029 to `已合入` with PR
numbers, but the table still ends at `033-A02-energy-u1a`; lane 034 added no row for itself.
Bookkeeping for the lead at merge time, not a defect in the contract.

### 7. INFO — `make test-mutations` is not a D01-specific check

`experiments/test_contract_mutations.py` builds all four mutants against
`Contracts.V1.Thresholds` / `Bindings.Thresholds` only (see its `IMPORTS` and `CASES`). It
proves the acceptance harness rejects `sorry`, a fabricated `axiom` and a weakened hypothesis in
general; it says nothing specific about `DatumLemmasAPI`. The D01-specific guarantee is the
`Tests/DatumLemmas.lean:14` `checkAxioms` line, which reports standard logical axioms only. No
action — recorded so the gate is not over-read.

### 8. INFO — a fourth same-body copy of the jet class is left unbridged

`A03.tame_products` states its clauses on `Contracts.V1.TameProduct.SmoothJets`
(`TameProduct.lean:207`), a separate `def` whose body is character-identical to the other three
(`ContDiff ℝ ∞ v ∧ ∀ n : ℕ, MemLp (iteratedFDeriv ℝ n v) 2 volume`). The binding bridges D01's
restatement to `Contracts.V1.SmoothSquareIntegrableJets` and to
`Contracts.V1.BoundedRep.SmoothSquareIntegrableJets`, but not to this one.

Not a defect: the D01 contract nowhere claims to feed `tame_products` (its "Out of scope" bullet
explicitly disclaims every Lemma A.1 estimate), and a consumer can cross the gap by unfolding.
But a 23rd bridge would make the anti-drift net complete across all four copies.

Related and also not actionable here: `TameProduct.lean:203-205` still says of unit L2 "the
converse is open, which is why the advection clause below is stated here rather than on
`MemHInfty`". `memHInfty_iff_smoothJets` closes that converse. `TameProduct.lean` is a frozen V1
specification, so this is a note for a hypothetical V2, exactly like the two `Data.lean`
docstring understatements that `ATTEMPTS_CONTRACT.md` §3 item 2 records.

---

## What was checked, and what came back clean

### Hygiene

* `verification/Contracts/V1/DatumLemmas.lean` imports exactly `Contracts.V1.Data`,
  `Contracts.V1.GradientL6`, `Contracts.V1.BoundedRepresentative` — three `Contracts.*` and
  nothing else. No Mathlib/Lean/Init import is even needed, so the allowlist and the
  `CONTRACT_CANONICAL_MODULES` escape hatch of `experiments/check_contracts.py:31-40` are not
  touched. `RealVectorSobolev` is brought in by `open NSFormalization.Paper3 (RealVectorSobolev)`,
  an `open`, not an import — the direct-import rule is unaffected.
* `grep -n "sorry\|axiom\|maxHeartbeats\|set_option\|native_decide"` over all three new files:
  **no match**. Not a single `set_option` of any kind; the contract, binding and test all
  elaborate at the default budget.
* `NSFormalization.Paper1.BoundaryCorollary` — the one module in the tree carrying a `sorry` —
  is absent from the 1126-module `D01.datum_lemmas` closure (and is hard-banned by
  `check_contracts.py`'s `visit`).
* `Tests/DatumLemmas.lean` follows the house pattern exactly: a `def checkedDatumLemmas :
  Contracts.V1.DatumLemmas.DatumLemmasAPI := Bindings.datumLemmas` plus
  `run_cmd TestSupport.checkAxioms`. 16 lines, no logic.

### Binding honesty — 33/33 fields

Read the whole of `verification/Bindings/DatumLemmas.lean`. There is **no `by` block anywhere in
the file**, no `le_antisymm`, no `rw`, no `simp`, no `constructor`. Every field is
`:= Upstream.theorem` or `fun … => Upstream.theorem args`. The only three fields carrying any
glue at all, and why each is structural rather than mathematical:

* `initialClass_smoothJets := fun _ ha => (D01.memHInfty_jetClasses ha.1.1 ha.1.2).1` — a
  projection out of a proved conjunction, plus the `initialClassR`/`MemHInfty` conjunct
  projections. `ATTEMPTS_CONTRACT.md` §2.2 explains the second conjunct is a registered
  `A03.bounded_representative` field already.
* `solution_slice_smoothJets := … (fun m => (u.sobolev m).imp fun _ h => h.2) …` — `Exists.imp`
  dropping a conjunct. `Data.ClassicalSolutionR.sobolev` (`Data.lean:643-645`) is
  `∀ m, ∃ G, ContinuousOn G (Ico 0 T) ∧ ∀ t ∈ Ico 0 T, IsSobolevDatum …`, so `h.2` keeps the
  datum half and discards `ContinuousOn`. This is precisely the "no time regularity" discard
  that the field docstring, the module docstring and the `contracts.json` scope string all
  declare. It weakens the hypothesis fed upstream; it cannot smuggle anything in.
* `compact_exists_homogeneousPath := fun _ hs _ hf hc => ⟨_, D01.Homogeneous.isHomogeneousPath_compact hs hf hc⟩`
  — existential introduction wrapping the concrete `compactHomogeneousPath`. Weakens by
  construction, and is the reason the field is stated existentially (a specification may not name
  an implementation definition).

### `rfl` bridges — 3 of 22 traced to both sides

The brief asked for three. All three identify the pair intended, and all three are load-bearing
(drop any one and the binding stops typechecking).

**(a) `datumLemmas_memForceR_eq` — the pair the brief named.**
Contract side `BlowupDensity.Contracts.V1.Data.MemForceR` (`Data.lean:544`); local side
`NSFormalization.Section4.D01.MemForceR` (`ForceClass.lean:158`). Both bodies, character for
character:

```
ContDiffOn ℝ ∞ f futureDomain ∧
  ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
    IsSobolevPath (m : ℝ) f G ∧ ContDiffOn ℝ ∞ G futureTimes ∧
    MemLp G 1 forceTimeMeasure ∧ MemLp G 2 forceTimeMeasure
```

and each sub-notion it names carries its own bridge in the same section —
`datumLemmas_futureTimes_eq`, `datumLemmas_forceTimeMeasure_eq`, `datumLemmas_isSobolevPath_eq`
— so the identification is not resting on an unchecked coincidence one level down. `rfl` closes
it (the module builds).

**(b) `datumLemmas_smoothSquareIntegrableJets_eq` and
`datumLemmas_boundedRep_smoothSquareIntegrableJets_eq`.**
Local side `NSFormalization.Section4.D01.SmoothSquareIntegrableJets` (`DatumToJets.lean:118`);
contract sides `BlowupDensity.Contracts.V1.SmoothSquareIntegrableJets` (`GradientL6.lean:106`,
the A05 class) and `BlowupDensity.Contracts.V1.BoundedRep.SmoothSquareIntegrableJets`
(`BoundedRepresentative.lean:152`, the A03 class). All three bodies are
`ContDiff ℝ ∞ v ∧ ∀ n : ℕ, MemLp (iteratedFDeriv ℝ n v) 2 volume`. Two separate bridges, one per
consumer contract, which is the right shape — a single bridge would leave the other spelling
free to drift.

**(c) `datumLemmas_partialDeriv_eq`.**
Local side `NSFormalization.Section4.A05.dirDeriv i z` (`A05/SmoothJets.lean:87`,
`fun x => fderiv ℝ w x (coordinateVector i)`); contract side
`BlowupDensity.Contracts.V1.partialDeriv i z` (`GradientL6.lean:83`,
`fun x => spatialDerivative (lift v) 0 x (coordinateVector j)`). `rfl` closes it because
`spatialDerivative` on the time-independent lift unfolds to `fderiv`. Load-bearing in the
sharpest way: the contract states `memHInfty_partialDeriv` with the contract's `partialDeriv`
while the bound theorem `D01.memHInfty_dirDeriv` concludes about `A05.dirDeriv`.

Name resolution inside the specification was re-derived rather than taken on trust: in
`namespace BlowupDensity.Contracts.V1.DatumLemmas`, bare `SmoothSquareIntegrableJets` resolves
through the ancestor namespace to `Contracts.V1`'s (GradientL6's) — `Data` declares no such
name, and `BoundedRep`'s copy needs its prefix, so there is no ambiguity to elaborate away.
Same for bare `partialDeriv` (`Data` declares none; `grep` confirms).

### Statement fidelity — 10 fields across all four groups

The brief asked for 8; ten were traced end to end (contract type ↔ upstream theorem ↔ paper).

**Group 1, jets ⟹ datum.**
`smoothJets_exists_datum` ← `SmoothDatum.lean:290 exists_isSobolevDatum_of_contDiff_memLp`, and
`smoothJets_exists_datum_fderiv` ← `:400 exists_isSobolevDatum_fderiv`. Types identical once
`SmoothSquareIntegrableJets` is split into `h.1, h.2`. Both quantify over **every real** `s`
with no compact-support, decay or `L¹` hypothesis — strictly weaker than the paper needs, as the
docstring claims; `01-introduction.tex:94` does define `H^s(R³)` at every real `s` and
`04-whole-space.tex:8` does use the non-integer `s_q = 2/q − 3/2`.

**Group 2, datum ⟹ jets.**

* `memHInfty_iff_smoothJets` ← `DatumToJets.lean:298 memHInfty_iff_smoothSquareIntegrableJets`.
  **Direct answer to the brief's question: yes, it is the same class, and there is no constant
  in it.** The upstream LHS is
  `ContDiff ℝ ∞ z ∧ ∀ m : ℕ, ∃ A : RealVectorSobolev (m:ℝ), IsSobolevDatum (m:ℝ) z A`, which is
  character for character `Data.MemHInfty` (`Data.lean:495`). The RHS is bridged by `rfl` to
  **both** `Contracts.V1.SmoothSquareIntegrableJets` (A05/`gradient_l6`) and
  `Contracts.V1.BoundedRep.SmoothSquareIntegrableJets` (A03/`bounded_representative`), identical
  bodies, different namespaces. One nuance the contract itself gets right: `A03`'s two clauses
  `supNorm_le` and `eLpNormTop_le` actually run on the *weaker* `BoundedRep.SmoothJetsUpTo 2`,
  reached by the already-registered `BoundedRepresentativeAPI.smoothJetsUpTo_of_allOrders` — and
  `solution_slice_smoothJets`'s docstring names exactly that route. `A03.tame_products` uses a
  fourth same-body copy that is not bridged; see finding 8.
* `jetSobolevENorm_le_sobolevENorm` ← `:343`. Exact, `Cjet := jetSobolevConst`,
  `Cjet_pos := jetSobolevConst_pos`. The docstring's "carries exactly one `(2π)^m`" checks out:
  `jetSobolevConst m = ∑_{j ≤ m} jetDatumConst j m`,
  `jetDatumConst j m = (‖physicalJetLp j‖ + 1) * frequencyUnit ^ (m:ℝ)`, and
  `frequencyUnit = 2 * Real.pi` (`Source/FourierConvention.lean:15`) — the factor pulls out of
  the sum once. Hypothesis is `ContDiff ℝ ∞ z` alone (no membership), and the empty-infimum
  branch is handled with `jetSobolevConst_pos` so `⊤` is never collapsed to `0`. The consumer
  claim about `04-whole-space.tex:53` ("an extension through `T` … bounded in `C_tH²` … hence
  bounded in `L^∞_x` by eq:Rproduct") is verbatim at that line.
* `solution_slice_smoothJets` ← `:396 smoothSquareIntegrableJets_slice`. The two upstream
  hypotheses are field-for-field `ClassicalSolutionR.velocity_smooth` (`Data.lean:632`) and the
  datum conjunct of `.sobolev` (`Data.lean:643-645`); the `ContinuousOn` conjunct is discarded,
  as declared in three places.

**Group 3, force class.**

* `memForceCompact_memForceR` ← `ForceClass.lean:189`, `memForceR_add` ← `:330`,
  `memForceCompact_of_smooth_support` ← `:352`, `memForceR_of_force_formula` ← `:428`. All four
  types identical to the upstream statements; all four bindings are pure permutations.
* `memForceCompact_of_smooth_support`'s three hypotheses are character for character
  `CorrectionAPI.force_smooth` / `force_compactSupport` / `force_positive_time`
  (`Contracts/V1/Correction.lean:426,429,440`, checked).
* `memForceR_of_force_formula`'s docstring is unusually and commendably candid: it says the field
  is registered because it is the manuscript's own display (`04-whole-space.tex:49`,
  `g_ε = g + H_ε + F_ε`) but that route 1 (`memForceR_of_compact_difference`) is the one R42 can
  discharge today, because `MemForceCompact (ScalingAPI.F ε)` is unavailable — nothing transports
  `PacketAPI.force_smooth`/`force_support` through `dilateField`. That matches
  `ForceClass.lean`'s own docstring and `REVIEW_FORCECLASS.md` issue 2. Registering an
  as-yet-undischargeable-but-true clause and saying so is the right call.

**Group 4, homogeneous witness.**

* `isHomogeneousSliceDatum_unique` ← `HomogeneousWitness.lean:445`. **Direct answer to the
  brief's question: yes, the field's unconditional statement is exactly what the module proves.**
  The upstream theorem binds `{s : ℝ}` with no hypothesis on `s`, and reduces to
  `homogeneousDatum_unique` (`:325`), also unconditional. The argument, read line by line: set
  `h := |ξ|^{-s}(G − G')`; the `Integrable` temperedness clause built into
  `Data.IsHomogeneousDatum` (`Data.lean:324`) gives `ψ·h ∈ L¹` for every Schwartz `ψ`; the two
  realization identities against the same `angularFourierDistribution u` give `∫ h·ψ = 0`;
  `locallyIntegrable_of_schwartz_mul` upgrades to `LocallyIntegrable h`;
  `ae_eq_zero_of_integral_schwartz_test_mul_eq_zero` gives `h =ᵐ 0`; and `|ξ|^{-s} ≠ 0` off the
  null set `{0}` gives `G = G'`. No step touches `s`, and structurally none can — polynomial
  ambiguity is exactly the failure of local integrability of `|ξ|^{-s}ĥ`, which the definition
  forbids outright. So `Data.lean:318-321`'s prediction of `-3/2 < s` for unit L7 is an
  *understatement*, not a contradiction. The field docstring says so and cites
  `REVIEW_HOMOGENEOUS.md` ruling **(b)** — the correct letter (verified: (a) is the `s < 3/2`
  upper bound, (b) is uniqueness at every real `s`).
* `schwartz_exists_homogeneousDatum` ← `:473` and `compact_exists_homogeneousDatum` ← `:519`.
  Types identical, hypothesis `-3 / 2 < s` only, both clauses (existence and the
  `‖A‖ₑ = homogeneousFourierENorm s z` identity) present on both. One thing worth flagging as a
  *strengthening*, not a defect: `04-whole-space.tex:70` states its finiteness argument for
  `-3/2 < s < 0`, while the clause has no upper bound. That is sound because the data are
  Schwartz — rapid decay handles large `|ξ|` at every `s`, and only the origin needs
  `s > -3/2` — and the docstring flags it explicitly ("No upper bound on `s` is needed"). The
  hypothesis is weaker than the paper's and the conclusion is the same, which is the safe
  direction.
* `compact_exists_homogeneousPath` ← `:658`, `bochnerDatumENorm_eq_eLpNorm_slice` ← `:667`,
  `eLpNorm_slice_le_forceHomogeneousENorm` ← `:683`. All three exact.

**Hypothesis strength.** No field examined has a hypothesis stronger than the paper's. Three are
visibly weaker (real-order datum existence; `ContDiff` only for the jet bound; no upper bound on
`s`), each flagged. The only fields that add a hypothesis the paper does not have —
`isSobolevDatum_add`, `isSobolevPath_add` and `isHomogeneousSliceDatum_sub`, each carrying a
Schwartz-pairing `Integrable` side condition — add it because Mathlib's Bochner integral
totalizes to `0` off the integrable set, which is the `Data.lean:148-155` caveat. The condition
is not removable: `REVIEW_HOMOGENEOUS.md` ruling (c) exhibits a concrete counter-scenario (a
Bernstein set) for the sub-clause without it. Each ships with its own discharger —
`memForceR_slice_integrable` on `F_R`, `schwartz_integrable_component` for Schwartz components —
so the condition costs a consumer nothing.

### Scope string in `verification/contracts.json`

Honest, and it names all three things the brief asked about.

* **Unregistered `forceHomogeneousENorm_eq_of_aestronglyMeasurable`** — covered in substance:
  "finiteness of forceHomogeneousENorm (its infimum also demands AEStronglyMeasurable, which no
  clause produces, so only the lower bound and the per-path identification are registered)". The
  module docstring adds "the conditional equality is the two of them together and is deliberately
  not a field", which is the same disclosure. Only the stated *reason* is off (finding 4).
* **Missing norm equivalence** — "Not asserted anywhere: the reverse inequality
  `sobolevENorm <= C * jetSobolevENorm` (no norm equivalence)", reinforced by a whole module
  docstring bullet noting the manuscript's `∑_{|α|≤m}‖∂^αz‖₂` form never appears either.
* **No time regularity** — "any time regularity of a datum path beyond what MemForceR itself
  carries (the ContinuousOn conjunct of ClassicalSolutionR.sobolev is discarded by every slice
  clause)".

It additionally disclaims the pressure datum, B02's `L¹∩L²` homogeneous class, the gradient order
shift, `F_rd`, and every Lemma A.1/B.1 estimate. Cross-read against
`research/D01/ATTEMPTS_CONTRACT.md` §2.1–2.4: the two agree item by item, and §2 lists nothing
omitted that the scope string fails to mention.

Its one imprecision is benign: it *summarizes* rather than enumerates what is registered, so
`smoothJets_sobolevENorm_ne_top`, `smoothJets_exists_datum_fderiv`, `initialClass_smoothJets`,
`memForceR_add_compact` and `memForceCompact_of_smooth_support` are not named individually. That
under-lists what is delivered, which is the safe direction for a scope string. A second small
ambiguity — "uniqueness … and additivity …, each with the Schwartz-pairing integrability side
condition" could be misread as attaching the side condition to uniqueness, which has none — also
errs toward claiming less.

---

## Commands and results

Environment: `bash scripts/lean-install.sh` (exit 0, which itself ends in `lake test`),
`. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, no `-j`, one `lake` process at a time, every
`lake` invocation from `verification/` (or via the `Makefile`'s `lake -d verification`).

```
$ cd .claude/worktrees/034-D01-lemma-contract/verification
$ lake build Contracts.V1.DatumLemmas Bindings.DatumLemmas Tests.DatumLemmas
```
> exit 0 — `Build completed successfully (9890 jobs).`
> `info: Tests/DatumLemmas.lean:14:0: Contract BlowupDensity.Tests.checkedDatumLemmas: checked;`
> `standard logical axioms only`
> No warning or error mentions any of the three new files. Every diagnostic in the log comes from
> replayed dependencies (`Source/PhysicalBesselSobolev:134` `ring` hint,
> `Source/PacketForceExtension:44`, `Source/ViscosityPacket:34`,
> `Paper3/SobolevDirectionalDerivative:103` deprecation) — the same set the four D01 lane reviews
> recorded.

```
$ cd .claude/worktrees/034-D01-lemma-contract
$ make check
```
> exit 0.
> `check_formalization_plan.py --check`: `task_count 30`, `source_manifest_entries 2975`,
> `missing_copied_imports []`, `citation_interfaces_reachable []`, `tracked_cache_free true`.
> The single `tokens_in_copied_umbrella_closure` entry is the pre-existing
> `NSFormalization/Paper1/BoundaryCorollary.lean:90 sorry`, which is banned from every contract
> closure and absent from this one.
> `check_contracts.py`: `registered_contracts: 10`, `Tests.DatumLemmas` present in the
> `D01.datum_lemmas` closure.
> `test_contract_policy.py`: `Ran 13 tests … OK`.
> `check_work_queue.py`: `30 work items: ownership, contract registration and task cards consistent.`

```
$ make test
```
> exit 0, 9951 jobs.
> `Tests/DatumLemmas.lean:14:0: Contract BlowupDensity.Tests.checkedDatumLemmas: checked;`
> **`standard logical axioms only`** — the line the brief required.
> The other nine contracts report the same on the same run (`Thresholds`, `Packet`, `Correction`,
> `CorrectionV2`, `GradientL6`, `BoundedRepresentative`, `Scaling`, `TameProduct`,
> `InsertionFamily`).

```
$ make test-mutations
```
> exit 0.
> `implementation_refactor: accepted`
> `admitted_proof: rejected as required`
> `extra_axiom: rejected as required`
> `weakened_hypothesis: rejected as required`
> `Mutation suite passed. This is an infrastructure check, not a PDE proof.`
> (Scope caveat in finding 7: the mutants are built against `Contracts.V1.Thresholds`.)

```
$ python3 experiments/check_contracts.py --base-ref origin/erenup/integration
```
> exit 0. `registered_contracts: 10`, **`base_compatibility_checked: true`** — so no existing
> `Contracts/` file, acceptance test, or registry entry was altered; `D01.datum_lemmas` is purely
> additive. `D01.datum_lemmas` closure: 1126 modules, of which the only `Contracts`/`Bindings`/
> `Tests` members are `Contracts.V1.{Data,GradientL6,BoundedRepresentative,DatumLemmas}`,
> `Bindings.DatumLemmas`, `TestSupport.Axioms`, `Tests.DatumLemmas`, and the four
> `NSFormalization.Section4.D01.*` proof modules plus `Section4.A05.SmoothJets` and
> `Section4.I03.Angular`.
> `origin/erenup/integration` = `8b3ae03`.

Hygiene greps:

```
$ grep -n "sorry\|axiom\|maxHeartbeats\|set_option\|native_decide" \
    verification/Contracts/V1/DatumLemmas.lean \
    verification/Bindings/DatumLemmas.lean \
    verification/Tests/DatumLemmas.lean
```
> no match.

```
$ grep -n "^import" verification/Contracts/V1/DatumLemmas.lean
```
> `import Contracts.V1.Data`
> `import Contracts.V1.GradientL6`
> `import Contracts.V1.BoundedRepresentative`

Upstream citation audit (all 31 `Section4/D01/*.lean:NNN` references in the contract, checked
against the actual `theorem`/`def` line): **31/31 exact**.

---

## Recommended follow-ups, in order

1. Fix the four documentation items — finding 1 (the `Data.lean:318-321` misattribution, the one
   that could actually mislead a reader about which bound is which), then findings 2, 3, 4.
2. Fix `ATTEMPTS_CONTRACT.md` §3 item 7, "21" → "22" (finding 5).
3. Add the `PLAN.md` row for lane 034 at merge (finding 6).
4. Consider a 23rd bridge to `Contracts.V1.TameProduct.SmoothJets` (finding 8) in a follow-up
   lane, and carry the two stale-docstring notes — `TameProduct.lean:203-205` and the two
   `Data.lean` understatements already recorded in `ATTEMPTS_CONTRACT.md` §3 item 2 — into
   whatever V2 of those specifications is eventually cut.

None of these is a merge blocker. The contract states what the four modules prove, and does not
state anything they do not.
