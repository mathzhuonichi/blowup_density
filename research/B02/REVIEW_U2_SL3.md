# Review — lane 084, task B02, unit 2 (`annularSchwartz`: SL3 reality, SL4a slice, SL4b integrability)

Reviewer: independent opus reviewer. Worktree
`/data_8T/ping/blowup_density/.claude/worktrees/084-B02-unit-2-sl3` at commit
`1401b8d`. Read/build only; no code changed. Scratch type-checks ran from `/tmp`,
so the worktree stayed clean (`git status --short` empty before and after).

## Verdict: **ACCEPT-WITH-NOTES**

SL3, SL4a and SL4b are proved unconditionally on `[propext, Classical.choice,
Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`/`maxHeartbeats`.
The statements are faithful to `04-whole-space.tex:249` and, more importantly,
they are *directly* consumable: I wrote SL4c **and** the full `annularSchwartz`
assembly in a `/tmp` scratch against the committed lemmas and **both compile with
zero errors, in 15 lines total** (§4). That closes the remaining L work on unit 2
to a single short lane.

Five notes. Findings 1–3 cost the next worker a little time or duplicate
existing repo content; 4–5 are phrasing/dedupe nits. None blocks the merge.

---

## 1. Commands and results

From the worktree after `bash scripts/lean-install.sh` (`== OK`),
`. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, one lake process at a time, lake
always from `verification/`.

| # | command (cwd) | result |
|---|---|---|
| 1 | `lake build NSFormalization.Section4.B02.AnnularReal` (`verification/`) | **`Build completed successfully (8817 jobs).`** Only pre-existing linter warnings, from `Paper3/RealPositiveDensity.lean:67,76,88,100` (`<;>` seq-focus) and `Paper3/RealVectorPositiveDensity.lean:29` (unused variable). **No warning from the new module.** |
| 2 | `lake env lean ../formalization/NSFormalization/Section4/B02/AnnularReal.lean` | **prints nothing**, exit 0. |
| 3 | `lake env lean ../research/B02/axioms_u2_sl3.lean` | **8 declarations, each exactly `[propext, Classical.choice, Quot.sound]`**: `angularFourier_conj`, `angularFourier_schwartz_add`, `angularFourier_schwartz_smul`, `postcompReCLM_ofReal_eq`, `angularFourier_realPart_apply`, `angularFourier_realPart_ae`, `isSliceDistribution_schwartzVector`, `integrable_weight_annular`. |
| 4 | `grep -nE 'sorry\|admit\|axiom\|native_decide\|maxHeartbeats' …/AnnularReal.lean` | **no match** (exit 1). (The only hits in the lane are the eight `#print axioms` lines of the audit script, as intended.) |
| 5 | `make check` (worktree root) | clean: `test_contract_policy.py` 13 tests `OK`; `check_work_queue.py` `30 work items: ownership, contract registration and task cards consistent.` |
| 6 | `lake env lean /tmp/084_review_sl4c.lean` (SL4a type ascription + SL4c + full SL4 assembly) | **exit 0, nothing printed** — see §4. |
| 7 | `lake env lean /tmp/084_review_repro.lean` (the two recorded frictions) | **both reproduce verbatim** — see §5. |
| 8 | `git status --short`; `git show --stat 1401b8d` | empty; exactly the 4 declared files, +360/−4. |
| 9 | `grep -n "B02" formalization/NSFormalization.lean`; `.github/workflows/contracts.yml:77-81` | B02 is outside the root import and outside `make test`'s registered closure (same as its siblings), but CI's *Compile changed modules outside the registered test closure* step (`experiments/build_changed_lean.py --base-ref`) compiles it. Coverage fine. |

Declaration line numbers match the brief exactly: `angularFourier_conj` :50,
`angularFourier_schwartz_add` :59, `angularFourier_schwartz_smul` :65,
`postcompReCLM_ofReal_eq` :73, `angularFourier_realPart_apply` :84,
`angularFourier_realPart_ae` :101, `isSliceDistribution_schwartzVector` :138,
`integrable_weight_annular` :156.

---

## 2. Statement fidelity

### 2.1 SL3's hypotheses match SL2's output and `IsAnnularDatum` exactly

* **`hφ` vs SL2.** SL2 (`AnnularSchwartz.lean:110`) concludes
  `∃ φ, ∀ ξ, angularFourier (φ : Space → ℂ) ξ = f ξ`, specialized at
  `f := fun ξ => ((‖ξ‖ ^ (-s) : ℝ) : ℂ) * g ξ` (SL1's subject, byte-identical to
  the weight inside `IsHomogeneousDatum`, `Cutoff.lean:248`). SL3's hypothesis is
  `∀ ξ, angularFourier (↑φ) ξ = ((‖ξ‖ ^ (-s) : ℝ) : ℂ) * g ξ` — the same up to
  beta. Not asserted by eye: in the assembly scratch, `choose φ hφ using` SL2 and
  then feeding `hφ i` straight into SL3/SL4c **elaborates with no massaging**.
* **`hae` vs `IsAnnularDatum`.** `IsAnnularDatum` (`Annular.lean:67`) supplies
  `∀ i, ((Z i : FourierData) : Space → ℂ) =ᵐ[volume] g i`; SL3/SL4b take
  `hae : ((W i : FourierData) : Space → ℂ) =ᵐ[volume] g`. Token-for-token the
  same three-coercion spelling; again confirmed by `hae i` being accepted
  directly in the assembly.
* **SL4b vs `IsHomogeneousDatum`'s first conjunct.** `integrable_weight_annular`'s
  conclusion is `Integrable (fun ξ => φ ξ * (((‖ξ‖ ^ (-s) : ℝ) : ℂ) * ((W i :
  FourierData) : Space → ℂ) ξ)) volume`, which is the `Integrable …` conjunct of
  `IsHomogeneousDatum s ((W i : FourierData)) (U i)` verbatim (`Cutoff.lean:246-249`).

### 2.2 SL4a's `U` really is a `VectorDistribution`

`VectorDistribution := Fin 3 → 𝓢'(Space, ℂ)` (`Cutoff.lean:238`), and
`IsHomogeneousSliceDatum s z G = ∃ U : VectorDistribution, IsSliceDistribution z U
∧ IsHomogeneousVectorDatum s U G` (`Cutoff.lean:258`). I checked the type directly:

```lean
example (ψ : Fin 3 → SchwartzMap Space ℝ) : VectorDistribution :=
  fun i => ((SchwartzMap.postcompCLM Complex.ofRealCLM (ψ i) : SchwartzMap Space ℂ) :
    𝓢'(Space, ℂ))       -- elaborates
```

so SL4a's second argument is exactly the object the existential wants, and
`isSliceDistribution_schwartzVector _` discharges the first conjunct with no
reshaping (confirmed inside the full assembly, §4). The real Schwartz vector is
`ψ i := postcompCLM reCLM φᵢ : 𝓢(Space,ℝ)` = the spec's `SchwartzMap Space ℝ`, and
`postcompCLM ofRealCLM (ψ i)` is *the same term* as SL3's subject
`postcompCLM ofRealCLM (postcompCLM reCLM φᵢ)` — lane 078's review finding 1
(the `realPartSchwartz` vs `postcompCLM` mismatch) is fully resolved: the lane
took the "state SL3 about `postcompCLM ofRealCLM (ψ i)`" option *and* supplied
the half-sum bridge.

### 2.3 Not vacuous

SL3's hypotheses are jointly satisfiable exactly where the spec field applies:
SL1 produces a smooth compactly supported `Gᵢ` from any annular `g`, SL2 produces
a `φ` with `∀ ξ, angularFourier ↑φ ξ = Gᵢ ξ`, and `IsAnnularDatum` supplies
`hae`. The assembly in §4 instantiates all of them, so there is no vacuity. The
conclusion also genuinely uses `W`'s reality: it is derived from `(W i).property`
via `mem_realSubspace_iff`, and if `g` were not a.e. Hermitian the real part's
transform would be `½(G ξ + conj (G (-ξ))) ≠ G ξ`. So SL3 is the manuscript's
`:249` step ("take real parts of each component … complex conjugation is an
isometry … its weight is real and even"), not a tautology. Nor could a degenerate
witness satisfy it: the statement quantifies over *all* `W`, `g`, `φ` meeting the
hypotheses and pins an a.e. identity; the `g = 0` case is a genuine instance, not
an escape.

### 2.4 `angularFourier_conj`: the sign/reflection convention is right

`angularFourier f ξ = frequencyUnit ^ (-3/2 : ℝ) • 𝓕 f (frequencyUnit⁻¹ • ξ)`
(`Source/FourierConvention.lean:23-24`) with `frequencyUnit = 2π : ℝ`, positive
(`:15,17`). `fourier_conjugate` (`RealSobolev.lean:61`) is
`𝓕 (fun x => conj (f x)) ξ = conj (𝓕 f (-ξ))`. Composing:

```
angularFourier (conj f) ξ = c • 𝓕 (conj f) (u⁻¹ • ξ)
                          = c • conj (𝓕 f (-(u⁻¹ • ξ)))        -- fourier_conjugate
                          = conj (c • 𝓕 f (u⁻¹ • (-ξ)))        -- smul_neg; c real
                          = conj (angularFourier f (-ξ))
```

which is exactly the module's four-rewrite proof (`smul_neg` reconciles
`u⁻¹ • (-ξ)` with `-(u⁻¹ • ξ)`; `Complex.real_smul` + `map_mul` +
`Complex.conj_ofReal` push the **real** amplitude `(2π)^(-3/2)` through `conj`).
The reflection lands in the frequency variable and the dilation commutes with it
because the scalar is a positive real — no stray sign, no factor of `2π` lost.
Cross-check: `Section4/D01/HomogeneousWitness.lean:190` `angularFourier_conj_neg`
(the real-`f` special case, already in the repo) uses the identical simp set
`[angularFourier, smul_neg, Complex.real_smul, map_mul, Complex.conj_ofReal]`.
Same convention, independently written. See finding 1.

The downstream use is also sign-correct: `hφreal` turns
`conj (g (-ξ)) = g ξ` into `conj (angularFourier ↑φ (-ξ)) = angularFourier ↑φ ξ`
by `map_mul` + `Complex.conj_ofReal` (weight real) + **`norm_neg`**
(`‖-ξ‖ = ‖ξ‖`, so the weight is even) — the manuscript's "its weight is real and
even" clause, formalized.

---

## 3. Consistency

* **Imports canonical.** `AnnularReal.lean` imports only
  `NSFormalization.Section4.B02.AnnularSchwartz` and `…B02.Cutoff`; everything
  else (`RealVectorSobolev`, `FourierData`, `realSymmetry_ae`,
  `angularFourierDistribution`) arrives transitively. This is a `formalization/`
  module, so the `Contracts/*` import policy does not apply; `make check`'s
  `test_contract_policy.py` is green anyway.
* **No restated definitions.** The module declares **zero** `def`/`structure` —
  eight theorems only. Nothing to drift.
* **Reality argument.** `AnnularReal.lean:109-117` (`hA` + `hSym`) is the
  `Annular.lean:198-207` pattern, reused as the brief specified. It is a *verbatim
  re-derivation* rather than a call to a shared lemma — but there is no shared
  lemma to call: `Annular.lean`'s copy is inline inside `annularTruncLp_mem`'s
  proof, so reuse would have required refactoring a module outside this lane. I
  judge this acceptable; see finding 5 for the extraction that should eventually
  happen.
* **`postcompReCLM_ofReal_eq` vs `realPartSchwartz`.** I grepped
  `Source/RealSobolev.lean` in full: it has `realPartSchwartz` (:84),
  `realPartSchwartz_apply` (:87), `conjugateSchwartz` (:54),
  `weightedFourierLp_realPart` (:99) — but **no lemma relating
  `postcompCLM ofRealCLM ∘ postcompCLM reCLM` to any of them**. So the new lemma
  is not a duplicate; it is the bridge lane 078's review finding 1 asked for. Its
  RHS is the unfolded half-sum rather than `realPartSchwartz φ` (finding 4).

---

## 4. Consumability: SL4c and the SL4 assembly, verified

`/tmp/084_review_sl4c.lean`, command 6, **exit 0**. SL4c goes through in **four
tactic lines**, and it does **not** need SL4b:

```lean
theorem sl4c {s : ℝ} (W : RealVectorSobolev s) (i : Fin 3)
    {g : Space → ℂ} (hae : ((W i : FourierData) : Space → ℂ) =ᵐ[volume] g)
    {φ : SchwartzMap Space ℂ}
    (hφ : ∀ ξ : Space, angularFourier (↑φ) ξ = ((‖ξ‖ ^ (-s) : ℝ) : ℂ) * g ξ)
    (χ : SchwartzMap Space ℂ) :
    angularFourierDistribution
        ((SchwartzMap.postcompCLM Complex.ofRealCLM
          (SchwartzMap.postcompCLM Complex.reCLM φ) : SchwartzMap Space ℂ) : 𝓢'(Space, ℂ)) χ
      = ∫ ξ : Space, (χ : Space → ℂ) ξ *
          (((‖ξ‖ ^ (-s) : ℝ) : ℂ) * ((W i : FourierData) : Space → ℂ) ξ) := by
  rw [angularFourierDistribution_schwartz_apply]
  refine integral_congr_ae ?_
  filter_upwards [angularFourier_realPart_ae W i hae hφ, hae] with ξ h1 h2
  rw [smul_eq_mul, h1, h2]
```

Nothing is missing: `angularFourierDistribution_schwartz_apply` (`AFD:218`)
applies to the SL4a `U i` with no massaging (its LHS head is the same coercion),
`smul_eq_mul` converts `•` to `*` in the ℂ case, and SL3 + `hae` close the a.e.
step in one `filter_upwards`.

And the **whole remaining unit** — the spec field itself — is eight more lines:

```lean
theorem annularSchwartz_assembled (s : ℝ) (δ R : ℝ) (hδ : 0 < δ) (_hδR : δ < R)
    (W : RealVectorSobolev s) (hW : IsAnnularDatum δ R W) :
    ∃ ψ : Fin 3 → SchwartzMap Space ℝ, IsHomogeneousSliceDatum s (schwartzVector ψ) W := by
  obtain ⟨g, hg, hsupp, hae⟩ := hW
  choose φ hφ using fun i : Fin 3 => exists_schwartz_angularFourier_eq
    (contDiff_rpow_mul_of_annulus (s := s) hδ (hg i) (hsupp i)).1
    (contDiff_rpow_mul_of_annulus (s := s) hδ (hg i) (hsupp i)).2
  refine ⟨fun i => SchwartzMap.postcompCLM Complex.reCLM (φ i),
    fun i => ((SchwartzMap.postcompCLM Complex.ofRealCLM
      (SchwartzMap.postcompCLM Complex.reCLM (φ i)) : SchwartzMap Space ℂ) : 𝓢'(Space, ℂ)),
    isSliceDistribution_schwartzVector _, fun i χ =>
      ⟨integrable_weight_annular hδ W i (hg i) (hsupp i) (hae i) χ,
        sl4c W i (hae i) (hφ i) χ⟩⟩
```

**Compiles as written**, `δ < R` unused (as SL1's review predicted). This is the
strongest available evidence that lane 084's three statements have the right
shape: they compose into the spec field with no adapters, no `mul_comm`, no
coercion surgery.

---

## 5. Honesty of `ATTEMPTS_U2_SL3.md`

I opened every cited declaration and re-ran the two recorded frictions.

**Cited declarations — all exist and say what is claimed.**

| citation | actual | ok |
|---|---|---|
| `fourier_conjugate` `RealSobolev.lean:61` | `𝓕 (fun x => conj (f x)) ξ = conj (𝓕 f (-ξ))` | ✅ |
| `realPartSchwartz_apply` `RealSobolev.lean:87` | `realPartSchwartz φ x = ((φ x).re : ℂ)`, proved from `change (1/2:ℝ) • (φ x + conj (φ x)) = _` — so the module's `exact (…).symm` closing "up to defeq" is exactly right | ✅ |
| `realSymmetry_ae` `:28`, `mem_realSubspace_iff` `:123` | ✅ both | ✅ |
| `schwartzAngularDilation_fourier_apply` `AFD:208` (`rfl`), `angularFourierDistribution_schwartz_apply` `AFD:218`, `schwartzAngularDilation_apply` `AFD:24` | ✅ all three | ✅ |
| `SchwartzMap.coe_apply` `TemperedDistribution.lean:143` | `(f : 𝓢'(E,F)) g = ∫ x, g x • f x` | ✅ |
| `Annular.lean:200-207` reality pattern | `hA` :200-201, `hSym` :202-207 | ✅ identical shape |

**Prediction 1 — "SL4a product order did not bite" — TRUE.** `SchwartzMap.coe_apply`
puts the *test* first (`∫ x, g x • f x`) and `IsSliceDistribution`
(`Cutoff.lean:241-243`) also puts the test first
(`∫ x, ψ x * ((z x i : ℝ) : ℂ)`). Both sides are `χ x * …`, so no `mul_comm` is
needed. Verified by reading both definitions, and by SL4a's proof being a single
`rw` + `simp only`.

**Prediction 2 — "SL4b via `Continuous.integrable_of_hasCompactSupport`, not
`Integrable.mul_bdd`" — TRUE and a real simplification.** The module's proof is
`φ.continuous.mul hGsmooth.continuous` + `hGcs.mul_left` + `Integrable.congr hae`.
The predicted `Cutoff.lean:284` route (`χ.integrable.mul_bdd (c := seminorm …)`)
would have needed a bound constant and an a.e. bound; the compact-support route
consumes SL1's `HasCompactSupport` conjunct, which was already being produced and
was otherwise unused. Claim accurate.

**The `smul_comm` sidestep — TRUE, reproduced** (`/tmp/084_review_repro.lean`):

```
example (r : ℝ) (X : 𝓢(Space,ℂ)) : schwartzAngularDilation (r • X) = r • schwartzAngularDilation X := by
  rw [map_smul]
-- error: failed to synthesize MulActionHomClass (𝓢(Space,ℂ) →L[ℂ] 𝓢(Space,ℂ)) ℝ 𝓢(Space,ℂ) 𝓢(Space,ℂ)
```

`schwartzAngularDilation` is `→L[ℂ]` (`AFD:17`), so `map_smul` with an `ℝ`
scalar genuinely fails (needs `map_smul_of_tower`), exactly as recorded; the
module instead unfolds `schwartzAngularDilation_apply` and finishes with
`smul_comm` on two commuting real scalars. Sound and cheaper.

**Friction 2 (`FourierTransform.*` must be qualified) — TRUE, reproduced:**
`rw [fourier_smul]` under `open scoped FourierTransform` gives
`Unknown identifier 'fourier_smul'`. Same mechanism as lane 078's recorded
`fourier_fourierInv_eq` failure.

**Friction 1 (missing `open scoped ComplexConjugate`) — consistent:**
`AnnularSchwartz.lean:41` lacks it, `Annular.lean:56` has it, and
`AnnularReal.lean:41` adds it. Matches the record.

**`U2_SPLIT.md` rows — accurate, with two stale cells.** SL3/SL4a/SL4b are marked
DONE (084) with the correct lemma names (`angularFourier_realPart_ae`,
`isSliceDistribution_schwartzVector`, `integrable_weight_annular`) and the five
supporting names; SL1/SL2 remain DONE (078); SL4c and SL4 remain TODO with the
right inputs and the right critical path. The "Lane 084" paragraph is accurate.
Two cells are wrong — findings 2 and 3.

---

## 6. Findings

**1. LOW — `angularFourier_conj` (`AnnularReal.lean:50`) is a more general
re-proof of `angularFourier_conj_neg` (`Section4/D01/HomogeneousWitness.lean:190`),
which is already in the repo with the same simp set.**
The new lemma drops D01's reality hypothesis, so it is strictly better, and
neither module imports the other — nothing is broken. But this is the third
handwritten copy of the same three-rewrite argument
(`RealSobolev.weightedFourierLp_conjugate:80-81` is a fourth variant), against a
LESSONS entry added only two commits earlier ("restatement dedupe must grep all
of NSFormalization", `a131f29`).
*Fix (simplifier pass, before this goes near a contract):* promote
`angularFourier_conj` to `Source/FourierConvention.lean` next to `angularFourier`,
and rewrite D01's `angularFourier_conj_neg` as its one-line corollary
(`hf` gives `(fun x => conj (f x)) = f` by `funext`, then `(angularFourier_conj f ξ).symm ▸ …`).
Out of this lane's scope; record it as a follow-up.

**2. LOW — `U2_SPLIT.md` SL4c row: "Needs SL4b's integrability to justify the
integrals agree" is false**, and `ATTEMPTS_U2_SL3.md`'s closing section repeats it
("… and `integrable_weight_annular` for integrability").
`MeasureTheory.integral_congr_ae` needs only the a.e. equality of the integrands;
my SL4c (§4) compiles with no integrability input at all. SL4b is needed for the
**first conjunct** of `IsHomogeneousDatum`, not for SL4c.
*Fix:* one-line correction in both files, so the next worker does not go hunting
for an obligation that is not there.

**3. NIT — `U2_SPLIT.md` SL4b row's inputs column is stale.** It still describes
the abandoned `Integrable.mul_bdd` / `Cutoff.lean:284` route, although the row is
marked DONE via `Continuous.integrable_of_hasCompactSupport`. `ATTEMPTS` records
the switch correctly; the table does not.
*Fix:* replace the cell with the route actually used (SL1's `HasCompactSupport`
conjunct + `Continuous.integrable_of_hasCompactSupport` + `Integrable.congr hae`).

**4. NIT — `postcompReCLM_ofReal_eq` could name `realPartSchwartz`.** The RHS
`(1/2 : ℝ) • (φ + conjugateSchwartz φ)` is defeq to `realPartSchwartz φ`
(`RealSobolev.lean:84` is literally `(1/2:ℝ) • (id + conjugateSchwartz)`), and
stating the lemma as `… = realPartSchwartz φ` would connect it to the existing
vocabulary (`weightedFourierLp_realPart`, `realProjection`) for the next consumer.
Harmless as-is — the unfolded form is what `angularFourier_realPart_apply`
immediately needs.

**5. INFO — the `mem_realSubspace_iff` + `realSymmetry_ae` extraction is now
written out in ~6 places.** `AnnularReal.lean:109-117` copies
`Annular.lean:198-207`; `D01/{HomogeneousWitness,SmoothDatum,DerivativeDatum}.lean`
and `Paper3/AngularSobolevCoordinates.lean` carry near-variants. The reusable
statement is
`theorem ae_conj_neg_of_mem_realSubspace {s} {h : FourierData} (hh : h ∈ realSubspace s) :
 (h : Space → ℂ) =ᵐ[volume] fun ξ => conj (h (-ξ))`, which would collapse each site
to one line. Belongs in `Source/RealSobolev.lean`, i.e. a separate MAINT lane —
not this one.

---

## 7. Recipe for SL4c + SL4 (next worker)

Both steps are already verified compiling against the committed lemmas (§4), so
the next lane is **transcription, not research: ~15 lines plus a docstring**,
in a new module (say `Section4/B02/AnnularAssembly.lean`, importing
`Section4.B02.AnnularReal`) or appended to `AnnularReal.lean`.

1. **SL4c (4 tactic lines).** State it with the same hypothesis block as SL3
   (`W`, `i`, `hae`, `φ`, `hφ`) plus a test `χ`, concluding
   `angularFourierDistribution ((postcompCLM ofRealCLM (postcompCLM reCLM φ) : 𝓢(Space,ℂ)) : 𝓢'(Space,ℂ)) χ
    = ∫ ξ, χ ξ * (((‖ξ‖^(-s):ℝ):ℂ) * ((W i : FourierData) : Space → ℂ) ξ)`.
   Proof: `rw [angularFourierDistribution_schwartz_apply]` (`AFD:218`);
   `refine integral_congr_ae ?_`;
   `filter_upwards [angularFourier_realPart_ae W i hae hφ, hae] with ξ h1 h2`;
   `rw [smul_eq_mul, h1, h2]`. **No integrability input** (finding 2).
2. **SL4 (8 lines).** `obtain ⟨g, hg, hsupp, hae⟩ := hW`; `choose φ hφ using
   fun i => exists_schwartz_angularFourier_eq (contDiff_rpow_mul_of_annulus hδ (hg i) (hsupp i)).1 (… ).2`;
   then a single `refine ⟨fun i => postcompCLM reCLM (φ i), fun i => (… : 𝓢'(Space,ℂ)),
   isSliceDistribution_schwartzVector _, fun i χ => ⟨integrable_weight_annular hδ W i (hg i) (hsupp i) (hae i) χ,
   sl4c W i (hae i) (hφ i) χ⟩⟩`. `δ < R` is unused — keep the binder (the spec
   field has it) and name it `_hδR`.
3. Extend `research/B02/axioms_u2_sl3.lean` (or add `axioms_u2_assembly.lean`)
   with the two new names, and register in the split table that the spec field
   `annularSchwartz` is inhabited — that discharges the last hypothesis of
   `Cutoff.lean`'s `spatialApproxHomogeneous_of`.
4. While there, fold in findings 2–4 (two brief corrections, one optional
   restatement) and open a MAINT item for findings 1 and 5.
