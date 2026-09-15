# Review — lane 078, task B02, unit 2 (`annularSchwartz`, split-and-start)

Reviewer: independent opus reviewer. Worktree
`/data_8T/ping/blowup_density/.claude/worktrees/078-B02-unit-2-split` at commit
`3291817`. Read/build only; no code changed. Scratch type-checks were run from
`/tmp` so the worktree stayed clean (`git status` empty before and after).

## Verdict: **ACCEPT-WITH-NOTES**

SL1 and SL2 are proved unconditionally, on `[propext, Classical.choice,
Quot.sound]`, with no `sorry`/`axiom`/`maxHeartbeats`. SL1's weight is
byte-identical to the weight inside `IsHomogeneousDatum`. SL2 is a genuine,
pointwise, non-vacuous inversion statement against the manuscript's angular
transform. The `U2_SPLIT.md` table is accurate: every SL3/SL4 statement
type-checks as written, SL4 is the spec field verbatim, every cited input exists
at the cited line, and the sizes are plausible. Both recorded failures in
`ATTEMPTS_U2.md` reproduce verbatim.

Five notes below. Finding 1 is the only one that costs the next worker real time
(a missing reconciliation step in the brief); finding 2 removes a 6-line
duplication; findings 3–5 are traps and nits for the SL3 worker. None blocks the
merge.

---

## 1. Commands and results

All from the worktree after `bash scripts/lean-install.sh` (`== OK`),
`. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, one lake process at a time, lake
always from `verification/`.

| # | command (cwd) | result |
|---|---|---|
| 1 | `lake build NSFormalization.Section4.B02.AnnularSchwartz` (`verification/`) | `Build completed successfully (8815 jobs).` Only pre-existing linter warnings from `Paper3/RealPositiveDensity.lean` and `Paper3/RealVectorPositiveDensity.lean`; none from the new module. |
| 2 | `lake env lean ../formalization/NSFormalization/Section4/B02/AnnularSchwartz.lean` | **prints nothing**, exit 0. |
| 3 | `lake env lean ../research/B02/axioms_u2.lean` | 3 declarations, each exactly `[propext, Classical.choice, Quot.sound]`: `contDiff_rpow_mul_of_annulus`, `schwartzAngularDilation_dilationInv`, `exists_schwartz_angularFourier_eq`. |
| 4 | `grep -nE 'sorry\|admit\|axiom\|native_decide\|maxHeartbeats' …/AnnularSchwartz.lean` | no match (exit 1). |
| 5 | `make check` (worktree root) | clean: `test_contract_policy.py` 13 tests OK; `check_work_queue.py` `30 work items: ownership, contract registration and task cards consistent.` |
| 6 | `lake env lean /tmp/078_review_typecheck.lean` (9 `#check`s for SL3/SL4a/SL4b/SL4c/SL4 + `SchwartzMap.coe_apply`) | all elaborate, no errors. See §3. |
| 7 | `lake env lean /tmp/078_review_failures.lean` (reproductions of the two `ATTEMPTS_U2.md` failures) | both fail exactly as recorded. See §4. |
| 8 | `lake env lean /tmp/078_helper.lean` (one-line derivation of the helper) | succeeds. See finding 2. |
| 9 | `git status --short` | empty. `git show --stat 3291817` = the 4 declared files, +273 lines, no others. |

CI note (not a finding): the B02 tree is not in `make test`'s registered-contract
closure and `formalization/NSFormalization.lean` does not import it, but
`.github/workflows/contracts.yml` has a *Compile changed modules outside the
registered test closure* step (`experiments/build_changed_lean.py --base-ref`),
so the new module is compiled in CI. Coverage is fine.

---

## 2. Statement fidelity (SL1, SL2)

**SL1 weight — byte-identical.** Extracted and diffed the two token strings with
the bound variable normalized:

```
Cutoff.lean:248  (((‖ξ‖ ^ (-s) : ℝ) : ℂ) * G ξ)   → ((‖ξ‖ ^ (-s) : ℝ) : ℂ) * X
AnnularSchwartz.lean:51  ((‖ξ‖ ^ (-s) : ℝ) : ℂ) * g ξ → ((‖ξ‖ ^ (-s) : ℝ) : ℂ) * X
```

`diff` empty. Identical up to the outer parenthesis and the variable name. The
docstring's "byte-for-byte" claim is accurate.

**SL1 hypotheses — `0 < δ` alone is right, and is a strict strengthening.**
The proof uses `hδ` in exactly one place: to derive `0 ∉ tsupport g` from
`tsupport g ⊆ {δ ≤ ‖ξ‖ ≤ R}` and `‖0‖ = 0`. Nothing else needs it.
- No condition on `s` is needed: `Real.rpow` with any real exponent is smooth
  away from `0`, which is all `ContDiffAt.rpow_const_of_ne` requires.
- No `δ < R` is needed: if `δ > R` the annulus is empty, `g ≡ 0`, and the claim
  is trivially true; the `HasCompactSupport` half only uses
  `closedFrequencyAnnulus δ R ⊆ closedBall 0 R`, valid regardless.

So SL1 is stated with strictly weaker hypotheses than the spec field supplies
(`0 < δ ∧ δ < R`). That is the correct direction — it makes SL1 reusable and
cannot weaken the eventual assembly.

**SL2 — `angularFourier` is the manuscript's transform.** `angularFourier` is
`Source/FourierConvention.lean:23`,
`angularFourier f ξ = frequencyUnit ^ (-3/2) • 𝓕 f (frequencyUnit⁻¹ • ξ)`, and
`angularFourier_eq_integral` (same file, :27) unfolds it to
`(2π)^(-3/2) ∫ exp(-i⟨x,ξ⟩) f x dx` — the manuscript normalization. It is
literally the same constant `angularFourier` that appears inside
`angularFourierDistribution_schwartz_apply` (`AngularFourierDilation.lean:218`,
whose proof rewrites through `schwartzAngularDilation_fourier_apply` at :208, a
`rfl`). Confirmed by reading both, not by name matching.

**SL2 — equality is pointwise for all `ξ`, as claimed.** The statement is
`∃ φ : SchwartzMap Space ℂ, ∀ ξ : Space, angularFourier (φ : Space → ℂ) ξ = f ξ`
— a genuine `∀ ξ`, not `=ᵐ[volume]`. Stronger than SL4c will need, and free here
because the proof is entirely Schwartz-algebraic.

**SL2 — not satisfiable by a degenerate implementation.** The lemma is universally
quantified over all smooth compactly supported `f` and its conclusion pins `φ`'s
transform to `f` at every point, so `f ≠ 0` forces `φ ≠ 0`. There is no vacuity
and no "`φ = 0` when `f = 0`" escape: a witness that ignored `f` would have to
satisfy `angularFourier 0 = f` for every such `f`, which is false. The one real
soundness question — whether the existential could be satisfied by a
non-Schwartz object — is closed by the type `SchwartzMap Space ℂ`.

**SL2 — no hidden annulus hypothesis.** `ofCompactSupport`
(`vendor/NavierStokesAndEuler/NavierStokes/R3/CompactSchwartz.lean:37`) takes
exactly `ContDiff ℝ ∞ f` and `HasCompactSupport f`, and builds the Schwartz map
by `weighted_derivative_bound` (:24), which only uses compactness of the support
and continuity of the weighted derivatives. The rest of SL2 is three rewrites at
the Schwartz-map/CLE level with no support reasoning at all. So the
`ofCompactSupport` route is sound for *any* compactly supported smooth `f`; the
annulus enters only upstream, in SL1, to produce such an `f`. Correctly factored.

---

## 3. The split table `U2_SPLIT.md`

**Target.** Lines 7–9 reproduce `research/B02/Spec.lean:362-364`
(`annularSchwartz`) verbatim — checked character by character against the spec,
including `0 < δ → δ < R →` and the `IsHomogeneousSliceDatum s (schwartzVector ψ) W`
conclusion.

**Type-checking.** I `#check`ed each remaining row as a `Prop` against the real
definitions (`/tmp/078_review_typecheck.lean`, command 6). All elaborate:

| row | elaborated to | verdict |
|---|---|---|
| SL3 rule | `∀ (φ : 𝓢(Space,ℂ)) ξ, angularFourier (fun x => (starRingEnd ℂ) (φ x)) ξ = (starRingEnd ℂ) (angularFourier ⇑φ (-ξ))` | well-typed |
| SL3 `g_conj_refl` | `∀ g i, (fun ξ => g i (-ξ)) =ᵐ[volume] fun ξ => (starRingEnd ℂ) (g i ξ)` | well-typed |
| SL3 conclusion | `angularFourier ⇑(realPartSchwartz (φ i)) =ᵐ[volume] fun ξ => ↑(‖ξ‖ ^ (-s)) * g i ξ` | well-typed |
| `ψ i` real | `SchwartzMap.postcompCLM Complex.reCLM : 𝓢(Space,ℂ) → 𝓢(Space,ℝ)` | well-typed, and `𝓢(Space,ℝ)` is exactly the spec's `SchwartzMap Space ℝ` |
| SL4a | `IsSliceDistribution (schwartzVector ψ) fun i => (SchwartzMap.toTemperedDistributionCLM Space ℂ volume) ((SchwartzMap.postcompCLM Complex.ofRealCLM) (ψ i))` | well-typed |
| SL4b | `Integrable (fun ξ => φ ξ * (↑(‖ξ‖ ^ (-s)) * ↑↑↑(W.ofLp i) ξ)) volume` | well-typed |
| SL4c | `(angularFourierDistribution (U i)) φ = ∫ ξ, φ ξ * (↑(‖ξ‖ ^ (-s)) * ↑↑↑(W.ofLp i) ξ)` | well-typed |
| SL4 | the spec field, verbatim | well-typed |

**Cited inputs all exist at the cited lines.** Verified by opening each:

| citation | actual | ok |
|---|---|---|
| `Annular.lean:200-207` reality pattern | `hA` at 200–201, `hSym` at 202–207 (`(A:FourierData) =ᵐ fun ξ => conj ((A:FourierData) (-ξ))`, built from `realSymmetry_ae` + `mem_realSubspace_iff … .mp A.property`) | ✅ exactly the pattern SL3 needs |
| `Cutoff.lean:284` `Integrable.mul_bdd` pattern | `integrable_schwartzVector` at :281, `refine χ.integrable.mul_bdd (c := …)` at :284 | ✅ |
| `fourier_conjugate` `RealSobolev.lean:61` | `theorem fourier_conjugate (f) (ξ) : 𝓕 (fun x => conj (f x)) ξ = conj (𝓕 f (-ξ))` | ✅ same `𝓕` (`Real.fourier_eq'`) as `angularFourier` uses |
| `realSymmetry_ae` `RealSobolev.lean:28` | ✅ | |
| `mem_realSubspace_iff` `RealSobolev.lean:123` | ✅ | |
| `ofCompactSupport` `CompactSchwartz.lean:37` | ✅ (`_apply` at :47) | |
| `schwartzAngularDilation_fourier_apply` `AFD:208` | ✅ | |
| `angularFourierDistribution_schwartz_apply` `AFD:218` | ✅ | |
| `schwartzAngularDilationEquiv` `right_inv` `AFD:58-64` | ✅ (`amplitude_inverse` is `private` at :32) | see finding 2 |
| `fourier_fourierInv_eq` `Notation.lean:217,222` | field at :217, `export FourierInvPair (…)` at :222, `attribute [simp]` at :225 | ✅ |
| `ContDiffAt.rpow_const_of_ne` `Pow/Deriv:624`, `contDiffAt_norm` `InnerProductSpace/Calculus:154`, `HasCompactSupport.mul_left` `Support:483` | ✅ all three | |
| `schwartzVector_apply` `Cutoff.lean:63` | actually :62 (statement spills to :63) | nit, finding 5 |

**Sizes.** SL3 **M** is right (a conj-reflection rule plus a.e. bookkeeping that
has to push `(W i) =ᵐ g i` through the measure-preserving negation, as
`Annular.lean:209` already does). SL4b **S**, SL4c **M**, SL4 **M** are all
plausible. SL4a **S** is now an over-estimate — see finding 3, it drops to near
trivial.

### SL3: exactly what the reality argument delivers, and what SL4c needs

The question is whether the a.e. conjugate-reflection symmetry of `g i` makes
`φ i` *real-valued*, or only makes `angularFourier (re φ i) =ᵐ g i`. Precisely:

- **Mathematically, `φ i` really is real-valued.** `Gᵢ` is continuous (SL1) and
  `volume` has full support on `Space`, so the a.e. Hermitian symmetry
  `Gᵢ(-ξ) = conj (Gᵢ ξ)` upgrades to an everywhere identity, and the inverse
  transform of a Hermitian function is real. But proving that *in Lean* costs an
  a.e.→everywhere upgrade plus a Fourier uniqueness/inversion argument — strictly
  more work than the alternative, and none of it is needed downstream.
- **The table does not claim it, and should not.** Its SL3 conclusion is only
  `angularFourier ↑(ψℂ i) =ᵐ[volume] Gᵢ` for `ψℂ i := realPartSchwartz φᵢ`,
  obtained from
  `angularFourier (re φ) ξ = ½[angularFourier φ ξ + conj (angularFourier φ (-ξ))]
   = ½[Gᵢ ξ + conj (Gᵢ (-ξ))] =ᵐ Gᵢ ξ`,
  where the last step is exactly `g_conj_refl` times the real weight
  (`‖-ξ‖ = ‖ξ‖` and `‖ξ‖^(-s)` real).
- **That weaker statement is precisely and only what SL4c needs**, because SL4c's
  conclusion is an integral identity closed by `integral_congr_ae` (with SL4b
  supplying integrability). An everywhere identity would buy nothing.

So the table's SL3 is correct as written and is the cheaper of the two routes; it
should not be "upgraded" to reality of `φ i`. The row states this itself ("Only
a.e. is needed (integral equality in SL4)"), and `ATTEMPTS_U2.md:64-65` says the
same. Note also that taking real parts is a genuine change of witness, not a
no-op you could skip: nothing in the Lean development knows `φ i` is already
real, and `schwartzVector` demands `SchwartzMap Space ℝ` anyway.

---

## 4. Honesty of `ATTEMPTS_U2.md`

Both recorded failures reproduce verbatim (`/tmp/078_review_failures.lean`,
command 7).

**Failure 1 (`simpa [Function.comp]`) — real.** Reproduction errors with

```
Type mismatch: After simplification, term hcomp has type
  ContDiffAt ℝ … (⇑Complex.ofRealCLM ∘ fun ξ => ‖ξ‖ ^ (-s)) ξ₀
but is expected to have type
  ContDiffAt ℝ … (fun ξ => ↑(‖ξ‖ ^ (-s))) ξ₀
```

word for word the mismatch `ATTEMPTS_U2.md:49-52` describes. The diagnosis is
also precise, not just directionally right: `Complex.ofRealCLM_apply` *is*
`@[simp]` (`Mathlib/Analysis/Complex/Basic.lean:328-329`), so the blocker is
genuinely the un-unfolded `∘` and not the `ℝ→ℂ` coercion. (`Function.comp_def` is
the lemma that would unfold it; passing the bare `def` does not.) The recorded
fix — ascribe to the lambda form, then `simpa only [Complex.ofRealCLM_apply]` —
is what the module does and it compiles.

**Failure 2 (`fourier_fourierInv_eq` namespace) — real.** Reproduction errors
with `Unknown identifier 'fourier_fourierInv_eq'`. Confirmed the cause by
reading `Mathlib/Analysis/Fourier/Notation.lean`: the scoped items in
`namespace FourierTransform` are only the two notations `𝓕`/`𝓕⁻` (:57-58),
while `export FourierInvPair (fourier_fourierInv_eq)` (:222) creates a plain
`FourierTransform.fourier_fourierInv_eq` that `open scoped FourierTransform`
does not bring into scope. The recorded fix (qualify it) and the recorded aside
(it is also `@[simp]`, :225) are both correct.

**One inaccurate justification** — see finding 2: `ATTEMPTS_U2.md:14-16` justifies
copying the right-inverse helper by "whose inline `amplitude_inverse` is
`private`". `amplitude_inverse` being private is true but irrelevant; the
*field* `right_inv` of the public `schwartzAngularDilationEquiv` is public and
proves the helper directly. Incomplete search, not a misreport.

---

## 5. Findings

**1. LOW — `U2_SPLIT.md` SL3 vs SL4a/SL4c use two unreconciled representations of
the same real Schwartz function; no row covers the bridge.**
SL3 concludes about `ψℂ i := realPartSchwartz φᵢ`. SL4a and SL4c are stated for
`postcompCLM Complex.ofRealCLM (ψ i)` with `ψ i := postcompCLM Complex.reCLM φᵢ`.
These are equal but not syntactically, and no row lists the reconciliation as an
input, so the next worker will hit it mid-proof.
*Fix:* add to SL3's row the one-line bridge
`SchwartzMap.ext` + `SchwartzMap.postcompCLM_apply`
(`Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:1052`) +
`Complex.reCLM_apply`/`Complex.ofRealCLM_apply` +
`realPartSchwartz_apply` (`RealSobolev.lean:87`), i.e.
`postcompCLM ofRealCLM (postcompCLM reCLM φ) = realPartSchwartz φ`. Or simpler:
state SL3 directly about `postcompCLM ofRealCLM (ψ i)` and drop
`realPartSchwartz` from the brief entirely.

**2. LOW — `AnnularSchwartz.lean:99-109`, the helper
`schwartzAngularDilation_dilationInv` is avoidable duplication of `AFD:58-64`.**
The six-line re-proof (including a re-derivation of the private
`amplitude_inverse`) is unnecessary. Verified working one-line replacement
(command 8):
```lean
theorem schwartzAngularDilation_dilationInv (X : SchwartzMap Space ℂ) :
    schwartzAngularDilation (schwartzAngularDilationInv X) = X :=
  schwartzAngularDilationEquiv.right_inv X
```
No `change`, no `ext`, no `hamp`. *Fix:* apply in the simplifier pass before this
module goes into a contract; better still, promote it to a public lemma in
`Paper3/AngularFourierDilation.lean` next to the equiv so the next consumer does
not copy it a third time. Also correct `ATTEMPTS_U2.md:14-16`, whose stated
justification for the copy does not hold.

**3. INFO (resolves a table TODO) — `U2_SPLIT.md` SL4a's open item "find the
named coercion lemma" is answered.**
It is `SchwartzMap.coe_apply`,
`Mathlib/Analysis/Distribution/TemperedDistribution.lean:143`:
`(f : 𝓢'(E,F)) g = ∫ x, g x • f x`. It is already used at
`AngularFourierDilation.lean:221`, inside a module this file imports. I confirmed
(command 6) that SL4a's `U i` elaborates to exactly
`SchwartzMap.toTemperedDistributionCLM Space ℂ volume (postcompCLM ofRealCLM (ψ i))`,
which is `coe_apply`'s LHS head, so it applies with no massaging; SL4a then closes
with `schwartzVector_apply` and `smul_eq_mul`. *Fix:* record it in the table; SL4a
is smaller than **S**.

**4. LOW — two namespace/scope traps the SL3 worker will hit, both siblings of
recorded failure 2.**
(a) `AnnularSchwartz.lean:41` opens `scoped ContDiff Topology FourierTransform`
but **not** `ComplexConjugate`; `Annular.lean:56` opens it, but `open scoped` does
not propagate through `import`, so SL3's `conj` will be an unknown identifier
until the line is added.
(b) SL3's linearity step: `angularFourier` is a bare function, not a bundled map,
so additivity must be routed through `schwartzAngularDilation_fourier_apply`
(`rfl`, `AFD:208`) to the Schwartz-level CLM, or through
`FourierTransform.fourier_add` / `fourier_smul` — which, exactly like
`fourier_fourierInv_eq`, are `export`ed into `namespace FourierTransform`
(`Notation.lean:97-98`) and are **not** reachable via `open scoped
FourierTransform`. *Fix:* note both in the SL3 row.

**5. NIT — `U2_SPLIT.md` citation/notation slips.**
`schwartzVector_apply` is at `Cutoff.lean:62`, not `:63`. SL4b/SL4c write `(W i) ξ`
where the elaborated term is `((W i : FourierData) : Space → ℂ) ξ` (three
coercions, `↑↑↑(W.ofLp i)`); harmless in a brief, but the next worker should write
the coercion out. *Fix:* optional.

---

## 6. Is the SL3 brief ready for the next worker?

Yes, with finding 1 folded in. The SL3 row already names the right decomposition
(pointwise conj-reflection rule for `angularFourier`, then a.e. reality of the
representative, then real parts), points at the one place in the repository where
the a.e. reality argument is already written out (`Annular.lean:200-207`, which I
read and confirmed is exactly the `realSymmetry_ae` + `mem_realSubspace_iff` +
negation-pushforward pattern SL3 needs), and — importantly — correctly scopes the
obligation to an a.e. identity rather than to reality of `φ i`, which is what
keeps SL3 at **M** instead of opening a Fourier-uniqueness sub-project. Its
statements type-check as written and its inputs all exist. The gaps are finding 1
(one reconciliation lemma, or a restatement that avoids needing it) and finding 4
(two scope traps that would otherwise cost an edit-compile cycle each). Adding
those three lines to the row makes it directly actionable; SL4a/SL4b are already
actionable as-is, with finding 3 shrinking SL4a further.
