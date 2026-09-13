# Review — lane 073, task D01, obligation P2, sub-lemmas SL3 (+SL2)

Reviewed: `formalization/NSFormalization/Section4/D01/LerayMultiplier.lean`,
`research/D01/ATTEMPTS_SL3.md`, `research/D01/axioms_sl3.lean` (commit `4e9440f`, 3 files,
528 lines, all additions — no existing module touched).
Context read: `research/D01/P2_SPLIT.md`, `research/D01/REVIEW_P2.md`,
`Section4/D01/LeraySymbol.lean`, `Source/FiniteHilbertBochner.lean`, `Source/RealSobolev.lean`,
`vendor/HeliCorgi/Formal/{R3LerayComplexFiberSymbol,R3LerayPointwiseL2,R3ConjugationReflection,R3LerayConjugationEquivariance}.lean`,
`paper/sections/02-preliminaries.tex` (eq:Rpressure and the `PP` symbol convention).
Read/build only; the reviewer wrote this file and nothing else.

## Verdict — **ACCEPT-WITH-NOTES**

The **Lean is accept-grade**: it builds, a fresh elaboration emits literally nothing, all 21
declarations are standard-axiom, and every statement is the statement it claims to be. Checked
against the paper, against lane 062's real symbol, and against HeliCorgi's solenoidal symbol: the
orientation `(I−P) = projection onto ℂ ∙ ξ` is right, the a.e. identification really pins the
operator, and neither the zero operator nor `P` could satisfy the delivered set.

The **`ATTEMPTS_SL3.md` blocker claim is false**, and that is the one thing that matters here,
because ATTEMPTS is what the next lane acts on. The claim is that *any* manipulation of
`FiniteHilbertBochner.assemble` from an importing module hits a whnf/isDefEq blow-up ("times out
even at 1,000,000 heartbeats — genuinely stuck, not merely slow"), and that the unblock therefore
requires new lemmas inside `Source/FiniteHilbertBochner.lean`. **Neither holds.** I proved
`coordinates_assemble`, the `assemble` isometry, and the reality-convention bridge from a scratch
file in `/tmp` that only imports the lane's own module — no `set_option maxHeartbeats`, no edits to
`Source/`, ~20 lines each, all elaborating in seconds (probes B, C, G below). Combined with the
lane's own `coordinates_norm`, the datum-carrier repackaging the lane declared out of reach is
essentially one short lane away, in the SL3 module itself.

So: merge the Lean, but **`ATTEMPTS_SL3.md` must be corrected before the follow-on lane is
briefed** (finding 1), or a lane will be sent to edit a shared `Source/` module for no reason.

---

## Part 1 — Build, axioms, hygiene (all pass)

All from `WT/verification` after `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, one lake at a time.

| # | Command | Result |
|---|---------|--------|
| 1 | `bash scripts/lean-install.sh` | `== OK` (full replay, exit 0) |
| 2 | `lake build NSFormalization.Section4.D01.LerayMultiplier` | exit 0, **`Build completed successfully (8844 jobs).`** Warnings in the run are all pre-existing vendor HeliCorgi linter noise (`R3CoordinateLinearAux`, `R3DivergencePointwise`, `R3LerayL2Operator`, `R3LerayFourierBridge`, `R3LerayComplexFiberSymbol`); **none** from the new module |
| 3 | `lake env lean ../formalization/NSFormalization/Section4/D01/LerayMultiplier.lean` (fresh elaboration) | exit 0, **0 bytes of output**. Toolchain sanity-checked against a deliberately broken file in the same session (`example : (1:Nat) = 2 := rfl` → error, exit 1), so the silence is real, not a silent replay |
| 4 | `lake env lean ../research/D01/axioms_sl3.lean` | exit 0; **21** `#print axioms` lines, every one `[propext, Classical.choice, Quot.sound]` |
| 5 | `grep -nE 'sorry\|admit\|axiom\|native_decide\|maxHeartbeats\|set_option'` on both new Lean files | only the module docstring line 34 (`"No `sorry`, no `axiom`; …"`) and the literal `#print axioms` lines. **Nothing in code**; no `set_option`, no heartbeat bump |
| 6 | `make check` (WT root) | **exit 0** — `check_formalization_plan.py --check`, `check_contracts.py`, `test_contract_policy.py` (13 tests OK), `check_work_queue.py` (30 work items consistent) |

**Import-closure audit** (transitive closure over every `import` line in `formalization/`,
`vendor/HeliCorgi`, `vendor/NavierStokesAndEuler`, `verification/`):

* closure of `…D01.LerayMultiplier` = 80 local modules, of which 28 are HeliCorgi `Formal.*`.
  The direct `import Formal.R3LerayPointwiseL2` is in `formalization/`, where it is allowed.
* Nothing under `verification/` contains `import Formal` or the string `LerayMultiplier`
  (grep over the whole tree, `.lake` excluded). The 52 upstream warnings cannot reach the
  `warningAsError = true` `Tests` library. ✔
* The module is not a contract, so the `Contracts/*` import policy does not apply; `make check`
  confirms. Like every other `Section4/*` module it is outside `NSFormalization.lean` and both
  `defaultTargets`, so CI compiles it only via `experiments/build_changed_lean.py` on this PR.

## Part 2 — Statement fidelity (correct)

**The symbol is `(I−P)`, not `P`, not zero.** Paper (`02-preliminaries.tex:76-77`): `𝐏` has symbol
`I − ξ⊗ξ/|ξ|²`, so `(I−P)` has symbol `ξ⊗ξ/|ξ|²` = the orthogonal projection onto the line `ℝ∙ξ`;
`eq:Rpressure` (`:90-92`) is `∇p = (I−𝐏)(f − ∇·(u⊗u))`, and `∇p` is a gradient, i.e. longitudinal.
The module's `complementSymbolComplex ξ := (ℂ ∙ r3FrequencyVectorComplex ξ).starProjection`
with `complementSymbolComplex_apply : … = (⟪ξ_ℂ,v⟫/‖ξ_ℂ‖²) • ξ_ℂ` is exactly `ξξᵀ/|ξ|²`
complexified. ✔ (Mathlib's `inner` is conjugate-linear in the *first* slot, so this really is
ℂ-linear in `v`, and `ξ_ℂ` has real entries, so the matrix is the real `ξξᵀ/|ξ|²`.)

**Same `ξ`, same complexification as upstream.** `vendor/HeliCorgi/Formal/R3LerayComplexFiberSymbol.lean:8,15,26`
reads `r3FrequencyVectorComplex ξ = toLp 2 (fun i => ((ξ i : ℝ) : ℂ))`,
`r3ComplexSolenoidalFiber ξ = (ℂ ∙ r3FrequencyVectorComplex ξ)ᗮ`,
`r3LeraySymbolComplex ξ = (r3ComplexSolenoidalFiber ξ).starProjection`. The lane's symbol is
`(ℂ ∙ r3FrequencyVectorComplex ξ).starProjection` — *the same submodule, without the `ᗮ`*, same
`ξ`, same `r3FrequencyVectorComplex`, same `R3C`. So
`r3LeraySymbolComplex_add_complementSymbolComplex : P ξ v + (I−P) ξ v = v` is the genuine
orthogonal decomposition `R3C = (ℂ∙ξ_ℂ)ᗮ ⊕ (ℂ∙ξ_ℂ)` (proved via
`Submodule.starProjection_orthogonal_val`), not an algebraic coincidence. ✔ Consistent with
lane 062's real `complementSymbol ξ = (ℝ ∙ ξ).starProjection`, of which this is the
complexification (the mirror relation carries over verbatim). ✔

**Could a wrong implementation satisfy the delivered set?** No.
* *Zero operator:* ruled out. `lerayComplementL2_ae` pins the CLM a.e. to the symbol, and the
  symbol is non-degenerate: `complementSymbolComplex_fixed_of_mem` at
  `v := ξ_ℂ ∈ ℂ ∙ ξ_ℂ` gives `(I−P)(ξ) ξ_ℂ = ξ_ℂ ≠ 0` for `ξ ≠ 0` (independently,
  upstream's `r3LeraySymbolComplex_self : P ξ ξ_ℂ = 0` plus the lane's `…_add_…` forces the same).
* *`P` instead of `(I−P)`:* ruled out by `…_add_…` together with `lerayL2_ae`, which ties the
  *complementary* operator to upstream's `r3LeraySymbolComplex`; the two differ (e.g. at `ξ = 0`,
  `complementSymbolComplex 0 = 0` since `ℂ∙0 = ⊥`, while `r3LeraySymbolComplex 0 = id`).
* *Coercion mismatch in `lerayComplementL2_ae`:* none. Both sides are `MNS2.R3 → MNS2.R3C`, LHS
  through the standard `Lp` coe, RHS through the same coe on `f` — the exact shape of upstream's
  `r3LerayPointwiseL2_ae`. The proof is `MemLp.coeFn_toLp` on a `toLp` of the pointwise action, so
  there is no room for a silent re-typing.

**Vacuity of the two fibre-facts-lifted lemmas.** Both hypotheses are satisfiable, and neither
lemma is vacuous:
* `lerayComplementL2_eq_self_of_longitudinal` assumes `∀ᵐ ξ, f ξ ∈ ℂ ∙ ξ_ℂ`. Satisfiable
  (trivially by `f = 0`; non-trivially by any `f ξ = g(ξ) • ξ_ℂ` with `g·‖ξ‖ ∈ L²`), and the
  conclusion `(I−P)f = f` is *false* for the zero operator on a non-zero such `f`, so the lemma
  has real discriminating content.
* `lerayComplementL2_eq_zero_of_transverse` assumes `∀ᵐ ξ, ⟪ξ_ℂ, f ξ⟫ = 0`. Same: satisfiable,
  and the conclusion is false for the identity on a non-zero transverse `f`.
  Together they are precisely SL5's "fixes `∇p`" and SL4's "kills a solenoidal field" at the
  `L²` level. ✔ (Neither non-vacuity witness is *proved* in Lean — normal for this repo, and not
  a finding; the pointwise non-degeneracy above already blocks the degenerate readings.)

**Reality (SL2) is about the right subspace.** Paper (`02-preliminaries.tex:73`): "Real vector
fields correspond to the closed subspace with `F(−ξ) = conj F(ξ)`".
`Source/RealSobolev.lean:19-24` defines `reflection = Lp.compMeasurePreservingₗᵢ ℝ (·↦ −·)`,
`conjugation = Complex.conjLIE.compLpL 2 volume`, `realSymmetry = conjugation ∘ reflection`, with
`realSymmetry_ae : realSymmetry h =ᵐ fun ξ => conj (h (−ξ))`, and
`realSubspace (_s) = {h | realSymmetry h = h}` (`:118,123`, and it really does discard `_s`, as
ATTEMPTS says ✔). The lane's `realSymmetryVec = conjugationVec ∘ reflectionVec` is the *same*
composition, with the *same* `measurePreserving_neg` and the componentwise `Complex.conjLIE`
(`conjR3C = piLpCongrRight 2 (fun _ => Complex.conjLIE)`), and `realSymmetryVec_ae` is the vector
analogue of `realSymmetry_ae`. I verified the agreement is not merely by eye — probe G below
**proves** `coordinates 2 volume (realSymmetryVec b) i = RealSobolev.realSymmetry (coordinates 2 volume b i)`
in nine lines. So "maps the reality subspace into itself" is about the right subspace,
componentwise. ✔ (See finding 3: that bridge lemma is not in the module, so nothing in Lean yet
connects the SL2 result to `RealVectorSobolev m`.)

## Part 3 — Consistency and duplication

* **Is the ℂ mirror a duplicate of `LeraySymbol.lean`?** No — genuinely new. The Fourier data are
  ℂ-valued (`R3C = EuclideanSpace ℂ (Fin 3)`), and lane 062's symbol is an
  `EuclideanSpace ℝ (Fin 3) →L[ℝ] …`; the two are different objects over different fields, and the
  ℂ one is the one an `L²` multiplier on `R3L2Velocity` can consume. Restating the seven fibre
  lemmas over ℂ is the right call, not a copy. ✔
* **Sections 2–3 vs. `Formal/R3LerayPointwiseL2.lean`.** The lane's `lerayComplementAction` /
  `aestronglyMeasurable_…` / `memLp_…` are a line-for-line mirror of upstream's
  `r3LerayPointwiseAction` / `aestronglyMeasurable_r3LerayPointwiseAction` /
  `memLp_r3LerayPointwiseAction` with `P` swapped for `(I−P)` — which is what `REVIEW_P2.md`
  recommended, and the genuinely new part (bundling into a `ContinuousLinearMap` with
  `opNorm ≤ 1`, which upstream never does) is delivered. ✔
* **Section 6 duplicates vendor code that is *not* imported** — see finding 2.
* **Imports.** `LeraySymbol` (canonical, lane 062), `Paper3.RealVectorPositiveDensity` (local,
  canonical), `Formal.R3LerayPointwiseL2` (vendor HeliCorgi, allowed in `formalization/`),
  `Mathlib.MeasureTheory.Function.L2Space` (for `L2.inner_def`, `L2.integrable_inner`). No local
  restatement of anything upstream beyond the ℂ mirror. ✔

## Part 4 — Honesty of ATTEMPTS (the blocker claim does not reproduce)

The three cited declarations are at the cited lines: `Source/FiniteHilbertBochner.lean:42`
`def assemble`, `:44` `def coordinates`, `:47` `theorem assemble_coordinates`. ✔ The carrier
analysis (`realSubspace` discards `s`; `Product (Fin 3) ℂ` is `R3C`) is correct. ✔

Everything else in the "Failures / blockers" section is wrong. Five scratch files under `/tmp`,
each `import NSFormalization.Section4.D01.LerayMultiplier` and nothing else, no `set_option`:

| probe | what | result |
|---|---|---|
| **A** | `change (coord i).compLpL 2 volume (∑ j, (insert j).compLpL 2 volume (h j)) = h i` — the worker's route 1, `change` to the unfolded `assemble` body, at concrete `Fin 3`/`ℂ`/`volume` | **succeeds instantly.** Only diagnostic is the expected `unsolved goals`. No blow-up |
| **B** | full `coordinates 2 volume (assemble 2 volume h) j = h j` at concrete `Fin 3`/`ℂ`/`(volume : Measure MNS2.R3)`, 18 lines, mirroring `assemble_coordinates`'s own a.e. proof (`Lp.coeFn_finsetSum` + `coeFn_compLpL` + `insert_apply`) | **exit 0.** One unused-simp-arg linter warning, nothing else |
| **C** | the same, stated *generically* in `ι/α/μ` (`coordinates_assemble'`), **plus** `assemble_norm' : ‖assemble 2 μ h‖ = ‖toLp 2 h‖` derived in four lines from it and the lane's own `coordinates_norm` | **exit 0, zero diagnostics.** This is the `assemble` isometry ATTEMPTS calls underivable |
| **D/E/F** | `assemble 2 volume h : MNS2.R3L2Velocity` typechecks; `coordinates 2 volume (lerayComplementL2 (assemble 2 volume h))` typechecks; its a.e. action `= fun ξ => (complementSymbolComplex ξ ((assemble 2 volume h) ξ)) j` proves through `coordinates_ae` + `lerayComplementL2_ae` | **exit 0, zero diagnostics.** The carrier identification `Lp (Product (Fin 3) ℂ) 2 volume ≡ R3L2Velocity` is free, and the whole round trip is already usable |
| **G** | `coordinates 2 volume (realSymmetryVec b) i = RealSobolev.realSymmetry (coordinates 2 volume b i)`, 9 lines | **exit 0** (a trailing `rfl` was rejected as "No goals to be solved" — the `rw` chain closes it) |

The only genuine friction I hit was a name clash (`FiniteHilbertBochner.insert` vs `Insert.insert`,
"Ambiguous term"), fixed by one `abbrev`. It is plausible the worker read that ambiguity error, or
a slow first elaboration, as the blow-up; but the claim as written — "genuinely stuck, not merely
slow", "every route is circular or needs the blocked defeq" — does not reproduce, and I did not
need a single heartbeat bump.

---

## Findings

### 1. (HIGH — `research/D01/ATTEMPTS_SL3.md:39-66`) The stated blocker is false, and the recommended next lane is the wrong lane.

ATTEMPTS asserts that manipulating `assemble` from an importing module is "genuinely stuck" even at
1,000,000 heartbeats, that `coordinates_assemble` and `‖assemble h‖ = ‖h‖` "cannot be derived …
without touching `assemble`'s internals (verified: every route is circular or needs the blocked
defeq)", and recommends adding both lemmas *inside* `Source/FiniteHilbertBochner.lean`. Probes A,
B and C refute all three: both lemmas prove from an importing module, generically, in ~20 lines
each, with no heartbeat bump and no edit to `Source/`. `assemble_norm'` in particular is four lines
on top of the lane's own `coordinates_norm`.

**Fix (documentation only, no code change):** rewrite the "Failures / blockers" and "Recommended
unblock" sections to say what is actually missing — the `codRestrict` onto the reality subspace and
the `RealVectorSobolev m` bundling — and delete the `Source/FiniteHilbertBochner.lean` recommendation.
Per `CLAUDE.md` rule 4, a negative result recorded in ATTEMPTS is only worth having if it is true;
this one would cost the next lane an unnecessary edit to a shared `Source/` module and a wrong
mental model of `Lp`/`compLpL` unification. Add the working route (a.e. via `Lp.coeFn_finsetSum`
+ `ContinuousLinearMap.coeFn_compLpL` + `insert_apply`, i.e. the same shape as
`assemble_coordinates`'s own proof) as the positive example.

### 2. (LOW — `LerayMultiplier.lean:287-360`) Section 6 re-proves vendor results that exist upstream, in a file the module does not import.

`vendor/HeliCorgi/Formal/R3ConjugationReflection.lean:44,82,136,175` already has `r3CConj`
(= `conjR3C`), `r3L2Conj`, `r3L2Reflect`, `IsR3RealVelocity`; and
`Formal/R3LerayConjugationEquivariance.lean:34,40,46,52,59` already has
`r3CConj_r3FrequencyVectorComplex`, `r3FrequencyVectorComplex_neg` (the *same name*),
`inner_r3FrequencyVectorComplex_r3CConj`, `r3CConj_r3LeraySymbolComplex`,
`r3LeraySymbolComplex_neg` — the exact five facts re-proved here for `(I−P)` instead of `P`. More
to the point, `:69` `reflect_conj_of_conjEquivariant_even_matrix` is a **generic** theorem: for any
`M : R3L2Velocity →L[ℂ] R3L2Velocity` realized a.e. by a conjugation-equivariant even matrix symbol,
`r3L2Reflect (r3L2Conj (M h)) = M (r3L2Reflect (r3L2Conj h))`. The lane has exactly the three
inputs it wants (`lerayComplementL2C_ae`, `conjR3C_complementSymbolComplex`,
`complementSymbolComplex_neg`), so `realSymmetryVec_lerayComplementL2` is an instance of it.

Neither vendor file is in the lane's 80-module closure, so reusing them means a new import
(`R3ConjugationReflection` is cheap; `R3LerayConjugationEquivariance` drags in the Fourier-transform
bridge and is not worth it). **No fix required** — the mirror is correct and self-contained, and
the repo's convention is to restate rather than import heavy vendor chains. Recorded so the next
lane knows the upstream cross-check exists, and so `EXTERNAL_REUSE.md` can point at it: proving
the lane's `realSymmetryVec_lerayComplementL2` *also* via
`reflect_conj_of_conjEquivariant_even_matrix` would be a strong independent check of SL2 at
near-zero cost.

### 3. (LOW — `LerayMultiplier.lean:362-367`, `:369-382`) Two scope overstatements in docstrings.

(a) `realSymmetryVec_lerayComplementL2_eq_self` is documented as "maps the reality subspace … into
itself". The subspace in question is the fixed-point set of the module's own `realSymmetryVec` on
the *raw* carrier; nothing in Lean yet connects it to `Source.RealSobolev.realSubspace` or to
`RealVectorSobolev m`. The docstring does spell out "the fixed points of `realSymmetryVec`", so it
is not misleading, but probe G shows the missing link is a nine-line lemma
(`coordinates (realSymmetryVec b) i = realSymmetry (coordinates b i)`) using only `coordinates`,
which the lane already handles. It should have shipped here.

(b) `coordinates_norm` is headed "**The `q = 2` isometry (SL3 datum-carrier bridge, reviewer's work
item)**". It is the `coordinates` half only, and it lands in the *ambient* `Product ι (Lp ℂ 2 μ)`,
not in `RealVectorSobolev m = Product (Fin 3) (RealSobolevHilbert m)`. `REVIEW_P2.md`'s work item
needs the `assemble` direction too (for `opNorm ≤ 1`, since `approximation_bound`-style bounds give
only `≤ |ι|`). Given finding 1 that direction was reachable in the same lane. Reword to
"the `coordinates` half of the `q = 2` isometry".

### 4. (INFO — `LerayMultiplier.lean:236-238`) `lerayL2_add_lerayComplementL2` is definitional.

`lerayL2 := 1 - lerayComplementL2`, so `lerayL2 + lerayComplementL2 = 1` closes by `abel` and
carries no mathematical content on its own. That is fine — the content is in `lerayL2_ae`, which
identifies `lerayL2` a.e. with HeliCorgi's genuine solenoidal symbol `r3LeraySymbolComplex`, and in
`r3LeraySymbolComplex_add_complementSymbolComplex`, which is the real orthogonal decomposition.
The docstring "**Helmholtz decomposition of the identity**" on the trivial lemma overstates it
slightly; the pair of lemmas together does earn the name. No action.

### 5. (INFO — `LerayMultiplier.lean:2`) `import NSFormalization.Paper3.RealVectorPositiveDensity` is wider than needed.

Nothing from that module is used; it is there to pull `Source.FiniteHilbertBochner` transitively
(`RealVectorSobolev` appears only in docstrings). `import NSFormalization.Source.FiniteHilbertBochner`
would do. Harmless — and arguably deliberate, since the follow-on lane needs `RealVectorSobolev`.
No action.

---

## Commands run (verbatim, with results)

```
bash scripts/lean-install.sh                                          → == OK (exit 0)
. scripts/lean-env.sh ; export LEAN_NUM_THREADS=6
cd verification
lake build NSFormalization.Section4.D01.LerayMultiplier               → Build completed successfully (8844 jobs).
lake env lean ../formalization/.../Section4/D01/LerayMultiplier.lean  → exit 0, 0 bytes of output
lake env lean /tmp/073-sanity.lean            (toolchain sanity)      → error on `(1:Nat) = 2 := rfl`, exit 1
lake env lean ../research/D01/axioms_sl3.lean                         → exit 0; 21 lines, all [propext, Classical.choice, Quot.sound]
grep -nE 'sorry|admit|axiom|native_decide|maxHeartbeats|set_option' <2 new .lean files>
                                                                      → docstring + `#print axioms` lines only
cd .. ; make check                                                    → exit 0 (13 policy tests OK; 30 work items consistent)
<transitive import-closure script>                                    → 80 local modules; 28 Formal.*; no verification/ module imports Formal or LerayMultiplier
lake env lean /tmp/073-assemble-probe.lean    (probe A)               → `change` succeeds; only `unsolved goals`
lake env lean /tmp/073-assemble-probe2.lean   (probe B)               → exit 0 (coordinates_assemble, concrete types)
lake env lean /tmp/073-assemble-probe3.lean   (probe C)               → exit 0 (generic coordinates_assemble' + assemble_norm')
lake env lean /tmp/073-carrier-probe.lean     (probes D/E/F)          → exit 0 (carrier ≡ R3L2Velocity; round trip + a.e. action)
lake env lean /tmp/073-reality-probe.lean     (probe G)               → exit 0 (coordinates ∘ realSymmetryVec = realSymmetry ∘ coordinates)
```

## Recommendation for the next lane (the datum-carrier repackaging)

Do it in `Section4/D01/LerayMultiplier.lean` (or a small `Section4/D01/LerayDatum.lean` importing
it) and **do not touch `Source/FiniteHilbertBochner.lean`** — finding 1 shows the defeq obstruction
that motivated that recommendation does not exist. The sequence is short and every step is now
evidenced by a probe: (i) `coordinates_assemble : coordinates 2 μ (assemble 2 μ h) j = h j`,
generically in `ι/α/μ`, by the a.e. route (`Lp.coeFn_finsetSum` + `ContinuousLinearMap.coeFn_compLpL`
+ `insert_apply` + `PiLp.single_apply`), ~18 lines — probe C; (ii) `assemble_norm`, four lines from
(i) plus the lane's own `coordinates_norm`, giving both directions of the bridge as isometries, so
`opNorm ≤ 1` transports by conjugation-by-isometry rather than through a `|ι|`-term triangle
inequality; (iii) bundle `coordinatesL`/`assembleL` as `≃ₗᵢ[ℝ]` (or as a pair of CLMs plus the two
round-trip lemmas — `assemble_coordinates` already exists upstream at `:47`) and define
`lerayComplementDatum := coordinatesL ∘ lerayComplementL2 ∘ assembleL`; (iv) `codRestrict` onto
`RealVectorSobolev m = Product (Fin 3) (RealSobolevHilbert m)` using the nine-line intertwiner
`coordinates (realSymmetryVec b) i = RealSobolev.realSymmetry (coordinates b i)` (probe G) together
with `realSymmetryVec_lerayComplementL2_eq_self` and `mem_realSubspace_iff` — note
`realSubspace` ignores its order argument, so one operator serves every `m`, as ATTEMPTS correctly
says. That closes SL3 as `P2_SPLIT.md` states it (`RVSᵐ →L[ℝ] RVSᵐ`, `opNorm ≤ 1`, a.e. action) and
SL2 at the datum level. Brief the lane off the **corrected** ATTEMPTS, not the committed one.
