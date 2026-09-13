# A01 — SIMP + tester pass (lane 113-SIMP-A01)

Scope: the four merged A01 modules
`Section4/A01/{ConvectionDivergence,ProjectedEquation,RadialPotential,PressureGauge}.lean`.
No new mathematics; every **exported** statement kept byte-for-byte identical
(names, binders, hypotheses, conclusions). Only proofs, private helpers and
docstrings changed. All work in worktree `.claude/worktrees/113-SIMP-A01`.

Baseline before touching anything: all four modules build and `lake env lean`
each is silent (exit 0, 0 lines); the three conformance files
`axioms_{a01,p1,m4}.lean` report exactly `[propext, Classical.choice, Quot.sound]`
for all 15 declarations; `Tests.RegularityPartial` = "checked; standard logical
axioms only".

## 1. Simplifier — changes made

Both changes are the two `PressureGauge.lean` items the lane-106 reviewer flagged
(`research/A01/REVIEW_M4.md` findings 1 & 2). Both helpers are `private` (not part
of the module's public API), so their proofs/docstrings are freely editable.
Each was first verified in a standalone probe (`research/A01/probes/simp_helpers.lean`)
before editing the module.

| module | decl (private) | before→after (proof body) | what was removed / why |
|---|---|---|---|
| PressureGauge | `fderiv_apply_component` | 11 → 3 lines | Replaced the `innerSL ℝ (coordinateVector b)` / `EuclideanSpace.inner_single_left` detour (the `hpt` sublemma + hand-built `heq`) by Mathlib's coordinate-evaluation CLM `EuclideanSpace.proj b`, for which `(EuclideanSpace.proj b) u = u b` holds `rfl`. Proof is now `have heq : H = ⇑(EuclideanSpace.proj b) ∘ G := hH` + one `rw` + `rfl`. |
| PressureGauge | `fderiv_fderiv_apply` | 6 → 1 line | Replaced the hand-rolled `ContinuousLinearMap.apply`-composition proof by `rw [fderiv_clm_apply hf (differentiableAt_const w)]; simp` (the `w`-slot is a constant, so `fderiv_clm_apply`'s second term vanishes under `simp`). `fderiv_clm_apply` is declared in `Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean:143` and is reached transitively through the module's existing imports — no new import (corrected per `REVIEW_SIMP.md` F7; the earlier draft mis-attributed it to `FDeriv/Mul.lean`). |

Module line counts: PressureGauge `221 → 211` (net −10; `git diff --stat` = +9/−19).
The other three modules (`ConvectionDivergence` 140, `ProjectedEquation` 68,
`RadialPotential` 246) are unchanged — see "left alone" below.

Verification after edits: incremental `lake build NSFormalization.Section4.A01.PressureGauge`
succeeds (2.0s); `lake env lean` on all four modules is silent; conformance and
the frozen-contract test are unchanged (§2).

### Negative example during simplification (recorded per brief)

- First probe of `fderiv_apply_component` via `EuclideanSpace.proj` **without** a
  trailing `rfl` left one goal open:
  ```
  ../research/A01/probes/simp_helpers.lean:18:43: error: unsolved goals
  ⊢ ((fderiv ℝ G x) v).ofLp b = (EuclideanSpace.proj b) ((fderiv ℝ G x) v)
  ```
  The remaining goal is `u.ofLp b = (EuclideanSpace.proj b) u`, true by `rfl`
  (`EuclideanSpace.proj b u` reduces to `u.ofLp b`). Adding a final `rfl` closes
  it — that is the committed proof. (Sanity probe `(EuclideanSpace.proj b) u = u b := rfl`
  succeeded, confirming the defeq.)

### Simplifications considered and left alone (with reasons)

- **`simp only` lists / dead `have`s across all four modules.** Left as-is:
  `linter.unusedVariables` and `linter.unusedSimpArgs` are on globally (they fire
  on unrelated dependency modules during the build, e.g. `Source/ViscosityPacket`),
  and all four A01 files elaborate with **zero** warnings, so there are no unused
  simp arguments and no unused named hypotheses to trim. The proofs are already tight.
- **Inlining `fderiv_fderiv_apply` at its single call site** (`hasSymmetricJacobian_pressureGradient`).
  Left alone: it is used inside a two-lemma `rw [fderiv_apply_component …, fderiv_fderiv_apply …]`;
  inlining `fderiv_clm_apply` there does not compose cleanly and would not reduce lines.
- **The duplicated basis-decomposition / basis-inner helpers** (`expand`, `basis_inner`
  in `RadialPotential.inner_fderiv_symm`; `expand`, `basisL` in
  `PressureGauge.pressureGradient_fderiv_slice`; `hcoord` in
  `RadialPotential.pressureGradient_pressurePotential`). These are small local `have`s
  that recur across the modules, but consolidating them needs a shared module and is
  a promotion, not a same-file simplification — flagged in the MAINT list (§4) instead.
- **`ConvectionDivergence.convection_term`** `simp only [add_apply, smul_apply,
  ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply]` + `rfl`:
  the four args are all live (linter silent), no trim available.

## 2. Tester — results

### (a) Rebuild + silence
- `lake build` of all four A01 modules: **success** (9881 jobs).
- `lake env lean` on each of the four: **exit 0, 0 output lines** (silent).

### (b) Conformance (axioms) — unchanged
Re-ran `research/A01/{axioms_a01,axioms_p1,axioms_m4}.lean`. All 15 declarations
(5 + 3 + 7) still report exactly `[propext, Classical.choice, Quot.sound]`; scan
for `sorryAx` / `native_decide` / `ofReduceBool` / errors = clean, exit 0 each.

### (c) Negative checks — revised after `REVIEW_SIMP.md` (F1, F4)

The first draft used a single method for all 11 exports — restate the theorem
minus one hypothesis, then apply the original theorem with that positional
argument omitted — and reported every failure as "the hypothesis is load-bearing".
The reviewer (F4) correctly flags this as **weak**: a missing positional argument
always errors, and the error only witnesses that *the theorem's signature still
has the argument*; it says nothing about whether the weaker statement is provable
by other means. Worse, this method got one of its own claims **wrong** (F1): the
old **N10** asserted `hsym` in `pressure_potential_of_pointwise` is load-bearing,
but `hsym` is in fact **redundant** — derivable from `hsm` + `hdp` — so its block
"fails" for the same superficial reason as the genuinely load-bearing N3/N6.

The checks are now split into two files:

**`research/A01/negative_simp.lean` — load-bearing evidence, MUST COMPILE SILENTLY.**
Holds the reviewer's §6 probes (transcribed verbatim; deprecation-only edits to
keep it warning-free), each carrying the three standard axioms:
- `Rev113.ConvDiv.hdiv_load_bearing` — **`hdiv` IS load-bearing**: proves the
  `hdiv`-free version of `navierStokesResidual_eq_iff_projected` is *False*, via
  the counterexample `u(t,y) = y₀ e₀` (`∇·u = 1`, `u(t,e₀) ≠ 0`).
- `Rev113.Radial.{G_not_symm, pot_eq, hG_load_bearing}` — **`hG` IS load-bearing**:
  counterexample `G(y) = y₁ e₀` (smooth, `¬ HasSymmetricJacobian`, radial potential
  `y₁y₀/2` whose derivative at `e₀` along `e₁` is `1/2 ≠ 0 = innerSL (G e₀)`).
- `Rev113.Gauge.{hsym_redundant, pressure_potential_of_pointwise_without_hsym}` —
  **`hsym` is NOT load-bearing** (F1): the `hsym`-free statement is *proved
  outright*, deriving the symmetric Jacobian from `hsm`+`hdp` via
  `pressureGradient_fderiv_slice` (Riesz) + `contDiff_infty_iff_fderiv` + Clairaut.
- `Rev113.Fidelity.*` — three `example`s deriving each probe's premise `H` from
  the real theorem + the dropped hypothesis, pinning that the probes' restatements
  are the frozen theorems minus exactly one hypothesis (no binder/conclusion drift).

**`research/A01/negative_simp_fail.lean` — signature checks, MUST FAIL.**
The original 11 blocks (N1–N11), kept under the header "Signature checks (NOT
load-bearing evidence)" with F4's caveat and an explicit note on N10. `lake env lean`
exits 1 with one type-mismatch per block (N10 emits two), at exactly these lines
(re-run tail in §4):

```
negative_simp_fail.lean:51:2   (N1  drop hu   from convectionDivergence_eq_advection_add_smul_div)
negative_simp_fail.lean:58:2   (N2  drop hdiv from convectionDivergence_eq_advection)
negative_simp_fail.lean:67:2   (N3  drop hdiv from navierStokesResidual_eq_iff_projected)
negative_simp_fail.lean:77:2   (N4  weaken Ioo→Ico in projected_of_classicalSolution)
negative_simp_fail.lean:92:20  (N5  drop hG   from inner_fderiv_symm)
negative_simp_fail.lean:99:30  (N6  drop hG   from hasFDerivAt_radialPotential)
negative_simp_fail.lean:106:48 (N7  drop hslice from pressureGradient_pressurePotential)
negative_simp_fail.lean:123:40 (N8  drop hp   from hasSymmetricJacobian_pressureGradient)
negative_simp_fail.lean:129:21 (N9  drop hp   from contDiff_gradSlice)
negative_simp_fail.lean:142:2 + 142:40 (N10 drop hsym — SPURIOUS per F1)
negative_simp_fail.lean:148:35 (N11 drop h    from fderiv_eq_of_pressureGradient_eq)
```

**Correction to the N10 claim.** `hsym` is redundant, not load-bearing. This is a
note for a `RegularityPartial` V2 / for whoever registers the A01 contract: the
minimal hypothesis set of `pressure_potential_of_pointwise` is `hsm` + `hdp`. The
frozen statement stays as-is (a redundant hypothesis is sound; the sole in-tree
consumer `pressure_potential_of_classicalSolution` supplies `hsym` from
`hasSymmetricJacobian_pressureGradient` at no cost). Recorded also in
`A01_SPLIT.md` row m4.

Exports with **no** Prop hypothesis — `convectionDivergence` (a definition),
`pressureGradient_fderiv_slice`, `pressureGradient_apply` — are unconditional
identities: nothing to drop, so no block (deliberate, not an omission).

### (d) Non-vacuity — `research/A01/nonvacuity_simp.lean` (compiles silently)
- **NV1** `HasSymmetricJacobian (fun x : Space => x)` — the identity field has
  Jacobian `id` (symmetric); shows the class of `inner_fderiv_symm`/… is inhabited.
- **NV2** `HasSymmetricJacobian id ∧ ContDiff ℝ ∞ id` — the exact hypothesis bundle
  of `hasFDerivAt_radialPotential` / `pressureGradient_pressurePotential` is inhabited.
- **NV3** `ContDiffOn ℝ ∞ (fun _ => (0:ℝ)) (Ico 0 T ×ˢ univ)` — the hypothesis of
  `hasSymmetricJacobian_pressureGradient` / `contDiff_gradSlice` is inhabited (zero pressure).
- **NV4** builds a concrete `PressureGaugeEquivOn (Ico 0 T) (pressurePotential …) (fun _ => 0)`
  by feeding the zero pressure through `hasSymmetricJacobian_pressureGradient`,
  `contDiff_gradSlice`, `D01.contDiff_slice_scalar` into `pressure_potential_of_pointwise`
  — simultaneously exercising three exports on a concrete smooth pressure and
  inhabiting `pressure_potential_of_pointwise`'s three per-time hypotheses.
- **NV5** the two hypotheses of `navierStokesResidual_eq_iff_projected`
  (`DifferentiableAt` + `spatialDivergence … = 0`) are inhabited by the zero velocity field.
- **NV6** (added after `REVIEW_SIMP.md` F5) the reviewer's **non-degenerate** witness
  `P(t,y) = y₀y₁` (`Rev113.NonVac`): `∇P(t,·) ≠ 0` (`P_grad_ne_zero`), so
  `hasSymmetricJacobian_pressureGradient`'s Clairaut content is genuinely exercised
  (`P_symm_jac`), and `P_gauge` is a non-degenerate instance of the m4 conclusion.
  NV1–NV5 use only identity / zero fields (∇ trivial); F5 flags them as inhabiting
  the class only at its degenerate point — correct but weak. NV6 is the strong witness.

`ClassicalSolutionR` (the hypothesis of `projected_of_classicalSolution` and
`pressure_potential_of_classicalSolution`) is **not** inhabited here: its
`sobolev`/`pressure_gradient` fields make a concrete instance an A02-level
construction, out of a SIMP lane's scope. NV4/NV5 inhabit the pointwise engines
those two theorems reduce to instead. This is a deliberate boundary, not a gap in
A01's math (see §3).

### (e) Gates
- `make check`: **green** — `check_contracts.py` OK, `test_contract_policy.py` 13/13,
  `check_work_queue.py` "30 work items … consistent".
- `cd verification && lake build Tests.RegularityPartial`: **green** —
  "Contract BlowupDensity.Tests.checkedRegularityPartial: checked; standard logical axioms only".

## 3. Gaps / things left alone
- No mathematical gap introduced or closed; this is a proof-simplification +
  test-hardening pass. The two rewritten items are `private` helpers, so no
  downstream consumer (`Bindings/RegularityPartial.lean`, `Section4/D01/*`) sees
  any change.
- Non-vacuity of `ClassicalSolutionR` is left to A02 (see §2d) — an existing
  structural obligation, unrelated to this lane.
- The pre-existing `pressurePotential` `rfl`-bridge debt flagged in
  `REVIEW_M4.md` finding 6 (`verification/Bindings`) is unchanged and out of this
  lane's scope (no `verification/` file edited).

## 4. MAINT list — general facts living in A01 that a later MAINT lane could promote
(Following lane 109's pattern: move Source/Paper3-level facts out of `Section4/*`,
leave an `alias` in place. I did **not** move any of these — statements are frozen
and this is a SIMP lane. Line numbers are post-edit.)

| fact | file:line | why it is not A01-specific | suggested home |
|---|---|---|---|
| `pressureGradient_fderiv_slice` | `PressureGauge.lean:62` | Riesz identity `fderiv (p(t,·)) x v = ⟪pressureGradient p t x, v⟫` — a general fact about the upstream `NavierStokes.ProblemStatement.pressureGradient`, no A01 content. | a Source-level "`pressureGradient` calculus facts" module (near `Source/…`), aliased in `PressureGauge`. |
| `pressureGradient_apply` | `PressureGauge.lean:84` | `pressureGradient p t x j = fderiv (p(t,·)) x eⱼ` — component read-off of the same upstream def. **F6 (REVIEW_SIMP.md): now duplicated verbatim** by PR #114 lane 111 — `NSFormalization.Section4.D01.pressureGradient_apply` (`D01/MomentumSlice.lean:127`) is the same statement up to bound-variable names (two different proofs: A01 routes through `pressureGradient_fderiv_slice` in 4 lines, D01 unfolds the sum in 6). No ambiguity today (neither module imports the other; the sole consumer `Bindings/RegularityPartial.lean` opens neither namespace), but a later module opening both hits the 109 `Ambiguous term` trap. | Reviewer's recommendation: one shared Source-level "`pressureGradient` calculus" module holding both `pressureGradient_fderiv_slice` and `pressureGradient_apply`, with both sites aliasing. If one existing copy must be picked, **keep A01's** (elder/merged first, a 4-line corollary of `pressureGradient_fderiv_slice` which must live somewhere anyway, and `D01.MomentumSlice`'s import closure is far heavier — measure before aliasing the other way, lesson 087). |
| `contDiff_gradSlice` | `PressureGauge.lean:117` | smoothness of the spatial-gradient slice of any `ContDiffOn ℝ ∞` scalar; general (depends only on `D01.contDiff_slice_scalar`). | a Source/Paper3-level smoothness module. |
| `inner_fderiv_symm` | `RadialPotential.lean:110` | pure inner-product-calculus: a symmetric Jacobian gives a symmetric bilinear form `⟪DG(z)v,w⟫`; zero NS content. | a shared calculus/inner-product lemma module (Source-level). |
| duplicated `expand` / `basis_inner` / `basisL` / `hcoord` local `have`s | `RadialPotential.lean:114,117`; `PressureGauge.lean:64,66`; `RadialPotential.lean:238` | the `EuclideanSpace (Fin 3)` basis decomposition `u = ∑ uᵢ•eᵢ` and `⟪u,eⱼ⟫ = uⱼ` recur verbatim; candidates for one shared helper (or a Mathlib orthonormal-basis lemma). | a shared `coordinateVector` lemma module; consolidate then reuse. |

## Commands run (key results)

### Round 1 (simplifier + initial tester)
- `lake build` 4 A01 modules — success (9881 jobs); incremental PressureGauge 2.0s.
- `lake env lean` ×4 modules — silent, exit 0.
- `lake env lean` `axioms_{a01,p1,m4}.lean` — 15 decls, only the 3 standard axioms, exit 0.
- `make check` — green (contracts, 13 policy tests, work-queue).
- `lake build Tests.RegularityPartial` — "checked; standard logical axioms only".

### Round 2 (revision after `REVIEW_SIMP.md`, ACCEPT-WITH-NOTES)
- `lake env lean ../research/A01/negative_simp.lean` (load-bearing checks) →
  `exit=0 lines=0` (silent — `hdiv`/`hG` counterexamples, `hsym`-redundancy derivation, fidelity).
- `lake env lean ../research/A01/negative_simp_fail.lean` (signature checks) →
  `exit=1`, errors at exactly:
  `51:2, 58:2, 67:2, 77:2, 92:20, 99:30, 106:48, 123:40, 129:21, 142:2, 142:40, 148:35`
  (N1–N11; N10 emits two, as flagged).
- `lake env lean ../research/A01/nonvacuity_simp.lean` (now incl. NV6 `P=y₀y₁`) → `exit=0 lines=0` (silent).
- `lake env lean ../research/A01/axioms_{a01,p1,m4}.lean` → exit 0 each; 5+3+7 decls,
  no `sorryAx`/`ofReduceBool`/`native_decide` (only the 3 standard axioms).
- `make check` → `exit=0` (13 policy tests OK; "30 work items … consistent").
- The four A01 modules are unchanged in round 2 (only the `research/A01/*` test files changed),
  so `Tests.RegularityPartial` and module silence from round 1 still hold.
