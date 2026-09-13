# Review — lane 106, A01 unit m4 (`Section4/A01/PressureGauge.lean`)

Reviewer: opus, light-but-strict, ran the Lean.  Commit under review `c6b4bc3`
(`erenup/106-A01-m4-gauge`, four files: the module, `research/A01/ATTEMPTS_M4.md`,
`research/A01/axioms_m4.lean`, one line of `research/A01/A01_SPLIT.md`).

## Verdict: **ACCEPT-WITH-NOTES**

All four checks pass.  The theorem is token-identical to the spec field, the
gauge direction is the field's, the gauge constant is genuinely a function of
time alone, the Hessian-symmetry step is taken on the *spatial slice* (so the
`t = 0` endpoint is not touched by any time derivative), and the result is
non-trivial — I refuted the "zero potential" implementation in Lean.  The eight
findings below are notes and scheduling items, none of them blocking.

---

## 1. Compiles / hygiene — PASS

| command (from the worktree; `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`) | result |
|---|---|
| `bash scripts/lean-install.sh` | exit 0, ends `== OK` (all registered contracts replayed, "standard logical axioms only") |
| `cd verification && lake build NSFormalization.Section4.A01.PressureGauge` | final line **`Build completed successfully (9879 jobs).`**, exit 0 |
| `cd verification && lake env lean ../formalization/NSFormalization/Section4/A01/PressureGauge.lean` | **0 bytes of output**, exit 0 — no error, no warning, no linter hit |
| `cd verification && lake env lean ../research/A01/axioms_m4.lean` | **7 declarations, each exactly `[propext, Classical.choice, Quot.sound]`**; the conformance `example` at `:21-25` elaborated silently (no error printed), i.e. `pressure_potential_of_classicalSolution` inhabits the spec field's type |
| `grep -nE 'sorry\|admit\|axiom\|native_decide\|maxHeartbeats' PressureGauge.lean axioms_m4.lean` | module: **no hit**; audit file: 7 hits, all the literal `#print axioms` lines |
| `make check` | **exit 0** (`check_formalization_plan --check`, `check_contracts`, `test_contract_policy` 13 tests OK, `check_work_queue` "30 work items … consistent") |

The seven audited declarations are `pressureGradient_fderiv_slice`,
`fderiv_eq_of_pressureGradient_eq`, `pressureGradient_apply`,
`contDiff_gradSlice`, `hasSymmetricJacobian_pressureGradient`,
`pressure_potential_of_pointwise`, `pressure_potential_of_classicalSolution`.
The two `private` helpers (`:96`, `:115`) are not separately audited but are in
the closure of the five public theorems that are.

## 2. Statement fidelity — PASS

**(a) Token-for-token.**  `research/A01/Spec.lean:227-229` reads

```
  pressure_potential : PressureGaugeEquivOn (Ico (0 : ℝ) T)
    (pressurePotential (fun z : SpaceTime => pressureGradient u.pressure z.1 z.2))
    u.pressure
```

and `PressureGauge.lean:212-213` reads

```
    PressureGaugeEquivOn (Ico (0 : ℝ) T)
      (pressurePotential (fun z : SpaceTime => pressureGradient u.pressure z.1 z.2)) u.pressure
```

— identical token stream (the spec's `u` is the `structure` parameter
`u : ClassicalSolutionR ν a f T`, the theorem's `u` the hypothesis of the same
type; `u.pressure` is spelled the same in both).  Line breaks differ, nothing else.

**Direction is the field's, not the reverse.**  `Section4/A02/SolutionClass.lean:108-109`
(verbatim `Contracts/V1/Data.lean:589`, and already `rfl`-bridged at
`verification/Bindings/Uniqueness.lean:54-55`):

```
def PressureGaugeEquivOn (I : Set ℝ) (p q : SpaceTimeScalar) : Prop :=
  ∃ c : ℝ → ℝ, ∀ t ∈ I, ∀ x : Space, q (t, x) = p (t, x) + c t
```

With `p := pressurePotential (∇p)` and `q := u.pressure`, the field asserts
`u.pressure (t,x) = potential (t,x) + c t`.  That is exactly what the proof
closes: at `:200-204` `hconst` gives `p (t,y) - Q (t,y) = p (t,0) - Q (t,0)` and
`linarith` turns it into the goal `p (t,x) = Q (t,x) + (p (t,0) - Q (t,0))`, i.e.
**pressure = potential + c**, the field's orientation.  Not reversed.

**(b) The gauge constant is a function of `t` only.**  `:186`
`refine ⟨fun t => p (t, 0) - Q (t, 0), ?_⟩` — the witness is produced *before*
`intro t ht x` (`:187`), so `x` is not in scope when `c` is built and cannot
occur in it.  Read literally: `c t = p(t,0) − Q(t,0)`, the pressure's value at
the spatial origin minus the potential's (which is in fact `0`, since the radial
integrand carries a factor `x`).  This is `02-preliminaries.tex:31`, "the scalar
pressure is determined up to a function of time".

**(c) The `C²` input for Clairaut is on the SLICE in `x`, and `t = 0` is fine.**
`hasSymmetricJacobian_pressureGradient` (`:142-167`) builds
`hslice : ContDiff ℝ ∞ (fun z : Space => p (t, z))` from
`NSFormalization.Section4.D01.contDiff_slice_scalar` (`D01/DatumToJets.lean:377`)
and then uses `(hslice.contDiffAt (x := x)).isSymmSndFDerivAt (n := ∞) (by simp)`
— `ContDiffAt` of the **`x`-slice on all of `Space`**, not of the space-time map
`p : ℝ × Space → ℝ` on the half-open slab.  So the second derivative that is
symmetrised is the spatial Hessian `∂_i∂_j p(t,·)`; no time direction is
differentiated and nothing one-sided is involved.  `contDiff_slice_scalar` gets
the slice at `t = 0` from `ContDiffOn ℝ ∞ p (Ico 0 T ×ˢ univ)` by
`ContDiffOn.comp` with `y ↦ (t,y)` and `MapsTo univ (Ico 0 T ×ˢ univ)` followed
by `contDiffOn_univ` — legitimate at the closed endpoint, and lane 101's reviewer
had already flagged that no `UniqueDiffOn` argument is needed.  This is the right
contrast with the D01 precedent: `D01/DivergenceTime.lean:115` calls
`isSymmSndFDerivAt` on the *full* `u : SpaceTime → Space` and is therefore
restricted to `Ioo 0 T`; m4, needing only spatial symmetry, stays on `Ico 0 T`.
`hp` is used only through `pressure_smooth`; the derivation is otherwise
independent of `t`'s position in `Ico 0 T`.

Departure from the manuscript's *route*, not its *statement*:
`02-preliminaries.tex:92-93` gets `∂_jG_k = ∂_kG_j` from `Ĝ ∥ ξ` (Fourier);
Lean gets it from Clairaut on the smooth `p`.  Both establish the same
hypothesis of the same potential identity; the Fourier content of eq:Rpressure
lives in the *other* field, `pressure_recovery` (see Finding 6).

**(d) Could a wrong implementation satisfy it?  No — checked in Lean.**
I wrote `/tmp/rev106/t3.lean` (compiles clean, only deprecation warnings from my
own `simp` lemma choices) with `pw : PressureField := fun z => ⟪e₀, z.2⟫`, i.e.
`p(t,x) = x₀`:

* `pw_hyps` — the three hypotheses of `pressure_potential_of_pointwise` hold for
  `pw` (its gradient is the constant field `e₀`), so the lemma is instantiable at
  a pressure that is **not** constant in `x`;
* `pw_thm` — the lane's theorem applied to `pw`;
* `pot_pw` — for this `pw` the radial potential evaluates to `⟪e₀, x⟫ = x₀`,
  i.e. the potential is **not** the zero function and actually reconstructs the
  pressure;
* `zero_potential_fails` — `¬ PressureGaugeEquivOn (Ico 0 1) (fun _ => 0) pw`:
  taking `x = 0` and `x = e₀` gives `c t = 0` and `c t = 1`.

So the answer to the prompt's question is: **no**.  A "zero potential"
implementation would force every pressure to be `x`-independent and the field
would be *false*, not vacuously true.  Correspondingly the proof cannot avoid
lane 101's analysis: `hasFDerivAt_radialPotential` is used twice and essentially
— once directly at `:194` to get `Differentiable ℝ (Q(t,·))` (the potential is an
integral; nothing else in scope knows it is differentiable), and once through
`pressureGradient_pressurePotential` at `:190`, which is the only source of
`∇Q = ∇p` and is itself proved from `hasFDerivAt_radialPotential`.  Delete either
and `is_const_of_fderiv_eq_zero` has nothing to act on.

## 3. Consistency — PASS

* **Imports canonical and all used.**  `A01.RadialPotential` (the two A01
  definitions + `hasFDerivAt_radialPotential` + `pressureGradient_pressurePotential`),
  `A02.SolutionClass` (`PressureGaugeEquivOn`, `ClassicalSolutionR`),
  `D01.DatumToJets` (`contDiff_slice_scalar`), `Mathlib…FDeriv.Symmetric`
  (`ContDiffAt.isSymmSndFDerivAt`), `Mathlib…MeanValue`
  (`is_const_of_fderiv_eq_zero`).  Five imports, five uses.
* **No restated definitions.**  The module declares zero `def`/`abbrev`/`structure`
  — only theorems.  `pressurePotential` and `HasSymmetricJacobian` are imported
  from `RadialPotential` via `open`, exactly as the brief requires.
  `grep -rn --include='*.lean' 'pressurePotential\|HasSymmetricJacobian'` over
  `formalization/NSFormalization`, `verification/{Contracts,Bindings,Tests}`
  returns, besides the two A01 modules, only `Contracts/V1/Data.lean:596` and a
  docstring mention in `Contracts/V1/InsertionFamily.lean:182`.  Still one copy.
* **No namespace clash among the four A01 modules.**  `ConvectionDivergence` and
  `ProjectedEquation` sit in `NSFormalization.Section4.A01`; `RadialPotential`
  and `PressureGauge` each in their own sub-namespace.  No declaration name is
  shared (`pressureGradient_apply` exists only here; `RadialPotential` has
  `pressureGradient_pressurePotential`, a different name).  `PressureGauge`
  `open`s `RadialPotential`, which exports the `SpatialField`/`SpaceTimeField`/
  `SpaceTimeScalar` abbrevs into the file's scope; harmless here because the
  module spells `PressureField`/`Space`/`SpaceTime`/`VelocityField` directly.
* **Private helpers vs Mathlib — see Findings 1 and 2.**  Both are re-derivable
  from existing Mathlib API; neither is wrong.

## 4. Honesty of `ATTEMPTS_M4.md` — PASS (with one unverifiable citation)

I opened the three cited declarations (`D01.contDiff_slice_scalar`
`DatumToJets.lean:377`; `ContDiffAt.isSymmSndFDerivAt`
`Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean:530`; the `isSymmSndFDerivAt`
precedent `D01/DivergenceTime.lean:115`) and reproduced both recorded failures.

**Failure 1 — the `Function.comp` form mismatch — reproduced verbatim**
(`/tmp/rev106/t1.lean`):

```
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  fderiv ℝ (⇑((innerSL ℝ) (coordinateVector b)) ∘ G) x
in the target expression
  ((fderiv ℝ G x) v).ofLp b = (fderiv ℝ (fun y => ((innerSL ℝ) (coordinateVector b)) (G y)) x) v
```

Exactly the wording ATTEMPTS records, and exactly the reason the module states
`heq : H = ⇑L ∘ G` in composition form first (`:104`, `:118`).

**Failure 2 — the `.symm` orientation — confirmed, in two parts**
(`/tmp/rev106/t2.lean`):

* the two second-derivative spellings are **not** defeq:
  `fderiv ℝ (fun y => (fderiv ℝ f y) w) x v = (fderiv ℝ (fderiv ℝ f) x v) w` is
  rejected by `rfl` ("Type mismatch … `?m = ?m`"), so the `fderiv_fderiv_apply`
  reduction is genuinely load-bearing and the lane-101 scratch's missing `hcomp`
  was a real hole, not a cosmetic one;
* with the reduction in place, `(hsymm.eq (cv i) (cv j)).symm` is refused —
  `((D²f) (cv j)) (cv i) = ((D²f) (cv i)) (cv j)` against the goal
  `((D²f) (cv i)) (cv j) = ((D²f) (cv j)) (cv i)` — while the same term without
  `.symm` (the module's `:167`) is accepted.  ATTEMPTS's claim "no `.symm`" is
  correct.

I also re-read `/tmp/a01p1rev/gauge.lean` and confirm `pressure_potential_of_pointwise`
is the lane-101 reviewer's proof (see Finding 3 for the small overstatement of
"verbatim").  `/tmp/a01p1rev/slice.lean` no longer exists on this machine — see
Finding 4.

---

## Findings

| # | severity | location | finding / suggested fix |
|---|---|---|---|
| 1 | note | `PressureGauge.lean:115-122` `fderiv_fderiv_apply` | Mathlib's `fderiv_clm_apply` (`Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean:143`) already gives this: `rw [fderiv_clm_apply hf (differentiableAt_const w)]; simp` closes it in two lines (verified, `/tmp/rev106/t4.lean`).  Consider replacing the hand-rolled helper in a later simplifier pass.  **Not a blocker** — the current proof is correct and self-contained. |
| 2 | note | `PressureGauge.lean:96-110` `fderiv_apply_component` | Coordinate evaluation on `EuclideanSpace ℝ (Fin 3)` already exists as the CLM `EuclideanSpace.proj b`, with `(EuclideanSpace.proj b) u = u b` by `rfl` (verified).  Using it would remove the `innerSL`/`inner_single_left` detour (`hpt`).  Same simplifier pass.  **Not a blocker.** |
| 3 | note | `PressureGauge.lean:174-176` docstring | "verbatim except that `PressureGaugeEquivOn` is now A02's and `fderiv_eq_of_pressureGradient_eq` is the version above" understates two further (trivial) edits against `/tmp/a01p1rev/gauge.lean`: the added `rw [hQ]` in `hQd`, and `.differentiableAt` directly on `hasFDerivAt_radialPotential` instead of the scratch's `(this.congr_fderiv rfl).differentiableAt`.  Both improvements; the word "verbatim" is just slightly too strong. |
| 4 | note | `research/A01/ATTEMPTS_M4.md:40` | The second failed approach is cited to `/tmp/a01p1rev/slice.lean`, which is **no longer on disk** (`/tmp/a01p1rev/` now holds `bridge, c1, eta, gauge_ax, gauge, normcheck, probes`).  `REVIEW_P1.md:142,208` also cite it.  The *substance* is independently confirmed above (both halves of Failure 2 reproduced from scratch), and `REVIEW_P1.md:220-228` independently records that the lane-101 reviewer did not finish `HasSymmetricJacobian`, so the claim is credible — but the artifact itself is gone.  Lesson for `logs/LESSONS.md`: cite scratch evidence by quoting the failing message into `ATTEMPTS`, not by pointing at `/tmp`. |
| 5 | note | `research/A01/A01_SPLIT.md:124` (row m4) | "Retires D01 L9(b)" — L9(b) is the *pointwise* gradient identity, which `RadialPotential.lean:17-20` already claims for lane 101.  m4 retires the gauge wrapping, not L9(b) a second time.  Cosmetic bookkeeping. |
| 6 | **medium (pre-existing, scheduling)** | `RadialPotential.lean:67-75`; `verification/Bindings/` | `pressurePotential` is a **local restatement** of `Contracts/V1/Data.lean:596` with **no `rfl` bridge yet** — `RadialPotential.lean:71` says "the `verification/Bindings` `rfl` bridge is a later lane".  `PressureGaugeEquivOn` *is* bridged (`Bindings/Uniqueness.lean:54-55`), `HasSymmetricJacobian` is not yet a contract object.  CLAUDE.md's rule is one bridge per rewritten definition; lane 106 makes that debt load-bearing, because the only thing tying `pressure_potential_of_classicalSolution` to the eventual contract field is the (currently unproved-in-Lean) claim that the two `pressurePotential`s coincide.  It is a **one-line `theorem … := rfl`** in a Bindings module.  Not this lane's regression — but it should be part of whichever lane first registers an A01 contract, and I would not let A01 reach `Contracts/V1` without it. |
| 7 | note (fidelity context) | `Spec.lean:224-229` vs `02-preliminaries.tex:91-100` | `pressure_potential` on its own carries **no Navier–Stokes content**: the proof consumes only `u.pressure_smooth`, so the theorem is really "every `C²` scalar field equals the radial potential of its own gradient, up to a function of time".  That is the correct reading of the spec — the spec deliberately puts the eq:Rpressure content in `pressure_recovery` and says so (`Spec.lean:232-233`) — but it means m4 is a *gauge-normalisation* result, and A01's pressure prescription is not half-done until m2 lands.  Recorded so nobody later reads "pressure_potential done" as "the pressure is pinned down". |
| 8 | cosmetic | `PressureGauge.lean:210-211` | Binders are `{a : Space → Space} {f : VelocityField}` where the spec writes `(a : SpatialField) (f : SpaceTimeField)`.  Reducible abbrevs, defeq, and neither occurs in the conclusion — but the A02/D01 precedent (`SolutionClass.lean:33-38`) is that keeping the abbreviations is what makes restatements token-identical with `Data.lean`.  Harmless here. |

---

## What A01's `ManuscriptLocalRegularity` still lacks

`research/A01/Spec.lean:167-229` has **four** fields imposed on top of
`ClassicalSolutionR`, and after this lane **two of the four are theorems of
`ClassicalSolutionR` — they are no longer obligations at all**:

* **`projected`** (`Spec.lean:214`) — lane 093,
  `Section4/A01/ProjectedEquation.lean:40` `projected_of_classicalSolution`,
  from `velocity_smooth` + `divergence` + `momentum` through E1's
  `navierStokesResidual_eq_iff_projected`.
* **`pressure_potential`** (`Spec.lean:227`) — **this lane**,
  `Section4/A01/PressureGauge.lean:210` `pressure_potential_of_classicalSolution`,
  from `pressure_smooth` alone.

The two that remain are the two with real analytic content, and both are gaps:

* **`sobolev_smooth`** (`Spec.lean:180`, split row **m1**, size **L**) — for
  every `m`, an order-`m` Sobolev datum path that is `ContDiffOn ℝ ∞` on
  `Ico 0 T`.  This is the all-order *time* smoothness of
  `appendix-a-local-theory.tex:71-76`, and it sits behind unit **T1**, which in
  turn sits behind **A3** (order-independent `T₀`) and **A2/A2b** (the Grönwall
  bootstrap + continuation shared with A04).  It cannot be harvested from
  `ClassicalSolutionR` — `ClassicalSolutionR.sobolev` gives only `ContinuousOn`,
  which is strictly weaker.  Not a next-lane candidate.
* **`pressure_recovery`** (`Spec.lean:197`, split row **m2**, size **M**) —
  `IsLerayComplement (f − ∇·(u⊗u)) (∇p)` on **`Ico 0 T`** (endpoint included).
  Its two inputs are **P3** (the physical eq:Rpressure, imports HeliCorgi's
  `Formal/R3HelmholtzPressure.lean:259` `r3HelmholtzPressure_gradient`, which
  builds today) and **P2** (`IsLerayComplement` single-valued, which the split
  table marks as needing a Liouville theorem for `L²`-harmonic fields — a gap).
  On `Ioo 0 T` it is D01 unit L9(c) and is equivalent to `momentum`; the genuine
  increment is the `t = 0` endpoint.

Together with the `ClassicalSolutionR` side (rows c1–c9, where **c3/B1** — one
jointly space-time `C^∞` field out of the `H^m`-valued time paths — is the
single biggest blocker, and `c9 : pressure_gradient ∈ L²` rides on P3), A01's
remaining owned work is the 13 units of `A01_SPLIT.md:180-200`.

**Recommended next A01 lane.**  Two candidates, in this order:

1. **The `Bindings` bridge for `pressurePotential`** (Finding 6) — an S-sized
   lane, a single `theorem pressurePotential_eq : Contracts.V1.Data.pressurePotential = NSFormalization.Section4.A01.RadialPotential.pressurePotential := rfl`
   plus, while there, the `Bindings` wrapper turning
   `pressure_potential_of_classicalSolution` and `projected_of_classicalSolution`
   into contract-side statements.  It converts two finished theorems into
   contract-visible assets and clears the only policy debt m4 leaves behind.
   Cheap, unblocked, and it is the step that makes lanes 093/101/106 *count*.
2. **Unit P3 → row m2 `pressure_recovery`** (M) — the last
   `ManuscriptLocalRegularity` field within reach, and the one that gives
   `pressure_potential` its physical meaning (Finding 7).  Its HeliCorgi input
   `r3HelmholtzPressure_gradient` is importable today (`A01_SPLIT.md:74`), so the
   lane's real content is the carrier bridge from the complex `L²`/`𝓢'` statement
   to the pointwise `∇p`, plus the `t = 0` endpoint.  Split it: **P3 first**
   (physical eq:Rpressure, with the P2 Liouville gap isolated as its own row), and
   only then m2.  Do **not** open `sobolev_smooth` / B1 as an S-or-M lane; it is
   the L-cluster and needs its own plan.

---

## Commands run (worktree `.claude/worktrees/106-A01-m4-gauge`)

```
bash scripts/lean-install.sh                                          # exit 0, "== OK"
. scripts/lean-env.sh; export LEAN_NUM_THREADS=6
cd verification
lake build NSFormalization.Section4.A01.PressureGauge                 # Build completed successfully (9879 jobs).
lake env lean ../formalization/NSFormalization/Section4/A01/PressureGauge.lean   # 0 bytes
lake env lean ../research/A01/axioms_m4.lean                          # 7 × [propext, Classical.choice, Quot.sound]
lake env lean /tmp/rev106/t1.lean    # reproduces ATTEMPTS failure 1 (Function.comp pattern)
lake env lean /tmp/rev106/t2.lean    # reproduces ATTEMPTS failure 2 (non-defeq forms; .symm rejected)
lake env lean /tmp/rev106/t3.lean    # non-triviality: zero_potential_fails, compiles clean
lake env lean /tmp/rev106/t4.lean    # Mathlib alternatives for the two private helpers, compiles clean
cd .. ; make check                                                    # exit 0
grep -nE 'sorry|admit|axiom|native_decide|maxHeartbeats' formalization/NSFormalization/Section4/A01/PressureGauge.lean   # no hit
git show --stat c6b4bc3                                               # 4 files, +306/-1
```

No files were modified by this review except this one.
