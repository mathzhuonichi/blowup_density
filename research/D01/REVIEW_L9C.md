# Review — lane 055, task D01, unit L9(c) (the pressure package)

Reviewed commit `172f06c` on `erenup/055-D01-unit-l9c`.
Files under review: `formalization/NSFormalization/Section4/D01/Pressure.lean`
(317 lines), `research/D01/ATTEMPTS_L9C.md`, `research/D01/axioms_l9c.lean`.

## Verdict: **ACCEPT-WITH-NOTES**

Everything the module asserts in Lean is correct, axiom-clean and honestly
scoped.  The claimed counterexample is **genuine** — I reconstructed its
structural half in Lean, `sorry`-free — so a force hypothesis really is
mandatory, and the shape `MemForceR f + SmoothSquareIntegrableJets (∂ₜu(t,·))`
is the right one.  No correctness defect was found at any severity.

The one MEDIUM finding is bookkeeping, not mathematics: the obligation booked as
**L9(c)** (`RECONCILIATION.md:160`, `COMPARISON_A.md:108`) is eq:Rpressure
`∇p = (I−P)(f − ∇·(u⊗u))` *in `L²`*, and that is not proved here in any form.
The lane says so plainly in its own prose; the lane *record* must say so too.

---

## 1. The counterexample — assessed first, because it is the load-bearing claim

**Claim (`Pressure.lean:56-63`, `ATTEMPTS_L9C.md:75-84`).**  The unconditional
statement "`SmoothSquareIntegrableJets (∇p(t,·))` for every
`ClassicalSolutionR ν a f T`" is false: take a smooth divergence-free `u` with all
slices `H^∞`, a smooth scalar `p` with `∇p ∈ L² \ H¹`, and *define* `f` by the
momentum equation.

**Assessment: the counterexample holds.**

*Step 1 — is `f` unconstrained?*  Yes.  `ClassicalSolutionR`
(`A02/SolutionClass.lean:113-138`, verbatim `Contracts/V1/Data.lean:624-648`) has
exactly ten fields — `velocity`, `pressure`, `horizon_pos`, `velocity_smooth`,
`pressure_smooth`, `initial`, `divergence`, `momentum`, `sobolev`,
`pressure_gradient` — and the parameter `f` occurs in **one** of them,
`momentum`, and nowhere else.  `pressure_gradient` is
`∀ t ∈ Ico 0 T, MemLp (fun x => pressureGradient pressure t x) 2 volume`, i.e.
order **zero** only; `sobolev` is a datum path for `velocity` alone.  So
defining `f := navierStokesResidual ν u p` makes `momentum` hold by `rfl` and
costs nothing else.  Confirmed.

*Step 2 — formalized.*  I built the structure in Lean (reviewer scratch
`/tmp/l9c_cex.lean`, not committed).  With `u ≡ 0`, `p(t,x) := P(x)`, `a := 0`,
`T := 1`, every field discharges for an **arbitrary** smooth `P : ℝ³ → ℝ` whose
gradient is in `L²`:

```lean
def counterexample (ν : ℝ) (P : Space → ℝ) (hP : ContDiff ℝ ∞ P)
    (hL2 : MemLp (fun x : Space =>
      pressureGradient (fun z : SpaceTime => P z.2) 0 x) 2 volume) :
    A02.ClassicalSolutionR ν (fun _ => 0)
      (fun z : SpaceTime => NavierStokesR3.ProblemStatement.navierStokesResidual ν
        (fun _ : SpaceTime => (0 : Space)) (fun w : SpaceTime => P w.2) z.1 z.2) 1
```

`velocity_smooth := contDiff_const.contDiffOn`,
`pressure_smooth := (hP.comp contDiff_snd).contDiffOn`, `initial := fun _ => rfl`,
`divergence` by `simp [spatialDivergence, spatialDerivative]`,
`momentum := fun t _ x => rfl`, `sobolev` from
`D01.exists_isSobolevDatum_of_contDiff_memLp` applied to the zero field
(`iteratedFDeriv_fun_zero`, `MemLp.zero`) with a constant datum path, and
`pressure_gradient := hL2`.  Result:

```
'counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
```

and `(fun x => pressureGradient (counterexample …).pressure t x) = ∇P` by `rfl`
at every `t`.

*Step 3 — the analytic half.*  What remains is the standard fact that a smooth
`P : ℝ³ → ℝ` exists with `∇P ∈ L²` but `D²P ∉ L²` (equivalently `∇P ∈ L² \ H¹`,
which is what `SmoothSquareIntegrableJets (∇P)` fails at order `n = 1`).  It
does: with `ψ` a fixed bump supported in the unit ball and disjoint centres
`x_k = 4k e₁`,
`P(x) = Σ_k (k λ_k)⁻¹ ψ(x − x_k) sin(λ_k x₁)`, `λ_k = 2^k`, is smooth (one term
near any point), `‖∇P‖₂² ≍ Σ k⁻² < ∞`, `‖D²P‖₂² ≍ Σ (λ_k/k)² = ∞`.

**Consequence, as the brief anticipates.**  C01's U4/U7 must carry `MemForceR f`
— and the C01 spec already does: `research/C01/REVIEW_U1U3.md:40` records "**No
extra hypotheses**: the binders `0 < ν`, `a ∈ initialClassR`, `MemForceR f` are
all …".  So the lane's hypothesis shape is compatible with the consumer, and
`research/C01/REVIEW_U1U3.md`'s Finding 2 ("the paper's class *does* imply
`∇p ∈ H^∞`") is **not** in conflict with this lane: that finding is about the
class *together with* `MemForceR f`, which is exactly the lane's conditional
theorem.  No MEDIUM finding here.

---

## 2. Findings

### Finding 1 — MEDIUM (bookkeeping) — the booked obligation L9(c) is not discharged

*Where:* the lane record / merge note, not the Lean.

`RECONCILIATION.md:160` books L9(c) as "eq:Rpressure `∇p = (I−P)(f − ∇·(u⊗u))` ⟺
`momentum` given `divergence` and `∇p ∈ L²`"; `COMPARISON_A.md:108` states the
same at the `L²` level.  **No form of eq:Rpressure is proved in this module** —
not the `(I−P)` identity, not even its order-zero `L²` version.  What is proved
is (a) the momentum rearrangement `∇p = f − ∂ₜu − (u·∇)u + νΔu` (one `abel`),
(b) three genuinely new `H^∞`-slice lemmas, (c) four reusable jet-closure
lemmas, (d) a conditional theorem, (e) a correct negative result.  The module and
`ATTEMPTS_L9C.md:99-103` say this outright ("even the fallback … is blocked by
the same bridge").

*Fix:* record the lane as **L9(c)-partial**; leave L9(c) open in
`RECONCILIATION.md` and in the work queue, and open the follow-up unit named in
§4 below.  Do not let the merge note read "L9(c) closed".

### Finding 2 — LOW (advisory) — the main theorem's hypothesis is equivalent to its conclusion

*Declaration:* `pressureGradient_slice_smoothSquareIntegrableJets`
(`Pressure.lean:309-315`).

Given `MemForceR f` and the module's own proved pieces
(`forceSlice_smoothL2_of_memForceR`, `advection_slice_smoothL2`,
`laplacian_slice_smoothL2`) plus `pressureGradient_slice_eq` and the
`smoothL2_*` closure lemmas, `SmoothSquareIntegrableJets (∂ₜu(t,·))` and
`SmoothSquareIntegrableJets (∇p(t,·))` are **interderivable in one line each
way**.  So the theorem is a repackaging of the gap, not a reduction of it; its
net new content for C01 is exactly the three slice lemmas, which C01's
`ATTEMPTS_U1U3.md:147-151` already anticipated ("yet all-order `L²` is `∇p` — so
this clause = root gap + routine work").

The module docstring (`:71-73`) does say "the two are interderivable", so this is
**not** a dishonesty finding.  It is a request that the record be unambiguous.

*Fix:* state the converse as well and package them as an `Iff`
(`pressureGradient_slice_smoothL2_iff_temporalDerivative`), so that a reader of
the declaration list cannot mistake the theorem for progress on the gap.

### Finding 3 — LOW — the in-tree Leray inventory is overstated in the Lean docstring

*Where:* `Pressure.lean:75` "The only in-tree Leray construction is HeliCorgi's".

False as written.  `NSFormalization/Source/ForcedCylinderLocal.lean:26` defines

```lean
def leray (q : ℕ) : SobolevSpace period q →L[ℝ] SobolevSpace period q :=
  ContinuousLinearMap.id ℝ _ - sobolevGradientProjection period q 1 0
```

— "the genuine Leray projection at ordinary spatial scale", a **continuous linear
map on `H^q`**, i.e. precisely the "bounded on `H^m`" property the docstring
calls missing — and `Paper1/PeriodicLeray{CoeffCore,Divergence,WeightedNorm,…}`
carry the periodic Fourier Leray correction.  Both are **periodic / cylinder**
constructions and cannot serve the whole-space `ℝ³` angular target, so the gap
itself stands unchanged.  `ATTEMPTS_L9C.md:99-101` hedges correctly ("No `L²`
order-0 form of `(I−P)` on physical angular-convention fields"); the Lean
docstring does not.

*Fix:* narrow `:75` to "the only whole-space-`ℝ³` Leray construction in tree is
HeliCorgi's; the `Source.ForcedCylinderLocal` and `Paper1.PeriodicLeray*`
projections are periodic and do not transfer".

### Finding 4 — LOW — `contDiff_futureSlice` is re-proved instead of reused

*Declaration:* `forceSlice_smoothL2_of_memForceR` (`Pressure.lean:290-302`).

Lines 292-299 re-derive `ContDiff ℝ ∞ (fun x : Space => f (t, x))` from
`ContDiffOn ℝ ∞ f futureDomain` in eight lines.  `D01.contDiff_futureSlice`
(`ForceClass.lean:301-303`) is that exact statement, proved in one:
`hf.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun x => ⟨ht, mem_univ x⟩)`.
`Pressure.lean` does not import `D01.ForceClass` (checked: the name is not in
scope after `import NSFormalization.Section4.D01.Pressure`).

*Fix:* `import NSFormalization.Section4.D01.ForceClass` and replace 292-299 with
`have hcd := contDiff_futureSlice hf.1 ht`.  (`D01.MemForceR` there is defeq to
the `A02.MemForceR` used here — recorded at `A02/SolutionClass.lean:30-40` — so
nothing else changes.)

### Finding 5 — LOW — citation slips in `ATTEMPTS_L9C.md`

All four are in the research note only; the Lean docstring's own citations are
correct where they overlap.

1. `:112` — `r3LerayComplementL2` cited at `R3HelmholtzPressure.lean:224`; the
   `def` is at **228** (as `Pressure.lean:77` correctly says).
2. `:115` — `r3HelmholtzPressure` cited at `:218`; the `def` is at **223**.
   (`r3HelmholtzPressure_gradient` at `:259` is exact.)
3. `:67-69` — "`A03/SmoothJets.lean:40-43` and `A05` both note the class is not
   closed under these".  That passage is about **derivative** (`∂_j`) closure,
   not additive/scalar closure; it does not support the claim.  The claim itself
   is true — I grepped `formalization` and `verification` for
   `smoothL2_add|smoothL2_sub|smoothL2_neg|smoothL2_const_smul|SmoothL2.add|
   SmoothL2.sub|SmoothL2.neg|SmoothL2.const_smul|SmoothL2.smul` and the only
   hits are this lane's — so only the citation needs fixing.
4. `Pressure.lean:16` names the consumer "units U4/U7"; `research/C01/
   COMPARISON.md:219-220` says "U3/U7" (`ATTEMPTS_U1U3.md:61` does say "U4/U7",
   so both readings have support).  Cosmetic.

### Finding 6 — LOW — the main theorem mixes the two spellings of one class

*Declaration:* `pressureGradient_slice_smoothSquareIntegrableJets`.

The hypothesis is written `A05.SmoothL2 (fun x => temporalDerivative …)`, the
conclusion `SmoothSquareIntegrableJets (fun x => pressureGradient …)`.  They are
the same predicate, so this is only presentational — I checked that a consumer
holding the contract-shaped hypothesis can still apply the theorem directly
(reviewer scratch, typechecks with no transport).

*Fix:* spell the hypothesis `SmoothSquareIntegrableJets` too.

### Finding 7 — LOW — the gap statement is slightly compressed

`Pressure.lean:69-73` reduces the missing input to "`(I−P)` bounded on every
`H^m`".  Discharging it on the manuscript's physical angular fields also needs
(i) the `L²` Helmholtz/Leray **decomposition itself** in that convention
(`ATTEMPTS_L9C.md:99-101` does say this; the Lean docstring does not), (ii)
placing the pointwise-solenoidal `∂ₜu(t,·) ∈ L²` into the *closed* solenoidal
subspace — that is D01 unit **L3** (`RECONCILIATION.md`, L3 row), booked
separately and also open — and (iii) `div ∂ₜu = ∂ₜ div u` (routine from
`velocity_smooth`, but unproved in tree).  None of this weakens the "one root
gap" framing, which is about the *hypothesis* and is accurate; it matters for
scoping the follow-up unit.

*Fix:* name (i)–(iii) in the docstring's gap paragraph so the follow-up unit is
sized correctly.

### Finding 8 — LOW (merge gate) — the branch is 34 commits behind integration

`git rev-list --count HEAD..origin/erenup/integration` = **34**;
`origin/erenup/integration..HEAD` = 1.  Consequently

```
python3 experiments/check_contracts.py --base-ref origin/erenup/integration
AssertionError: Removed stable specification: verification/Contracts/V2/DatumLemmas.lean
```

fails purely from staleness — that file was added on integration after the branch
point and is absent from this worktree.  The lane touched no contract.  (I read
the V2 file: it is the L12 force-norm clause at real orders, no pressure content,
so no interaction with this unit.)

*Fix:* rebase onto `origin/erenup/integration`, then re-run `lake build
NSFormalization.Section4.D01.Pressure` and the full `scripts/gates.sh` before
merging.

---

## 3. What was checked and passed (no finding)

* **Signs of `pressureGradient_slice_eq`.**  `navierStokesResidual ν u p t x =
  ∂ₜu + (u·∇)u − ν•Δu + ∇p` (`vendor/NavierStokesAndEuler/NavierStokes/R3/
  ProblemStatement.lean:57-62`) and `momentum` sets it `= f (t, x)`
  (`Contracts/V1/Data.lean:640-641`, `A02/SolutionClass.lean:130-131`).
  Rearranged: `∇p = f − ∂ₜu − (u·∇)u + ν•Δu`.  Matches `Pressure.lean:160-162`
  exactly.  The module `open`s `NavierStokes.ProblemStatement`, so
  `temporalDerivative`/`advection`/`spatialLaplacian`/`pressureGradient` are the
  same declarations the residual is built from — checked, no convention drift.
* **The registered tame clause.**  `Bindings/TameProduct.lean:126-127` binds
  `TameProductAPI.smoothJets_advectionTame :=
  NSFormalization.Section4.A03.advectionTame`, which is what
  `advectionOf_smoothL2` (`Pressure.lean:247`) uses.  `A03.SmoothL2` and
  `A05.SmoothL2` are syntactically identical definitions
  (`A03/SmoothJets.lean:60`, `A05/SmoothJets.lean:44`), so the hypothesis passes
  without transport.  Confirmed the registered clause, not a private variant.
* **`laplacian_slice_smoothL2` / `advection_slice_smoothL2` use only the two
  permitted class fields.**  Both route through `velocity_slice_smoothL2`, which
  consumes `u.velocity_smooth` and `u.sobolev` (dropping the unused
  `ContinuousOn` conjunct) via `DatumToJets.smoothSquareIntegrableJets_slice`.
  Neither touches `divergence`, `momentum` or `pressure_gradient`.  Consistent
  with the counterexample, where both remain true.
* **`SmoothSquareIntegrableJets v ↔ A05.SmoothL2 v` really is `Iff.rfl`.**  Yes.
  `D01.SmoothSquareIntegrableJets` (`DatumToJets.lean:118`) and `A05.SmoothL2`
  (`A05/SmoothJets.lean:44`) are both
  `ContDiff ℝ ∞ v ∧ ∀ n, MemLp (iteratedFDeriv ℝ n v) 2 volume`.  I went one step
  further than the conformance file and checked it against the **registered
  contract**, not only the D01 restatement:
  `BlowupDensity.Contracts.V1.SmoothSquareIntegrableJets v ↔
  D01.SmoothSquareIntegrableJets v := Iff.rfl`,
  `… ↔ A05.SmoothL2 v := Iff.rfl`, and
  `BlowupDensity.Contracts.V1.Data.MemForceR f = A02.MemForceR f := rfl` all
  typecheck; and the whole main theorem retypes with the contract's own classes
  in both binder and conclusion, by `exact`, with no transport.  This is the
  strongest form of the claim the conformance file makes.
* **The new helpers are genuinely absent elsewhere.**  `smoothL2_add/sub/neg/
  const_smul`: no other hit in `formalization` or `verification` (grep in
  Finding 5.3).  `exists_isSobolevDatum_of_sobolevENorm_ne_top`: only the
  converse `sobolevENorm_ne_top_of_contDiff_memLp` (`SmoothDatum.lean:315`)
  exists; the `iInf_of_empty` idiom appears once more at
  `DatumToJets.lean:353` inside a different lemma.  `advectionOf_smoothL2`,
  `laplacian_slice_smoothL2` and `forceSlice_smoothL2_of_memForceR` have no
  counterpart in tree.  All five additions are real.
* **Honesty spot-check of the recorded `simp only … rfl` fix**
  (`ATTEMPTS_L9C.md:165-170`).  Reproduced both halves in a scratch file.  The
  accepted `simp only [spatialLaplacian, Fin.sum_univ_three]; rfl` closes the
  identity.  The rejected
  `simp only [spatialLaplacian, spatialDerivative, A05.dirDeriv, Fin.sum_univ_three]`
  leaves exactly the described residue — `fderiv ℝ (fun y => fderiv ℝ … (coordinateVector i)) x (coordinateVector i)`
  against `fderiv ℝ (A05.dirDeriv i …) x (coordinateVector i)`, i.e. the
  `dirDeriv` equation lemma not firing on the unapplied argument under `fderiv`.
  **The record is accurate.**
* **Module registration.**  No `Section4.*` module is imported by
  `formalization/NSFormalization.lean`; `experiments/build_changed_lean.py`
  compiles changed modules directly.  Project pattern, not a gap.

---

## 4. The honest remaining unit

Stated as I would book it, sharpening `ATTEMPTS_L9C.md:94-103` with Finding 7:

> **D01/L9(c)-remainder.**  On `Space → Space` in the manuscript's angular
> convention: (i) the `L²` Helmholtz decomposition `L² = L²_σ ⊕ G` with its
> projection `P`, (ii) `IsSolenoidal z ∧ MemLp z 2 → z ∈ L²_σ` (= unit **L3**),
> (iii) `(I−P)` bounded on `H^m` for every `m`.  Then eq:Rpressure
> `∇p(t,·) = (I−P)(f(t,·) − ∇·(u⊗u)(t,·))` at order 0 *and* its `H^∞` upgrade,
> and hence `pressureGradient_slice_smoothSquareIntegrableJets` unconditionally
> on `MemForceR f`.

The HeliCorgi inventory in `ATTEMPTS_L9C.md:107-145` is otherwise **accurate**:
`MNS2.r3LerayComplementL2` (`R3HelmholtzPressure.lean:228`) and
`MNS2.r3HelmholtzPressure_gradient` (`:259`) are what they are said to be
(`∇p = −(I−P)F` componentwise in `𝓢'`, edge 2a only — the upstream docstring
does flag "nothing here identifies `F` with the Navier–Stokes nonlinearity"), and
the four obstructions listed (cycles vs angular convention, distributional vs
classical derivative, complex `R3C` vs real `Space`, order 0 vs `H^m`) are all
real.  One imprecision: `Section4/HeliCorgiPort.lean` pins
`r3HelmholtzPressure` (`:37`) and `r3HelmholtzPressure_gradient` (`:40`) but
**not** `r3LerayComplementL2`; it is nevertheless in scope, since the port
imports `Formal.R3HelmholtzPressure` whole.

---

## 5. Commands and results

All from the worktree `.claude/worktrees/055-D01-unit-l9c`, after
`bash scripts/lean-install.sh` (→ `== OK`), `. scripts/lean-env.sh`,
`LEAN_NUM_THREADS=6`, no `-j`, lake invoked only from `verification/`, one at a
time.

| # | command | result |
|---|---|---|
| 1 | `bash scripts/lean-install.sh` | `== OK` |
| 2 | `cd verification && lake build NSFormalization.Section4.D01.Pressure` | **exit 0**, `Build completed successfully (9883 jobs)` |
| 3 | `grep -n -i "D01/Pressure" <build log>` | **no diagnostics from the file** (all warnings in the log are pre-existing, from `Paper3/*`, `Source/*`) |
| 4 | `cd verification && lake env lean ../formalization/NSFormalization/Section4/D01/Pressure.lean` | **exit 0, zero bytes of output** — fresh elaboration, no warnings.  (Linters are active in this mode: my scratch files run the same way did emit `unusedVariables` warnings.) |
| 5 | `cd verification && lake env lean ../research/D01/axioms_l9c.lean` | **exit 0**; all six — `pressureGradient_slice_eq`, `laplacian_slice_smoothL2`, `advection_slice_smoothL2`, `pressureGradient_slice_smoothL2_of`, `forceSlice_smoothL2_of_memForceR`, `pressureGradient_slice_smoothSquareIntegrableJets` — report exactly `[propext, Classical.choice, Quot.sound]`; the `SmoothSquareIntegrableJets ↔ A05.SmoothL2` `Iff.rfl` example typechecks |
| 6 | `grep -n -E "sorry\|admit\|native_decide\|axiom\|maxHeartbeats\|set_option" formalization/NSFormalization/Section4/D01/Pressure.lean` | **no matches** |
| 7 | same grep on `research/D01/axioms_l9c.lean` | only the six `#print axioms` lines and the word "axioms" in the docstring — nothing outside comments/`#print` |
| 8 | `make check` | **exit 0** (`check_formalization_plan`, `check_contracts`, `test_contract_policy` 13/13, `check_work_queue` 30 items) |
| 9 | `cd verification && lake test` | **exit 0**; all ten registered contracts "checked; standard logical axioms only" |
| 10 | `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` | **fails on staleness only** — `AssertionError: Removed stable specification: verification/Contracts/V2/DatumLemmas.lean`; see Finding 8 |

Reviewer scratch files (in `/tmp`, **not** committed, each run with
`cd verification && lake env lean …`):

| file | purpose | result |
|---|---|---|
| `/tmp/l9c_spot.lean` | the recorded Laplacian `simp/rfl` fix and its rejected predecessor | accepted tactic closes; rejected tactic fails with exactly the recorded residual goal |
| `/tmp/l9c_cex.lean` | the counterexample as a real `A02.ClassicalSolutionR` | **builds**, `depends on axioms: [propext, Classical.choice, Quot.sound]` |
| `/tmp/l9c_defeq.lean` | main theorem applied with a `D01.SmoothSquareIntegrableJets` hypothesis | typechecks |
| `/tmp/l9c_contracts.lean` | main theorem retyped against `BlowupDensity.Contracts.V1.SmoothSquareIntegrableJets` + `…Data.MemForceR`, plus both `Iff.rfl`s and the `MemForceR` `rfl` | all typecheck |

No code was changed by this review.
