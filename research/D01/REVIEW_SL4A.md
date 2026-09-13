# Review — lane 074 (D01 · P2 sub-lemma SL4α, `div ∂ₜu = 0`)

Reviewer: opus (lane-review). Date 2026-09-13.
Worktree `.claude/worktrees/074-D01-p2-sl4a-div`, branch `erenup/074-D01-p2-sl4a-div`
(base: integration at `1b6418b`, i.e. **before** PR #73/lane 066 landed — see finding 1).

Files reviewed: `formalization/NSFormalization/Section4/D01/DivergenceTime.lean`,
`research/D01/ATTEMPTS_SL4A.md`, `research/D01/axioms_sl4a.lean`.

## Verdict

**ACCEPT-WITH-NOTES.**

The Lean is correct, complete and honest. The theorem is the right statement, stated on the
vendor operators and the canonical A02 solution class, with the correct (and necessary) `Ioo`
time hypothesis. All four gate checks pass. Every note below is documentation accuracy; none
of them touches the proof, and none needs a code change before merge.

---

## 1. Gate checks — all pass

| check | result |
|---|---|
| `lake build NSFormalization.Section4.D01.DivergenceTime` | `Build completed successfully (8815 jobs).` |
| `lake env lean ../formalization/.../DivergenceTime.lean` | **no output**, exit 0 — zero warnings from the module's own lines |
| `lake env lean ../research/D01/axioms_sl4a.lean` | all 4 declarations `[propext, Classical.choice, Quot.sound]` |
| `grep -nE 'sorry\|admit\|axiom\|native_decide\|maxHeartbeats'` | one hit, line 46, **inside the module docstring prose** ("No `sorry`, no `axiom`"); no code hit |
| `make check` | `test_contract_policy` 13 tests OK; `check_work_queue` 30 items consistent; architecture OK |

Axiom audit verbatim:

```
'…DivergenceTime.spatialDivergence_temporalDerivative_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'…DivergenceTime.spatial_fderiv_hasDerivAt'                    depends on axioms: [propext, Classical.choice, Quot.sound]
'…DivergenceTime.fderiv_spatial_slice'                         depends on axioms: [propext, Classical.choice, Quot.sound]
'…DivergenceTime.deriv_time_slice'                             depends on axioms: [propext, Classical.choice, Quot.sound]
```

CI coverage: the module is a leaf (nothing imports it, it is not in the registered contract
closure, so `make test` will not reach it), **but** `.github/workflows/contracts.yml` runs
`experiments/build_changed_lean.py --base-ref $BASE_SHA`, which selects with
`git diff --name-only --diff-filter=ACMRT` — `A` covers newly added files, so CI will compile
it. No coverage gap.

## 2. Statement fidelity — correct

Elaborated statement (`set_option pp.fullNames true`, `#check`):

```
∀ {ν : ℝ} {a : …A02.SpatialField} {f : …A02.SpaceTimeField} {T : ℝ}
  (u : …A02.ClassicalSolutionR ν a f T) {t : ℝ}, t ∈ Set.Ioo 0 T →
  ∀ (x : NavierStokes.ProblemStatement.Space),
    NavierStokes.ProblemStatement.spatialDivergence
      (fun p => NavierStokes.ProblemStatement.temporalDerivative u.velocity p.1 p.2) t x = 0
```

* **Vendor operators, not a local mirror.** `spatialDivergence` and `temporalDerivative` resolve
  to `NavierStokes.ProblemStatement.*` (`vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:55,67`),
  where `spatialDivergence u t x = ∑ i, (spatialDerivative u t x (coordinateVector i)) i` and
  `spatialDerivative u t x = fderiv ℝ (fun y => u (t,y)) x`. That is the genuine Euclidean
  divergence; there is no way for a "wrong implementation" to satisfy it by construction.
* **The argument really is `∂ₜu`.** `fun p : SpaceTime => temporalDerivative u.velocity p.1 p.2`
  evaluates at `(s,y)` to `∂ₜu(s,y)`; `spatialDivergence … t x` then differentiates in `y` at
  fixed `t`. So the conclusion is literally `div_x (∂ₜu)(t,x) = 0`. The worker's note that the
  curried `fun s x => …` does **not** type-check against `VelocityField` (because
  `Space = EuclideanSpace ℝ (Fin 3)` is itself a Pi type) is correct.
* **Solution class is the canonical one.** `ClassicalSolutionR` is `Section4.A02.SolutionClass`
  (the single canonical A02 restatement), not a re-declared copy. Hypotheses actually consumed:
  `velocity_smooth : ContDiffOn ℝ ∞ velocity (Ico 0 T ×ˢ univ)` and
  `divergence : ∀ t ∈ Ico 0 T, ∀ x, spatialDivergence velocity t x = 0`. Both are real fields;
  nothing else is used, so there is no hidden strengthening.
* **`Ioo` vs `Ico` is correct *and* necessary** — this is the sharpest design point of the lane
  and the worker got it right. Both `Ico`-neighbourhood steps (`Ico 0 T ×ˢ univ ∈ 𝓝 (t,x)` and
  `Ico_mem_nhds_iff.mpr ht`) require `t` interior. At `t = 0` the statement is not merely
  unprovable, it can be **false**: `velocity : ℝ × Space → Space` is a total function with no
  constraint for `t < 0`, `temporalDerivative` is the two-sided `fderiv`, and the `divergence`
  field only constrains `t ≥ 0`; so a solution whose extension to `t < 0` is chosen adversarially
  can have a genuine two-sided `∂ₜu(0,·)` with nonzero divergence. Excluding `t = 0` is the only
  sound choice. The theorem does not claim it.
* The `divergence` field being over `Ico 0 T` (not `Ioo`, as the task brief said) is strictly
  stronger and is exactly what makes step 3 of the proof work; ATTEMPTS flags this correctly.
* Paper anchor: appendix A `\eqref{eq:Rhigh}` ("The pressure term vanishes by solenoidality") is
  the Leray-projection step P2 serves; `research/D01/P2_SPLIT.md:151` ("SL4 (task c1) — α") is the
  sub-lemma. Content matches.
* **Non-vacuity (pre-existing, not this lane's debt).** No inhabitant of `ClassicalSolutionR` is
  constructed anywhere in the tree (33 modules quantify over it; `A02/Restrict.lean:83`,
  `A02/Maximal.lean:101` only transport existing ones). Every D01/A02 theorem is conditional in
  the same way. Flagged for the record only.

## 3. Consistency / duplication — the copy is justified and faithful

* **Imports are clean**: `NSFormalization.Section4.A02.SolutionClass` + six `Mathlib.Analysis.Calculus.*`.
  Nothing else. No HeliCorgi `Formal.*`, no `Euler.*`, no `Citations/`, no
  `Paper1/BoundaryCorollary`. (`Contracts/*` import policy does not apply — this is a
  `formalization/` module, not a contract.)
* **No definition is restated.** The module declares *no* `def`/`abbrev`/`structure` — four
  theorems only. So there is zero `rfl`-bridge / drift surface. Good.
* **The three helpers are byte-identical to vendor**, verified by extracting each declaration and
  diffing the non-blank code lines:

  ```
  fderiv_spatial_slice      : D01  8 lines, vendor  8 lines -> BYTE-IDENTICAL
  deriv_time_slice          : D01  6 lines, vendor  6 lines -> BYTE-IDENTICAL
  spatial_fderiv_hasDerivAt : D01 39 lines, vendor 39 lines -> BYTE-IDENTICAL
  ```
  (vs `vendor/NavierStokesAndEuler/Euler/CurlTimeDerivative.lean:14,25,33`; only the docstrings
  were rewritten.)
* **The copy is justified by import-closure weight**, and by a wider margin than ATTEMPTS claims.
  `Euler.CurlTimeDerivative → Euler.MeanBoundaryOperator → Euler.MeanGradientTestSpace →
  {Euler.MeanCutoffCurlBound, Euler.MeanSolenoidalSpace} → Euler.EulerProof`, and
  `Euler.EulerProof` is a **20,755-line** monolith. Measured:

  | route | local modules | lines |
  |---|---|---|
  | import `Euler.CurlTimeDerivative` | +6 | +21,853 (20,755 of them `EulerProof`) |
  | copy 53 lines (chosen) | +0 | +53 |

  For three statements that mention nothing but `fderiv`/`deriv`/`ContDiffAt`, copying is the
  right call.
* The claim that `A05.SmoothJets.dirDeriv_comm` does not apply is **correct**: it is stated for
  `w : Space → F` (`SmoothJets.lean:111`), purely coordinate–coordinate, no time direction.

## 4. Honesty of ATTEMPTS — accurate except one now-stale paragraph

Cited declarations opened and confirmed:

| citation | status |
|---|---|
| `A04.TimeDerivative.timeDeriv_isSobolevDatum` "available" | **true** — `formalization/NSFormalization/Section4/A04/TimeDerivative.lean:182`. Namespace is `NSFormalization.Section4.A04` (module `A04.TimeDerivative`), not `…A04.TimeDerivative.…`. Concludes `IsSobolevDatum (m:ℝ) (fun x => deriv (fun r => w.velocity (r,x)) t) (deriv G t)` for `2 ≤ m`, `t ∈ Ioo 0 T`. Matches the ATTEMPTS description. |
| `Leray.complementSymbol_eq_zero_of_inner_eq_zero` "available" | **true** — `formalization/NSFormalization/Section4/D01/LeraySymbol.lean:133`, `(h : inner ℝ ξ v = 0) : complementSymbol ξ v = 0`. Exactly the "kills a transverse fibre" fact claimed. |
| vendor exchange lemma at `Euler/CurlTimeDerivative.lean:33` | **true** — line number exact, statement identical (see §3). |
| `A05.SmoothJets.dirDeriv_comm` "does not apply" | **true** (see §3). |
| `#print axioms` standard for all four decls | **true** (reproduced, §1). |

### Finding 1 (LOW — stale, update ATTEMPTS) — `research/D01/ATTEMPTS_SL4A.md`, §"Transverse statement … precise gap", the **Blocker** paragraph

It says `DerivativeDatum.lean` / `isSobolevDatum_partialDeriv` "is on the (unmerged) lane-066
worktree only and is *not present* on `erenup/integration`". That was true at this branch's base
(`1b6418b`) but is **no longer true**: lane 066 / PR #73 merged as `070d883`, and
`git cat-file -e origin/erenup/integration:formalization/NSFormalization/Section4/D01/DerivativeDatum.lean`
succeeds — `isSobolevDatum_partialDeriv` is at line **245** of that file. Not dishonesty, just
staleness. Two things the lead should fold into the rewrite:

* The merged signature is **not** the `P2_SPLIT.md:189` sketch. Actual:
  ```lean
  theorem isSobolevDatum_partialDeriv {Z : SmoothL2Field Space} (j : Fin 3) (m : ℕ)
      {A : RealVectorSobolev ((m : ℝ) + 1)} (hA : IsSobolevDatum ((m : ℝ) + 1) Z.field A) :
      IsSobolevDatum (m : ℝ) (partialDeriv j Z.field)
        (WithLp.toLp 2 fun i => angularDirectionalDerivativeReal ((m:ℝ)+1) (coordinateVector j) (A i))
  ```
* So the follow-up lane is not a pure "compose (ii)→(iii)": it additionally needs (a) a
  `SmoothL2Field` packaging of `∂ₜu(t,·)`, and (b) order bookkeeping `m+1 → m` (the datum drops
  one order), neither of which the current gap paragraph mentions. Worth naming these explicitly
  so the next lane is scoped honestly.

**Fix:** rewrite that paragraph (ATTEMPTS is a non-generated file, safe to edit). No code change.

### Finding 2 (LOW — wording) — `DivergenceTime.lean:44` module docstring, and the mirrored sentence in ATTEMPTS §"Reuse vs reproduction"

"…imports only the canonical A02 restatement, `NavierStokes.R3.ProblemStatement`, and Mathlib."
The module does **not** import `NavierStokes.R3.ProblemStatement`; its import list is
`NSFormalization.Section4.A02.SolutionClass` plus six Mathlib modules. The operators come from
`NavierStokes.ProblemStatement` (note: *not* the `R3.` namespace —
`vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:29`), pulled in transitively
through A02. **Fix:** say "imports only the canonical A02 restatement and Mathlib; the vendor
operators arrive transitively from `NavierStokes.ProblemStatement`." Cosmetic, non-blocking.

### Finding 3 (LOW — wording, but a real maintenance signal) — `DivergenceTime.lean:41-45` and ATTEMPTS §"Reuse vs reproduction"

Both say the helpers were reproduced "**verbatim in technique**". They are in fact **byte-identical
proof text** (§3). "Verbatim in technique" reads as "same idea, independently rewritten", which
would tell a future maintainer the wrong thing. **Fix:** state plainly that the three proofs are a
literal copy of `Euler/CurlTimeDerivative.lean:14,25,33`, so that if the vendor pin moves the copy
is a known re-sync point. Consider adding the closure numbers from §3 as the justification.

### Finding 4 (INFO — planning doc drift) — `research/D01/P2_SPLIT.md:151-158`

The SL4 row plans `div_temporalDerivative_eq_zero` with a sketch statement
`(∑ i, spatialDerivative (fun y => temporalDerivative u.velocity t y) i x i) = 0`, which is not
well-typed (`spatialDerivative` takes a `VelocityField`, i.e. a pair argument). The delivered
`spatialDivergence_temporalDerivative_eq_zero` is the correct form and the better name. **Fix:**
when the lead updates P2_SPLIT, point the SL4α row at the real name/module and drop the "Blocker:
SL4α … unproved in tree" line — SL4α is now proved.

---

## Commands run (all from the lane worktree)

```
bash scripts/lean-install.sh                      # idempotent, ended "== OK"
. scripts/lean-env.sh ; export LEAN_NUM_THREADS=6

cd verification && lake build NSFormalization.Section4.D01.DivergenceTime
  -> Build completed successfully (8815 jobs).
     (warnings emitted are pre-existing ones from NSFormalization.Paper3.*, not this module)

cd verification && lake env lean ../formalization/NSFormalization/Section4/D01/DivergenceTime.lean
  -> (no output), exit 0

cd verification && lake env lean ../research/D01/axioms_sl4a.lean
  -> 4 declarations, each [propext, Classical.choice, Quot.sound]

cd verification && lake env lean /tmp/sl4a_probe.lean      # pp.fullNames #check, §2
  -> vendor NavierStokes.ProblemStatement.{spatialDivergence,temporalDerivative}, A02.ClassicalSolutionR

grep -nE 'sorry|admit|axiom|native_decide|maxHeartbeats' formalization/.../DivergenceTime.lean
  -> 46: docstring prose only

make check
  -> check_formalization_plan / check_contracts / test_contract_policy (13 OK) / check_work_queue (30 items) all pass

git cat-file -e origin/erenup/integration:formalization/NSFormalization/Section4/D01/DerivativeDatum.lean
  -> present (lane 066 / PR #73 / 070d883); isSobolevDatum_partialDeriv at :245
```

Plus two read-only measurements scripted in-session: per-declaration byte-diff of the three
helpers against the vendor module (§3), and transitive local-import closure sizes for the
`Euler.CurlTimeDerivative` route vs the copy (§3).
