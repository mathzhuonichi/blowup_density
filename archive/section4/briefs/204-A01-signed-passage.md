# Lane 204-A01-signed-passage — `CylinderSignedEnergyPassage`: the unabsorbed signed regularized energy inequality passes to the maximal-approximation limit with the dissipation retained

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/204-A01-signed-passage` (git branch `erenup/204-A01-signed-passage`, based on branch `erenup/203-A01-signed-limit`
= `origin/erenup/integration` + lane 203's `Section4/A01/SignedLimit.lean` (`def CylinderSignedEnergyPassage`, the proved maximal derivative-word square-integral
convergence, the signed quotient absorption, and `cylinderSignedRootLimit_of_forcingBound` conditional on the passage)). On integration: lanes 198 (`MildEnergyPremises`:
`energy_maximal_limit`, representatives, vendor premises), 199 (`MildEnergyEnvelope`: `regularized_full_energy_hasDerivAt` — the level-`n` signed identity retaining
the negative full gradient square), 200 (`ForcingFamilyBound`: `Z` identification at the limit), 201 (`RootComparison`). Read `CLAUDE.md`, `collaboration/HANDOFF.md` §0
and §2 P7, `research/A01/REPORT_203.md` (§3: the exact statement, verbatim below), `research/A01/ATTEMPTS_SIGNED_LIMIT.md` (what was tried), the reviews of 201 and 203
(`research/A01/REVIEW_201-A01-root-comparison.md` §3 route; `REVIEW_203-…md` when present), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
  Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example` on zero data (never as certification of the general premise).
- **Satisfiability rule:** if one genuinely missing analytic fact remains, isolate it as ONE named hypothesis with the exact statement.

## Target (lane 203, verbatim)
```lean
def CylinderSignedEnergyPassage {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n) : Prop :=
  ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S) (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))),
    (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS (coefficients 1 hq (sobolevPath F hF q)) (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t) →
    ∀ U : TimeLp T (SobolevSpace 1 (2+q)),
      Filter.Tendsto (fun n => pathLp T hT (maximalApproximation 1 q T n u)) Filter.atTop (𝓝 U) →
    ∀ ε : ℝ, 0 < ε →
      let r := extendPath T hT (energyRootPath u)
      let H := fun s => (r s * cylinderEnergyForcing hq hT hTS F hF u U s - ν * (energyGradientNorm U s)^2) / Real.sqrt ((r s)^2+ε^2)
      ∀ t ∈ Icc (0 : ℝ) T, IntervalIntegrable H volume 0 t ∧ Real.sqrt ((r t)^2+ε^2) ≤ Real.sqrt ((r 0)^2+ε^2) + ∫ s in (0 : ℝ)..t, H s
```
(If the branch's `def` carries `ha` via `let _solenoidal := ha`, prove it as stated; a re-cut to a real binder may be proposed in the report.)

## Route
1. Level `n`: for the regularized competitor `maximalApproximation 1 q T n u`, lane 199's `regularized_full_energy_hasDerivAt` gives `d/dt (½ r_n²) = −ν‖∇_words‖² + ⟨forcing_n⟩`;
   divide by `√(r_n²+ε²)` (the `ε`-regularized root: `d/dt √(r_n²+ε²) = r_n r_n'/√(r_n²+ε²)`), integrate on `[0,t]` (FTC for the `C¹` scalar path) — this is the level-`n` inequality
   in exactly the target's shape with `r_n`, `forcing_n`, `∇U_n`.
2. Pass `n → ∞`: `r_n → r` (lane 198's value-family convergence `regularizedValueFamily_tendsto` and the root path definition), the forcing term
   `regularizedWeightedForcing_tendsto` / `weightedMetricPath_tendsto` (lane 198/vendor), the dissipation `∫ ‖∇U_n‖² → ∫ energyGradientNorm U²` (lane 203's proved
   derivative-word square-integral convergence), and dominated convergence for the quotient (the denominator is `≥ ε`, so the integrands are dominated by
   `(|r_n forcing_n| + ν‖∇U_n‖²)/ε` with uniform-in-`n` `L¹` bounds from the strong `TimeLp` limit). Conclude `IntervalIntegrable H` and the limiting inequality.
3. If one convergence is genuinely unavailable (name the vendor lemma you needed and the error), isolate exactly that statement as the single named input.

## Deliverables
1. New module `formalization/NSFormalization/Section4/A01/SignedPassage.lean` (namespace `NSFormalization.Section4.A01`): the level-`n` inequality, the passage,
   `cylinderSignedEnergyPassage : CylinderSignedEnergyPassage …`, and the compositions `cylinderSignedRootLimit_of_forcingBound'`, `finiteMildEnergy_of_forcingBound''`.
2. Records `research/A01/ATTEMPTS_SIGNED_PASSAGE.md`, update `research/A01/A3_SPLIT.md` A3-M2 sub-row "envelope/limit", conformance `research/A01/axioms_signed_passage.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.SignedPassage` (silent), `lake env lean` on the module (0 output), the axioms file,
`make check` from the worktree root.

## Report
Commit on your branch; end with four parts. Also write it to `research/A01/REPORT_204.md`.
