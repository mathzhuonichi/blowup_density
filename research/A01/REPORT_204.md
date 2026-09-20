# REPORT 204 — signed energy passage with dissipation retained

## 1. What is proved

`CylinderSignedEnergyPassage` is proved exactly as imported from lane 203,
without an additional analytic hypothesis. The conclusion retains the full
negative `ν * (energyGradientNorm U s)^2`, the actual `cylinderEnergyForcing`,
the same arbitrary strong maximal limit U, every positive epsilon, and every
t in the closed interval, with integrability explicit.

```lean
theorem cylinderSignedEnergyPassage {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) :
    CylinderSignedEnergyPassage hq hν a ha F hF
```

The compositions remove lane 203's `hpass` premise:

```lean
theorem cylinderSignedRootLimit_of_forcingBound' {q : ℕ} (hq : 6 ≤ q)
    {ν S : ℝ} (hν : 0 < ν) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) {E A : ℝ}
    (hb : 0 ≤ E * ‖sobolevPath F hF (q+1)‖)
    (hFB : ForcingFamilyBound hq hν a F hF E A) :
    CylinderSignedRootLimit hq hν a ha F hF E A
```

```lean
theorem finiteMildEnergy_of_forcingBound'' {q : ℕ} (hq : 6 ≤ q)
    {ν S : ℝ} (hν : 0 < ν) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) {E A : ℝ}
    (hE : mildNormConstant q ≤ E)
    (hFB : ForcingFamilyBound hq hν a F hF E A) :
    FiniteMildEnergy hq hν a ha F hF E A
```

## 2. What is in Lean

* `formalization/NSFormalization/Section4/A01/SignedPassage.lean`: 27 new
  declarations, including the level-n inequality, exact transport/pressure
  cancellations, closed-interval FTC, root and forcing convergence, the full
  gradient-family identification, and the signed limiting assembly.
* `maximal_weighted_dissipation_limit` proves integrability and convergence of
  the epsilon-weighted full dissipation on every subinterval. It requires only
  strong maximal convergence, not the mild equation or solenoidality.
* The varying inverse-root weight passes by continuity of scalar multiplication
  on time L² and subinterval inner products. No common integrable pointwise
  dominator is asserted. The full derivative family is represented in `PiLp 2`;
  prepended and appended coordinates are identified by finite reindexing of
  the complete word sum, without a numerical loss.
* `research/A01/axioms_signed_passage.lean`: every module declaration and four
  zero-data helpers audited; all 31 outputs are exactly the three permitted
  axioms. Positive-horizon zero-data finite-energy non-vacuity, a nonzero
  dissipating scalar path, zero-horizon integrability, and a doubled-dissipation
  negative control compile.
* `research/A01/ATTEMPTS_SIGNED_PASSAGE.md`: successful/failed routes and
  resolved diagnostics. `research/A01/A3_SPLIT.md`: only the requested
  envelope/limit row updated. This report supplies the lane handoff.

No existing Lean module or verification file was edited. No heartbeat override
was needed. No prohibited proof mechanism is used.

## 3. Gaps and scope

**No remaining analytic input for the signed passage.** A provisional weighted
convergence input was eliminated by the completed proof. The inherited
`let _solenoidal := ha` definition is unchanged; the new theorem actually uses
ha to obtain divergence-freeness and finite-level cancellation, so no re-cut
is needed to prove the requested statement.

The finite-energy composition still needs `ForcingFamilyBound` and the
existing initial normalization `mildNormConstant q ≤ E`. The root-limit
composition explicitly retains `0 ≤ E * ‖sobolevPath F hF (q+1)‖`, as in lane
203. This lane does not prove a general forcing-family/commutator estimate,
does not remove those constant conditions, and does not claim all of A01 is
unconditional. No unresolved Lean error remains. REVIEW_203 is absent from
this checkout; the requested 201 review route and 203 report/attempts were read.

## 4. Validation and commit

Lean runs use the pinned v4.34.0-rc2 environment and run Lake from verification/
with `LEAN_NUM_THREADS=6`. Logs are gitignored `tmp/passage-*.log`.

```
lake build NSFormalization.Section4.A01.SignedPassage
lake env lean ../formalization/NSFormalization/Section4/A01/SignedPassage.lean
lake env lean ../research/A01/axioms_signed_passage.lean
make check                    # worktree root
lake test                     # verification/; the make-test target
make test-mutations           # worktree root; subprocess cwd is verification/
git diff --check
```

Build, direct Lean, the 31-declaration audit, make check, registered tests and
repository mutation controls pass. Direct module checking produces **0 bytes**.
The new module emits no warnings; the Lake build is not literally silent
because it replays inherited dependency warnings. The source mutation that
changes the finite-level dissipative coefficient from ν to 2ν is rejected for
the expected mathematical type mismatch; its nonzero scalar control passes.

All changes are confined to this worktree and committed on
`erenup/204-A01-signed-passage`. No push, merge, or rebase was performed.
