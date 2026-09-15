# REPORT 193 — base-order a-priori family

## 1. Theorems, exact statements, and named inputs

Delivered on the order-six local horizon, **conditional on one finite-order
energy estimate** `MildGronwall`. Base existence, uniqueness, lowering, cap
transfer, and the scalar Grönwall argument are proved. No all-order constructor
is used to obtain the bounds.

All signatures below are copied from the new module; proofs are omitted here.
The namespace is `NSFormalization.Section4.A01`, with the opens recorded in
`AprioriFamily.lean`. `S` is the chosen base horizon and `R₆` its vendor radius.
`E q` and `C q` are nonnegative norm-comparison/energy constants fixed before
competitors and subwindows; their admissibility is the `MildGronwall` input.
The exact residual predicate and explicit radius are:

```lean
def MildGronwall {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) (E C : ℝ) : Prop :=
  ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))),
    (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
      (coefficients 1 hq (sobolevPath F hF q))
      (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t) →
    ∃ y : C(Icc (0 : ℝ) T, ℝ),
      (∀ t, ‖u t‖ ≤ y t) ∧
      y ⟨0, le_rfl, hT⟩ ≤ E * ‖ordinarySobolev (q+1) a.toLp a.translation_contDiff‖ ∧
      ∀ t : Icc (0 : ℝ) T,
        y t ≤ y ⟨0, le_rfl, hT⟩ + ∫ s in (0 : ℝ)..t.val,
          (C * (256 * ‖restrictOperator 1 (Nat.succ_le_succ hq)
            (extendPath T hT u s)‖ ^ 2) * extendPath T hT y s +
            E * ‖sobolevPath F hF (q+1)‖)
```

```lean
def aprioriRadius {S : ℝ} (a : SmoothL2Field Space)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (R₆ : ℝ) (E C : ℕ → ℝ) (q : ℕ) : ℝ :=
  E q * (‖ordinarySobolev (q+1) a.toLp a.translation_contDiff‖ +
    S * ‖sobolevPath F hF (q+1)‖) * Real.exp (C q * (256 * R₆^2 * S))
```

The exact theorem signatures are:

```lean
theorem quadratic_mild_prefix {q : ℕ} {ν S T : ℝ} (hν : 0 < ν)
    (hT : 0 ≤ T) (hTS : T ≤ S)
    (C : Coefficients (Icc (0 : ℝ) S) (SobolevSpace 1 (q+1)) (SobolevSpace 1 q))
    (a : SobolevSpace 1 (q+1)) (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q+1)))
    (hu : ∀ t, u t = quadraticDuhamel 1 ν hν (hT.trans hTS) le_rfl C a u t) :
    ∀ t, (u.comp (timeInclusion hTS)) t = quadraticDuhamel 1 ν hν hT hTS C a
      (u.comp (timeInclusion hTS)) t
```

```lean
theorem quadratic_mild_unique_window {q : ℕ} {ν S T : ℝ} (hν : 0 < ν)
    (hT : 0 ≤ T) (hTS : T ≤ S)
    (C : Coefficients (Icc (0 : ℝ) S) (SobolevSpace 1 (q+1)) (SobolevSpace 1 q))
    (a : SobolevSpace 1 (q+1)) (u v : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (hu : ∀ t, u t = quadraticDuhamel 1 ν hν hT hTS C a u t)
    (hv : ∀ t, v t = quadraticDuhamel 1 ν hν hT hTS C a v t) : u = v
```

```lean
theorem base_identification {ν S T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hTS : T ≤ S)
    (a : SmoothL2Field Space) (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u₆ : C(Icc (0 : ℝ) S, SobolevSpace 1 7))
    (h₆ : ∀ t, u₆ t = quadraticDuhamel 1 ν hν (hT.trans hTS) le_rfl
      (coefficients 1 (le_refl 6) (sobolevPath F hF 6))
      (ordinarySobolev 7 a.toLp a.translation_contDiff) u₆ t)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 7))
    (hu : ∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
      (coefficients 1 (le_refl 6) (sobolevPath F hF 6))
      (ordinarySobolev 7 a.toLp a.translation_contDiff) u t) :
    u = u₆.comp (timeInclusion hTS)
```

```lean
theorem hasAprioriBound_base {ν S R₆ : ℝ} (hν : 0 < ν) (hS : 0 ≤ S)
    (a : SmoothL2Field Space) (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u₆ : C(Icc (0 : ℝ) S, SobolevSpace 1 7)) (hR : ‖u₆‖ ≤ R₆)
    (h₆ : ∀ t, u₆ t = quadraticDuhamel 1 ν hν hS le_rfl
      (coefficients 1 (le_refl 6) (sobolevPath F hF 6))
      (ordinarySobolev 7 a.toLp a.translation_contDiff) u₆ t) :
    HasAprioriBound (le_refl 6) hν a F hF R₆
```

```lean
theorem lower_identification {q : ℕ} (hq : 6 ≤ q) {ν S T : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T) (hTS : T ≤ S)
    (a : SmoothL2Field Space) (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u₆ : C(Icc (0 : ℝ) S, SobolevSpace 1 7))
    (h₆ : ∀ t, u₆ t = quadraticDuhamel 1 ν hν (hT.trans hTS) le_rfl
      (coefficients 1 (le_refl 6) (sobolevPath F hF 6))
      (ordinarySobolev 7 a.toLp a.translation_contDiff) u₆ t)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (hu : ∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
      (coefficients 1 hq (sobolevPath F hF q))
      (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t) :
    (restrictOperator 1 (Nat.succ_le_succ hq)).compLeftContinuous ℝ _ u =
      u₆.comp (timeInclusion hTS)
```

```lean
theorem exists_base_apriori {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space) (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) :
    ∃ (T : ℝ) (_hT : 0 < T) (hTS : T ≤ S),
      HasAprioriBound (le_refl 6) hν a (fun t => F (timeInclusion hTS t))
        (fun n => (hF n).comp (timeInclusion hTS).continuous)
        (‖ordinarySobolev 7 a.toLp a.translation_contDiff‖ + 1)
```

```lean
theorem h2_cap_transfer {q : ℕ} (hq : 6 ≤ q) {S T R₆ : ℝ}
    (hTS : T ≤ S) (u₆ : C(Icc (0 : ℝ) S, SobolevSpace 1 7)) (hR : ‖u₆‖ ≤ R₆)
    (hi : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 7 (0, θ) (u₆ t) = u₆ t)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (hl : (restrictOperator 1 (Nat.succ_le_succ hq)).compLeftContinuous ℝ _ u =
      u₆.comp (timeInclusion hTS))
    (U : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2))
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (v : A02.SpaceTimeField)
    (hslice : ∀ t : Icc (0 : ℝ) T, (fun x => v (↑t, x)) =ᵐ[volume] ⇑(U t))
    (hcont : ContinuousOn (fun s => sobolevNormAt 2 v s) (Ico (0 : ℝ) T)) :
    ∀ t ∈ Icc (0 : ℝ) T,
      (∫ s in (0 : ℝ)..t, sobolevNormAt 2 v s ^ 2) ≤ 256 * R₆ ^ 2 * T
```

```lean
theorem hb_of_base {ν S R₆ : ℝ} (hν : 0 < ν) (hS : 0 ≤ S)
    (a : SmoothL2Field Space) (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u₆ : C(Icc (0 : ℝ) S, SobolevSpace 1 7)) (hR : ‖u₆‖ ≤ R₆)
    (h₆ : ∀ t, u₆ t = quadraticDuhamel 1 ν hν hS le_rfl
      (coefficients 1 (le_refl 6) (sobolevPath F hF 6))
      (ordinarySobolev 7 a.toLp a.translation_contDiff) u₆ t)
    (E C : ℕ → ℝ) (hE : ∀ q, 0 ≤ E q) (hC : ∀ q, 0 ≤ C q)
    (hMG : ∀ q (hq : 6 ≤ q), MildGronwall hq hν a F hF (E q) (C q)) :
    ∀ q (hq : 6 ≤ q), HasAprioriBound hq hν a F hF (aprioriRadius a F hF R₆ E C q)
```

```lean
theorem hb_of_base_inv {ν S R₆ : ℝ} (hν : 0 < ν) (hS : 0 ≤ S)
    (a : SmoothL2Field Space) (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u₆ : C(Icc (0 : ℝ) S, SobolevSpace 1 7)) (hR : ‖u₆‖ ≤ R₆)
    (h₆ : ∀ t, u₆ t = quadraticDuhamel 1 ν hν hS le_rfl
      (coefficients 1 (le_refl 6) (sobolevPath F hF 6))
      (ordinarySobolev 7 a.toLp a.translation_contDiff) u₆ t)
    (E C : ℕ → ℝ) (hE : ∀ q, 0 ≤ E q) (hC : ∀ q, 0 ≤ C q)
    (hMG : ∀ q (hq : 6 ≤ q), MildGronwall hq hν a F hF (E q) (C q)) :
    ∀ q (hq : 6 ≤ q), HasAprioriBoundInv hq hν a F hF (aprioriRadius a F hF R₆ E C q)
```

The detailed satisfiability audit gives one sentence per substantive named
input in [ATTEMPTS_A3_M2_193.md](ATTEMPTS_A3_M2_193.md). In particular, the
residual is a standard finite-order energy envelope and does not require a
solution to be constant beyond its terminal time. The zero-data example
constructs the envelope for every order on `[0,1]` without assuming a bound.

## 2. Files

* `formalization/NSFormalization/Section4/A01/AprioriFamily.lean`: 11 declarations.
* `research/A01/axioms_a3_m2_193.lean`: all 11 declarations, three zero-data
  helper proofs, and a non-vacuous all-order application of `hb_of_base`.
* `research/A01/probe193_wiring.lean`: copies lane 192's full combined
  `constructorInputs_of_bounds` statement at `9ca0a45` as a theorem parameter and composes it with this
  family; it checks with zero output.
* `research/A01/ATTEMPTS_A3_M2_193.md`: vendor budgets, restart/continuation
  interfaces, negative routes, force-order correction, and input satisfiability.
* `research/A01/ATTEMPTS_A3_M2.md`: appended pointer, preserving lane 142 history.
* `research/A01/A3_SPLIT.md`: A3-M2 row updated to distinguish the proved
  classical estimate from the conditional mild family.
* `research/A01/REPORT_193.md`: this report.

The requested `axioms_a3_m2.lean` already audits lane 142. It is preserved
unchanged to respect the no-existing-Lean-module-edits rule; both that audit
and the new `axioms_a3_m2_193.lean` were checked.

## 3. Gaps and error text

The remaining analytic task is to prove `MildGronwall` for the nonzero
finite-order mild competitors, choosing `E` and `C`. Scalar Grönwall itself
is available and discharged. Existing classical energy results cannot be
applied to a finite-order continuous cylinder path. The diagnostic was:

```
error: Application type mismatch: The argument
  u
has type
  C(↑(Icc 0 1), ↥(SobolevSpace 1 7))
but is expected to have type
  NSFormalization.Section4.A02.ClassicalSolutionR ?m.16 ?m.17 ?m.18 ?m.19
in the application
  highOrder_bddAbove_of_kbnd hν✝ ha✝ hf✝ hf1✝ u
```

Lane 169 differentiates the datum path at `m ≤ q-1`, while the required
energy bound is at `m = q+1`; it does not alone close this gap. Using the
all-order constructor first would assume the bound family and is not done.

The radius uses `S * ‖sobolevPath F hF (q+1)‖`, a proved elementary time-integral
majorant within the assembly, rather than the sharper physical L¹ norm.
The force order `q+1` is intentional: the requested draft's `L¹H^q` does not
match the `H^{q+1}` energy identity without another estimate.

The vendor chooses `S₆ = ε/2` existentially from two positive-time Picard
budgets; it does not expose a closed formula in the input norms. The radius
is exactly `‖ordinarySobolev 7 a.toLp a.translation_contDiff‖+1`.

Lane 192's `CylinderWiring.lean` is present on its branch but not importable
in this checkout, so composition is a checked copied-interface probe only.
The requested review file is absent:

```
sed: can't read research/A01/REVIEW_192-A01-wiring-hsob.md: No such file or directory
```

No unresolved compiler errors remain in the delivered files. There are no
new proof placeholders or nonstandard axioms. Every printed declaration in
the new audit has exactly `[propext, Classical.choice, Quot.sound]`.

## 4. Commands and results

Every Lean shell sourced `. scripts/lean-env.sh`, and every Lake command ran
from `verification/` with `LEAN_NUM_THREADS=6`.

* `lake build NSFormalization.Section4.A01.AprioriFamily`: exit 0. Output
  captured in `tmp/build193.log`; inherited dependency warnings are replayed,
  but the new module has no warnings. This is not a claim of an entirely
  warning-free dependency build.
* `lake env lean ../formalization/NSFormalization/Section4/A01/AprioriFamily.lean`:
  exit 0, **zero output** (`tmp/module193.log`).
* `lake env lean ../research/A01/axioms_a3_m2_193.lean`: exit 0; 14 exact
  three-axiom reports, zero-data example checked (`tmp/axioms193.log`).
* `lake env lean ../research/A01/axioms_a3_m2.lean`: exit 0, original lane-142
  audit retained and passing (`tmp/axioms142.log`).
* `lake env lean ../research/A01/probe193_wiring.lean`: exit 0, **zero output**
  (`tmp/probe193.log`).
* `make check` from the worktree root: exit 0 (`tmp/check193.log`).
* `lake test` from `verification/` (the `make test` target's underlying
  operation, with the required working directory): exit 0 (`tmp/test193.log`).
* `make test-mutations`: exit 0; implementation refactor accepted and the
  three invalid mutations rejected (`tmp/mutations193.log`).
* `git diff --check`: exit 0.

Only this worktree was changed; no push, merge, or rebase was performed.

## Review follow-up: lane 196 proof route for `MildGronwall`

The review's proposed energy work (then lane 194, now lane 196) should start
from `EulerMildMajorantEnergy.mild_majorized_energy_subinterval`
(`vendor/NavierStokesAndEuler/Euler/MildMajorantEnergy.lean:22-65`). Its
regularized-word prerequisites include `regularized_word_hasDerivAt`
(`vendor/NavierStokesAndEuler/Euler/RegularizedWordEquation.lean:54-70`),
which supplies the full-order word equation without assuming a top-order time
derivative, and `finite_cylinder_viscous_energy`
(`vendor/NavierStokesAndEuler/Euler/CylinderViscousEnergy.lean:24-86`).
Specialize this regularized mild-energy chain to the constant Euclidean metric
and the finite word family through order `q+1`; identify the scalar energy
with a continuous majorant of the cylinder norm. This is a proof route, not
an existing proof of `MildGronwall`: the mild-equation adapter, divergence and
pressure constraints, maximal-regularity/forcing limits (the vendor entry's
lines 39-50), and norm comparison/majorant bounds still need discharge.

For the top-order nonlinear term, use `A03.outerProductTame`
(`formalization/NSFormalization/Section4/A03/OuterTameProduct.lean:165-179`),
its real-norm transport `A04.outerSobolevNormAt_le`
(`formalization/NSFormalization/Section4/A04/HighEnergy.lean:157-179`), and
feed the resulting tame bound through `A04.inner_energy_Rhigh`
(`formalization/NSFormalization/Section4/A04/HighEnergy.lean:125-146`).
The finite-order adapter must justify the real-norm finiteness premises and
retain the dissipative term needed to absorb the nonlinear gradient factor.
Lane 169/178's datum derivative route only reaches `m ≤ q-1`
(`formalization/NSFormalization/Section4/A01/DatumPathDeriv.lean:400-438`),
short of `q+1`; using the all-order constructor first would be circular.
The vendor Picard ball bounds provide the short base horizon, but using them
for the desired high-order estimate makes the radius depend on itself.
They are not the right energy entry. The nonzero `MildGronwall` proof remains
open in lane 196; this records-only fix changes no production theorem.

## Records/probe fix validation (2026-09-15)

`probe193_wiring.lean` now copies the complete combined export at lane 192
commit `9ca0a45`, `CylinderWiring.lean:139-161` (also checked against the
current branch). Its shared witnesses retain lift agreement, divergence,
angular invariance, Duhamel, and both continuous and all-time-order datum
paths. Only unused binder names differ. The sibling module is still absent,
so this checks composition with a theorem parameter, not an imported proof.
The review and its two probes are committed unchanged as historical artifacts:
`probes/rev193_constructor_and_zero.lean` checks the older `3eaab5c` interface
and proves the zero-data family with vendor base radius `1`;
`probes/rev193_mutation_fail.lean` records the intentional negative test.

Rerun with `scripts/lean-env.sh` sourced, Lake in `verification/`, and
`LEAN_NUM_THREADS=6`:

* `lake build NSFormalization.Section4.A01.AprioriFamily`: exit 0,
  10022 jobs; inherited dependency warnings only.
* `lake env lean ../formalization/NSFormalization/Section4/A01/AprioriFamily.lean`:
  exit 0, zero output.
* `lake env lean ../research/A01/axioms_a3_m2.lean` and
  `lake env lean ../research/A01/axioms_a3_m2_193.lean`: exit 0; respectively
  four and fourteen reports with only `[propext, Classical.choice, Quot.sound]`.
* `lake env lean ../research/A01/probe193_wiring.lean` and
  `lake env lean ../research/A01/probes/rev193_constructor_and_zero.lean`:
  exit 0, zero output.
* `lake env lean ../research/A01/probes/rev193_mutation_fail.lean`: expected
  exit 1 at line 35, `Type mismatch`: `hb_of_base` concludes `aprioriRadius`,
  but the mutation demands `mutatedRadius255`.
* `make check`: exit 0, 13 policy tests pass and 30 work items consistent.
* `git diff --check`: exit 0.

No production module or theorem changed in this fix; no push was performed.
