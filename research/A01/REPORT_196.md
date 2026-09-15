# REPORT 196 — finite-order mild energy reduction

## 1. Theorems, exact statements, and constants

**Conditional delivery under the satisfiability rule; general-data A3-M2 remains
open.** The full-word Euclidean norm, both norm comparisons, its continuous
path and regularized metric limit, the actual regularized quadratic word PDE,
the tame/Young algebra, and the scalar/family assembly are proved.

The ONE analytic residual is `FiniteMildEnergy`. Neither it nor general-data
unconditional `mildGronwall`, `hb_of_base'`, or `hb_of_base_inv'` is claimed.
The latter three delivered theorems explicitly take the residual as a premise.

Constants:

* Proved norm comparison:
  `mildNormConstant q = Real.sqrt (Fintype.card (SobolevWord (q+1)) : ℝ) >= 0`.
  Here `SobolevWord (q+1)` is the complete finite family through order `q+1`.
* Proved absorption: for an energy-envelope constant `A`,
  `C = A^2/(4*ν) >= 0` when `0 < ν`. The nonlinear driver is exactly
  `256 * ‖restrictOperator 1 (Nat.succ_le_succ hq) (extendPath T hT u s)‖^2`.
* The envelope's comparison constant `E >= 0` and tame constant `A` are fixed
  before every competitor/window. A general-data choice satisfying the energy
  premise is **not proved**. The word comparison constant is a concrete
  candidate component, not a claim that the analytic estimate is discharged.
* The checked zero-data instance takes `E(q)=1`, `A(q)=0`, `C(q)=0`, `ν=1`,
  `S=1`, base radius zero. Its all-order a-priori radius is zero.

Exact residual (same opens/namespace as the module):

```lean
def FiniteMildEnergy {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) (E A : ℝ) : Prop :=
  ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))),
    (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
      (coefficients 1 hq (sobolevPath F hF q))
      (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t) →
    ∃ (x : C(Icc (0 : ℝ) T, ℝ)) (d g : ℝ → ℝ),
      (∀ t, 0 ≤ x t) ∧ (∀ t, ‖u t‖ ≤ Real.sqrt (x t)) ∧
      Real.sqrt (x ⟨0, le_rfl, hT⟩) ≤
        E * ‖ordinarySobolev (q+1) a.toLp a.translation_contDiff‖ ∧
      (∀ t ∈ Ioo 0 T, HasDerivAt (extendPath T hT x) (d t) t) ∧
      ∀ t ∈ Ioo 0 T,
        (1/2) * d t + ν * (g t)^2 ≤
          A * (16 * ‖restrictOperator 1 (Nat.succ_le_succ hq)
            (extendPath T hT u t)‖) * Real.sqrt (extendPath T hT x t) * g t +
          (E * ‖sobolevPath F hF (q+1)‖) * Real.sqrt (extendPath T hT x t)
```

Exact principal theorem signatures follow. Definitions appearing here are
those imported or declared in the module; no classical solution is implicit.

```lean
theorem euclideanWordNorm_bounds {q : ℕ} (u : SobolevSpace 1 (q+1)) :
    ‖u‖ ≤ euclideanWordNorm u ∧ euclideanWordNorm u ≤ mildNormConstant q * ‖u‖
```

```lean
theorem euclidean_full_word_limit (q : ℕ) (T : ℝ)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))) :
    let d := fun (_ : Unit) (W : SobolevWord (q+1)) => W.1.val
    let w := fun (_ : Unit) (W : SobolevWord (q+1)) => W.2
    let hd : ∀ i W, d i W ≤ q+1 := fun _ W => Nat.le_of_lt_succ W.1.isLt
    let K := ContinuousMap.const (Icc (0 : ℝ) T) (ContinuousLinearMap.id ℝ (LiftL2 1))
    Filter.Tendsto (fun n => EulerMetricPathConvergence.metricPath T K
      (EulerRegularizedEnergyFamily.regularizedValueFamily 1 d w hd n T u ()))
      Filter.atTop (𝓝 (EulerMetricPathConvergence.metricPath T K
        (EulerRegularizedEnergyFamily.energyValueFamily 1 d w hd T u ())))
```

```lean
theorem quadratic_regularized_word {q m : ℕ} (hm : m ≤ q+1) (n : ℕ)
    (w : Fin m → Fin 4) {ν S T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hTS : T ≤ S)
    (D : Coefficients (Icc (0 : ℝ) S) (SobolevSpace 1 (q+1)) (SobolevSpace 1 q))
    (u₀ : SobolevSpace 1 (q+1)) (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (hu : ∀ t, u t = quadraticDuhamel 1 ν hν hT hTS D u₀ u t)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => value 1 (extendPath T hT (regularizedWordPath 1 hm n w T u) r))
      (ν • jetLaplacian 1 (toJet 1 (regularizedWordPath 1 hm n w T u
        ⟨t, ht.1.le, ht.2.le⟩)) +
        value 1 (regularizedWordBlock 1 hm n w
          (sourcePath (D.comp (timeInclusion hTS)) u ⟨t, ht.1.le, ht.2.le⟩))) t
```

```lean
theorem mild_energy_absorption {ν A l x g b d : ℝ} (hν : 0 < ν) (hx : 0 ≤ x)
    (h : (1/2)*d + ν*g^2 ≤ A*(16*l)*Real.sqrt x*g + b*Real.sqrt x) :
    d ≤ 2 * ((A^2/(4*ν)) * (256*l^2) * x + b*Real.sqrt x)
```

```lean
theorem outer_tame_low {m : ℕ} (hm : 2 ≤ m) {z : Space → Space}
    (hz : A03.MemHmVector m z)
    (h2 : D01.sobolevENorm 2 z ≠ ⊤) (hmz : D01.sobolevENorm (m : ℝ) z ≠ ⊤)
    {l : ℝ} (hl : (D01.sobolevENorm 2 z).toReal ≤ 16*l) :
    (A03.outerSobolevENorm (m : ℝ) z z).toReal ≤
      A03.outerTameConst m * (16*l) * (D01.sobolevENorm (m : ℝ) z).toReal
```

```lean
theorem inner_mild_energy {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {G Gt N P L F : H} {ν A l x g b d : ℝ} (hν : 0 < ν) (hx : 0 ≤ x)
    (hd : d = 2 * ⟪G, Gt⟫) (hmom : Gt = ν • L - N - P + F)
    (hlap : ⟪G, L⟫ ≤ -g^2) (hpr : ⟪G, P⟫ = 0)
    (hnl : -⟪G, N⟫ ≤ A*(16*l)*Real.sqrt x*g)
    (hG : ‖G‖ = Real.sqrt x) (hF : ‖F‖ = b) :
    d ≤ 2 * ((A^2/(4*ν)) * (256*l^2) * x + b*Real.sqrt x)
```

```lean
theorem mildGronwall {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) {E A : ℝ} (hE : 0 ≤ E)
    (henergy : FiniteMildEnergy hq hν a ha F hF E A) :
    MildGronwall hq hν a ha F hF E (A^2/(4*ν))
```

```lean
theorem hb_of_base' {ν S R₆ : ℝ} (hν : 0 < ν) (hS : 0 ≤ S)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u₆ : C(Icc (0 : ℝ) S, SobolevSpace 1 7)) (hR : ‖u₆‖ ≤ R₆)
    (h₆ : ∀ t, u₆ t = quadraticDuhamel 1 ν hν hS le_rfl
      (coefficients 1 (le_refl 6) (sobolevPath F hF 6))
      (ordinarySobolev 7 a.toLp a.translation_contDiff) u₆ t)
    (E A : ℕ → ℝ) (hE : ∀ q, 0 ≤ E q)
    (henergy : ∀ q (hq : 6 ≤ q), FiniteMildEnergy hq hν a ha F hF (E q) (A q)) :
    ∀ q (hq : 6 ≤ q), HasAprioriBound hq hν a F hF
      (aprioriRadius a F hF R₆ E (fun q => A q^2/(4*ν)) q)
```

```lean
theorem hb_of_base_inv' {ν S R₆ : ℝ} (hν : 0 < ν) (hS : 0 ≤ S)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u₆ : C(Icc (0 : ℝ) S, SobolevSpace 1 7)) (hR : ‖u₆‖ ≤ R₆)
    (h₆ : ∀ t, u₆ t = quadraticDuhamel 1 ν hν hS le_rfl
      (coefficients 1 (le_refl 6) (sobolevPath F hF 6))
      (ordinarySobolev 7 a.toLp a.translation_contDiff) u₆ t)
    (E A : ℕ → ℝ) (hE : ∀ q, 0 ≤ E q)
    (henergy : ∀ q (hq : 6 ≤ q), FiniteMildEnergy hq hν a ha F hF (E q) (A q)) :
    ∀ q (hq : 6 ≤ q), HasAprioriBoundInv hq hν a F hF
      (aprioriRadius a F hF R₆ E (fun q => A q^2/(4*ν)) q)
```

The remaining declarations are `mildNormConstant_nonneg`,
`euclideanWordNorm`, `euclideanWordNorm_eq`, and
`continuous_euclideanWordNorm`. `euclideanWordNorm` is exactly the vendor
`familyMetricNorm` of the identity operator applied to the complete derivative
array. Its formula is `sqrt (sum W, norm (u.val W)^2)`.

## 2. Files

* `formalization/NSFormalization/Section4/A01/MildGronwall.lean`: 15 declarations.
* `research/A01/axioms_mild_gronwall.lean`: audits all 15 declarations and four
  zero-data helpers; unconditional zero-data family application, nonstationary
  scalar example, and a genuine negative `ENNReal.toReal` example.
* `research/A01/ATTEMPTS_MILD_GRONWALL.md`: vendor/interface audit, successful
  reductions, rejected routes, satisfiability limits, and resolved diagnostics.
* `research/A01/A3_SPLIT.md`: only the requested A3-M2 row updated, retaining
  its earlier history and explicitly marking the general analytic gap open.
* `research/A01/REPORT_196.md`: this report.

The review fix edits `AprioriFamily.lean` only for the permitted insertion and
threading of the solenoidal datum hypothesis. Other pre-existing Lean modules
remain untouched.

## 3. Gaps and error text

The missing fact is the existence of the scalar squared-energy envelope in
`FiniteMildEnergy`, quantitatively uniform over competitors and subwindows.
Its supply from the nonlinear regularized word system remains unproved.
This is a substantial analytic residual, including its general-data constants.
The scalar reduction and family corollaries are complete under that one input.

The vendor `mild_majorized_energy_subinterval` requires divergence/gradient
constraints and higher Bochner state/source/pressure representatives; its
conclusion still contains a forcing-family norm. The identity metric alone
does not turn that term into the tame dissipative bound needed here.
At full cutoff `q+1`, choose external order `N = q − 5`, so `N + 6 = q + 1`;
the wrapper remains unusable directly because it is specific to
`CorrectionData`/`SpatialBudget`.

Both energy predicates now take an explicit solenoidal datum hypothesis. This
resolves the vendor datum-interface mismatch but does not construct the
remaining higher Bochner representatives or energy envelope.

The residual's differentiable `x` is an envelope, not the literal word norm
squared; it need only be differentiable inside the interval. No stationary
extension beyond the horizon is demanded. Zero-data satisfiability is proved
for every competitor. A nonzero PDE witness for the full residual has not
been constructed; the nonstationary scalar example is not presented as one.

The requested review file is missing:

```
sed: can't read research/A01/REVIEW_193-A01-a3-m2-bounds.md: No such file or directory
```

A transient continuity elaboration attempt failed with:

```
(deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached
```

It was resolved by finite-sum continuity using `wordOperator`, without any
heartbeat option. Other resolved diagnostics are in the attempts record.
There are no remaining Lean errors. The gap is explicit in the theorem
signature, not concealed by a placeholder or nonstandard axiom.

## 4. Commands and results

Every Lean shell sourced `. scripts/lean-env.sh`. All Lake invocations ran
from `verification/` with `LEAN_NUM_THREADS=6`. Dependency packages were
confirmed to be the existing shared symlink before building.

* `lake build NSFormalization.Section4.A01.MildGronwall`: exit 0
  (`tmp/build196.log`, 10067 jobs). The module itself has no warnings; Lake
  replays inherited dependency warnings. Therefore the full build log is
  **not literally silent**.
* `lake env lean ../formalization/NSFormalization/Section4/A01/MildGronwall.lean`:
  exit 0, **zero bytes of output** (`tmp/module196.log`).
* `lake env lean ../research/A01/axioms_mild_gronwall.lean`: exit 0,
  **19 reports, each exactly `[propext, Classical.choice, Quot.sound]`**;
  all examples checked (`tmp/axioms196.log`).
* `make check` from the worktree root: exit 0 (`tmp/check196.log`).
* `lake test` from `verification/` (the required-cwd equivalent of
  `make test`): exit 0 (`tmp/test196.log`).
* `make test-mutations`: exit 0; refactor accepted and all three invalid
  mutations rejected (`tmp/mutations196.log`).
* `git diff --check`: exit 0.
* Forbidden proof-token and heartbeat-option search in both new Lean files:
  no matches.

Only this worktree was changed. No push, merge, or rebase was performed.
