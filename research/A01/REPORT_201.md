# REPORT 201 — root comparison

## 1. Theorems with exact statements

Partial analytic closure, with the requested satisfiable residual isolated.
The scalar integral comparison, closed-horizon uniqueness, positive-root absorption and
zero-root regularization limit are proved. The forcing-bound assembly has
ONE additional analytic premise `CylinderSignedRootLimit` and an explicit
initial normalization `mildNormConstant q ≤ E`. It concludes lane 199's
`CylinderRootComparison` and `FiniteMildEnergy` without changing either
definition. The signed-limit premise and both assembly theorems are restricted
to solenoidal initial data. This is not a proof from `ForcingFamilyBound` alone.

All statements below are in namespace `NSFormalization.Section4.A01`, with
the imports/opens in `RootComparison.lean`. The exact declarations are:

```lean
theorem scalar_differential_comparison {T : ℝ} (hT : 0 ≤ T)
    {α w d : ℝ → ℝ} (hα : Continuous α) (hw : ContinuousOn w (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt w (d t) t)
    (hle : ∀ t ∈ Ioo 0 T, d t ≤ α t * w t) (hzero : w 0 ≤ 0) :
    ∀ t ∈ Icc 0 T, w t ≤ 0
```

```lean
theorem scalar_integral_comparison {T b c : ℝ} (hT : 0 ≤ T)
    {α r : ℝ → ℝ} (hα : Continuous α) (hr : Continuous r)
    (hα0 : ∀ t ∈ Icc 0 T, 0 ≤ α t)
    (hint : ∀ t ∈ Icc 0 T, r t ≤ c + ∫ s in (0 : ℝ)..t, (α s * r s + b)) :
    ∀ t ∈ Icc 0 T, r t ≤ energyComparison α b c t
```

```lean
theorem energyComparison_unique_on_Icc {T b c : ℝ} (hT : 0 ≤ T)
    {α y : ℝ → ℝ} (hα : Continuous α) (hy : ContinuousOn y (Icc 0 T))
    (hy0 : y 0 = c)
    (hyd : ∀ t ∈ Ioo 0 T, HasDerivAt y (α t * y t + b) t) :
    ∀ t ∈ Icc 0 T, y t = energyComparison α b c t
```

```lean
theorem positive_root_absorption {ν k r g b d : ℝ} (hν : 0 < ν) (hr : 0 < r)
    (h : r*d + ν*g^2 ≤ k*r*g + b*r) : d ≤ k^2/(4*ν)*r+b
```

```lean
theorem regularized_root_comparison_limit (α : ℝ → ℝ) {b c r t : ℝ}
    (hc : 0 ≤ c) (hr : 0 ≤ r)
    (hreg : ∀ ε : ℝ, 0 < ε → Real.sqrt (r^2+ε^2) ≤
      energyComparison α b (Real.sqrt (c^2+ε^2)) t) :
    r ≤ energyComparison α b c t
```

```lean
def CylinderSignedRootLimit {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) (E A : ℝ) : Prop :=
  let _solenoidal := ha
  ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))),
    (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
      (coefficients 1 hq (sobolevPath F hF q))
      (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t) →
    ∀ U : TimeLp T (SobolevSpace 1 (2+q)),
      Filter.Tendsto (fun n => pathLp T hT
        (maximalApproximation 1 q T n u)) Filter.atTop (𝓝 U) →
      (∀ᵐ r ∂timeMeasure T,
        extendPath T hT (energyRootPath u) r * cylinderEnergyForcing hq hT hTS F hF u U r ≤
          A * (16 * ‖restrictOperator 1 (Nat.succ_le_succ hq) (extendPath T hT u r)‖) *
            extendPath T hT (energyRootPath u) r * energyGradientNorm U r +
          (E * ‖sobolevPath F hF (q+1)‖) * extendPath T hT (energyRootPath u) r) →
      ∀ t ∈ Icc (0 : ℝ) T,
        extendPath T hT (energyRootPath u) t ≤ energyRootPath u ⟨0, le_rfl, hT⟩ +
          ∫ s in (0 : ℝ)..t,
            ((cylinderEnvelopeDriver hq hT A u s)^2/(4*ν) *
              extendPath T hT (energyRootPath u) s + E * ‖sobolevPath F hF (q+1)‖)
```

```lean
theorem cylinderRootComparison_of_forcingBound {q : ℕ} (hq : 6 ≤ q)
    {ν S : ℝ} (hν : 0 < ν) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) {E A : ℝ}
    (hE : mildNormConstant q ≤ E)
    (hlimit : CylinderSignedRootLimit hq hν a ha F hF E A)
    (hFB : ForcingFamilyBound hq hν a F hF E A) :
    CylinderRootComparison hq hν a F hF E A
```

```lean
theorem finiteMildEnergy_of_forcingBound {q : ℕ} (hq : 6 ≤ q)
    {ν S : ℝ} (hν : 0 < ν) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) {E A : ℝ}
    (hE : mildNormConstant q ≤ E)
    (hlimit : CylinderSignedRootLimit hq hν a ha F hF E A)
    (hFB : ForcingFamilyBound hq hν a F hF E A) :
    FiniteMildEnergy hq hν a ha F hF E A
```

The coefficient is exactly `(cylinderEnvelopeDriver hq hT A u s)^2/(4*ν)`,
where the driver is `A*(16*low)`. Every finite word through order q+1 is
retained by the imported root; the same maximal-approximation witness U is
passed to both the forcing bound and signed-limit premise. Constants are
fixed before windows and competitors. Solenoidality is carried into the
substantive signed-limit premise and through both assemblies, while lane 199's
`CylinderRootComparison` conclusion remains unchanged. The initial mild identity and the
proved Euclidean-word norm comparison supply the initial root bound.

## 2. Files

- New `formalization/NSFormalization/Section4/A01/RootComparison.lean`:
  eight declarations; no existing Lean module modified; no heartbeat override.
- New `research/A01/axioms_root_comparison.lean`: all eight declarations and
  five zero-data helpers audited. Both residual and forcing hypotheses are
  proved for every zero-data competitor and maximal limit; the new finite
  energy theorem is then applied. Includes T=0, nonstationary scalar data
  with zero initial root, regularization at zero, and negative scalar checks.
- New `research/A01/ATTEMPTS_ROOT_COMPARISON.md`: failed routes and diagnostics.
- Updated only the requested A3-M2 envelope row in `research/A01/A3_SPLIT.md`.
- Added the reviewer-supplied review and three probes; the collision probe now
  checks coexistence of integration's global theorem and the renamed Icc theorem.
- This report, updated after rebasing onto integration.

## 3. Gaps with error text

`CylinderSignedRootLimit` above is the ONE missing analytic fact. It is a
substantive absorbed integrated bound on the root along the maximal-approximation
limit, not a generic limit-continuity lemma, and is lane 203's target. In detail,
lane 199 proves the regularized signed identity; the existing limiting
estimate from lane 198 drops dissipation. Its limit cannot simply be used
as a signed bound. Nor does a bound on the limiting family directly bound
each regularized family. The passage to the absorbed signed integrated
inequality is not established here. The regularized scalar algebra and
subsequent scalar comparison/zero-root limit are established. Its explicit
`ha` argument restricts the obligation to the incompressible setting needed
for the transport and pressure cancellations. No all-order
constructor or `ClassicalSolutionR` energy theorem is used on a mild path.

The requested `hFB`-only statement also omits initial normalization. The
current imported `ForcingFamilyBound hq hν a F hF E A` uses E
only in E*‖F‖. For zero force it is independent of E, whereas comparison at
t=0 requires root(u₀)≤E*‖u₀‖. Thus the delivered theorem explicitly requires
`mildNormConstant q ≤ E`. The negative scalar checks document the issue;
no nonzero PDE counterexample has been constructed or claimed. That imported
interface and lane 199's `CylinderRootComparison` are consumed unchanged.

No unresolved compiler error remains. Resolved diagnostics included:

```
Unknown identifier `TimeLp`
Unknown identifier `𝓝`
Tactic `rewrite` failed: Did not find an occurrence of the pattern deriv z t
Unknown identifier `mul_nonpos_iff_of_pos_right`
Type mismatch ... (cylinderEnvelopeDriver hq hT A u ^ 2) x ...
Type mismatch ... zero_sob (q + 1) ... expected ... =ᵐ[liftMeasure 1] ...
```

The fixes are recorded in ATTEMPTS_ROOT_COMPARISON.md. No claim of general
nonzero-data forcing-bound closure or unconditional finite energy is made.

## 4. Commands

All Lean commands source `. scripts/lean-env.sh`; Lake is run only from
`verification/`, with `LEAN_NUM_THREADS=6`. Final gate commands:

```
lake build NSFormalization.Section4.A01.RootComparison
lake env lean ../formalization/NSFormalization/Section4/A01/RootComparison.lean
lake env lean ../research/A01/axioms_root_comparison.lean
lake env lean ../research/A01/probes/rev201_integration_collision.lean
lake env lean ../research/A01/probes/rev201_controls.lean
# rev201_mutation.lean must fail: it asserts the false 1/(8ν) absorption
make check                         # worktree root
make test                          # worktree root; invokes lake test
git diff --check
```

The successful commands exit 0; the mutation probe is expected to exit nonzero.
The direct module check produces no diagnostics. The build succeeds and only
replays pre-existing dependency warnings. All 13 audited declarations use
exactly the standard axioms `[propext, Classical.choice, Quot.sound]`.
The collision and controls probes pass; the mutation probe fails at the
intended `1/(4*ν)` versus `1/(8*ν)` type mismatch. `make check` and `make test`
both pass. `git diff --check` is clean.

Work is committed on `erenup/201-A01-root-comparison`. No push, merge or
files outside this worktree were edited.
