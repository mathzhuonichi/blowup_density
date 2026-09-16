# REPORT 203 — signed maximal-limit reduction

## 1. Theorems with exact statements

**Conditional progress, not unconditional analytic closure.** Seven declarations
are added. The principal conclusion is the imported lane-201
`CylinderSignedRootLimit`, unchanged. Its proof now consumes an unabsorbed
signed regularized-root integral inequality, uses hFB only on the limiting
family, absorbs the full negative gradient square, and removes epsilon.
The actual imported `ForcingFamilyBound` has no `ha` argument.

The literal requested hypothesis list is **not achieved**: root assembly also
requires the scalar sign `0 ≤ E * ‖sobolevPath F hF (q+1)‖`. The finite-energy
export retains lane 201's initial normalization, which supplies this sign.
There is exactly ONE further **analytic** input, `CylinderSignedEnergyPassage`;
it is not constructed here for general nonzero data. This limitation is not
hidden inside an enlarged forcing-bound definition.

Exact principal statements (under the module's imports/opens):

```lean
theorem maximal_word_square_integral_limit {q m : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (hm : m ≤ 2+q) (w : Fin m → Fin 4)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (U : TimeLp T (SobolevSpace 1 (2+q)))
    (hU : Filter.Tendsto (fun n => pathLp T hT (maximalApproximation 1 q T n u))
      Filter.atTop (𝓝 U)) :
    Filter.Tendsto (fun n => ∫ s,
      ‖word 1 (extendPath T hT (maximalApproximation 1 q T n u) s) hm w‖^2
        ∂timeMeasure T) Filter.atTop
      (𝓝 (∫ s, ‖word 1 (U s) hm w‖^2 ∂timeMeasure T))
```

```lean
theorem signed_quotient_absorption {ν k r g z b ε : ℝ}
    (hν : 0 < ν) (hr : 0 ≤ r) (hb : 0 ≤ b) (hε : 0 < ε)
    (h : r*z ≤ k*r*g+b*r) :
    (r*z-ν*g^2) / Real.sqrt (r^2+ε^2) ≤ k^2/(4*ν)*r+b
```

```lean
theorem cylinderSignedRootLimit_of_forcingBound {q : ℕ} (hq : 6 ≤ q)
    {ν S : ℝ} (hν : 0 < ν) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) {E A : ℝ}
    (hb : 0 ≤ E * ‖sobolevPath F hF (q+1)‖)
    (hFB : ForcingFamilyBound hq hν a F hF E A)
    (hpass : CylinderSignedEnergyPassage hq hν a ha F hF) :
    CylinderSignedRootLimit hq hν a ha F hF E A
```

```lean
theorem finiteMildEnergy_of_forcingBound' {q : ℕ} (hq : 6 ≤ q)
    {ν S : ℝ} (hν : 0 < ν) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) {E A : ℝ}
    (hE : mildNormConstant q ≤ E)
    (hFB : ForcingFamilyBound hq hν a F hF E A)
    (hpass : CylinderSignedEnergyPassage hq hν a ha F hF) :
    FiniteMildEnergy hq hν a ha F hF E A
```

`strong_time_square_integral_limit` and
`mapped_time_square_integral_limit` prove the underlying strong-L² square
passage, including literal representatives. The word theorem applies directly
to the witness of `energy_maximal_limit`. It covers every gradient word at
order q+2, but does not claim to have proved the varying weighted denominator
passage merely by proving this unweighted whole-window statement.

## 2. Files

* `formalization/NSFormalization/Section4/A01/SignedLimit.lean`: seven new
  declarations, no heartbeat overrides, no existing Lean modules edited.
* `research/A01/axioms_signed_limit.lean`: seven module declarations and five
  zero-data helpers audited. Every report has exactly
  `[propext, Classical.choice, Quot.sound]`. The positive-horizon zero example
  proves the analytic premise for every competitor and maximal limit, then
  applies the new finite-energy export. It is not evidence for a general-data
  premise. A nonzero scalar absorption example and a negative-sign control
  also compile.
* `research/A01/ATTEMPTS_SIGNED_LIMIT.md`: positive/negative routes, exact
  remaining analytic work, and resolved diagnostics.
* `research/A01/A3_SPLIT.md`: only the requested envelope/limit sub-row updated.
* `research/A01/REPORT_203.md`: this four-part report.

## 3. Gaps with error text

The exact ONE remaining analytic input is:

```lean
def CylinderSignedEnergyPassage {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) : Prop :=
  let _solenoidal := ha
  ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))),
    (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
      (coefficients 1 hq (sobolevPath F hF q))
      (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t) →
    ∀ U : TimeLp T (SobolevSpace 1 (2+q)),
      Filter.Tendsto (fun n => pathLp T hT (maximalApproximation 1 q T n u))
        Filter.atTop (𝓝 U) →
    ∀ ε : ℝ, 0 < ε →
      let r := extendPath T hT (energyRootPath u)
      let H := fun s => (r s * cylinderEnergyForcing hq hT hTS F hF u U s -
        ν * (energyGradientNorm U s)^2) / Real.sqrt ((r s)^2+ε^2)
      ∀ t ∈ Icc (0 : ℝ) T,
        IntervalIntegrable H volume 0 t ∧
        Real.sqrt ((r t)^2+ε^2) ≤ Real.sqrt ((r 0)^2+ε^2) + ∫ s in (0 : ℝ)..t, H s

```

This is a signed regularized integral estimate for the actual finite-order
competitor and its actual maximal limit, with the complete `energyGradientNorm`
and the actual `cylinderEnergyForcing`. It is independent of E, A, and hFB;
no comparison conclusion or absorbed coefficient occurs in it. Integrability
is explicit, preventing a junk-integral interpretation. Only positive epsilon
is used. Solenoidality is an explicit scope restriction inherited from lane
201; it will be needed to supply pressure and transport cancellation.

The remaining supply must connect `regularized_full_energy_hasDerivAt` to this
predicate using the lane-198 source/pressure representatives and the vendor
cancellations. The derivative-word square convergence is proved, but the
subinterval passage with the **varying inverse regularized root**, together
with the cancellation assembly, remains open. Neither the dissipation-free
vendor theorem nor hFB supplies it. No all-order constructor is used.

No stronger lane-200 export is consumed or requested by this conditional
route: pass to the signed limit first and then apply its existing limiting
hFB. If instead absorption is done before n tends to infinity, an additional
bound on each n-indexed forcing family would be required; that alternate
route is not implemented or claimed here.

There is also a scalar interface correction. At r=0, k=g=z=0, b=-1 the tame
premise says 0≤0, whereas the regularized quotient conclusion would say
0≤-1. The conformance file checks this negative example. It is not presented
as a formal PDE counterexample to the user's unrestricted statement.
`mildNormConstant q≤E` implies the required sign and is independently needed
by lane 201 at the initial time. Thus neither the hFB-only finite-energy
claim nor the CylinderCommutatorBound-only claim is established here.

No unresolved compiler error remains. Actual resolved diagnostics include:

```
error: not a positivity goal
Tactic `apply` failed: could not unify the conclusion of `@add_le_add_left`
Unknown identifier `EulerMildTopWord.mapPath`
Unknown identifier `intervalIntegrable_congr_ae_restrict`
error: don't know how to synthesize placeholder for argument `f`
```

See ATTEMPTS_SIGNED_LIMIT.md for resolutions. No prohibited proof mechanism
or extra logical axiom is used.

## 4. Commands

All Lean shells source `. scripts/lean-env.sh`; Lake runs only in
`verification/`, with `LEAN_NUM_THREADS=6`.

```
lake build NSFormalization.Section4.A01.SignedLimit
lake env lean ../formalization/NSFormalization/Section4/A01/SignedLimit.lean
lake env lean ../research/A01/axioms_signed_limit.lean
make check             # worktree root
make test              # worktree root
make test-mutations    # worktree root
git diff --check
```

All commands exit 0. Direct module checking produces **0 bytes**. The build
succeeds, but is not literally silent: Lake replays existing dependency
warnings; SignedLimit itself emits none. The audit has 12 declarations with
exactly the three permitted axioms and no warnings/errors. The mutation suite
accepts its valid refactor and rejects all three invalid mutations; it is an
infrastructure check, not an analytic closure claim.

Logs are gitignored `tmp/signed-{build,direct,axioms,check,test,mutations}.log`.
All changes are confined to this worktree. No push, merge, or rebase was run.
The lane changes are committed on `erenup/203-A01-signed-limit`.
