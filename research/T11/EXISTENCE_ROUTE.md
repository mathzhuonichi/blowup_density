# U9a / lane 311: route decision

Choose **R2: a native coefficient-path construction following A01's prescribed-horizon,
a-priori-bound and causal-window strategy**. Reuse R1's endpoint-safe Duhamel analysis as
an integration library. This lane proves the linear first rung, not arbitrary-data existence.
There is no completed torus `TorusTwoSpaceContract` and no proof of
`PeriodicQuantitativeLocalInput` in this delivery.

## Evidence and limits

The search covered `Paper1/Periodic*.lean`, all `Section3/`,
`Section4/{A01,A02,A04,D01}`, and `vendor/HeliCorgi/Formal/`, using the mandated
`grep -rn` (108 matching lines for the principal candidate names). Sources actually read:

| Source | What it provides / what it still asks for |
| --- | --- |
| `Formal/UniformRestartContinuation.lean:29,59` | `FlowMapUniformRestartPackage` already assumes `restart_past_terminal`; its theorem selects a time close enough to T. It constructs no PDE solution. Its `zero_fixed_before` also needs care for a forced affine flow map. |
| `Formal/EndpointSafeTwoSpaceDuhamel.lean` | Exact positive-time smoothing, null endpoint, Bochner integrability and two-space mild semantics. No torus operators are supplied. |
| `Formal/EndpointSafeTwoSpacePicard.lean:719,887` | Genuine abstract Banach construction once the two-space contract and linear contraction exist. The displayed mild equation is unforced. |
| `Paper1/PeriodicHeatMultiplier.lean` | Already proves scalar complete-lp heat contraction and one-derivative smoothing. The smoothing estimate is **present**, not an absent lemma. |
| `Paper1/PeriodicPicardContraction.lean` | Uniqueness in a supplied contractive ball; no existence and no concrete nonlinear estimate. |
| `Paper1/PeriodicPicardDuhamelLipschitz.lean` | Time-length gain from an assumed same-space integrand difference bound. Derivative loss has not thereby disappeared. |
| `Paper1/PeriodicMildWitnessAdapter.lean` | Fixed-point orientation/packaging only. |
| `Paper1/PeriodicShearLocal.lean` | Actual unforced Flow constructor from a supplied heat/shear profile. It does not supply arbitrary profiles or the forced local input. |
| `Paper1/PeriodicLocalLifespan.lean:73` | `ClassicalPeriodicLocalTheory.local_flow` and `.finite_h2_extension` are hypotheses. Neither gives the H¹-uniform, all-order quantitative statement without further analysis. |
| `Section4/A01/{Horizon,AprioriInvariance}.lean` | Prescribed horizon and bounds on every subwindow, with angle-invariant cylinder paths. This is a strategy to transfer, not a theorem applicable to periodic physical fields. |
| `Paper1/PeriodicFiniteOrderMild.lean`, `PeriodicOrdinaryLocal.lean` | Their ordinary representative requires whole-space L²; importing this obligation would exclude nonzero spatially periodic data. |

`Section3/T10/FourierCalculus.lean` is present on this checkout. T10's registered
`T01.torus_data` ends before the solution-class layer; no registered contract is changed.
The new module reuses `ClassicalSolutionT` rather than making a second local structure.

R1's H³/H² fixed-point interval is controlled by H³ initial data. It does not imply a
uniform interval on an H¹ ball. R2 also has to solve that problem: choosing R2 does not
prove the H¹ statement, or authorize replacing it with H⁷. Its advantage here is the
explicit all-order, common-horizon construction plan already exercised by A01.

## Exact delivered two-space contract

All definitions are in `NSFormalization.Section3.T11.LocalExistenceProbe`.
`TorusTwoSpaceContract ν` contains
`MNS2.EndpointSafeTwoSpaceDuhamelContract ℝ (PeriodicSobolev 3) (PeriodicSobolev 2)`
and the following identifying equations:

* Write `W(k)=1+4π²∑ᵢkᵢ²`, `hν(t,k)=exp(-νt(W(k)-1))`.
  The initial evolution is multiplication by `hν(t,k)` on H³ weighted coefficients.
* Positive smoothing H²→H³ multiplies by `sqrt(W(k))*hν(t,k)`.
  Its exact majorant is `torusSmoothingKernel ν t = sqrt(1+1/(ν*t))`.
* `torusConvectionSymbol A B i k` is the order-two weighted Fourier coefficient
  of `∑ⱼ ∂ⱼ(uⱼvᵢ)`: remove both order-three weights, convolve on Z³, multiply
  by `2π i kⱼ`, and restore `W(k)`. `torusProjectedConvectionSymbol` then
  applies the actual Leray symbol, retaining the zero-mode convention.
  `bilinear_symbol` pins the continuous bilinear operator to this formula.
  Proving absolute summability and boundedness of this convolution is U9b's work.
* `torusForcedPicard C A F u t` is `H(t)A + ∫₀ᵗH(t-s)F(s)ds - ∫₀ᵗS(t-s)Q(u(s),u(s))ds`.
  Here F is the **projected order-three** force path. Endpoint smoothing uses the
  upstream zero branch at nonpositive elapsed time. The same-order force evolution
  has the honest identity at elapsed time zero.
* With `beta=‖Q‖*C.analytic.kernelPrimitive T`, `TorusPicardConstants C T R b`
  requires `T>0`, `R>0`, `b≥0`, `b+beta*R²≤R`, and `2*beta*R<1`.
  The last number is the ball Lipschitz constant. The force/linear path must actually
  be bounded by b; a later solver may not treat the numeric certificate as that bound.
* `TorusForcedMildOn` requires continuity, initial value, both actual-vector
  integrability clauses and the forced equation. Divergent integrals totalized by
  zero cannot satisfy its integrability fields.

**Phantom-index warning:** T10's `PeriodicSobolev s` abbreviates the same real submodule
for every s. Type-correctness alone cannot certify a change of Sobolev order.
The multiplier and symbol equations above explicitly enforce every reweighting.

## Proved first rung and non-vacuity

`torusMultiplier_norm_le` constructs a bounded even real multiplier on canonical
three-vector data and proves `‖M A‖≤C‖A‖`, with **no dimension factor**. It proves
conjugate-reflection preservation and uses the Euclidean product norm. This supplies:

```lean
torusHeat_norm_le (s : ℝ) {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
  (A : PeriodicSobolev s) : ‖torusHeat s hν ht A‖ ≤ ‖A‖

torusHeatSmoothing_norm_le (s : ℝ) {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
  (A : PeriodicSobolev s) :
  ‖torusHeatSmoothing s hν ht A‖ ≤ torusSmoothingKernel ν t * ‖A‖
```

Also proved: identity at zero, the heat semigroup law, positive-smoothing coherence,
and preservation of coefficient solenoidality. These are unconditional canonical-carrier
results; they do not assume either local input or the two-space contract.
`torus_bilinear_bound` is explicitly conditional on the contract; it is the abstract
operator-norm estimate, **not** a proof of the Fourier convolution estimate.

`torusHomogeneousSolution` constructs a full `ClassicalSolutionT` with velocity `b(t)c`,
force `b'(t)c` and pressure zero, for any globally smooth b with b(0)=1. Its regularity
theorem proves all three original fields on the same horizon. `nonzero_forced_witness`
uses `c=e₁`, `b(t)=2-exp(-t)`, `g(t)=exp(-t)e₁`, ν=T=1. It proves a finite common K
bounds both the datum and **every** force order, and both velocity and force are nonzero
at (0,0). This tests the exact local input's premises and conclusion at a nontrivial
instance; it does not claim to prove the universally quantified input.

## Residual input and a quantifier issue for the lead

The only named unresolved local-existence input is verbatim:

```lean
def PeriodicQuantitativeLocalInput : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ → ∃ δ : ℝ, 0 < δ ∧
    ∀ a : SpatialField, a ∈ initialClassT → periodicSobolevENorm 1 a ≤ K →
      ∀ g : SpaceTimeField, ContDiff ℝ ∞ g → IsPeriodicOn univ g →
        (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ K) →
          ∃ w : ClassicalSolutionT ν a g δ, PeriodicLocalRegularity ν a g δ w
```

**U10 cannot infer this same-K-for-all-m premise from smoothness and compact time
support alone.** Those assumptions give a finite bound separately for each m, not a
single bound over m. For example a nonzero time bump times a nonzero spatial Fourier
mode has norms growing like `W(k)^(m/2)`. A force-family compactness argument controls
restart times at each fixed m; it does not remove growth as m→∞. This is a statement-level
issue in the planned U9→U10 edge, independent of the H¹ versus H³/H⁷ issue.
No modification to the supplied input or the restart field is made here. The lead must
resolve this edge explicitly before claiming assembly of the general continuation API.

## Subsequent sub-lanes: exact targets

These are proposed units, not additional hypotheses of this lane. Sizes count substantial
proof work, not wrapper lines. All notation below is now defined in the delivered module.

**U9b — native complete carrier, heat CLMs, convolution and kernel; L+ (roughly 2–3 modules).**
Target:

```lean
∀ ν : ℝ, 0 < ν → Nonempty (TorusTwoSpaceContract ν)
```

Supply real-submodule closedness/completeness, joint strong heat continuity, the
H³×H³→H² projected convolution bound, integrable kernel, and actual operator symbols.
Reuse the proved vector estimates and coherence. An H³ instance is useful but does not
claim the H¹ local input. Do not pass an ordinary whole-space representative.

**U9c — forced coefficient fixed point on prescribed windows; L (1–2 modules).**
Target (an exact Lean statement, using the instances pinned in the module):

```lean
∀ (ν : ℝ) (C : TorusTwoSpaceContract ν)
  (A : PeriodicSobolev 3) (F : ℝ → PeriodicSobolev 3) (T R b : ℝ),
  TorusPicardConstants C T R b → ContinuousOn F (Icc 0 T) →
  (∀ t, ∀ ht : t ∈ Icc (0 : ℝ) T,
    ‖C.analytic.linearEvolution ⟨t, ht.1⟩ A +
      ∫ s in (0 : ℝ)..t,
        C.analytic.linearEvolution (Real.toNNReal (t-s)) (F s)‖ ≤ b) →
  ∃ u : ℝ → PeriodicSobolev 3,
    TorusForcedMildOn C A F T u ∧ ∀ t ∈ Icc (0 : ℝ) T, ‖u t‖ ≤ R
```

Carry causal-window uniqueness and restriction to shorter intervals. Transfer the
Banach argument, adding the actual force integral. The linear H³ ball interval may
not be relabelled an H¹-controlled one.

**U9d — common-horizon bootstrap and physical/pressure recovery; L+ (2–3 modules).**
Target:

```lean
∀ (ν : ℝ), 0 < ν → ∀ (C : TorusTwoSpaceContract ν)
  (a : SpatialField) (g : SpaceTimeField) (T : ℝ),
  a ∈ initialClassT → ContDiff ℝ ∞ g → IsPeriodicOn univ g → 0 < T →
  ∀ (A : PeriodicSobolev 3) (F P u : ℝ → PeriodicSobolev 3),
    IsPeriodicDatum 3 a A → IsPeriodicSobolevPath 3 g F →
    (∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t)) →
    TorusForcedMildOn C A P T u →
    ∃ w : ClassicalSolutionT ν a g T,
      PeriodicLocalRegularity ν a g T w ∧
      IsPeriodicSobolevPathOn 3 (Ico 0 T) w.velocity u
```

The conclusion has all integer orders on the **original T**, pressure Poisson on
Ico (including zero), projected equation on Ioo, and normalized Haar pressure.
U1/U2 and T10 Fourier calculus are dependencies. No demand on a chosen a.e. Lp
representative's pointwise smoothness; reconstruct a smooth field first.

**U9e — low-order lifespan/common-horizon closure; L+ / analytic research risk.**
Exact target is `PeriodicQuantitativeLocalInput` above, unchanged. It requires a
lifespan uniform over the H¹ datum ball; U9b–d alone have not established that
uniformity. A01-style high-order a-priori bounds must control all causal windows
and retain a common low-order time. A higher-order or fixed-force replacement
requires the separately named V2 decision described in T11_SPLIT §3.1; it is not
an allowed proof of this target. The U9→U10 force-quantifier issue above also
requires lead reconciliation, independently of this proof campaign.

## U9b status

Lane 313 implements `Section3/T11/LocalExistence.lean` on route R2. The first
subsequent-sub-lane target is proved **conditionally on projected convolution
boundedness**; the second target is proved with exactly its displayed premises.
The primed input is copied verbatim from amendment 1; its lifespan consequence
is `quantitative_lifespan_lower_bound'`. No H¹ existence theorem is asserted.

Unconditional analytic work: closedness and completeness of the real vector
carrier, bounded heat/smoothing CLMs, joint strong heat continuity including zero,
local integrability of the exact smoothing kernel, and absolute convergence of
**every** convolution in the symbol on arbitrary coefficient data. In particular,
no divergent `tsum` is being assigned an intended convection value.

The **one residual analytic input** is exactly:

```lean
def TorusConvolutionInput : Prop :=
  ∃ Q : PeriodicSobolev 3 →L[ℝ] PeriodicSobolev 3 →L[ℝ] PeriodicSobolev 2,
    ∀ A B i k, (Q A B).1 i k = torusProjectedConvectionSymbol A B i k
```

This packages bounded real bilinearity of the specified symbol, not a solution,
fixed point, or the two-space contract. `torusTwoSpaceContract_nonempty` proves:

```lean
(H : TorusConvolutionInput) → (ν : ℝ) → 0 < ν → Nonempty (TorusTwoSpaceContract ν)
```

`PeriodicQuantitativeLocalInput'` is the mandated eventual target, not another
assumption of the coefficient construction. Neither it nor the old input is used
by the contract constructor or the fixed-point proofs.

`torusForcedPicard_exists` proves the exact U9c displayed existence target.
`torusAffinePicard_exists_unique` constructs the Banach fixed point in the complete
closed ball. `torusForcedMildOn_unique` proves equality on `[0,T]` for two solutions
in the certified radius, and `TorusForcedMildOn.restrict` and
`TorusPicardConstants.restrict` transfer the semantics and certificate to every
`0 < S ≤ T`. Force integrability, nonlinear integrability and the initial value
are part of the constructed certificate, not additional hypotheses.

There is also an explicit H³ bound. Put `q = ‖C.analytic.bilinear‖`,
`b = ‖A‖ + B`, where `B ≥ 0` bounds `‖F(t)‖` on `[0,1]`, and set

```text
η = min (1/(q*(b+1)^2+1)) (1/(2*(q*(2*(b+1))+1)))
T = min 1 ((η/(1+2/sqrt(ν)))^2).
```

`torusForcedPicard_quantitative` constructs the unique ball solution on this
positive `T`, with radius `b+1`. The mass estimate is
`C.analytic.kernelPrimitive T ≤ T + 2*(sqrt ν)⁻¹*sqrt T`.
This is a coefficient H³ theorem with a force supremum bound. It is not the
amended H¹/all-order-force lower bound, which is only derived conditionally from
`PeriodicQuantitativeLocalInput'`.

Remaining exact work:

* **U9c:** discharge `TorusConvolutionInput` above, using the now-proved absolute
  convergence and the weight-specific H³×H³→H² estimate. The original prescribed
  window fixed-point target, its ball uniqueness, and restriction are delivered
  in this lane; they need no new named assumption once the contract exists.
  A nonzero constant datum and force instantiate the coefficient theorem for any
  exact contract. Constant-mode symbol tests and the primed physical nonzero
  witness are unconditional. These tests do not claim to prove the global input.
* **U9d:** the common-horizon bootstrap/physical recovery target stays exactly:

  ```lean
  ∀ (ν : ℝ), 0 < ν → ∀ (C : TorusTwoSpaceContract ν)
    (a : SpatialField) (g : SpaceTimeField) (T : ℝ),
    a ∈ initialClassT → ContDiff ℝ ∞ g → IsPeriodicOn univ g → 0 < T →
    ∀ (A : PeriodicSobolev 3) (F P u : ℝ → PeriodicSobolev 3),
      IsPeriodicDatum 3 a A → IsPeriodicSobolevPath 3 g F →
      (∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t)) →
      TorusForcedMildOn C A P T u →
      ∃ w : ClassicalSolutionT ν a g T,
        PeriodicLocalRegularity ν a g T w ∧
        IsPeriodicSobolevPathOn 3 (Ico 0 T) w.velocity u
  ```
* **U9e:** prove `PeriodicQuantitativeLocalInput'` verbatim in amendment 1,
  including the H¹ datum ball, order-wise `M`, and one common positive horizon.
  No conversion from the coefficient force supremum bound to an order-wise
  `L¹_t H^m`-controlled lifespan is claimed here.

The probe, guarded axiom audit, attempts and gate report are respectively
`probes/existence_u9b.lean`, `axioms_existence_u9b.lean`,
`ATTEMPTS_EXISTENCE_U9B.md`, and `REPORT_313.md` under `research/T11/`.


## U9d status — lane 318 (partial; target remains open)

`Section3/T11/PhysicalRecovery.lean` constructs the actual inverse Fourier
series of every H³ datum, proves absolute convergence, reality, periodicity,
spatial continuity and both datum/field inverse identities. The physical
velocity of the supplied mild coefficient solution is jointly continuous on
`Icc 0 T ×ˢ univ`, recovers a at zero, and has **exactly** u as its H³ datum
path on `Ico 0 T` (indeed on every time set). Reweight transport is explicit;
no phantom order cast is used. Nonzero datum AND force instantiate the genuine
coefficient solver. The affine constant family additionally satisfies both the
mild equation and the full classical/regularity conclusion on arbitrary T>0.

**This does not close U9d or the requested complete (ii)+(iii) fallback.** No
new named input is assumed: the general all-order bootstrap, divergence,
physical pressure recovery and Duhamel differentiation are still unproved
obligations. Their exact combined target remains the U9d statement above,
unchanged; it is reproduced in `REPORT_318.md`. No whole-target restatement is
introduced as a peeling hypothesis, and no global classical local-theory
assumption is imported to manufacture existence.

One analytical caution for resuming: H^m convection lives in H^(m-1), so a
direct full-order heat gain to H^(m+1) has the nonintegrable naive kernel
(t-s)^(-1). The existing integrable one-derivative smoothing estimate alone
does not prove that step. Fractional bootstrap or additional persistence/time
regularity estimates are needed. This is not a counterexample to U9d.

The new probe checks only the delivered sub-results and the homogeneous full
recovery case; its name `physical_recovery_closes.lean` is the requested artifact
name, **not evidence that the general target closes**. Details, actual compiler
errors and the missing work are in `ATTEMPTS_PHYSICAL_RECOVERY.md`.
