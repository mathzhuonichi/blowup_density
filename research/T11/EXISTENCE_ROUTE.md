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

## U9d1 status — lane 319

Conditional delivery, **not unconditional persistence**. The checkout lacks
lane 318's PhysicalRecovery module and its status paragraph, and lacks lane
312's ForcePaths. `Persistence.lean` proves a common-horizon half-order
induction and real-order descent from the ONE input below. The next named
obligation is **U9d1-analytic follow-up: prove TorusHalfStepInput**; no lane
number is assigned here. The input still includes the endpoint Duhamel argument,
real-order nonlinear estimates and gain-3/2 heat smoothing. Existing heat
smoothing is only sigma=1. The forbidden whole-order kernel is (t-s)^(-1);
the intended half-order route uses (t-s)^(-3/4).

```lean
def TorusHalfStepInput : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (C : TorusTwoSpaceContract ν)
    (a : SpatialField) (g : SpaceTimeField) (T : ℝ),
    a ∈ initialClassT → ContDiff ℝ ∞ g → IsPeriodicOn univ g → 0 < T →
    ∀ (A : PeriodicSobolev 3) (F P u : ℝ → PeriodicSobolev 3),
      IsPeriodicDatum 3 a A → IsPeriodicSobolevPath 3 g F →
      (∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t)) →
      TorusForcedMildOn C A P T u →
      ∀ r : ℝ, 3 ≤ r → ∀ v : ℝ → PeriodicSobolev r,
        ContinuousOn v (Ico 0 T) →
        (∀ t ∈ Ico 0 T, IsPeriodicReweight 3 r (u t) (v t)) →
        ∃ w : ℝ → PeriodicSobolev (r + 1 / 2),
          ContinuousOn w (Ico 0 T) ∧
          ∀ t ∈ Ico 0 T, IsPeriodicReweight r (r + 1 / 2) (v t) (w t)

```

The physical result `torusForcedMildOn_persistence` uses canonical
`IsPeriodicReweight 3 m (u t) (u_m t)`, continuous on Ico 0 T and bounded on
all compact subsets. The brief's raw weighted-sequence equality erases the
Sobolev index and is trivial; `persistence_literal_target` records that defect,
not a physical bootstrap. No existing API statement is replaced. Non-vacuity:
actual mild solution u(t)=(1+t)e₁, nonzero force e₁, inhabited contract, and
explicit realizations at all orders. See ATTEMPTS_PERSISTENCE.md and REPORT_319.md.

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


## U9d2 status — lane 320 (partial; target remains open)

`ClassicalAssembly.lean` defines U9d1's exact local conclusion as follows:

```lean
def PersistenceInput (T : ℝ) (u : ℝ → PeriodicSobolev 3) : Prop :=
  ∀ m : ℕ, ∃ u_m : ℝ → PeriodicSobolev (m : ℝ),
    ContinuousOn u_m (Ico 0 T) ∧
      ∀ t ∈ Ico 0 T, ∀ i k,
        torusPhysicalCoeff (m : ℝ) (u_m t) i k = torusPhysicalCoeff 3 (u t) i k
```

The physical coefficient equality is proved equivalent to `IsPeriodicReweight`.
From it: the exact continuous all-order Sobolev field and C∞ spatial slices of
`torusPhysicalVelocity u`. From the exact mild equation and the original Leray
force graph: coefficient solenoidality, then physical divergence zero on Ico,
including zero. No smoothing estimate with a nonintegrable kernel is used.
The projected equation is proved for an existing ClassicalSolutionT via the
canonical convection identity; this does not supply the missing momentum equation.

The general U9d existential target above is unchanged and remains unproved even
with PersistenceInput. Time regularity (including initial-boundary joint smoothness),
physical pressure and its identities, momentum and final assembly remain open.
No further named input is introduced: this is explicitly a partial delivery,
not successful application of the complete single-further-input peeling fallback.
A common-horizon nonzero constant-force trajectory satisfies the input, the genuine
mild equation and full recovery together. All 26 named declarations pass exact
standard-three-axiom guards. Details: REPORT_320.md and ATTEMPTS_CLASSICAL_ASSEMBLY.md.

## U9d2a status — lane 326 (pressure; partial, target unchanged)

`Section3/T11/MildPressure.lean` **constructs** the pressure of the mild
solution and proves every pressure clause of `ClassicalSolutionT` except the
joint slab smoothness. Sole named input: lane 320's `PersistenceInput T u`; no
new `def … : Prop` is introduced, and no target statement is weakened.

The coefficient pressure is the genuine Leray complement, derived from
`Section3/T10/Leray.lean`'s symbol:

```lean
def lerayPotentialCoeff (S : SpatialField) (k : PeriodicFrequency) : ℂ :=
  if k = 0 then 0
  else (∑ j : Fin 3, (k j : ℂ) * sourceComponentCoeff S j k) /
    ((2 * Real.pi * Complex.I) * ((∑ j : Fin 3, (k j : ℝ) ^ 2 : ℝ) : ℂ))
```

with `mildPressureCoeff g u t := lerayPotentialCoeff (fun x ↦ mildPressureSource g u (t,x))`,
`mildPressureSource g u z = g z − convectionDivergenceT (torusPhysicalVelocity u) z.1 z.2`,
and the physical pressure `mildPressure g u` the scalar Fourier inversion
`Re ∑' k p̂(t)(k) e^{2πik·x}`. Its defining property is proved against the T10
symbol at every Sobolev order: for `k ≠ 0` and any `hB : IsPeriodicDatum s S B`,

```lean
periodicDerivativeSymbol i k * lerayPotentialCoeff S k =
  torusPhysicalCoeff s B i k - ((periodicFrequencyWeight k ^ (-s/2) : ℝ) : ℂ) * periodicLeray s B i k
```

Proved fields (bundled as the **conclusion** `MildPressureFields g u T`, built by
`mildPressure_fields` from `ContDiff ℝ ∞ g`, `IsPeriodicOn univ g` and
`PersistenceInput T u`): `pressure_periodic`, `pressure_gauge` (the zero mode is
the gauge), `pressure_gradient` (`MemLp` of the lifted gradient), spatial `C^∞`
of every slice, the gradient datum `(I − P)(F − Q)`, and
`PeriodicLocalRegularity.pressure_poisson` in its exact shape

```lean
scalarSpatialLaplacianT (mildPressure g u) t x =
  spatialDivergence g t x -
    spatialDivergence (fun z : SpaceTime ↦ convectionDivergenceT (torusPhysicalVelocity u) z.1 z.2) t x
```

proved by Fourier uniqueness from `−4π²|k|² p̂(k) = 2πi k·Ŝ(k)`, not by
term-by-term differentiation. The source is identified with `F − Q` at the level
of physical Fourier data (`mildPressureSourceCoeff_eq_force_sub_convection`).

The **canonical coefficient-side `F − Q`** is proved, not merely the physical
form: this lane supplies the missing **periodic convolution theorem**

```lean
theorem periodicFourierCoeff_mul {f g : Space → ℂ}
    (hpf : IsPeriodicSpatial f) (hsf : ContDiff ℝ ∞ f)
    (hpg : IsPeriodicSpatial g) (hsg : ContDiff ℝ ∞ g) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ f x * g x) k =
      ∑' l, periodicFourierCoeff f l * periodicFourierCoeff g (k - l)
```

and from it `periodicFourierCoeff_convection_eq_torusConvectionDatum`
(`periodicFourierCoeff ((∇·(u⊗u))_i(t,·)) k = torusPhysicalCoeff 2 (torusConvectionDatum (u t) (u t)) i k`),
`torusConvectionDatum_isPeriodicDatum`, `mildPressureSourceCoeff_eq_canonical`
(`Ŝ_j = torusPhysicalCoeff 3 (F t) j k − torusPhysicalCoeff 2 (torusConvectionDatum (u t) (u t)) j k`),
`mildPressure_gradient_canonical` (`∇p̂_i(k) = (k_i/|k|²)(k·(F̂−Q̂)(k))`) and
`mildPressure_gradient_leray_canonical` (the T10 `periodicLeray` complement taken
literally at `G₂ − Q`). Lane 327 can consume `periodicFourierCoeff_mul` directly.

The **coefficient pressure is in every `H^m`**: `mildPressure_scalar_datum`
exhibits `W(k)^{m/2} p̂(t)(k)` as a `T12.IsPeriodicScalarDatum (m : ℝ)` of the
slice, whence `mildPressure_memPeriodicHm : T12.MemPeriodicHmScalar m` for every
`m` and every `t ∈ Ico 0 T`. Both are bundled in `MildPressureFields`.

**The one residual is exactly**

```lean
pressure_smooth : ContDiffOn ℝ ∞ (mildPressure g u) (Ico (0 : ℝ) T ×ˢ (univ : Set Space))
```

and it is *not derivable* from the permitted input: `PersistenceInput` gives only
`ContinuousOn u_m (Ico 0 T)`, so no time derivative of `t ↦ p̂(t)(k)` exists yet.
It needs the still-open Duhamel differentiation of `TorusForcedMildOn`. Joint
*continuity* on the slab is likewise unproved; with the convolution theorem now
available its only remaining ingredients are a locally uniform all-order weighted
convolution bound (needs `W(k)^N ≤ 4^N (W(l)^N + W(k−l)^N)`, the
`ConvolutionBound.lean` shift being stated only at exponent 3) and continuity in
`t` of the convolution sums — see `ATTEMPTS_MILD_PRESSURE.md` §3.2.

Non-vacuity: a one-mode smooth periodic force together with the affine-constant
persistent path gives all the fields **and** a nonzero pressure slice
(`mildPressure_nonzero_instance`). The general U9d existential target above is
unchanged. Details: `REPORT_326.md`, probe `probes/mild_pressure_closes.lean`,
audit `axioms_mild_pressure.lean` (all 95 module declarations, every line exactly
the standard three axioms; the concrete lattice mode used by the non-vacuity
witness lives in the probe, so no module declaration has a smaller axiom set). Review and its resolution: `REVIEW_326-T11-U9d2a-pressure.md`,
`REPORT_326.md` §1 and `ATTEMPTS_MILD_PRESSURE.md` §0'.
## U9d1c status (lane 330)

`TorusHalfStepInput` is **proved**: `Section3/T11/DuhamelHalfStep.lean` contains
`theorem torusHalfStepInput : TorusHalfStepInput`, and with it
`persistence_halfOrder_ladder_unconditional` and `persistence_unconditional` —
lane 319's conditional persistence with its one named input discharged, on the
original horizon and with no shrinkage. The U9d1 residual recorded above is
therefore closed; the general U9d existential target (physical field, time
regularity, pressure, momentum) is unchanged and still open.

Route, with `σ = r + 1/2`:
`w(t) = e^{νtΔ}A′ + ∫₀ᵗ e^{ν(t−τ)Δ}P_σ(τ)dτ − ∫₀ᵗ S_frac(ν(t−τ))Q_r(v τ, v τ)dτ`.
`A′` is the order-`σ` datum of the smooth initial field; `Q_r` is lane 328's
real-order projected convolution `H^r × H^r → H^{r−1}`; `S_frac` is lane 329's
gain-`3/2` smoothing with the integrable endpoint kernel `(ν(t−τ))^{-3/4}`; the
exponents match exactly, `W^{3/4}W^{(r−3)/2} = W^{(σ−3)/2}W^{1/2}`.

Two things the brief's version of the route did not have. (i) The **force must
be used at the top order**: gaining `σ` derivatives from the order-three force
costs the kernel `(t−τ)^{-σ/2}`, integrable only for `σ < 2`, whereas `r ≥ 3` is
arbitrary. Hence `exists_continuous_lerayForcePath σ`, which builds a
*continuous* order-`σ` Leray force path from `ContDiff ℝ ∞ g` by taking the
integer-order continuous datum path of `Section3/T10/ForcePaths.lean` at
`m = ⌈σ⌉₊`, descending with the bounded `persistenceDown`, and projecting with
(ii) the new **bounded Leray operator at every real order**,
`torusLerayCLM (s : ℝ) : PeriodicSobolev s →L[ℝ] PeriodicSobolev s`
(`Section3/T10/Leray.lean` only had an existential), which commutes with order
transport and is unique, so the hypothesis' `P t` is literally `torusLerayCLM 3 (F t)`.

Integrability and continuity of the singular Duhamel term are not re-proved: the
module builds a genuine
`MNS2.EndpointSafeTwoSpaceDuhamelContract ℝ (PeriodicSobolev (r+1/2)) (PeriodicSobolev (r-1))`
(`torusFracContract`) out of lanes 328/329, so HeliCorgi's endpoint-safe theory
applies verbatim; continuity on the half-open `Ico 0 T` is obtained from closed
subwindows. All 45 declarations pass exact standard-three-axiom guards.
Details: `REPORT_330.md`, `ATTEMPTS_DUHAMEL_HALF_STEP.md`.

## U9d2b status — lane 327 (Duhamel time differentiation and the momentum equation)

`formalization/NSFormalization/Section3/T11/MildMomentum.lean` (74 declarations,
no named input beyond `PersistenceInput`, no `def … : Prop`).

* **Closed (i):** every Fourier coefficient of a forced mild solution is
  differentiable at every interior time with
  `d/dt û(t)(k) = −ν·4π²|k|²·û(t)(k) + (P̂(F − Q(u,u)))^(t)(k)`, in the weighted
  `H³` coefficients (`mild_coeff_hasDerivAt`) and in the physical ones
  (`mild_physicalCoeff_hasDerivAt`).  The route is: coefficient functional →
  scalar Duhamel identity (`mild_coeff_duhamel`) → forced scalar ODE
  (`heat_duhamel_hasDerivAt`, FTC + the heat-symbol product rule).
* **Closed (ii), first order:** `torusPhysicalVelocity u` is differentiable in
  time on `Ioo 0 T ×ˢ univ`, with derivative the Fourier series
  `mildTimeDerivative C P u t` (`torusPhysicalVelocity_hasDerivAt`,
  `temporalDerivative_torusPhysicalVelocity'`); that field is `C^∞` and periodic
  in `x`.  Continuity up to `t = 0` is lane 318's
  `torusForcedMildOn_physical_continuous`.
* **Closed (iii):** `momentum_of_pressure` proves the exact
  `ClassicalSolutionT.momentum` field, and `projected_of_pressure` the exact
  `PeriodicLocalRegularity.projected` field, for any pressure whose gradient has
  the Leray-complement data `(I−P)(F−Q)`; `momentum_of_mildPressure` /
  `projected_of_mildPressure` instantiate them with lane 326's constructed
  `mildPressure g u`.
* **New general tools:** the weight submultiplicativity `W(k) ≤ 2W(l)W(k−l)`
  with the one-power-gain convolution estimate `convolution_norm_bound`, the
  frequency-local Leray symbol `lerayAt`, and `torusPhysicalCoeff_bilinear`
  showing the contract's bilinear map is exactly the Leray projection of lane
  326's canonical `torusConvectionDatum`.  The periodic convolution theorem and
  the convection identification are reused from the merged lane 326
  (`periodicFourierCoeff_mul`,
  `periodicFourierCoeff_convection_eq_torusConvectionDatum`); the dedupe after
  the merge is recorded in `ATTEMPTS_MILD_MOMENTUM.md` §5.
* **Force-side persistence is discharged, not assumed:**
  `persistenceInput_force_of_smooth` derives `PersistenceInput T F` from
  `ContDiff ℝ ∞ g`, `IsPeriodicOn univ g` and `IsPeriodicSobolevPath 3 g F`
  (`CriterionBridge.exists_periodicDatum_smooth` +
  `T10/ForcePaths.continuous_datum_path`), so `PersistenceInput T u` is the only
  named input of the lane.
* **Still open:** the *joint* `C^∞` fields
  `ContDiffOn ℝ ∞ (torusPhysicalVelocity u) (Ico 0 T ×ˢ univ)` and
  `ContDiffOn ℝ ∞ (mildPressure g u) (Ico 0 T ×ˢ univ)`.  Iterating the time
  derivative needs the mild equation at Sobolev orders `5, 7, …`;
  `TorusForcedMildOn` is an `H³ × H²` statement and `PersistenceInput` gives only
  continuity at the higher orders.  See `REPORT_327.md` §3 and
  `ATTEMPTS_MILD_MOMENTUM.md` §3.1.

## U9d2c status — lane 334 (the U9d target is closed)

`formalization/NSFormalization/Section3/T11/MildClassical.lean` (1383 lines,
77 declarations) proves

```lean
theorem mild_to_classical (ν : ℝ) (hν : 0 < ν) (C : TorusTwoSpaceContract ν)
    (a : SpatialField) (g : SpaceTimeField) (T : ℝ)
    (ha : a ∈ initialClassT) (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g) (hT : 0 < T)
    (A : PeriodicSobolev 3) (F P u : ℝ → PeriodicSobolev 3)
    (hA : IsPeriodicDatum 3 a A) (hF : IsPeriodicSobolevPath 3 g F)
    (hPL : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    (hu : TorusForcedMildOn C A P T u) :
    ∃ w : ClassicalSolutionT ν a g T,
      PeriodicLocalRegularity ν a g T w ∧
      IsPeriodicSobolevPathOn 3 (Ico 0 T) w.velocity u
```

i.e. **the U9d existential target above, verbatim and with no named input**.
`PersistenceInput T u` (lane 320) is discharged from lane 330's
`persistence_unconditional`; `PersistenceInput T F` and
`ContinuousOn P (Icc 0 T)` are discharged from the smoothness of `g`.

The two residuals recorded by lanes 326 and 327 are proved:

```lean
ContDiffOn ℝ ∞ (torusPhysicalVelocity u) (Ico (0:ℝ) T ×ˢ (univ : Set Space))   -- torusPhysicalVelocity_contDiffOn
ContDiffOn ℝ ∞ (mildPressure g u)        (Ico (0:ℝ) T ×ˢ (univ : Set Space))   -- mildPressure_contDiffOn
```

together with `PeriodicLocalRegularity.sobolev_smooth`
(`ContDiffOn ℝ ∞` of the order-`m` Sobolev datum path), which needs the same
machinery.

**Route.**  Each time derivative costs two Sobolev orders and lane 330 supplies
every order, so the induction never runs out.  In `H^m`,

`v_m(b) = v_m(0) + ∫₀ᵇ (νΔ v_{m+2}(s) + P_m(s) − Q_m(s)) ds`,

with `νΔ : H^{m+2} →L H^m` the bounded multiplier `−ν·4π²|k|²·W(k)⁻¹`,
`P_m = torusLerayCLM m ∘ F_m` and `Q_m` lane 328's real-order projected
convolution of `v_{m+3}` descended one order.  Coefficientwise this is lane
327's `mild_physicalCoeff_hasDerivAt` plus the one-sided scalar FTC; as a
Banach-valued identity it yields `HasDerivWithinAt v_m (…) (Ico 0 T) t` and
therefore `ContDiffOn ℝ (j+1)` from `ContDiffOn ℝ j`, by induction on `j`
uniformly in `m` (`mildTower_contDiffOn`).  The order-`m` datum path of the
smooth force is `C^∞` in time by the same argument, with differentiation under
the **cube** integral as the scalar input (`datumPath_contDiff`).

Joint smoothness on the half-open slab needs no `contDiffOn_tsum` (there is
none in Mathlib): the Fourier inversion is packaged as a *functional*-valued
series `torusEvalSeriesCLM s i x = ∑' k, χ_k(x) • (coefficient functional)`,
whose terms are bounded by `W(k)^{-s/2}` uniformly in `x`, so `contDiff_tsum`
gives `ContDiff ℝ n` in `x` as soon as `2n + 6 ≤ s`; the field is then the
bounded bilinear evaluation of that family against the smooth path `v_s`, and
`ContDiffOn ℝ ∞ = ∀ n, ContDiffOn ℝ n` lets `s` depend on `n`.

For the pressure the **projected** convolution is useless (the Leray-projected
convection is divergence free, so the pressure potential annihilates it), so the
lane builds the unprojected real-order convolution as a genuine bounded bilinear
map `torusConvUnprojCLM` (lane 328 exports the norm bound but keeps bilinearity
`private`) and the Leray potential as the bounded operator
`pressurePotentialCLM` with symbol `−2πik_j/(4π²|k|²)`; `sum_pressureSymbol_eq`
identifies it with lane 326's `lerayPotentialCoeff`.

**Corollary** `exists_classical_of_picard`: for every `ν > 0`, every
`a ∈ initialClassT` and every smooth unit-periodic `g` there are `δ > 0` and a
`ClassicalSolutionT ν a g δ` with all three regularity clauses — unconditional.
This is **not** `PeriodicQuantitativeLocalInput'`: the horizon depends on `‖A‖`
and on a force supremum, so `Restart.lean`'s named U9e input is unchanged.

Non-vacuity: `mild_to_classical_affine_constant` instantiates every hypothesis
on the constant-force affine family over an arbitrary `T > 0`; the probe takes
`c = coordinateVector 0` and shows the produced classical velocity is nonzero.
All 77 declarations pass exact standard-three-axiom guards.  Details:
`REPORT_334.md`, `ATTEMPTS_MILD_CLASSICAL.md`,
`probes/mild_classical_closes.lean`, `axioms_mild_classical.lean`.
