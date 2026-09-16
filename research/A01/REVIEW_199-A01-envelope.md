REJECT

## 1. What the lane claims

Reviewed HEAD `376a7b1411fe312465c118344bcb09a997e9767f`; integration ref `86d5bf867d5a33a002a1a9ab9140fced8306cde7`. This is a **scope rejection, not a discovered false Lean theorem**. The brief asks for both general-data predicates, allowing a fallback that closes one and isolates the other. Neither is closed. `research/A01/REPORT_199.md:9` and `research/A01/ATTEMPTS_ENVELOPE.md:5` accurately disclose that limitation; `research/A01/A3_SPLIT.md:69` and :70 correctly remain OPEN/CONDITIONAL. The useful partial results can be retained, but they do not meet that fallback.

Read CLAUDE.md, lane-review/SKILL.md, LESSONS top 40, HANDOFF §0/P7, the 198 report/review, both preceding attempts records, and the 199 report/attempts. The existing package symlink was verified; no installer or git mutation was needed. Only this new report and permitted rev199 probes were written. Here M = `formalization/NSFormalization/Section4/A01/MildEnergyEnvelope.lean`, P = `formalization/NSFormalization/Section4/A01/MildEnergyPremises.lean`, G = `formalization/NSFormalization/Section4/A01/MildGronwall.lean`, V = `vendor/NavierStokesAndEuler/Euler/`, and Mathlib paths are under `verification/.lake/packages/mathlib/Mathlib/`.

All seven Lean snippets in REPORT_199 match the actual source after whitespace normalization: regularized theorem M:72, explicit function M:96, four conditional exports M:214/:233/:243/:253, and predicate M:200. The other advertised declarations exist at M:17/:50/:101/:118/:121/:128/:135/:160/:186/:190. E(q) is the existing `mildNormConstant` G:22, sqrt(card(SobolevWord(q+1))); **no general-data A(q) is supplied** (REPORT_199:111). The conditional theorems use arbitrary fixed E,A with hE and hcomparison, not a hidden construction of constants.

Opened the paper with `sed -n '17,18p;129,145p' paper/sections/appendix-a-local-theory.tex`: :17 is the tensor tame bound; :132–136 is the signed H^m energy inequality; :140–145 removes the scalar norm regularization and obtains high-order continuation. Lane 199 supplies preparatory cylinder and scalar results, not that full argument.

## 2. What is in Lean

### Signed identity and exact vendor composition

The actual competitor theorem is M:72–87 (quoted verbatim):

```lean
theorem regularized_full_energy_hasDerivAt {q : ℕ} (n : ℕ)
    {ν S T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hTS : T ≤ S)
    (D : Coefficients (Icc (0 : ℝ) S) (SobolevSpace 1 (q+1)) (SobolevSpace 1 q))
    (u₀ : SobolevSpace 1 (q+1)) (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (hu : ∀ t, u t = quadraticDuhamel 1 ν hν hT hTS D u₀ u t)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    let v := fun (W : SobolevWord (q+1)) r => extendPath T hT
      (EulerRegularizedWordEquation.regularizedWordPath 1
        (Nat.le_of_lt_succ W.1.isLt) n W.2 T u) r
    let f := fun W : SobolevWord (q+1) => extendPath T hT
      (EulerRegularizedWordTime.sourceWordPath 1 (Nat.le_of_lt_succ W.1.isLt) n W.2 T
        (sourcePath (D.comp (timeInclusion hTS)) u)) t
    HasDerivAt (fun s => familyEnergy (ContinuousLinearMap.id ℝ (LiftL2 1))
      (fun W => value 1 (v W s)))
      (2 * ∑ W, ⟪value 1 (v W t), f W⟫_ℝ -
        2 * ν * ∑ W, ∑ i : Fin 4, ‖(toJet 1 (v W t)).word (fun _ : Fin 1 => i)‖^2) t
```

This is the full `SobolevWord(q+1)` family, including shorter words, at identity metric and for each regularization index n. The source is the actual `sourcePath (D.comp (timeInclusion hTS)) u`, not an assumed independent forcing estimate. M:91 supplies each derivative using V`RegularizedForcingWord.lean:55`:

```lean
theorem regularized_word_hasDerivAt_clamped {q m : ℕ} (hm : m ≤ q+1) (n : ℕ) (w : Fin m → Fin 4)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : SobolevSpace period (q+1)) (f : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q+1)))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period (q+1) (2*ν*t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r (extendPath T hT f (t.val-r)))
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => value period (extendPath T hT (regularizedWordPath period hm n w T u) r))
      (ν • jetLaplacian period (toJet period (extendPath T hT (regularizedWordPath period hm n w T u) t)) +
        extendPath T hT (sourceWordPath period hm n w T f) t) t
```

M:57 composes V`FiniteMetricEnergy.lean:98`:

```lean
theorem family_energy_hasDerivAt (K : ℝ → H →L[ℝ] H) (e : ι → ℝ → H)
    (t ν : ℝ) (K' : H →L[ℝ] H) (e' transport pressure forcing lap : ι → H)
    (hK : HasDerivAt K K' t) (he : ∀ i, HasDerivAt (e i) (e' i) t)
    (hsym : ∀ v w, ⟪K t v, w⟫_ℝ = ⟪v, K t w⟫_ℝ)
    (heq : ∀ i, e' i + transport i + pressure i = forcing i + ν • lap i)
    (hp : ∀ i, ⟪K t (e i t), pressure i⟫_ℝ = 0) :
    HasDerivAt (fun s => familyEnergy (K s) (fun i => e i s))
      (∑ i, (⟪K' (e i t), e i t⟫_ℝ + 2 * ⟪K t (e i t), forcing i + ν • lap i⟫_ℝ -
        2 * ⟪K t (e i t), transport i⟫_ℝ)) t
```

M:41 composes V`MetricHeatEnergy.lean:73`:

```lean
theorem metric_second_derivative_identity (K : SmoothCoefficient period) (a : LiftTangent)
    (f f' f'' : LiftL2 period)
    (hf : HasDerivAt (fun t => translation period (translationPath period a t) f) f' 0)
    (hf' : HasDerivAt (fun t => translation period (translationPath period a t) f') f'' 0) :
    ⟪K.operator f, f''⟫_ℝ = -⟪K.operator f', f'⟫_ℝ -
      ⟪directionalCoefficientOperator period K a f, f'⟫_ℝ
```

M:36–45 proves that the identity metric's directional coefficient operator vanishes; M:19 gives exactly `inner(f,jetLaplacian J) = -sum i, norm(J.word i)^2`. M:55–56 retains **−2ν** times the gradient-square sum in the derivative, hence **−ν** in half the derivative. No Young absorption or dropped dissipation enters this identity. The abstract family lemma uses zero transport/pressure because these are left inside the unaltered projected source; it does not assert that Navier–Stokes transport itself is zero.

**Regularization is not removed anywhere in M.** The scalar construction M:160 is independent of the regularized identity M:72. The missing signed-limit/comparison link is expressly named at M:197. This matches the report, but does not finish the paper's approximation argument.

### Scalar ODE and envelope

M:96 defines `y(t)=exp(integral 0..t α)*(c+b*integral 0..t exp(-integral 0..s α))`. M:101 uses `intervalIntegral.integral_hasDerivAt_right`, the exponential derivative and product rule to prove `y'=αy+b` **at every real t** when α is continuous. M:118 proves y(0)=c; M:121 proves nonnegativity for b,c,t≥0. The cylinder driver is the continuous clamped function `k=A*(16*norm(restrictOperator ... u))` (M:186–195), so α=k²/(4ν) is continuous.

M:146–157 constructs x=y², d=2y(k²y/(4ν)+b), g=ky/(2ν). M:178–183 proves local equality of the clamp and global y on every interior neighborhood. Thus the derivative is everywhere on Ioo, not merely almost everywhere; no unjustified differentiation of a TimeLp representative occurs. The initial value used downstream is c=E‖ordinarySobolev(q+1)a‖, and b=E‖sobolevPath F hF(q+1)‖ (M:222–224).

M:128–132 proves `½d+νg²=k*y*g+b*y` as equality. Reviewer probe `research/A01/probes/rev199_algebra.lean:3` independently kernel-checks substitution k=A(16 low) with α=(A²/(4ν))*(256 low²). The exact intended A²/(4ν) is retained. M:248 exports that same coefficient to MildGronwall.

**Uniqueness is not proved or invoked in this lane.** An explicit definition establishes existence, not by itself a uniqueness theorem. This omission does not invalidate the envelope witness. For the requested uniqueness check, the mathematical route is to subtract two solutions and differentiate `exp(-integral α)*(y1-y2)`, obtaining zero derivative and equality from the initial value. Alternatively use Mathlib `Analysis/ODE/ExistUnique.lean:193`, `ODE_solution_unique_of_mem_Icc_right`, with a compact-interval bound on |α| as its Lipschitz constant; :326 `ODE_solution_unique` asks for a uniform-in-time Lipschitz constant, so arbitrary continuous α cannot be plugged into that global hypothesis without a restriction/bound. No uniqueness claim in REPORT_199 is falsely advertised.

### Named input, non-vacuity, and hygiene

Exact remaining predicate (M:200–211):

```lean
def CylinderRootComparison {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) (E A : ℝ) : Prop :=
  ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))),
    (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
      (coefficients 1 hq (sobolevPath F hF q))
      (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t) →
    ∀ t, energyRootPath u t ≤
      energyComparison (fun s => (cylinderEnvelopeDriver hq hT A u s)^2/(4*ν))
        (E * ‖sobolevPath F hF (q+1)‖)
        (E * ‖ordinarySobolev (q+1) a.toLp a.translation_contDiff‖) t
```

The final `t` is inferred as `Icc 0 T` by `energyRootPath u t`: it does not quantify over negative times or outside the horizon. Constants precede the window and competitor. For solenoidal a and appropriately chosen constants, classify this as **(a): a restriction of the standard limiting-root comparison fact**, not an extra smoothness/extension requirement. It is stronger than merely bounding the cylinder max-word norm, but the full Euclidean family is the intended energy and G:38 gives its norm comparisons. The predicate itself has no ha binder; the intended supply theorem must take ha, as M:214 does. It is not claimed true for arbitrary E,A or arbitrary nonsolenoidal data. There is no nonzero-data proof in this lane.

M:239 deliberately ignores U, hU, the integrated estimate and the forcing bound: root comparison directly supplies FiniteMildEnergy. Thus ForcingFamilyBound is **not a second premise of this new chain**; it is a separately unfinished target. The `ha` proof is carried by FiniteMildEnergy's interface; its mathematical solenoidality content must be used when proving hcomparison. These unused/interface binders do not make the conditional theorem false, but they prevent describing it as the requested analytic conversion proof.

Zero-data examples are genuine: `research/A01/axioms_envelope.lean:44` proves zero mildness, :58 proves comparison for **all** competitors by `quadratic_mild_unique_window`, and :74/:83 apply the new theorems with ν=S=1, E=mildNormConstant q and A=1. The horizon is positive; neither target nor comparison is assumed. :93/:96 also check nonstationary scalar y=1+t and y=t. No extra zero-instance probe was necessary. These examples do not establish nonzero PDE satisfiability.

There are 17 named module declarations plus four zero helpers, all 21 auditing to exactly `[propext, Classical.choice, Quot.sound]`. The new module and conformance file have no forbidden proof tokens or heartbeat overrides. M uses actual real norms, with no ENNReal.toReal loophole; the contemplated real tame bridge explicitly requires finiteness (`A04/HighEnergy.lean:164–167`). T=0 is allowed, not forced; positive windows are tested. No all-order constructor or ClassicalSolutionR-level theorem is applied to the mild path.

The three-dot lane diff is exactly one new Lean module plus four records (only A3_SPLIT is modified), 5 files/705 insertions/2 deletions. No verification file was touched. The requested **two-dot stat is not just the new module plus records**: integration advanced and it reports integration-only modules such as ConstructorAssembly and PressureRegularity as deletions. This is branch drift, not an edit by lane 199. Exact stat is recorded below. `experiments/build_changed_lean.py:13–20` includes new formalization modules; its dry run selects MildEnergyEnvelope, so it is covered by the changed-module mechanism even though make test's registered closure alone is not its conformance audit.

## 3. Gaps and fixes

1. **Blocking — neither original target closed.** M:237 requires CylinderRootComparison for EnvelopeConversion; P:314 remains only the ForcingFamilyBound definition. Missing-target probe `research/A01/probes/rev199_targets.lean:2` reproduces three Unknown identifier errors, quoted below. This is consistent with REPORT_199:9–14, but violates the brief's “if only one ... closes, deliver it” fallback. Fix: supply at least one requested general-data target with fixed explicit constants and isolate the other exact residual; full completion additionally needs both targets and unconditional downstream exports. Keeping this as a separately scoped preparatory lane is a lead decision, not a one-line proof fix.
2. **Follow-up — scalar uniqueness.** Add the uniqueness theorem if the acceptance scope includes the lead's existence/uniqueness checkpoint; M:101/:118 currently supplies only the explicit solution and initial value. No need to change the successful envelope construction.
3. **Record note — diff/silence.** Build exits 0 with dependency warning replay, while the module itself is silent and direct checking produces zero bytes. The current two-dot stat is not module+records only; use the three-dot lane diff to attribute changes and retain the branch-drift qualification.

**Search audit.** Ran `grep -rnE` over the entire `formalization/NSFormalization/Section4` tree, separately for commutator/ForcingFamilyBound/CylinderRootComparison/signed limits/word and tensor pairing/tame lemmas and for energyComparison/forcing words/root comparison/word descent/regularized limits/ODE uniqueness (logs `/tmp/rev199_search.log`, `/tmp/rev199_gap_search.log`). This checks each reported gap: forcing identification and quantitative family norm, physical/cylinder pairing, finite tame bound on this carrier, signed limit, scalar comparison, and general-data constants/exports. Searches find substantial reusable mathematics, so a blanket “no word bridge/no nonlinear estimate in the tree” would be wrong. In particular `A01/L2Descent.lean:142/:157/:200` already descends all spatial words, but requires angular invariance and, for the jet comparison, a smooth representative. `A01/OrderTwoCap.lean:129` supplies the factor 16 with honest finite norms. `A04/NonlinearBound.lean:131` is a generic datum pairing bound with explicit slice/data premises; :185 is ClassicalSolutionR-specific and cannot be used on this mild path. None of these opened candidates discharges the final predicate as stated. The report's narrower “unfinished on the actual carrier” claim is supported; absence of useful machinery is not.

**Concrete signed-limit/comparison route.** Start with M:72 on every n. Obtain the genuine maximal limit with P:137 (`exists_maximal_mild_limit`, not a wrapper discarding convergence). V`RegularizedWordTime.lean:80` `regularizedWordPath_first_tendsto` gives strong time-L² H¹ convergence of each energy word, hence gradient-square integrals; :51 `sourceWordPath_time_tendsto` supplies the source convergence with `ForcedSourceUpgrade.sourceTime_restriction` (P:292). G:71 `euclidean_full_word_limit` and V`RegularizedEnergyFamily.lean:44` give uniform root/value-family convergence. Integrate the signed identity on interior subintervals, pass products using L²×L²→L¹ convergence and squares using strong L² convergence, then recover endpoints by continuity/integrability. This is precisely where spatial heat regularization should be removed; P:205–207's existing root estimate already dropped viscosity and cannot replace this step. Identify the finite cylinder/ordinary tensor pairing, use `A03/OuterTameProduct.lean:177`, `A04/HighEnergy.lean:164` with both finiteness proofs, then generic `inner_energy_Rhigh` at :136 and G:38 norm constants. For the root, use sqrt(energy+ε²) to handle zeros, absorb with the exact coefficient and pass ε↓0. An integrating factor gives comparison with M:96; Mathlib `Analysis/ODE/Gronwall.lean:112` is a relevant one-sided derivative comparison tool, but its constant K form does not directly supply variable α, nor does `ODE_solution_unique` prove an inequality from an a.e. derivative. Establish the absolute-continuity/integral comparison step explicitly. This is a concrete proof route, not a claim those assembled steps are already kernel-proved.

Exact `ForcingFamilyBound` (P:314–328):

```lean
def ForcingFamilyBound {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) (E A : ℝ) : Prop :=
  ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))),
    (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
      (coefficients 1 hq (sobolevPath F hF q))
      (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t) →
    ∀ U : TimeLp T (SobolevSpace 1 (2+q)),
      Filter.Tendsto (fun n => pathLp T hT (maximalApproximation 1 q T n u)) Filter.atTop (𝓝 U) →
      ∀ᵐ r ∂timeMeasure T,
        extendPath T hT (energyRootPath u) r * cylinderEnergyForcing hq hT hTS F hF u U r ≤
          A * (16 * ‖restrictOperator 1 (Nat.succ_le_succ hq) (extendPath T hT u r)‖) *
            extendPath T hT (energyRootPath u) r * energyGradientNorm U r +
          (E * ‖sobolevPath F hF (q+1)‖) * extendPath T hT (energyRootPath u) r
```

**Separate ForcingFamilyBound route.** Exact predicate is P:314–328: for every actual competitor and every strong maximal limit U, almost everywhere `root*Z ≤ A*(16*low)*root*energyGradientNorm U + (E*norm(forcePath))*root`. V`RegularizedForcingWord.lean:73–81` defines each limiting word as word(source)+transport(word state)+word(pressure); V`WeightedForcingTime.lean:34` identifies Z as the actual family norm, not a signed pairing. Leray source plus positive gradient-complement pressure reconstructs raw force−advection (P:25/:34/:56/:260); adding transport(word state) leaves force words minus transport commutators. Vendor `ExternalTransportCommutator.lean:38` `transportCommutator_eq_sum` identifies the scalar product commutators and :66 `transportCommutatorNorm_bound` bounds them by a derivative convolution. `SobolevTransportCommutator.lean:70` and :111 provide Sobolev/pointwise commutator identification, but with smooth representatives and H⁶/external-word indexing. These must be adapted to the actual full finite family, finite regularity and a.e. Bochner representative, then bounded with data-independent constants and the intended low/high factors. The A03 tame estimate and A04 real conversion help control products; `inner_energy_Rhigh` alone bounds only a signed pairing and does not imply a family-norm estimate. V`RegularizedForcingWord.lean:84` and `WeightedForcingTime.lean:51` already provide strong forcing limits; they do not supply that quantitative bound. The existence of these vendor commutator lemmas is explicitly acknowledged, not treated as missing.

**Lanes 200/201.** Give lane 200 the actual-carrier source+pressure/word-commutator identification and a quantitative full-family bound with explicit E(q),A(q), preserving the finite-order mild carrier; reuse the generic A03/A04 and vendor commutator ingredients above, proving every finiteness/representative premise. Give lane 201 the signed integrated limit from M:72, scalar regularized-root comparison (including the zero-root limit and endpoints), and the supply theorem for CylinderRootComparison, then compose M:214/:243/:253; add scalar uniqueness there. Their interfaces must share the exact word family, constants and maximal limit. Until that work is done, A3-M2 remains open.

## 4. Commands and results

All Lean commands: `. scripts/lean-env.sh`, `export LEAN_NUM_THREADS=6`; lake ran only from verification/, one invocation at a time. make commands ran from the worktree root. Every positive gate exited 0, including the separately run make test (the gates script's filtered test output alone would not suffice). No verification changes required the extra gates, but they were run anyway. Below are exact outputs, bounded to the first/last 40 lines per command; empty logs are indicated outside code fences.

### `lake build NSFormalization.Section4.A01.MildEnergyEnvelope`

Exit 0; 219 output lines, 12820 bytes.

First 40 lines:

```text
⚠ [8927/9481] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [h]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:39:23: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [insert, coord]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [10092/10248] Replayed Formal.R3LerayFrequencySymbol
warning: ../vendor/HeliCorgi/Formal/R3LerayFrequencySymbol.lean:43:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [10112/10248] Replayed NSFormalization.Source.RealSobolev
warning: NSFormalization/Source/RealSobolev.lean:90:30: This simp argument is unused:
  Complex.smul_re

Hint: Omit it from the simp argument list.
  [apply] simp [Complex.smul_im]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/RealSobolev.lean:90:47: This simp argument is unused:
  Complex.smul_im

Hint: Omit it from the simp argument list.
  [apply] simp [Complex.smul_re]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/RealSobolev.lean:90:64: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
```

[Middle omitted.] Last 40 lines:

```text
⚠ [10153/10248] Replayed Formal.R3LerayComplexFiberSymbol
warning: ../vendor/HeliCorgi/Formal/R3LerayComplexFiberSymbol.lean:42:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
ℹ [10168/10248] Replayed NSFormalization.Source.PhysicalBesselSobolev
info: NSFormalization/Source/PhysicalBesselSobolev.lean:134:4: Try this:
  [apply] ring_nf

  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.

  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
⚠ [10173/10248] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [10176/10248] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  [apply] simp [viscosityVelocity, dilateField, viscosityHomeomorph, Prod.map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [10190/10248] Replayed NSFormalization.Paper3.SobolevDirectionalDerivative
warning: NSFormalization/Paper3/SobolevDirectionalDerivative.lean:103:16: `SchwartzMap.smul_apply` has been deprecated: Use `smul_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).
⚠ [10240/10248] Replayed NSFormalization.Section4.A01.AprioriFamily
warning: NSFormalization/Section4/A01/AprioriFamily.lean:148:31: Variable name `ha` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _ha

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [10241/10248] Replayed NSFormalization.Section4.A01.MildGronwall
warning: NSFormalization/Section4/A01/MildGronwall.lean:150:31: Variable name `ha` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _ha

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (10248 jobs).
```

### `lake env lean ../formalization/NSFormalization/Section4/A01/MildEnergyEnvelope.lean`

Exit 0; 0 output lines, 0 bytes.

No output.

### `lake env lean ../research/A01/axioms_envelope.lean`

Exit 0; 31 output lines, 2487 bytes.

```text
'NSFormalization.Section4.A01.identity_jetLaplacian_pairing' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.full_word_energy_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.regularized_full_energy_hasDerivAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.energyComparison' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.energyComparison_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.energyComparison_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.energyComparison_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.energyComparison_balance' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.squared_comparison_envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.comparison_envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderEnvelopeDriver' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderEnvelopeDriver_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.CylinderRootComparison' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.finiteMildEnergy_of_rootComparison' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.envelopeConversion_of_rootComparison' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.mildGronwall_of_rootComparison' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.hb_of_base_of_rootComparison' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.NSFormalization.Section4.A01.zero_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.NSFormalization.Section4.A01.zero_sob' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.NSFormalization.Section4.A01.zero_mild' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.NSFormalization.Section4.A01.zero_comparison' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `make check`

Exit 0; 28234 output lines, 1159606 bytes.

First 40 lines:

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 514,
    "vendor/NavierStokesAndEuler": 2486,
    "vendor/HeliCorgi": 129
  },
  "source_manifest_entries": 2975,
  "missing_copied_imports": [],
  "citation_interfaces_reachable": [],
  "tokens_in_copied_umbrella_closure": [
    {
      "module": "NSFormalization.Paper1.BoundaryCorollary",
      "path": "formalization/NSFormalization/Paper1/BoundaryCorollary.lean",
      "line": 90,
      "token": "sorry"
    }
  ],
  "tracked_cache_free": true,
  "source_hashes_match": false
}
Explicit axiom/admission tokens, all copied sources: 11
python3 experiments/check_contracts.py
{
  "registered_contracts": 29,
  "closures": {
    "R41.threshold_arithmetic": [
      "Bindings.Thresholds",
      "Contracts.V1.Thresholds",
      "NSFormalization.Paper3.Thresholds",
      "TestSupport.Axioms",
      "Tests.Thresholds"
    ],
    "I01.packet": [
      "Bindings.Packet",
      "Contracts.V1.Packet",
      "NSFormalization.Paper1.ScalarEnergy",
      "NSFormalization.Section4.I01.Energy",
      "NSFormalization.Section4.I01.Extension",
```

[Middle omitted.] Last 40 lines:

```text
      "NavierStokes.TransitionRamp",
      "NavierStokes.TransportPrimitive",
      "NavierStokes.TrueConeLoop",
      "NavierStokes.UniformAngularReset",
      "NavierStokes.UniformBlockBounds",
      "NavierStokes.UniformCone",
      "NavierStokes.UniformFourierAlias",
      "NavierStokes.UniformHarmonicInteraction",
      "NavierStokes.UniformPrimaryWeights",
      "NavierStokes.ValidBandGluing",
      "NavierStokes.ValidDyadicBandCover",
      "NavierStokes.VariableGaugeMean",
      "NavierStokes.ViscousPropagator",
      "NavierStokes.VolterraAnalyticBounds",
      "NavierStokes.VolterraParity",
      "NavierStokes.VolterraRegularity",
      "NavierStokes.WaveEdgeExtension",
      "NavierStokes.WaveEnvelopeTransport",
      "NavierStokes.WaveInteractionBounds",
      "NavierStokes.WaveStateRegularity",
      "NavierStokes.WeightedClasses",
      "NavierStokes.WeightedODEJets",
      "NavierStokes.WeightedQuotients",
      "NavierStokes.WeightedRadialPrimitive",
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.GradientL6V2"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.043s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

### `make test`

Exit 0; 344 output lines, 21755 bytes.

First 40 lines:

```text
lake -d verification test
⚠ [8778/9011] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [h]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:39:23: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [insert, coord]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [9876/10573] Replayed NSFormalization.Source.BoundedReferenceFlux
warning: NSFormalization/Source/BoundedReferenceFlux.lean:17:5: Variable name `hU0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hU0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9877/10573] Replayed NSFormalization.Source.BoundedReferenceComparison
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:34: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:76: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
ℹ [10242/10573] Replayed Tests.Thresholds
info: Tests/Thresholds.lean:13:0: Contract BlowupDensity.Tests.checkedThresholds: checked; standard logical axioms only
⚠ [10248/10573] Replayed NSFormalization.Source.RieszPotentialNearField
warning: NSFormalization/Source/RieszPotentialNearField.lean:21:17: Variable name `hR` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hR
```

[Middle omitted.] Last 40 lines:

```text

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: NSFormalization/Source/FractionalRealization.lean:104:2: Try this:
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
ℹ [10548/10573] Replayed Tests.GradientL6V2
info: Tests/GradientL6V2.lean:22:0: Contract BlowupDensity.Tests.checkedGradientL6V2: checked; standard logical axioms only
ℹ [10553/10573] Replayed Tests.EnergyHighPartialV2
info: Tests/EnergyHighPartialV2.lean:30:0: Contract BlowupDensity.Tests.checkedEnergyHighPartialV2: checked; standard logical axioms only
ℹ [10556/10573] Replayed Tests.DatumLemmasV3
info: Tests/DatumLemmasV3.lean:31:0: Contract BlowupDensity.Tests.checkedDatumLemmasV3: checked; standard logical axioms only
ℹ [10557/10573] Replayed Tests.Correction
info: Tests/Correction.lean:19:0: Contract BlowupDensity.Tests.checkedCorrection: checked; standard logical axioms only
ℹ [10558/10573] Replayed Tests.MaximalPartial
info: Tests/MaximalPartial.lean:16:0: Contract BlowupDensity.Tests.checkedMaximalPartial: checked; standard logical axioms only
ℹ [10559/10573] Replayed Tests.Uniqueness
info: Tests/Uniqueness.lean:16:0: Contract BlowupDensity.Tests.checkedUniqueness: checked; standard logical axioms only
ℹ [10560/10573] Replayed Tests.HomogeneousNorm
info: Tests/HomogeneousNorm.lean:17:0: Contract BlowupDensity.Tests.checkedHomogeneousNorm: checked; standard logical axioms only
ℹ [10565/10573] Replayed Tests.HomogeneousPartialV2
info: Tests/HomogeneousPartialV2.lean:35:0: Contract BlowupDensity.Tests.checkedHomogeneousPartialV2: checked; standard logical axioms only
ℹ [10568/10573] Replayed Tests.MaximalPartialV2
info: Tests/MaximalPartialV2.lean:24:0: Contract BlowupDensity.Tests.checkedMaximalPartialV2: checked; standard logical axioms only
ℹ [10571/10573] Replayed Tests.InsertionLifespanV2
info: Tests/InsertionLifespanV2.lean:32:0: Contract BlowupDensity.Tests.checkedInsertionLifespanV2: checked; standard logical axioms only
ℹ [10572/10573] Replayed Tests.TameProduct
info: Tests/TameProduct.lean:14:0: Contract BlowupDensity.Tests.checkedTameProduct: checked; standard logical axioms only
ℹ [10573/10573] Replayed Tests.EnergyAbsorptionV4
info: Tests/EnergyAbsorptionV4.lean:18:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionV4: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:19:0: Contract BlowupDensity.Bindings.energyAbsorptionPartialV3_of_v4: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:100:0: Contract BlowupDensity.Tests.energyAbsorptionV4_terminalFinite: checked; standard logical axioms only
```

### `bash scripts/gates.sh NSFormalization.Section4.A01.MildEnergyEnvelope`

Exit 0; 28496 output lines, 1176909 bytes.

First 40 lines:

```text
== make check
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 514,
    "vendor/NavierStokesAndEuler": 2486,
    "vendor/HeliCorgi": 129
  },
  "source_manifest_entries": 2975,
  "missing_copied_imports": [],
  "citation_interfaces_reachable": [],
  "tokens_in_copied_umbrella_closure": [
    {
      "module": "NSFormalization.Paper1.BoundaryCorollary",
      "path": "formalization/NSFormalization/Paper1/BoundaryCorollary.lean",
      "line": 90,
      "token": "sorry"
    }
  ],
  "tracked_cache_free": true,
  "source_hashes_match": false
}
Explicit axiom/admission tokens, all copied sources: 11
python3 experiments/check_contracts.py
{
  "registered_contracts": 29,
  "closures": {
    "R41.threshold_arithmetic": [
      "Bindings.Thresholds",
      "Contracts.V1.Thresholds",
      "NSFormalization.Paper3.Thresholds",
      "TestSupport.Axioms",
      "Tests.Thresholds"
    ],
    "I01.packet": [
      "Bindings.Packet",
      "Contracts.V1.Packet",
      "NSFormalization.Paper1.ScalarEnergy",
      "NSFormalization.Section4.I01.Energy",
```

[Middle omitted.] Last 40 lines:

```text
info: Tests/Thresholds.lean:13:0: Contract BlowupDensity.Tests.checkedThresholds: checked; standard logical axioms only
info: Tests/Scaling.lean:18:0: Contract BlowupDensity.Tests.checkedScaling: checked; standard logical axioms only
info: Tests/EnergyAbsorptionPartial.lean:15:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionPartial: checked; standard logical axioms only
info: Tests/Packet.lean:14:0: Contract BlowupDensity.Tests.checkedPacket: checked; standard logical axioms only
info: Tests/EnergyAbsorptionPartialV3.lean:41:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionPartialV3: checked; standard logical axioms only
info: Tests/DatumLemmasV2.lean:23:0: Contract BlowupDensity.Tests.checkedDatumLemmasV2: checked; standard logical axioms only
info: Tests/EnergyHighPartial.lean:17:0: Contract BlowupDensity.Tests.checkedEnergyHighPartial: checked; standard logical axioms only
info: Tests/EnergyAbsorptionPartialV2.lean:32:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionPartialV2: checked; standard logical axioms only
info: Tests/InsertionLifespan.lean:24:0: Contract BlowupDensity.Tests.checkedInsertionLifespan: checked; standard logical axioms only
info: Tests/InsertionFamily.lean:19:0: Contract BlowupDensity.Tests.checkedInsertionFamily: checked; standard logical axioms only
info: Tests/RegularityPartial.lean:17:0: Contract BlowupDensity.Tests.checkedRegularityPartial: checked; standard logical axioms only
info: Tests/BochnerPartial.lean:14:0: Contract BlowupDensity.Tests.checkedBochnerPartial: checked; standard logical axioms only
info: Tests/DatumLemmas.lean:14:0: Contract BlowupDensity.Tests.checkedDatumLemmas: checked; standard logical axioms only
info: Tests/BoundedRepresentative.lean:14:0: Contract BlowupDensity.Tests.checkedBoundedRepresentative: checked; standard logical axioms only
info: Tests/CorrectionV2.lean:28:0: Contract BlowupDensity.Tests.checkedCorrectionV2: checked; standard logical axioms only
info: Tests/HomogeneousPartial.lean:15:0: Contract BlowupDensity.Tests.checkedHomogeneousPartial: checked; standard logical axioms only
info: Tests/GradientL6.lean:13:0: Contract BlowupDensity.Tests.checkedGradientL6: checked; standard logical axioms only
info: Tests/GradientL6V2.lean:22:0: Contract BlowupDensity.Tests.checkedGradientL6V2: checked; standard logical axioms only
info: Tests/EnergyHighPartialV2.lean:30:0: Contract BlowupDensity.Tests.checkedEnergyHighPartialV2: checked; standard logical axioms only
info: Tests/DatumLemmasV3.lean:31:0: Contract BlowupDensity.Tests.checkedDatumLemmasV3: checked; standard logical axioms only
info: Tests/Correction.lean:19:0: Contract BlowupDensity.Tests.checkedCorrection: checked; standard logical axioms only
info: Tests/MaximalPartial.lean:16:0: Contract BlowupDensity.Tests.checkedMaximalPartial: checked; standard logical axioms only
info: Tests/Uniqueness.lean:16:0: Contract BlowupDensity.Tests.checkedUniqueness: checked; standard logical axioms only
info: Tests/HomogeneousNorm.lean:17:0: Contract BlowupDensity.Tests.checkedHomogeneousNorm: checked; standard logical axioms only
info: Tests/HomogeneousPartialV2.lean:35:0: Contract BlowupDensity.Tests.checkedHomogeneousPartialV2: checked; standard logical axioms only
info: Tests/MaximalPartialV2.lean:24:0: Contract BlowupDensity.Tests.checkedMaximalPartialV2: checked; standard logical axioms only
info: Tests/InsertionLifespanV2.lean:32:0: Contract BlowupDensity.Tests.checkedInsertionLifespanV2: checked; standard logical axioms only
info: Tests/TameProduct.lean:14:0: Contract BlowupDensity.Tests.checkedTameProduct: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:18:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionV4: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:19:0: Contract BlowupDensity.Bindings.energyAbsorptionPartialV3_of_v4: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:100:0: Contract BlowupDensity.Tests.energyAbsorptionV4_terminalFinite: checked; standard logical axioms only
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
== gates OK
```

### `python3 experiments/check_contracts.py --base-ref origin/erenup/integration`

Exit 0; 28202 output lines, 1158635 bytes.

First 40 lines:

```text
{
  "registered_contracts": 29,
  "closures": {
    "R41.threshold_arithmetic": [
      "Bindings.Thresholds",
      "Contracts.V1.Thresholds",
      "NSFormalization.Paper3.Thresholds",
      "TestSupport.Axioms",
      "Tests.Thresholds"
    ],
    "I01.packet": [
      "Bindings.Packet",
      "Contracts.V1.Packet",
      "NSFormalization.Paper1.ScalarEnergy",
      "NSFormalization.Section4.I01.Energy",
      "NSFormalization.Section4.I01.Extension",
      "NSFormalization.Section4.I01.Quiet",
      "NSFormalization.Source.Insertion",
      "NSFormalization.Source.PacketEndpoint",
      "NSFormalization.Source.PacketEnergy",
      "NSFormalization.Source.PacketForceExtension",
      "NSFormalization.Source.PacketPressure",
      "NSFormalization.Source.PacketScaling",
      "NSFormalization.Source.ParabolicScaling",
      "NSFormalization.Source.SelectedPacketEnergy",
      "NSFormalization.Source.ViscosityPacket",
      "NSFormalization.Source.ViscosityScaling",
      "NavierStokes.ActivationBounds",
      "NavierStokes.ActivationCone",
      "NavierStokes.ActivationContinuation",
      "NavierStokes.ActivationHolomorphic",
      "NavierStokes.ActivationStocks",
      "NavierStokes.ActiveAnnulusWeight",
      "NavierStokes.ActualBaseResidual",
      "NavierStokes.ActualBaseVelocityBounds",
      "NavierStokes.ActualCandidateAssembly",
      "NavierStokes.ActualCandidateConstruction",
      "NavierStokes.ActualCarrierGeometry",
      "NavierStokes.ActualCarrierTransport",
      "NavierStokes.ActualCarrierTransportBase",
```

[Middle omitted.] Last 40 lines:

```text
      "NavierStokes.TerminalEdgeFactor",
      "NavierStokes.TerminalHistoryBridge",
      "NavierStokes.TerminalPressure",
      "NavierStokes.TerminalStress",
      "NavierStokes.TimeLocalization",
      "NavierStokes.TorusAverages",
      "NavierStokes.TorusInverse",
      "NavierStokes.TorusMeanRequestRebase",
      "NavierStokes.TransitionRamp",
      "NavierStokes.TransportPrimitive",
      "NavierStokes.TrueConeLoop",
      "NavierStokes.UniformAngularReset",
      "NavierStokes.UniformBlockBounds",
      "NavierStokes.UniformCone",
      "NavierStokes.UniformFourierAlias",
      "NavierStokes.UniformHarmonicInteraction",
      "NavierStokes.UniformPrimaryWeights",
      "NavierStokes.ValidBandGluing",
      "NavierStokes.ValidDyadicBandCover",
      "NavierStokes.VariableGaugeMean",
      "NavierStokes.ViscousPropagator",
      "NavierStokes.VolterraAnalyticBounds",
      "NavierStokes.VolterraParity",
      "NavierStokes.VolterraRegularity",
      "NavierStokes.WaveEdgeExtension",
      "NavierStokes.WaveEnvelopeTransport",
      "NavierStokes.WaveInteractionBounds",
      "NavierStokes.WaveStateRegularity",
      "NavierStokes.WeightedClasses",
      "NavierStokes.WeightedODEJets",
      "NavierStokes.WeightedQuotients",
      "NavierStokes.WeightedRadialPrimitive",
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.GradientL6V2"
    ]
  },
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

### `lake env lean ../research/A01/probes/rev199_algebra.lean`

Exit 0; 3 output lines, 200 bytes.

```text
../research/A01/probes/rev199_algebra.lean:7:63: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
```

### `lake env lean ../research/A01/probes/rev199_mutation.lean`

Exit 1; 11 output lines, 481 bytes.

```text
Try this:
  [apply] ring_nf

  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.

  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
../research/A01/probes/rev199_mutation.lean:6:31: error: unsolved goals
ν : ℝ
hν : 0 < ν
k b y : ℝ
⊢ y * ν * b * 4 + y ^ 2 * k ^ 2 * 3 = y * ν * b * 4 + y ^ 2 * k ^ 2 * 2
```

### `lake env lean ../research/A01/probes/rev199_targets.lean`

Exit 1; 3 output lines, 466 bytes.

```text
../research/A01/probes/rev199_targets.lean:2:7: error(lean.unknownIdentifier): Unknown identifier `NSFormalization.Section4.A01.forcingFamilyBound_of_cylinder`
../research/A01/probes/rev199_targets.lean:3:7: error(lean.unknownIdentifier): Unknown identifier `NSFormalization.Section4.A01.envelopeConversion_of_cylinder`
../research/A01/probes/rev199_targets.lean:4:7: error(lean.unknownIdentifier): Unknown identifier `NSFormalization.Section4.A01.finiteMildEnergy`
```

### `python3 experiments/build_changed_lean.py --base-ref origin/erenup/integration --dry-run`

Exit 0; 1 output lines, 70 bytes.

```text
Changed Lean modules: NSFormalization.Section4.A01.MildEnergyEnvelope
```

### `git diff --name-only origin/erenup/integration...HEAD`

Exit 0; 5 output lines, 187 bytes.

```text
formalization/NSFormalization/Section4/A01/MildEnergyEnvelope.lean
research/A01/A3_SPLIT.md
research/A01/ATTEMPTS_ENVELOPE.md
research/A01/REPORT_199.md
research/A01/axioms_envelope.lean
```

### `git diff origin/erenup/integration --stat`

Exit 0; 42 output lines, 2687 bytes.

First 40 lines:

```text
 NEXT_SESSION.md                                    |   2 -
 PLAN.md                                            |   8 +-
 collaboration/HANDOFF.md                           |   8 +-
 .../Section4/A01/ConstructorAssembly.lean          | 597 ---------------------
 .../Section4/A01/MildEnergyEnvelope.lean           | 268 +++++++++
 .../Section4/A01/PressureRegularity.lean           | 441 ---------------
 logs/AGENT_RUNS.csv                                |  11 -
 logs/LESSONS.md                                    |   1 -
 research/A01/A3_SPLIT.md                           |  74 +--
 research/A01/ATTEMPTS_B2_ASSEMBLY.md               | 222 --------
 research/A01/ATTEMPTS_ENVELOPE.md                  | 120 +++++
 research/A01/ATTEMPTS_PRESSURE_REGULARITY.md       | 102 ----
 research/A01/REPORT_180.md                         | 142 -----
 research/A01/REPORT_189.md                         |  85 ---
 research/A01/REPORT_199.md                         | 202 +++++++
 research/A01/REVIEW_180-A01-b2-assembly.md         | 364 -------------
 research/A01/REVIEW_189-A01-pressure-regularity.md | 470 ----------------
 research/A01/axioms_b2_assembly.lean               | 145 -----
 research/A01/axioms_envelope.lean                  | 111 ++++
 research/A01/axioms_pressure_regularity.lean       |  51 --
 research/A01/probes/a01_constructor_pipeline.lean  | 169 ------
 ...torical_rev180_194_195_197_pressure_supply.lean | 141 -----
 .../probes/rev180_actual_supplier_pipeline.lean    |  75 ---
 research/A01/probes/rev180_constructor_loop.lean   |  71 ---
 research/A01/probes/rev180_divergence_closed.lean  |  31 --
 research/A01/probes/rev180_h189_unsat.lean         |  57 --
 research/A01/probes/rev180_hsob_compat.lean        |  26 -
 research/A01/probes/rev180_mutation_fail.lean      |  49 --
 .../rev180_pressure_gradient_representative.lean   | 152 ------
 .../A01/probes/rev180_pressure_residual_fail.lean  |  17 -
 .../rev180_pressure_supply_hpairs_mismatch.lean    |  65 ---
 .../A01/probes/rev180_pressure_supply_zero.lean    | 167 ------
 .../A01/probes/rev180_rows_supplier_mismatch.lean  |  27 -
 .../A01/probes/rev180_sixth_bridge_mismatch.lean   |  65 ---
 .../A01/probes/rev180_sobolev_residual_fail.lean   |  20 -
 research/A01/probes/rev189_assembly_400k.lean      | 475 ----------------
 .../probes/rev189_assembly_endpoint_mutation.lean  | 475 ----------------
 research/A01/probes/rev189_definition_axioms.lean  |   2 -
 research/A01/probes/rev189_endpoint_htime.lean     |  78 ---
 research/A01/probes/rev189_mutation_Icc.lean       |  30 --
```

Remaining lines (within last 40):

```text
 scripts/codex_review.sh                            |   3 +-
 41 files changed, 717 insertions(+), 4902 deletions(-)
```

The algebra probe's style warning is confined to reviewer scratch code; its equality and concrete counterexample both kernel-check. The mutation changes a numerical coefficient while retaining every binder and proof tactic: its residual equates the coefficient 3 with 2 on y²k². The successful algebra probe also refutes the mutated formula at ν=k=y=1,b=0, so this is a substantive failure, not an elaboration or missing-argument trick.

Additional hygiene commands: `git diff --check` exited 0 with no output; `rg -n '\b(sorry|admit|axiom|native_decide)\b|maxHeartbeats' formalization/NSFormalization/Section4/A01/MildEnergyEnvelope.lean research/A01/axioms_envelope.lean` exited 1 with no output (no matches). Both whole-tree grep searches exited 0; candidates are assessed in §3. All 21 axiom lists above are exactly the required set, including line-wrapped lists. The report-source snippet comparison returned True for all seven snippets.

Final disposition: **REJECT against the original deliverable scope.** Required fix: close at least one original general-data predicate with explicit constants, leaving only the permitted exact residual; supply both for unconditional closure. Additional requested checkpoint: formalize scalar ODE uniqueness. Preserve the current honest partial-result records and branch-drift/build-warning qualifications.
