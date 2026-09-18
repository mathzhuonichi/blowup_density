# T21 draft A — paper/Lean comparison

This lane keeps the registered Section 3 vocabulary and copies the reconciled
T19/T20 statement blocks verbatim before adding the T21 assembly.  The torus
has one force time exponent (`L¹_t`, hence `q = 1`) and one critical order,
`s_c = 1/2`; there is no whole-space `q = 2` branch.

## Clause table

| Paper clause | Lean field/definition in `DraftA.lean` | Section 4 R41 counterpart | Choice or difference |
|---|---|---|---|
| `02-preliminaries.tex:7-14`: `𝓧=C^∞_{div}(𝕋)` and `𝓕=C_c^∞(𝕋×(0,∞))` | Registered `initialClassT` and `forceClassT` from `TorusLocalTheory` | `initialClassR` and `forceClassR` in `Data`/R41 | The torus periodicity and positive-time compact support are retained in the registered classes; no weaker carrier is introduced by T21. |
| `02-preliminaries.tex:38-48`: `𝓑_{ν,a,T}={f∈𝓕:T_max^ν(a,f)≤T}` and `𝓑⁰_{ν,T}=𝓑_{ν,0,T}` | Registered `breakdownSetT ν a T`; T21's `zeroInitialVelocity` specializes it for `𝓑⁰` | `breakdownSetR`, `breakdownSetRZero` | The lifespan inequality is in `ℝ≥0∞`, `≤ ENNReal.ofReal T`; the T21 `rfl` example checks the registered `breakdownSetT` specialization. |
| `03-torus.tex:1-7`: all spatial norms and the `L¹_tH^s_x` force topology | Registered `forceSobolevENormT 1 s`; `criticalRho` abbreviates its `s=1/2` instance | `forceSobolevENorm`, `forceSobolevENormL1`, and `RelativelyDense` | Norms are totalized in `ℝ≥0∞`; all density fields retain force-class membership and positive radii. |
| `03-torus.tex:8`: equip `𝓕` with relative `L¹(0,∞;H^s)` topology | Registered `RelativelyDenseT 1 s forceClassT S`; its positive `ℝ≥0∞`-radius approximation clause is the relative-closure interface | `R41.main_thresholds.MainThresholdsAPI` uses `RelativelyDense` with the same shape | No new topology instance is installed. The force class is the ambient relative space, and every norm is the registered extended-valued `forceSobolevENormT`. |
| `03-torus.tex:10-12`, (i): fixed `a∈𝓧`, `s<1/2`, `𝓑_{ν,a,T}` dense in `𝓕` | `MainTheoremAPI.fixedInitialDensity`; same proposition as `T19.PeriodicDensityAPI.fixedInitialDensity` | `MainThresholdsAPI.fixedInitialDensity` | Quantifier order is `∀a, a∈𝓧, ∀ν>0, ∀T>0, ∀s<1/2`; the torus threshold is written literally rather than through a two-value exponent. |
| `03-torus.tex:10-16`, (ii), “if” direction | `MainTheoremAPI.zeroInitialDensity_subcritical` | `MainThresholdsAPI.zeroInitialDensityIff` (forward implication) | It is stored as its own field so the two directions remain independently consumable; the zero datum is `zeroInitialVelocity`. |
| `03-torus.tex:10-16`, (ii), “only if” direction | `MainTheoremAPI.zeroInitialDensity_only_if` | `MainThresholdsAPI.zeroInitialDensityIff` (reverse implication) | The antecedent is the complete `RelativelyDenseT` predicate, so equality `s=1/2` is included in the obstruction. |
| Full theorem display `03-torus.tex:8-16` | `mainStatement` (clause (i) conjoined with the zero-data biconditional) | `MainThresholdsAPI` fields plus its `thresholdValues` | The structure splits the biconditional, while the public statement alias restores the paper's `↔`. |
| `03-torus.tex:506-509`: the ball `{g∈𝓕 : ‖g‖_{L¹_tH^{1/2}}<cν}` | `criticalForceBall critical ν` | R41 implementation `R41.nonDensityZero_L1` uses the radius `R43.criticalConst*ν`; the registered R41 theorem has no separate ball field | The ball is a relative set: strict inequality in `criticalRho` plus `g∈forceClassT`. The radius is `ENNReal.ofReal (critical.c*ν)`, since all force norms are `ℝ≥0∞`. |
| `03-torus.tex:506-509`: `c` is the `prop:critical` constant and the radius is nonempty for `ν>0` | `NonDensityAPI.criticalRadius_pos`; `criticalForceBall` takes `NSFormalization.Section3.T20.CriticalRegularityTAPI` as a parameter, so its `c` is exactly `critical.c` | `R43.CriticalRegularityAPI.c`, `hc`; R41's `RMainNonDensity` records a positive radius | T21 exports no second constant. `NonDensityAPI` is `Prop`-valued because the constant is already data in the T20 `Type`-valued API. |
| `03-torus.tex:506-509`: the ball contains zero | `NonDensityAPI.zeroForce_mem_forceClass` and `zero_mem_criticalBall` | `R41.zero_mem_forceClassR`; `R41.nonDensityZero_L1` uses it to contradict density | `zeroForce : SpaceTimeField` is kept separate from `zeroInitialVelocity : SpatialField`; both are explicit zero functions. |
| `03-torus.tex:506-509`: the critical ball misses `𝓑⁰_{ν,T}` | `NonDensityAPI.criticalBall_disjoint_zeroBreakdown` | `R41.criticalRadius_le_forceSobolevENorm`, `R41.not_breakdownDenseR_zero_L1`; torus-only set is `breakdownSetT ν zeroInitialVelocity T` | The field states actual set disjointness. Its proof will apply `CriticalRegularityTAPI.globalRegularity` and contradict `maximalLifespanT≤ENNReal.ofReal T`. |
| `03-torus.tex:507-509`: `‖g‖_{L¹H^{1/2}}≤‖g‖_{L¹H^s}` for `s≥1/2` | `NonDensityAPI.sobolevMonotonicity` | `R41.forceSobolevENorm_mono_order` | This is a new torus lemma: compare `periodicFrequencyWeight k ^ (1/4)` and `^ (s/2)` coefficientwise, transport paths, then use monotonicity of `eLpNorm`. The field includes `g∈forceClassT` so every norm is attached to the paper's integrable force class. |
| `03-torus.tex:506-509`: non-density for every `s≥1/2` | `NonDensityAPI.nonDensity` and `nonDensityStatement` | `MainThresholdsAPI.zeroInitialDensityIff` contains the R41 non-density direction; implementation `R41.not_breakdownDenseR_zero_of_q`/`not_breakdownDenseR_zero_L1` proves it | The torus conclusion is only `q=1`; the `L²_t`/`s=-1/2` branch is deliberately absent. |
| Assembly of T21 | `mainOfInputs : Prop`, namely `∀ density : PeriodicDensityAPI, ∀ critical : CriticalRegularityTAPI, NonDensityAPI critical → MainTheoremAPI` | R41 assembly consumes `MainThresholdsAPI` plus the R42/R43/R44 packages; `R41.main_thresholds` is the registered analogue | This is an explicit signature, not an unproved inhabitant of the arrow. T19 supplies the subcritical branch and T20 supplies the critical constant/global-regularity branch. |

## Registered vocabulary and copied blocks

The file imports and uses `TorusData`, `TorusLocalTheory`, `Packet`,
`PacketImport`, `MainThresholds`, and `CompletedDensity`.  In particular:

* `ClassicalSolutionT`, `RegularThroughT`, `maximalLifespanT`,
  `forceClassT`, `initialClassT`, `breakdownSetT`, `RelativelyDenseT`,
  `forceSobolevENormT`, and the energy norms are never redefined.
* `PeriodicDensityAPI`, `MixedRegionAPI`, `StrongClosureAPI`, and
  `ProjectionAPI` are copied verbatim from the canonical T19 block under
  `BlowupDensity.T19`.
* The T20 scalar/calculus declarations and `CriticalRegularityTAPI` are copied
  verbatim under `NSFormalization.Section3.T20`; `criticalRho` is the same
  registered `forceSobolevENormT 1 (1/2)` spelling.  The file contains an
  `example … := rfl` drift check for this equality and another for the
  registered `breakdownSetT` specialization.

The T19 structures are `Prop`-valued because they export no numerical data.
T20 is `Type`-valued because it exports `c`, `C₀`, `C₁`, `CH1`, and the
continuation constant.  T21's `NonDensityAPI` consumes that selected T20
constant rather than introducing a duplicate; `MainTheoremAPI` is `Prop`-
valued because the theorem exports only density propositions.

## Ambiguities resolved

1. The theorem's prose suppresses the positivity assumptions on `ν` and `T`,
   although `𝓑_{ν,a,T}` is only used for the physical regime.  They are made
   explicit in every T21 field and statement alias (`ν>0`, `T>0`).
2. “Open ball” is interpreted relative to `𝓕`: `criticalForceBall` contains
   exactly the force-class membership and a strict extended-norm inequality.
   No unregistered topological-space instance is needed because
   `RelativelyDenseT` is the registered relative-closure shape.
3. The corollary's centre is the zero force, while `𝓑⁰` means zero *initial
   velocity*.  These are deliberately different Lean definitions.
4. The paper writes `1/2` rather than `criticalOrder 1`; the T19 input retains
   the arithmetic bridge `PeriodicDensityAPI.thresholdValue`, and T21 writes
   the visible paper value literally.
5. Norms remain `ℝ≥0∞` throughout.  There is no real `sSup`, no `.toReal` in
   T21, and no field that can be discharged by `True`, a zero radius, or an
   empty witness type.

## Needs-a-lemma list for a proof/assembly implementation

### T19 branch consumed by `thm:main`

* `PeriodicDensityAPI.fixedInitialDensity` gives clause (i) directly and,
  instantiated at `a = zeroInitialVelocity`, gives the forward half of (ii).
* `PeriodicDensityAPI.thresholdValue` bridges the registered `criticalOrder 1`
  arithmetic to the paper's literal `1/2`.
* The proof of that T19 field consumes `regularReferenceSingular` and the
  T11 local-theory vocabulary; the earlier-breaking case is handled by the
  `≤T` breakdown set, while the regular-reference case uses exact lifespan
  `=ENNReal.ofReal T`.

### T20 critical branch consumed by `cor:nondensity`

* `CriticalRegularityTAPI.c`, `hc`, and `globalRegularity` give
  `criticalRho g < ENNReal.ofReal (c*ν) →
  maximalLifespanT ν zeroInitialVelocity g = ⊤`.
* `zeroForce_mem_forceClass` is a T11 force-class fact; the T20 `meanBound`,
  `bIntegral`, bootstrap, and continuation fields are the proof inputs from
  which `globalRegularity` is constructed, not additional T21 conclusions.
* An order lemma turns global lifespan into exclusion from breakdown:
  `¬(⊤ ≤ ENNReal.ofReal T)` for finite `T` (using `T>0` and
  `ENNReal.ofReal_ne_top`).

### T11 norm/topology and torus-specific lemmas

* Use the registered `RelativelyDenseT` definition exactly as written in
  `TorusLocalTheory`: `∀g∈Y, ∀r:ℝ≥0∞, 0<r → ∃f∈S,
  forceSobolevENormT q s (f-g)<r`.
* Prove the coefficientwise monotonicity of the Bessel weights for
  `1/2≤s`, lift it to representing `PeriodicSobolev` paths, preserve
  `AEStronglyMeasurable`, and apply `eLpNorm` monotonicity at time exponent
  `q=1`.  This is the exact content required by
  `NonDensityAPI.sobolevMonotonicity`; it is not available as a registered T11
  field yet.
* A small normalization lemma identifies the zero-centred distance with
  `criticalRho` (`forceSobolevENormT 1 (1/2) (g-zeroForce) = criticalRho g`).
* To pass from the `H^{1/2}` ball to every `H^s` topology, use the preceding
  monotonicity and instantiate `RelativelyDenseT` at the positive radius
  `ENNReal.ofReal (critical.c*ν)`; the zero witness then contradicts the ball
  disjointness field.
* T11 supplies the class hypotheses on all norm occurrences:
  `forceClassT`, `initialClassT`, `breakdownSetT`, `maximalLifespanT`, and
  `ClassicalSolutionT`.  No integrability-free norm or totalized real integral
  may be substituted.

## Implementation candidates

The closest completed Section 4 proof components are:

* `formalization/NSFormalization/Section4/R41/NonDensityL1.lean`:
  `forceSobolevENorm_mono_order`, `criticalRadius_le_forceSobolevENorm`,
  `zero_mem_forceClassR`, and `not_breakdownDenseR_zero_L1`;
* `formalization/NSFormalization/Section4/R41/NonDensity.lean`:
  the two-case `q` assembly and `RMainNonDensity` shape;
* `formalization/NSFormalization/Section4/R41/ClassFacts.lean`:
  smooth/compact force-class facts and the zero-force instance;
* `formalization/NSFormalization/Paper1/PeriodicMain.lean`:
  `GaugeSeparated`, `not_GaugeDense_of_GaugeSeparated`,
  `zero_slice_GaugeDense_iff_subcritical`, and `paper1_main`;
* `formalization/NSFormalization/Paper1/ManuscriptTopology.lean`:
  `denseAt_iff_approximation`, `not_denseAt_of_regular_ball`, and the
  identification of positive-radius approximation with closure;
* `formalization/NSFormalization/Paper1/PeriodicDense.lean`,
  `PeriodicDensityDichotomy.lean`, and `PeriodicDensityFiber.lean` for the
  T19 insertion/dichotomy witnesses.

The Section 4 `R41.main_thresholds` contract (with its
`fixedInitialDensity`, `zeroInitialDensityIff`, threshold arithmetic, and
regular-reference rider) is the comparison target, not an imported proof of
the torus theorem.  The torus-only additions are the single `1/2` threshold,
the critical ball from T20's periodic mean-removal argument, and the periodic
Fourier-weight monotonicity lemma.
