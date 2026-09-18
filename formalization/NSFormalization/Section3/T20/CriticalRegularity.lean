import NSFormalization.Section3.T10.PeriodicData
import NSFormalization.Section3.T11.LocalTheory
import NSFormalization.Section3.T11.Assembly
import NSFormalization.Section3.T12.MeanZeroCalculus
import NSFormalization.Section3.T12.SpectralGap
import NSFormalization.Section3.T12.FourierEmbeddings
import NSFormalization.Section3.T12.TameProduct

/-!
# T20 canonical critical regularity statement

This module restates the reconciled `research/T20/Spec.lean` T20-specific
vocabulary over the canonical Section3/T10, T11, and T12 modules.  The copied
T10/T11/T12 declarations are not repeated here.
-/

noncomputable section
namespace NSFormalization.Section3.T20

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02
  (SpatialField SpaceTimeField SpaceTimeScalar forceTimeMeasure)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open NSFormalization.Section3.T12
open scoped ContDiff ENNReal BigOperators

/-! ## 1. The untranslated mean reduction -/

/-- `03-torus.tex:395-405`: for the zero initial datum, the data-defined mean
path `m(t) = ∫₀ᵗ meanT(g(s)) ds`.  This is T11's `galileanMeanT` without
performing the Galilean spatial translation. -/
def meanPathT (g : SpaceTimeField) (t : ℝ) : Space :=
  galileanMeanT (fun _ : Space ↦ 0) g t

/-- `03-torus.tex:395-401`: the untranslated mean-free velocity
`v(t,x) = u(t,x) - m(t)`. -/
def meanFreeVelocity (g u : SpaceTimeField) : SpaceTimeField :=
  fun q ↦ u q - meanPathT g q.1

/-- `03-torus.tex:397-401`: the mean-free force
`h(t,x) = g(t,x) - meanT(g(t,·))`. -/
def meanFreeForce (g : SpaceTimeField) : SpaceTimeField :=
  fun q ↦ g q - forceMeanT g q.1

/-- `03-torus.tex:408-411`: the constant transport `(m(t)·∇)v`, written
as the spatial Fréchet derivative of `v(t,·)` applied to `m(t)`. -/
def constantTransportT (m : ℝ → Space) (v : SpaceTimeField) : SpaceTimeField :=
  fun q ↦ spatialDerivative v q.1 q.2 (m q.1)

/-- `03-torus.tex:411`: the fixed-time operator `z ↦ (m·∇)z`, used
to state skew-adjointness and commutation with `Λ` without arbitrary values in
the time coordinate. -/
def constantTransportSpatialT (m : Space) (v : SpatialField) : SpatialField :=
  fun x ↦ spatialDerivative (fun q ↦ v q.2) 0 x m

/-- `03-torus.tex:404-405`: the extended-valued integral
`∫₀ᵗ |meanT(g(s))| ds`; unlike a totalized real integral, failure of
measurability or integrability cannot turn this quantity into a junk zero. -/
def meanForceIntegralT (g : SpaceTimeField) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Ioc (0 : ℝ) t, ENNReal.ofReal ‖forceMeanT g s‖

/-! ## 2. Critical and continuation quantities -/

/-- `03-torus.tex:414-418`: `y(t)=‖v(t)‖_{Ḣ^(1/2)}` in the registered
mean-zero coefficient realization. -/
def criticalY (v : SpaceTimeField) (t : ℝ) : ℝ≥0∞ :=
  periodicHomogeneousENorm (1 / 2) (fun x ↦ v (t, x))

/-- `03-torus.tex:414-418`: `z(t)=‖v(t)‖_{Ḣ^(3/2)}` in the registered
mean-zero coefficient realization. -/
def criticalZ (v : SpaceTimeField) (t : ℝ) : ℝ≥0∞ :=
  periodicHomogeneousENorm (3 / 2) (fun x ↦ v (t, x))

/-- `03-torus.tex:414-418`: `b(t)=‖h(t)‖_{Ḣ^(1/2)}`. -/
def criticalB (h : SpaceTimeField) (t : ℝ) : ℝ≥0∞ :=
  periodicHomogeneousENorm (1 / 2) (fun x ↦ h (t, x))

/-- `03-torus.tex:441-444` (`eq:bintegral`): the proof's full-time
`B = ∫₀∞ b(t) dt`, kept in `ℝ≥0∞` so divergence is `⊤`. -/
def criticalBIntegral (h : SpaceTimeField) : ℝ≥0∞ :=
  ∫⁻ t, criticalB h t ∂forceTimeMeasure

/-- `03-torus.tex:383-389`: the critical inhomogeneous force size
`ρ = ‖g‖_{L¹(0,∞;H^(1/2))}`. -/
def criticalRho (g : SpaceTimeField) : ℝ≥0∞ :=
  forceSobolevENormT 1 (1 / 2) g

/-- `03-torus.tex:482-484`: `‖∇v‖²₂`, expressed through T12's
registered-spelling gradient tensor.  Its uses below explicitly assert that
the extended norm is finite before applying `toReal`. -/
def gradientSqT (v : SpatialField) : ℝ :=
  (periodicLpENorm 2 (gradientTensor v)).toReal ^ 2

/-- `03-torus.tex:468-484`: `‖Δv‖²₂`, expressed through T12's
registered-spelling componentwise Laplacian. -/
def laplacianSqT (v : SpatialField) : ℝ :=
  (periodicLpENorm 2 (laplacian v)).toReal ^ 2

/-- `03-torus.tex:479-488`: `‖h‖²₂` on the normalized unit torus. -/
def lTwoSqT (h : SpatialField) : ℝ :=
  (periodicLpENorm 2 h).toReal ^ 2

/-- `03-torus.tex:488-500`: the full positive-time integral
`∫₀∞ ‖h(t)‖²₂ dt`, with divergence represented by `⊤`. -/
def meanFreeForceLTwoSqIntegral (h : SpaceTimeField) : ℝ≥0∞ :=
  ∫⁻ t, (periodicLpENorm 2 (fun x ↦ h (t, x))) ^ (2 : ℝ) ∂forceTimeMeasure

/-- `03-torus.tex:494-500`: the right-hand integrand in the orthogonal
constant/mean-zero `H²` decomposition of `u`. -/
def meanModeCriterionIntegral (S : ℝ) (g u : SpaceTimeField) : ℝ≥0∞ :=
  ∫⁻ t in Ioo (0 : ℝ) S,
    ENNReal.ofReal ‖meanPathT g t‖ ^ (2 : ℝ) +
      periodicSobolevENorm 2 (fun x ↦ meanFreeVelocity g u (t, x)) ^ (2 : ℝ)

/-- `03-torus.tex:411`: the real `L²(T³)` pairing used to state
skew-adjointness of constant transport.  Its API field below carries explicit
integrability hypotheses for both scalar integrands. -/
def periodicPairing (v w : SpatialField) : ℝ :=
  ∫ y : PeriodicTorus,
    (inner ℝ (torusLift v y) (torusLift w y) : ℝ) ∂periodicTorusMeasure

/-! ## 3. Proposition 3.7 and its displayed proof estimates -/

/-- Proposition `prop:critical` together with the named estimates in its
proof (`03-torus.tex:383-503`).  The interface is indexed by the binding T11
local/continuation/mean-reduction packages and the binding T12 calculus
package, making the DAG dependencies explicit without copying their facts as
new T20 fields.  It is **Type-valued** because the universal smallness radius
and the three absolute estimate constants are mathematical data selected
before every viscosity, force, and solution.  Their positivity and the two
bootstrap shrinkings prevent vacuous thresholds.

The estimates are stated for the untranslated field `v=u-m`; hence
`meanFreeEquation` retains `constantTransportT`.  Every occurrence of a
totalized norm is protected collectively by `reductionRegular`, while every
`toReal` use has an explicit `≠ ⊤` conclusion there. -/
structure CriticalRegularityTAPI : Type where
  /-- `03-torus.tex:383-387`: the universal smallness constant, selected
  before `ν` and `g`.
  Exact quantifier order: dependency packages first, then this constant,
  before every viscosity and force in the theorem fields.
  Non-vacuity: `hc` below forces a genuinely positive ball. -/
  c : ℝ

  /-- `03-torus.tex:383-387`: positivity of the universal smallness constant.
  Exact quantifier order: there are no later parameters.
  Non-vacuity: with `ν>0`, `ENNReal.ofReal (c*ν)` is positive. -/
  hc : 0 < c

  /-- `03-torus.tex:426-440`: the absolute constant in the critical
  trilinear estimate, fixed before all PDE data.
  Exact quantifier order: it is structure data before `ν,g,T,w,t`.
  Non-vacuity: `C₀_pos` excludes the zero-constant trap. -/
  C₀ : ℝ

  /-- `03-torus.tex:426-440`: positivity of `C₀`.
  Exact quantifier order: no later parameters.
  Non-vacuity: the bootstrap level `ν/(2*C₀)` is meaningful. -/
  C₀_pos : 0 < C₀

  /-- `03-torus.tex:467-484`: the absolute coefficient of `y‖Δv‖²₂`
  in the `H¹` convection estimate, fixed before all PDE data.
  Exact quantifier order: it is structure data before `ν,g,T,w,t`.
  Non-vacuity: `C₁_pos` below rules out zero. -/
  C₁ : ℝ

  /-- `03-torus.tex:467-484`: positivity of the `H¹` convection constant.
  Exact quantifier order: no later parameters.
  Non-vacuity: the second bootstrap shrinking is therefore genuine. -/
  C₁_pos : 0 < C₁

  /-- `03-torus.tex:479-484`: the absolute constant after Young's inequality
  in `eq:H1energy`.
  Exact quantifier order: it is structure data before `ν,g,T,w,t`.
  Non-vacuity: `CH1_pos` below prevents a zero right-hand coefficient. -/
  CH1 : ℝ

  /-- `03-torus.tex:479-484`: positivity of the `H¹` energy constant.
  Exact quantifier order: no later parameters.
  Non-vacuity: this constrains the actual constant used in `hOneEnergy`. -/
  CH1_pos : 0 < CH1

  /-- `03-torus.tex:492-500`: the absolute constant in the assembled
  squared-`H²` continuation bound.
  Exact quantifier order: it is structure data before `ν,g,T,w,S`.
  Non-vacuity: `hCcriterion` below forces it to be positive. -/
  Ccriterion : ℝ

  /-- `03-torus.tex:492-500`: positivity of the continuation constant.
  Exact quantifier order: no later parameters.
  Non-vacuity: the finite bound in `continuationBound` is quantitative. -/
  hCcriterion : 0 < Ccriterion

  /-- `03-torus.tex:457`: the first required shrinking
  `c < 1/(4 C₀)`.
  Exact quantifier order: constants were selected first.
  Non-vacuity: together with positivity it gives a nonempty, absorbing
  bootstrap regime. -/
  c_lt_C₀ : c < 1 / (4 * C₀)

  /-- `03-torus.tex:477-480`: the second required shrinking
  `c < 1/(4 C₁)`.
  Exact quantifier order: constants were selected first.
  Non-vacuity: this is the stated absorption gate for `eq:H1energy`. -/
  c_lt_C₁ : c < 1 / (4 * C₁)

  reductionRegular : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
        ∀ t ∈ Ico (0 : ℝ) T,
          let v := fun x ↦ meanFreeVelocity g w.velocity (t, x)
          let h := fun x ↦ meanFreeForce g (t, x)
          IsMeanZeroT v ∧ SmoothPeriodicT v ∧
            MemPeriodicHomogeneous (1 / 2) v ∧
            MemPeriodicHomogeneous (3 / 2) v ∧
            MemPeriodicHmVector 2 v ∧
            IsMeanZeroT h ∧ SmoothPeriodicT h ∧
            MemPeriodicHomogeneous (1 / 2) h ∧
            periodicLpENorm 2 h ≠ ⊤ ∧
            periodicLpENorm 2 (gradientTensor v) ≠ ⊤ ∧
            periodicLpENorm 2 (laplacian v) ≠ ⊤

  meanBound : ∀ (g : SpaceTimeField), g ∈ forceClassT →
    ∀ t : ℝ, 0 ≤ t →
      ENNReal.ofReal ‖meanPathT g t‖ ≤ meanForceIntegralT g t ∧
        meanForceIntegralT g t ≤ criticalRho g

  /-- `03-torus.tex:407-410`, `eq:meanfree`: the untranslated mean-free field
  solves
  `∂ₜv+(v·∇)v+(m·∇)v-νΔv+∇p=h`.
  Exact quantifier order: `ν,hν,g,hg,T,w,t,ht,x`.
  Non-vacuity: this is a pointwise vector equation for the explicit `v`, `m`,
  `h`, and the normalized pressure of a full classical solution. -/
  meanFreeEquation : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
        ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
          temporalDerivative (meanFreeVelocity g w.velocity) t x +
              advection (meanFreeVelocity g w.velocity) t x +
              constantTransportT (meanPathT g)
                (meanFreeVelocity g w.velocity) (t, x) -
              ν • spatialLaplacian (meanFreeVelocity g w.velocity) t x +
              pressureGradient w.pressure t x =
            meanFreeForce g (t, x)

  /-- `03-torus.tex:411`: for fixed `m`, `(m·∇)` is skew-adjoint in
  periodic `L²`.
  Exact quantifier order: `m,v,w`, smooth-periodic hypotheses, followed by
  integrability of the two concrete pairing integrands.
  Non-vacuity: the conclusion is an equality of actual torus integrals; the
  integrability premises rule out Bochner-integral junk zeros. -/
  constantTransportSkew : ∀ (m : Space) (v w : SpatialField),
    SmoothPeriodicT v → SmoothPeriodicT w →
      Integrable
        (fun y : PeriodicTorus ↦
          (inner ℝ (torusLift (constantTransportSpatialT m v) y)
            (torusLift w y) : ℝ)) periodicTorusMeasure →
      Integrable
        (fun y : PeriodicTorus ↦
          (inner ℝ (torusLift v y)
            (torusLift (constantTransportSpatialT m w) y) : ℝ))
        periodicTorusMeasure →
        periodicPairing (constantTransportSpatialT m v) w =
          -periodicPairing v (constantTransportSpatialT m w)

  /-- `03-torus.tex:411`: constant transport commutes with the Fourier
  multiplier `Λ`.
  Exact quantifier order: `m,v,Lv`, smooth periodicity, then the T12 Lambda
  graph.
  Non-vacuity: the conclusion is the same concrete coefficientwise Lambda
  graph for the two transported physical fields. -/
  constantTransportCommutesLambda :
    ∀ (m : Space) (v Lv : SpatialField), SmoothPeriodicT v →
      IsPeriodicLambda v Lv →
        IsPeriodicLambda (constantTransportSpatialT m v)
          (constantTransportSpatialT m Lv)

  /-- `03-torus.tex:420-440`, `eq:criticalenergy`:
  `½(y²)' + (ν-C₀y)z² ≤ by` at every interior time.
  Exact quantifier order: `ν,hν,g,hg,T,w,t,ht`, followed by an actual
  derivative witness.
  Non-vacuity: existence of `E'` prevents an implication from a nonexistent
  derivative; `reductionRegular` makes every `toReal` operand finite. -/
  criticalEnergy : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
        ∀ t ∈ Ioo (0 : ℝ) T,
          ∃ E' : ℝ,
            HasDerivAt
                (fun s ↦ (criticalY (meanFreeVelocity g w.velocity) s).toReal ^ 2)
                E' t ∧
              E' / 2 +
                  (ν - C₀ *
                    (criticalY (meanFreeVelocity g w.velocity) t).toReal) *
                    (criticalZ (meanFreeVelocity g w.velocity) t).toReal ^ 2 ≤
                (criticalB (meanFreeForce g) t).toReal *
                  (criticalY (meanFreeVelocity g w.velocity) t).toReal

  /-- `03-torus.tex:441-444`, `eq:bintegral`:
  `∫₀∞ b(t)dt ≤ ρ`.
  Exact quantifier order: `g,hg`; no viscosity or solution is needed.
  Non-vacuity: both sides are fail-safe `ℝ≥0∞` quantities based on
  integrable Fourier data paths, and `g∈forceClassT` is explicit. -/
  bIntegral : ∀ (g : SpaceTimeField), g ∈ forceClassT →
    criticalBIntegral (meanFreeForce g) ≤ criticalRho g

  /-- `03-torus.tex:446-458`, `eq:ybound`, after the continuity bootstrap:
  `y(t) ≤ ∫₀ᵗ b(s)ds ≤ ρ` throughout the classical lifespan.
  Exact quantifier order: `ν,hν,g,hg,hsmall,T,w,t,ht`.
  Non-vacuity: the strict smallness hypothesis uses the positive finite
  threshold `cν`, and the conclusion bounds the concrete homogeneous norm. -/
  yBound : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      criticalRho g < ENNReal.ofReal (c * ν) →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
          ∀ t ∈ Ico (0 : ℝ) T,
            criticalY (meanFreeVelocity g w.velocity) t ≤
                ∫⁻ s in Ioc (0 : ℝ) t, criticalB (meanFreeForce g) s ∧
              (∫⁻ s in Ioc (0 : ℝ) t, criticalB (meanFreeForce g) s) ≤
                criticalRho g

  /-- `03-torus.tex:467-484`, `eq:H1energy`:
  `(‖∇v‖²₂)' + ν‖Δv‖²₂ ≤ Cν⁻¹‖h‖²₂`.
  Exact quantifier order: `ν,hν,g,hg,hsmall,T,w,t,ht`, followed by an
  actual derivative witness.
  Non-vacuity: `reductionRegular` supplies finiteness for every norm passed
  to `toReal`, and existence of `E'` rules out a vacuous derivative premise. -/
  hOneEnergy : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      criticalRho g < ENNReal.ofReal (c * ν) →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
          ∀ t ∈ Ioo (0 : ℝ) T,
            ∃ E' : ℝ,
              HasDerivAt
                  (fun s ↦ gradientSqT
                    (fun x ↦ meanFreeVelocity g w.velocity (s, x))) E' t ∧
                E' + ν * laplacianSqT
                    (fun x ↦ meanFreeVelocity g w.velocity (t, x)) ≤
                  CH1 * ν⁻¹ * lTwoSqT
                    (fun x ↦ meanFreeForce g (t, x))

  /-- `03-torus.tex:486-500`: orthogonal mode decomposition and the finite
  squared-`H²` bound used in `eq:criterion`:
  `∫₀ˢ‖u‖²_{H²} ≤ Sρ² + Cν⁻²∫₀∞‖h‖²₂ < ∞`.
  Exact quantifier order: `ν,hν,g,hg,hsmall,T,w,S,hS,hST`.
  Non-vacuity: the final conjunct explicitly proves the displayed upper bound
  finite; neither compact support nor a failed datum can be a junk zero. -/
  continuationBound : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      criticalRho g < ENNReal.ofReal (c * ν) →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
          ∀ (S : ℝ), 0 < S → S ≤ T →
            squaredHTwoIntegralT S w.velocity =
                meanModeCriterionIntegral S g w.velocity ∧
              meanModeCriterionIntegral S g w.velocity ≤
                ENNReal.ofReal S * criticalRho g ^ (2 : ℝ) +
                  ENNReal.ofReal (Ccriterion * (ν⁻¹) ^ 2) *
                    meanFreeForceLTwoSqIntegral (meanFreeForce g) ∧
              ENNReal.ofReal S * criticalRho g ^ (2 : ℝ) +
                  ENNReal.ofReal (Ccriterion * (ν⁻¹) ^ 2) *
                    meanFreeForceLTwoSqIntegral (meanFreeForce g) ≠ ⊤

  globalRegularity : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      criticalRho g < ENNReal.ofReal (c * ν) →
        maximalLifespanT ν (fun _ : Space ↦ 0) g = ⊤

end NSFormalization.Section3.T20

/-! Existential statement form of the T20 API; no inhabitant is constructed. -/
namespace NSFormalization.Section3.T20
def criticalRegularityStatement : Prop := Nonempty CriticalRegularityTAPI

end NSFormalization.Section3.T20
