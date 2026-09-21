import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

namespace MNS2

open MeasureTheory Set Filter
open scoped Interval NNReal Topology

noncomputable section

section EndpointMeasurability

variable {Z : Type*} [NormedAddCommGroup Z]

/--
Continuity away from the two endpoints suffices for strong measurability on an interval.

For `0 ≤ t`, the interval measure uses `Ioc 0 t`, while `Ioo 0 t` differs only by the
right endpoint.  The equality of the two restricted measures is the precise reason no
continuity claim at the singular Duhamel endpoint is needed.
-/
theorem aestronglyMeasurable_interval_of_continuousOn_Ioo
    {t : ℝ} (ht : 0 ≤ t) {f : ℝ → Z}
    (hf : ContinuousOn f (Ioo 0 t)) :
    AEStronglyMeasurable f (volume.restrict (Ι (0 : ℝ) t)) := by
  have hmeas :
      AEStronglyMeasurable f (volume.restrict (Ioo (0 : ℝ) t)) :=
    hf.aestronglyMeasurable measurableSet_Ioo
  rw [restrict_Ioo_eq_restrict_Ioc] at hmeas
  simpa [uIoc_of_le ht] using hmeas

end EndpointMeasurability

section EndpointSafeTwoSpaceDuhamel

universe u v w

variable {𝕜 : Type u} {X : Type v} {Y : Type w}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/--
Totalize an operator family that is genuinely available only at positive elapsed time.

The nonpositive branch is the zero operator.  In particular, this definition never asks
for an artificial proof of `0 < 0` at the Duhamel endpoint.
-/
def endpointSafePositiveOperator
    (S : ∀ τ : ℝ, 0 < τ → Y →L[𝕜] X) (τ : ℝ) : Y →L[𝕜] X :=
  if hτ : 0 < τ then S τ hτ else 0

@[simp]
theorem endpointSafePositiveOperator_of_pos
    (S : ∀ τ : ℝ, 0 < τ → Y →L[𝕜] X)
    {τ : ℝ} (hτ : 0 < τ) :
    endpointSafePositiveOperator S τ = S τ hτ := by
  simp [endpointSafePositiveOperator, hτ]

@[simp]
theorem endpointSafePositiveOperator_of_nonpos
    (S : ∀ τ : ℝ, 0 < τ → Y →L[𝕜] X)
    {τ : ℝ} (hτ : τ ≤ 0) :
    endpointSafePositiveOperator S τ = 0 := by
  simp [endpointSafePositiveOperator, not_lt.mpr hτ]

@[simp]
theorem endpointSafePositiveOperator_zero
    (S : ∀ τ : ℝ, 0 < τ → Y →L[𝕜] X) :
    endpointSafePositiveOperator S 0 = 0 := by
  exact endpointSafePositiveOperator_of_nonpos S le_rfl

/--
Coherence with a jointly strongly continuous same-space evolution makes the positive-time
smoothing action jointly continuous away from elapsed time zero.

At a point `τ₀ > 0`, freeze `a = τ₀ / 2` and use
`S(τ)y = H(τ-a)(S(a)y)` locally.  The proof never asks for operator-norm continuity of `H`.
-/
theorem continuousOn_endpointSafePositiveOperator_of_coherent
    (H : ℝ≥0 → X →L[𝕜] X)
    (S : ∀ τ : ℝ, 0 < τ → Y →L[𝕜] X)
    (hH : Continuous (fun p : ℝ≥0 × X => H p.1 p.2))
    (hcoherent : ∀ (a : ℝ) (ha : 0 < a) (b : ℝ≥0),
      S (a + (b : ℝ)) (add_pos_of_pos_of_nonneg ha b.2) =
        (H b).comp (S a ha)) :
    ContinuousOn
      (fun p : ℝ × Y => endpointSafePositiveOperator S p.1 p.2)
      (Ioi 0 ×ˢ (Set.univ : Set Y)) := by
  intro p hp
  have hp0 : 0 < p.1 := hp.1
  let a : ℝ := p.1 / 2
  have ha : 0 < a := by
    dsimp [a]
    linarith
  have hap : a < p.1 := by
    dsimp [a]
    linarith
  let G : ℝ × Y → X := fun q =>
    H (Real.toNNReal (q.1 - a)) (S a ha q.2)
  have htime : Continuous (fun q : ℝ × Y => Real.toNNReal (q.1 - a)) :=
    continuous_real_toNNReal.comp (continuous_fst.sub continuous_const)
  have hstate : Continuous (fun q : ℝ × Y => S a ha q.2) :=
    (S a ha).continuous.comp continuous_snd
  have hG : Continuous G := by
    exact hH.comp (htime.prodMk hstate)
  have heq_of_gt : ∀ q : ℝ × Y, a < q.1 →
      endpointSafePositiveOperator S q.1 q.2 = G q := by
    intro q hqa
    have hq0 : 0 < q.1 := ha.trans hqa
    let b : ℝ≥0 := Real.toNNReal (q.1 - a)
    have hbcoe : (b : ℝ) = q.1 - a := by
      exact Real.coe_toNNReal _ (sub_nonneg.mpr hqa.le)
    have hsum : a + (b : ℝ) = q.1 := by
      rw [hbcoe]
      ring
    have hc := congrArg (fun L : Y →L[𝕜] X => L q.2)
      (hcoherent a ha b)
    simpa [endpointSafePositiveOperator, hq0, G,
      ContinuousLinearMap.comp_apply, hsum] using hc
  have hevent : ∀ᶠ q : ℝ × Y in 𝓝 p, a < q.1 :=
    continuousAt_fst.eventually_const_lt hap
  have heq :
      (fun q : ℝ × Y => endpointSafePositiveOperator S q.1 q.2) =ᶠ[𝓝 p] G :=
    hevent.mono fun q hq => heq_of_gt q hq
  exact (hG.continuousAt.congr_of_eventuallyEq heq).continuousWithinAt

/-- Scalar totalization matching `endpointSafePositiveOperator`. -/
def endpointSafePositiveMajorant (k : ℝ → ℝ) (τ : ℝ) : ℝ :=
  if 0 < τ then k τ else 0

@[simp]
theorem endpointSafePositiveMajorant_of_pos
    (k : ℝ → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    endpointSafePositiveMajorant k τ = k τ := by
  simp [endpointSafePositiveMajorant, hτ]

@[simp]
theorem endpointSafePositiveMajorant_of_nonpos
    (k : ℝ → ℝ) {τ : ℝ} (hτ : τ ≤ 0) :
    endpointSafePositiveMajorant k τ = 0 := by
  simp [endpointSafePositiveMajorant, not_lt.mpr hτ]

@[simp]
theorem endpointSafePositiveMajorant_zero (k : ℝ → ℝ) :
    endpointSafePositiveMajorant k 0 = 0 := by
  exact endpointSafePositiveMajorant_of_nonpos k le_rfl

theorem endpointSafePositiveMajorant_nonneg
    (k : ℝ → ℝ) (hk : ∀ τ, 0 < τ → 0 ≤ k τ) (τ : ℝ) :
    0 ≤ endpointSafePositiveMajorant k τ := by
  by_cases hτ : 0 < τ
  · simpa [endpointSafePositiveMajorant, hτ] using hk τ hτ
  · simp [endpointSafePositiveMajorant, hτ]

/-- On a nonnegative interval, totalizing a positive-time majorant changes only the left endpoint. -/
theorem intervalIntegrable_endpointSafePositiveMajorant
    (k : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hk : IntervalIntegrable k volume 0 t) :
    IntervalIntegrable (endpointSafePositiveMajorant k) volume 0 t := by
  refine hk.congr ?_
  intro s hs
  rw [uIoc_of_le ht] at hs
  exact (endpointSafePositiveMajorant_of_pos k hs.1).symm

/-- Time reversal preserves interval-integrability of the endpoint-safe elapsed-time kernel. -/
theorem intervalIntegrable_endpointSafePositiveMajorant_sub
    (k : ℝ → ℝ) {t : ℝ}
    (hk : IntervalIntegrable (endpointSafePositiveMajorant k) volume 0 t) :
    IntervalIntegrable
      (fun s : ℝ => endpointSafePositiveMajorant k (t - s)) volume 0 t := by
  simpa using (hk.comp_sub_left t).symm

/-- A positive-time operator estimate extends exactly to the endpoint-safe totalization. -/
theorem norm_endpointSafePositiveOperator_apply_le
    (S : ∀ τ : ℝ, 0 < τ → Y →L[𝕜] X) (k : ℝ → ℝ)
    (hS : ∀ (τ : ℝ) (hτ : 0 < τ) (y : Y),
      ‖S τ hτ y‖ ≤ k τ * ‖y‖)
    (τ : ℝ) (y : Y) :
    ‖endpointSafePositiveOperator S τ y‖ ≤
      endpointSafePositiveMajorant k τ * ‖y‖ := by
  by_cases hτ : 0 < τ
  · simpa [endpointSafePositiveOperator, endpointSafePositiveMajorant, hτ] using
      hS τ hτ y
  · simp [endpointSafePositiveOperator, endpointSafePositiveMajorant, hτ]

/-- The operator norms of a curried continuous bilinear map give its standard product bound. -/
theorem norm_continuousBilinear_apply_le
    (Q : X →L[𝕜] X →L[𝕜] Y) (u v : X) :
    ‖Q u v‖ ≤ ‖Q‖ * ‖u‖ * ‖v‖ := by
  calc
    ‖Q u v‖ ≤ ‖Q u‖ * ‖v‖ := (Q u).le_opNorm v
    _ ≤ (‖Q‖ * ‖u‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right (Q.le_opNorm u) (norm_nonneg v)
    _ = ‖Q‖ * ‖u‖ * ‖v‖ := rfl

/--
The actual two-space Duhamel integrand at final time `t`.

`Q (u s) (u s)` lies in the rough space `Y`; positive elapsed-time smoothing maps it
back to the solution space `X`.  The endpoint `s = t` is definitionally handled by the
zero branch of `endpointSafePositiveOperator`.
-/
def endpointSafeTwoSpaceDuhamelIntegrand
    (S : ∀ τ : ℝ, 0 < τ → Y →L[𝕜] X)
    (Q : X →L[𝕜] X →L[𝕜] Y)
    (t : ℝ) (u : ℝ → X) (s : ℝ) : X :=
  endpointSafePositiveOperator S (t - s) (Q (u s) (u s))

@[simp]
theorem endpointSafeTwoSpaceDuhamelIntegrand_endpoint
    (S : ∀ τ : ℝ, 0 < τ → Y →L[𝕜] X)
    (Q : X →L[𝕜] X →L[𝕜] Y)
    (t : ℝ) (u : ℝ → X) :
    endpointSafeTwoSpaceDuhamelIntegrand S Q t u t = 0 := by
  simp [endpointSafeTwoSpaceDuhamelIntegrand]

theorem endpointSafeTwoSpaceDuhamelIntegrand_of_lt
    (S : ∀ τ : ℝ, 0 < τ → Y →L[𝕜] X)
    (Q : X →L[𝕜] X →L[𝕜] Y)
    (t : ℝ) (u : ℝ → X) {s : ℝ} (hs : s < t) :
    endpointSafeTwoSpaceDuhamelIntegrand S Q t u s =
      S (t - s) (sub_pos.mpr hs) (Q (u s) (u s)) := by
  simp [endpointSafeTwoSpaceDuhamelIntegrand, sub_pos.mpr hs]

theorem endpointSafeTwoSpaceDuhamelIntegrand_of_le
    (S : ∀ τ : ℝ, 0 < τ → Y →L[𝕜] X)
    (Q : X →L[𝕜] X →L[𝕜] Y)
    (t : ℝ) (u : ℝ → X) {s : ℝ} (hs : t ≤ s) :
    endpointSafeTwoSpaceDuhamelIntegrand S Q t u s = 0 := by
  have hnonpos : t - s ≤ 0 := sub_nonpos.mpr hs
  simp [endpointSafeTwoSpaceDuhamelIntegrand,
    endpointSafePositiveOperator_of_nonpos S hnonpos]

/-- A continuous trajectory gives a continuous actual integrand away from both endpoints. -/
theorem continuousOn_endpointSafeTwoSpaceDuhamelIntegrand_Ioo
    (S : ∀ τ : ℝ, 0 < τ → Y →L[𝕜] X)
    (Q : X →L[𝕜] X →L[𝕜] Y)
    {t : ℝ} {u : ℝ → X}
    (hu : ContinuousOn u (Icc 0 t))
    (hS : ContinuousOn
      (fun p : ℝ × Y => endpointSafePositiveOperator S p.1 p.2)
      (Ioi 0 ×ˢ (Set.univ : Set Y))) :
    ContinuousOn (endpointSafeTwoSpaceDuhamelIntegrand S Q t u) (Ioo 0 t) := by
  have huIoo : ContinuousOn u (Ioo 0 t) :=
    hu.mono fun _ hs => ⟨hs.1.le, hs.2.le⟩
  have hQ : ContinuousOn (fun s => Q (u s) (u s)) (Ioo 0 t) :=
    (Q.continuous.comp_continuousOn huIoo).clm_apply huIoo
  have helapsed : ContinuousOn (fun s : ℝ => t - s) (Ioo 0 t) :=
    continuousOn_const.sub continuousOn_id
  have hpair : ContinuousOn
      (fun s : ℝ => (t - s, Q (u s) (u s))) (Ioo 0 t) :=
    helapsed.prodMk hQ
  have hmaps : MapsTo
      (fun s : ℝ => (t - s, Q (u s) (u s)))
      (Ioo 0 t) (Ioi 0 ×ˢ (Set.univ : Set Y)) := by
    intro s hs
    exact ⟨sub_pos.mpr hs.2, Set.mem_univ _⟩
  exact hS.comp' hpair hmaps

/--
Strong measurability of the actual vector-valued integrand follows from positive-time
continuity and the nullity of the right endpoint.  This is stronger than measurability of
the scalar smoothing kernel alone.
-/
theorem aestronglyMeasurable_endpointSafeTwoSpaceDuhamelIntegrand_interval
    (S : ∀ τ : ℝ, 0 < τ → Y →L[𝕜] X)
    (Q : X →L[𝕜] X →L[𝕜] Y)
    {t : ℝ} (ht : 0 ≤ t) {u : ℝ → X}
    (hu : ContinuousOn u (Icc 0 t))
    (hS : ContinuousOn
      (fun p : ℝ × Y => endpointSafePositiveOperator S p.1 p.2)
      (Ioi 0 ×ˢ (Set.univ : Set Y))) :
    AEStronglyMeasurable (endpointSafeTwoSpaceDuhamelIntegrand S Q t u)
      (volume.restrict (Ι (0 : ℝ) t)) := by
  exact aestronglyMeasurable_interval_of_continuousOn_Ioo ht
    (continuousOn_endpointSafeTwoSpaceDuhamelIntegrand_Ioo S Q hu hS)

/-- Pointwise norm bound for the actual endpoint-safe integrand. -/
theorem norm_endpointSafeTwoSpaceDuhamelIntegrand_le
    (S : ∀ τ : ℝ, 0 < τ → Y →L[𝕜] X)
    (Q : X →L[𝕜] X →L[𝕜] Y)
    (k : ℝ → ℝ)
    (hk : ∀ τ, 0 < τ → 0 ≤ k τ)
    (hS : ∀ (τ : ℝ) (hτ : 0 < τ) (y : Y),
      ‖S τ hτ y‖ ≤ k τ * ‖y‖)
    (t : ℝ) (u : ℝ → X) (s : ℝ) :
    ‖endpointSafeTwoSpaceDuhamelIntegrand S Q t u s‖ ≤
      endpointSafePositiveMajorant k (t - s) * ‖Q‖ * ‖u s‖ ^ 2 := by
  let K := endpointSafePositiveMajorant k (t - s)
  have hK : 0 ≤ K := endpointSafePositiveMajorant_nonneg k hk (t - s)
  calc
    ‖endpointSafeTwoSpaceDuhamelIntegrand S Q t u s‖ ≤
        K * ‖Q (u s) (u s)‖ := by
      exact norm_endpointSafePositiveOperator_apply_le S k hS (t - s)
        (Q (u s) (u s))
    _ ≤ K * (‖Q‖ * ‖u s‖ * ‖u s‖) :=
      mul_le_mul_of_nonneg_left
        (norm_continuousBilinear_apply_le Q (u s) (u s)) hK
    _ = endpointSafePositiveMajorant k (t - s) * ‖Q‖ * ‖u s‖ ^ 2 := by
      simp only [K]
      ring

/-- Uniform trajectory control turns the pointwise estimate into the scalar majorant used below. -/
theorem norm_endpointSafeTwoSpaceDuhamelIntegrand_le_of_trajectory_norm
    (S : ∀ τ : ℝ, 0 < τ → Y →L[𝕜] X)
    (Q : X →L[𝕜] X →L[𝕜] Y)
    (k : ℝ → ℝ)
    (hk : ∀ τ, 0 < τ → 0 ≤ k τ)
    (hS : ∀ (τ : ℝ) (hτ : 0 < τ) (y : Y),
      ‖S τ hτ y‖ ≤ k τ * ‖y‖)
    (t : ℝ) (u : ℝ → X) (R : ℝ) (hR : 0 ≤ R)
    (s : ℝ) (hu : ‖u s‖ ≤ R) :
    ‖endpointSafeTwoSpaceDuhamelIntegrand S Q t u s‖ ≤
      endpointSafePositiveMajorant k (t - s) * ‖Q‖ * R ^ 2 := by
  calc
    ‖endpointSafeTwoSpaceDuhamelIntegrand S Q t u s‖ ≤
        endpointSafePositiveMajorant k (t - s) * ‖Q‖ * ‖u s‖ ^ 2 :=
      norm_endpointSafeTwoSpaceDuhamelIntegrand_le S Q k hk hS t u s
    _ ≤ endpointSafePositiveMajorant k (t - s) * ‖Q‖ * R ^ 2 := by
      apply mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg (u s)) hR).2 hu)
      exact mul_nonneg
        (endpointSafePositiveMajorant_nonneg k hk (t - s)) (norm_nonneg Q)

/--
Bochner interval-integrability of the actual two-space Duhamel integrand.

The theorem deliberately assumes strong measurability of the *actual vector-valued
integrand*, not merely of the trajectory or the scalar kernel.  All remaining size control
is reduced to the displayed scalar majorant and an a.e. uniform trajectory norm bound.
-/
theorem intervalIntegrable_endpointSafeTwoSpaceDuhamelIntegrand
    [CompleteSpace X]
    (S : ∀ τ : ℝ, 0 < τ → Y →L[𝕜] X)
    (Q : X →L[𝕜] X →L[𝕜] Y)
    (k : ℝ → ℝ)
    (hk : ∀ τ, 0 < τ → 0 ≤ k τ)
    (hS : ∀ (τ : ℝ) (hτ : 0 < τ) (y : Y),
      ‖S τ hτ y‖ ≤ k τ * ‖y‖)
    (t : ℝ) (u : ℝ → X) (R : ℝ) (hR : 0 ≤ R)
    (hmeas : AEStronglyMeasurable
      (endpointSafeTwoSpaceDuhamelIntegrand S Q t u)
      (volume.restrict (Ι (0 : ℝ) t)))
    (hu : ∀ᵐ s ∂volume.restrict (Ι (0 : ℝ) t), ‖u s‖ ≤ R)
    (hmajorant : IntervalIntegrable
      (fun s : ℝ =>
        endpointSafePositiveMajorant k (t - s) * ‖Q‖ * R ^ 2)
      volume 0 t) :
    IntervalIntegrable
      (endpointSafeTwoSpaceDuhamelIntegrand S Q t u) volume 0 t := by
  refine hmajorant.mono_fun' hmeas ?_
  filter_upwards [hu] with s hs
  exact norm_endpointSafeTwoSpaceDuhamelIntegrand_le_of_trajectory_norm
    S Q k hk hS t u R hR s hs

/--
Convenience form using the original positive-time kernel on `[0,t]`.

The endpoint totalization, time reversal `τ = t - s`, and multiplication by the constant
quadratic/trajectory factor are all discharged internally.
-/
theorem intervalIntegrable_endpointSafeTwoSpaceDuhamelIntegrand_of_kernel
    [CompleteSpace X]
    (S : ∀ τ : ℝ, 0 < τ → Y →L[𝕜] X)
    (Q : X →L[𝕜] X →L[𝕜] Y)
    (k : ℝ → ℝ)
    (hk : ∀ τ, 0 < τ → 0 ≤ k τ)
    (hS : ∀ (τ : ℝ) (hτ : 0 < τ) (y : Y),
      ‖S τ hτ y‖ ≤ k τ * ‖y‖)
    (t : ℝ) (ht : 0 ≤ t) (u : ℝ → X) (R : ℝ) (hR : 0 ≤ R)
    (hmeas : AEStronglyMeasurable
      (endpointSafeTwoSpaceDuhamelIntegrand S Q t u)
      (volume.restrict (Ι (0 : ℝ) t)))
    (hu : ∀ᵐ s ∂volume.restrict (Ι (0 : ℝ) t), ‖u s‖ ≤ R)
    (hkernel : IntervalIntegrable k volume 0 t) :
    IntervalIntegrable
      (endpointSafeTwoSpaceDuhamelIntegrand S Q t u) volume 0 t := by
  have hsafe :
      IntervalIntegrable (endpointSafePositiveMajorant k) volume 0 t :=
    intervalIntegrable_endpointSafePositiveMajorant k ht hkernel
  have hrev : IntervalIntegrable
      (fun s : ℝ => endpointSafePositiveMajorant k (t - s)) volume 0 t :=
    intervalIntegrable_endpointSafePositiveMajorant_sub k hsafe
  have hmajorant : IntervalIntegrable
      (fun s : ℝ =>
        endpointSafePositiveMajorant k (t - s) * ‖Q‖ * R ^ 2)
      volume 0 t := by
    simpa only [mul_assoc] using (hrev.mul_const (‖Q‖ * R ^ 2))
  exact intervalIntegrable_endpointSafeTwoSpaceDuhamelIntegrand
    S Q k hk hS t u R hR hmeas hu hmajorant

/-!
## Bundled production contract

The free-function API above is intentionally retained.  The following structure bundles exactly
the data needed by a two-space mild equation while keeping the two Stokes roles type-separated:

* `linearEvolution` is a strongly continuous semigroup on nonnegative time in `X` and is used
  only on the initial datum;
* `positiveSmoothing` maps the rough nonlinear space `Y` into `X` for positive elapsed time;
* `bilinear` is the quadratic source map `X × X → Y`;
* `smoothingKernel` and its fields certify the positive-time bound and local integrability.
-/

/-- Analytic data for an endpoint-safe two-space quadratic mild equation. -/
structure EndpointSafeTwoSpaceDuhamelContract
    (𝕜 : Type u) (X : Type v) (Y : Type w)
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] where
  /-- Same-space linear evolution used on the initial datum. -/
  linearEvolution : ℝ≥0 → X →L[𝕜] X
  /-- The same-space evolution is the identity at elapsed time zero. -/
  linear_zero :
    linearEvolution 0 = ContinuousLinearMap.id 𝕜 X
  /-- Semigroup law on the honest nonnegative-time domain. -/
  linear_add : ∀ a b : ℝ≥0,
    linearEvolution (a + b) =
      (linearEvolution a).comp (linearEvolution b)
  /-- Strong/joint continuity of the action; operator-norm continuity is not assumed. -/
  continuous_linear_action :
    Continuous (fun p : ℝ≥0 × X => linearEvolution p.1 p.2)
  /-- Genuine smoothing from the rough space, available only at positive elapsed time. -/
  positiveSmoothing : ∀ τ : ℝ, 0 < τ → Y →L[𝕜] X
  /-- Continuous bilinear source map; its diagonal is the quadratic nonlinearity. -/
  bilinear : X →L[𝕜] X →L[𝕜] Y
  /-- Scalar positive-time smoothing majorant. -/
  smoothingKernel : ℝ → ℝ
  /-- Positivity of the majorant wherever smoothing is used. -/
  smoothingKernel_nonneg : ∀ τ : ℝ, 0 < τ → 0 ≤ smoothingKernel τ
  /-- Pointwise operator estimate for positive elapsed time. -/
  norm_positiveSmoothing_apply_le :
    ∀ (τ : ℝ) (hτ : 0 < τ) (y : Y),
      ‖positiveSmoothing τ hτ y‖ ≤ smoothingKernel τ * ‖y‖
  /-- The scalar singularity is locally integrable at the elapsed-time endpoint. -/
  intervalIntegrable_smoothingKernel :
    ∀ T : ℝ, 0 ≤ T → IntervalIntegrable smoothingKernel volume 0 T
  /-- Positive-time smoothing is the coherent rough-to-strong extension of the semigroup. -/
  smoothing_coherent :
    ∀ (a : ℝ) (ha : 0 < a) (b : ℝ≥0),
      positiveSmoothing (a + (b : ℝ))
          (add_pos_of_pos_of_nonneg ha b.property) =
        (linearEvolution b).comp (positiveSmoothing a ha)

namespace EndpointSafeTwoSpaceDuhamelContract

variable
    (C : EndpointSafeTwoSpaceDuhamelContract 𝕜 X Y)

/-- Endpoint-safe totalization of the contract's genuinely positive-time smoothing family. -/
def endpointSafeSmoothing (τ : ℝ) : Y →L[𝕜] X :=
  endpointSafePositiveOperator C.positiveSmoothing τ

@[simp]
theorem endpointSafeSmoothing_of_pos
    {τ : ℝ} (hτ : 0 < τ) :
    C.endpointSafeSmoothing τ = C.positiveSmoothing τ hτ := by
  exact endpointSafePositiveOperator_of_pos C.positiveSmoothing hτ

@[simp]
theorem endpointSafeSmoothing_of_nonpos
    {τ : ℝ} (hτ : τ ≤ 0) :
    C.endpointSafeSmoothing τ = 0 := by
  exact endpointSafePositiveOperator_of_nonpos C.positiveSmoothing hτ

@[simp]
theorem endpointSafeSmoothing_zero :
    C.endpointSafeSmoothing 0 = 0 := by
  exact endpointSafePositiveOperator_zero C.positiveSmoothing

/-- The contract's actual endpoint-safe, `X`-valued Duhamel integrand. -/
def duhamelIntegrand
    (t : ℝ) (trajectory : ℝ → X) (s : ℝ) : X :=
  endpointSafeTwoSpaceDuhamelIntegrand
    C.positiveSmoothing C.bilinear t trajectory s

@[simp]
theorem duhamelIntegrand_endpoint
    (t : ℝ) (trajectory : ℝ → X) :
    C.duhamelIntegrand t trajectory t = 0 := by
  exact endpointSafeTwoSpaceDuhamelIntegrand_endpoint
    C.positiveSmoothing C.bilinear t trajectory

theorem duhamelIntegrand_of_lt
    (t : ℝ) (trajectory : ℝ → X) {s : ℝ} (hs : s < t) :
    C.duhamelIntegrand t trajectory s =
      C.positiveSmoothing (t - s) (sub_pos.mpr hs)
        (C.bilinear (trajectory s) (trajectory s)) := by
  exact endpointSafeTwoSpaceDuhamelIntegrand_of_lt
    C.positiveSmoothing C.bilinear t trajectory hs

theorem duhamelIntegrand_of_le
    (t : ℝ) (trajectory : ℝ → X) {s : ℝ} (hs : t ≤ s) :
    C.duhamelIntegrand t trajectory s = 0 := by
  exact endpointSafeTwoSpaceDuhamelIntegrand_of_le
    C.positiveSmoothing C.bilinear t trajectory hs

/-- The bundled laws supply joint positive-time continuity of the smoothing action. -/
theorem continuousOn_endpointSafeSmoothing_action :
    ContinuousOn
      (fun p : ℝ × Y => C.endpointSafeSmoothing p.1 p.2)
      (Ioi 0 ×ˢ (Set.univ : Set Y)) := by
  exact continuousOn_endpointSafePositiveOperator_of_coherent
    C.linearEvolution C.positiveSmoothing
    C.continuous_linear_action C.smoothing_coherent

/-- A continuous trajectory gives a continuous bundled integrand off the null endpoints. -/
theorem continuousOn_duhamelIntegrand_Ioo
    {t : ℝ} {trajectory : ℝ → X}
    (htrajectory : ContinuousOn trajectory (Icc 0 t)) :
    ContinuousOn (C.duhamelIntegrand t trajectory) (Ioo 0 t) := by
  exact continuousOn_endpointSafeTwoSpaceDuhamelIntegrand_Ioo
    C.positiveSmoothing C.bilinear htrajectory
    C.continuousOn_endpointSafeSmoothing_action

/-- Actual-vector strong measurability, derived rather than assumed by the bundled contract. -/
theorem aestronglyMeasurable_duhamelIntegrand_interval
    {t : ℝ} (ht : 0 ≤ t) {trajectory : ℝ → X}
    (htrajectory : ContinuousOn trajectory (Icc 0 t)) :
    AEStronglyMeasurable (C.duhamelIntegrand t trajectory)
      (volume.restrict (Ι (0 : ℝ) t)) := by
  exact aestronglyMeasurable_endpointSafeTwoSpaceDuhamelIntegrand_interval
    C.positiveSmoothing C.bilinear ht htrajectory
    C.continuousOn_endpointSafeSmoothing_action

/-- Bundled form of the pointwise quadratic Duhamel estimate. -/
theorem norm_duhamelIntegrand_le
    (t : ℝ) (trajectory : ℝ → X) (s : ℝ) :
    ‖C.duhamelIntegrand t trajectory s‖ ≤
      endpointSafePositiveMajorant C.smoothingKernel (t - s) *
        ‖C.bilinear‖ * ‖trajectory s‖ ^ 2 := by
  exact norm_endpointSafeTwoSpaceDuhamelIntegrand_le
    C.positiveSmoothing C.bilinear C.smoothingKernel
    C.smoothingKernel_nonneg C.norm_positiveSmoothing_apply_le
    t trajectory s

/--
The bundled local-integrability certificate reduces Bochner integrability to strong
measurability of the actual integrand and an a.e. trajectory norm bound.
-/
theorem intervalIntegrable_duhamelIntegrand_of_trajectory_norm
    [CompleteSpace X]
    (t : ℝ) (ht : 0 ≤ t) (trajectory : ℝ → X)
    (R : ℝ) (hR : 0 ≤ R)
    (hmeas : AEStronglyMeasurable
      (C.duhamelIntegrand t trajectory)
      (volume.restrict (Ι (0 : ℝ) t)))
    (htrajectory :
      ∀ᵐ s ∂volume.restrict (Ι (0 : ℝ) t), ‖trajectory s‖ ≤ R) :
    IntervalIntegrable (C.duhamelIntegrand t trajectory) volume 0 t := by
  exact intervalIntegrable_endpointSafeTwoSpaceDuhamelIntegrand_of_kernel
    C.positiveSmoothing C.bilinear C.smoothingKernel
    C.smoothingKernel_nonneg C.norm_positiveSmoothing_apply_le
    t ht trajectory R hR hmeas htrajectory
    (C.intervalIntegrable_smoothingKernel t ht)

/--
A continuous trajectory on the compact interval automatically gives an actual Bochner-integrable
Duhamel integrand.  The compact norm bound is combined with the vector-valued measurability theorem
above and the contract's locally integrable scalar smoothing majorant.
-/
theorem intervalIntegrable_duhamelIntegrand_of_continuousOn
    [CompleteSpace X]
    {t : ℝ} (ht : 0 ≤ t) {trajectory : ℝ → X}
    (htrajectory : ContinuousOn trajectory (Icc 0 t)) :
    IntervalIntegrable (C.duhamelIntegrand t trajectory) volume 0 t := by
  obtain ⟨R, hRupper⟩ := isCompact_Icc.bddAbove_image htrajectory.norm
  have hRu : ∀ s ∈ Icc (0 : ℝ) t, ‖trajectory s‖ ≤ R := by
    intro s hs
    exact hRupper (mem_image_of_mem _ hs)
  have hR : 0 ≤ R :=
    (norm_nonneg (trajectory 0)).trans (hRu 0 ⟨le_rfl, ht⟩)
  have hmeas := C.aestronglyMeasurable_duhamelIntegrand_interval ht htrajectory
  have hae :
      ∀ᵐ s ∂volume.restrict (Ι (0 : ℝ) t), ‖trajectory s‖ ≤ R := by
    rw [uIoc_of_le ht]
    exact ae_restrict_of_forall_mem measurableSet_Ioc fun s hs =>
      hRu s ⟨hs.1.le, hs.2⟩
  exact C.intervalIntegrable_duhamelIntegrand_of_trajectory_norm
    t ht trajectory R hR hmeas hae

section MildPredicate

-- Time integration is real even when the operator field `𝕜` is complex.
variable [NormedSpace ℝ X]

/--
The mild equation at one certified time.

The integrability clause is part of the predicate, so the equation cannot hold merely because
mathlib totalizes the Bochner integral of a non-integrable function by zero.
-/
def IsMildAt
    (t : ℝ≥0) (u₀ : X) (trajectory : ℝ → X) : Prop :=
  IntervalIntegrable (C.duhamelIntegrand (t : ℝ) trajectory) volume 0 (t : ℝ) ∧
  trajectory (t : ℝ) =
    C.linearEvolution t u₀ -
      ∫ s in (0 : ℝ)..(t : ℝ), C.duhamelIntegrand (t : ℝ) trajectory s

/--
A continuous trajectory on `[0,T]` satisfying the two-space mild equation at every time.

The initial term always uses the same-space `linearEvolution`; only the nonlinear source passes
through the endpoint-safe `Y → X` smoothing family.
-/
def IsMildSolutionOn
    (T : ℝ) (u₀ : X) (trajectory : ℝ → X) : Prop :=
  0 ≤ T ∧
  ContinuousOn trajectory (Icc (0 : ℝ) T) ∧
  trajectory 0 = u₀ ∧
  ∀ t, ∀ ht : t ∈ Icc (0 : ℝ) T,
    C.IsMildAt ⟨t, ht.1⟩ u₀ trajectory

/-- At time zero, the mild equation is exactly the initial-value condition. -/
theorem isMildAt_zero_iff
    (u₀ : X) (trajectory : ℝ → X) :
    C.IsMildAt (0 : ℝ≥0) u₀ trajectory ↔ trajectory 0 = u₀ := by
  simp [IsMildAt, C.linear_zero]

/-- Extract the initial-value clause from a certified mild trajectory. -/
theorem initial_value
    {T : ℝ} {u₀ : X} {trajectory : ℝ → X}
    (h : C.IsMildSolutionOn T u₀ trajectory) :
    trajectory 0 = u₀ := by
  exact h.2.2.1

/-- Extract the actual endpoint-safe Duhamel equation at a certified time. -/
theorem equation_at_time
    {T : ℝ} {u₀ : X} {trajectory : ℝ → X}
    (h : C.IsMildSolutionOn T u₀ trajectory)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    IntervalIntegrable (C.duhamelIntegrand t trajectory) volume 0 t ∧
    trajectory t =
      C.linearEvolution ⟨t, ht.1⟩ u₀ -
        ∫ s in (0 : ℝ)..t, C.duhamelIntegrand t trajectory s := by
  exact h.2.2.2 t ht

end MildPredicate

end EndpointSafeTwoSpaceDuhamelContract

end EndpointSafeTwoSpaceDuhamel

end

end MNS2
