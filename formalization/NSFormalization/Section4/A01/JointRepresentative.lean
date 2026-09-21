import NSFormalization.Section4.A01.DatumPathSmooth
import NSFormalization.Section4.D01.DerivativeDatum
import NSFormalization.Section4.A03.ScalarTameProduct
import NSFormalization.Source.FourierPhysicalJets
import Euler.BoundedEvaluationDifferentiation
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# A jointly smooth representative of the ordinary cylinder solution

The order-two angular bounded representative is used for the value of the
field.  Higher-order datum paths prove its regularity.  At finite joint order
`N`, the order-`N+2` path supplies the spatial derivatives, while its `C^N`
time regularity supplies the time derivatives.  Continuous representatives
of two data orders agree everywhere because they represent the same physical
slice almost everywhere.
-/

noncomputable section

open Set Filter MeasureTheory
open Asymptotics ContinuousLinearMap
open NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source.RealSobolev
open NSFormalization.Source.FourierPhysicalJets (complexTupleToVector)
open scoped ContDiff Topology SchwartzMap ENNReal LineDeriv

namespace NSFormalization.Section4.A01

open NSFormalization.Section4.D01
open NSFormalization.Section4.A03
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Source.ForcedCylinderLocal
open EulerLpTranslation EulerMeanOrdinaryLift EulerCylinderSobolevSpace
  EulerLiftedGradientSpace EulerCylinderSobolev EulerQuadraticSource
  EulerVolterraConvolution

/-! ## Differentiation of a bounded evaluation on a closed time set -/

/-- Closed-set form of `EulerBoundedEvaluation.hasFDerivAt`.  The time path
only needs a within derivative; the spatial variable remains unrestricted. -/
theorem boundedEvaluation_hasFDerivWithinAt
    {X H V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (E : X → H →L[ℝ] V) (C : ℝ) (hE : ∀ x, ‖E x‖ ≤ C)
    (u : ℝ → H) (u' : H) (S : Set ℝ) (t : ℝ) (x : X)
    (hu : HasDerivWithinAt u u' S t) (D : X →L[ℝ] V)
    (hx : HasFDerivAt (fun y => E y (u t)) D x)
    (hc : ContinuousAt (fun y => E y u') x) :
    HasFDerivWithinAt (fun q : ℝ × X => E q.2 (u q.1))
      (((toSpanSingleton ℝ (E x u')).comp (fst ℝ ℝ X)) +
        D.comp (snd ℝ ℝ X)) (S ×ˢ (univ : Set X)) (t, x) := by
  let l : Filter (ℝ × X) := 𝓝[S ×ˢ (univ : Set X)] (t, x)
  have hl : l = 𝓝[S] t ×ˢ 𝓝 x := by
    simp only [l, nhdsWithin_prod_eq, nhdsWithin_univ]
  have htend : Tendsto (Prod.fst : ℝ × X → ℝ) l (𝓝[S] t) := by
    rw [hl]
    exact tendsto_fst
  have hxend : Tendsto (Prod.snd : ℝ × X → X) l (𝓝 x) := by
    rw [hl]
    exact tendsto_snd
  have hfst : (fun q : ℝ × X => q.1 - t) =O[l] fun q => q - (t, x) := by
    apply IsBigO.of_bound 1
    exact Eventually.of_forall (fun q => by
      change ‖(q - (t, x)).1‖ ≤ 1 * ‖q - (t, x)‖
      rw [one_mul]
      exact norm_fst_le (q - (t, x)))
  have hsnd : (fun q : ℝ × X => q.2 - x) =O[l] fun q => q - (t, x) := by
    apply IsBigO.of_bound 1
    exact Eventually.of_forall (fun q => by
      change ‖(q - (t, x)).2‖ ≤ 1 * ‖q - (t, x)‖
      rw [one_mul]
      exact norm_snd_le (q - (t, x)))
  have hr : (fun q : ℝ × X => u q.1 - u t - (q.1 - t) • u') =o[l]
      fun q => q - (t, x) :=
    (hu.isLittleO.comp_tendsto htend).trans_isBigO hfst
  have hbound : (fun q : ℝ × X => E q.2 (u q.1 - u t - (q.1 - t) • u')) =O[l]
      fun q => u q.1 - u t - (q.1 - t) • u' := by
    apply IsBigO.of_bound C
    exact Eventually.of_forall (fun q =>
      ((E q.2).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hE q.2) (norm_nonneg _)))
  have hfirst := hbound.trans_isLittleO hr
  have hcont : Tendsto (fun q : ℝ × X => E q.2 u' - E x u') l (𝓝 0) := by
    simpa only [sub_self, Function.comp_def] using
      (hc.tendsto.comp hxend).sub_const (E x u')
  have hsmall : (fun q : ℝ × X => E q.2 u' - E x u') =o[l] fun _ => (1 : ℝ) :=
    (isLittleO_one_iff ℝ).mpr hcont
  have hsecond : (fun q : ℝ × X => (q.1 - t) • (E q.2 u' - E x u')) =o[l]
      fun q => q - (t, x) := by
    have hh := (isBigO_refl (fun q : ℝ × X => q.1 - t) l).smul_isLittleO hsmall
    simp only [smul_eq_mul, mul_one] at hh
    exact hh.trans_isBigO hfst
  have hthird : (fun q : ℝ × X => E q.2 (u t) - E x (u t) - D (q.2 - x)) =o[l]
      fun q => q - (t, x) :=
    (hx.isLittleO.comp_tendsto hxend).trans_isBigO hsnd
  apply hasFDerivWithinAt_iff_isLittleO.mpr
  change (fun q : ℝ × X => E q.2 (u q.1) - E x (u t) -
    (((toSpanSingleton ℝ (E x u')).comp (fst ℝ ℝ X)) +
      D.comp (snd ℝ ℝ X)) (q - (t, x))) =o[l] fun q => q - (t, x)
  apply ((hfirst.add hsecond).add hthird).congr_left
  intro q
  simp only [map_sub, map_smul, add_apply, comp_apply, toSpanSingleton_apply,
    coe_fst', coe_snd', smul_sub]
  module

/-! ## Scalar Sobolev evaluation -/

/-- Schwartz functions are dense in the angular datum carrier at every order. -/
theorem denseRange_angularDatum (s : ℝ) : DenseRange (angularDatum s) := by
  change DenseRange (fun f => cyclesToAngular s (weightedFourierLp s f))
  exact (Function.Surjective.denseRange (cyclesToAngular s).surjective).comp
    (denseRange_weightedFourierLp s) (cyclesToAngular s).continuous

/-- The angular multiplier differentiates an angular Schwartz datum literally. -/
theorem angularDirectionalDerivative_angularDatum (s : ℝ) (a : Space)
    (f : SchwartzMap Space ℂ) :
    angularDirectionalDerivative s a (angularDatum s f) =
      angularDatum (s - 1) (∂_{a} f) := by
  change cyclesToAngular (s - 1)
      (sobolevDirectionalDerivative s a
        ((cyclesToAngular s).symm (cyclesToAngular s (weightedFourierLp s f)))) =
    cyclesToAngular (s - 1) (weightedFourierLp (s - 1) (∂_{a} f))
  rw [ContinuousLinearEquiv.symm_apply_apply,
    sobolevDirectionalDerivative_weightedFourierLp]

/-- The bounded representative of an angular Schwartz datum is the original
Schwartz function. -/
theorem angularBoundedRepresentative_angularDatum (s : ℝ) (hs : 2 ≤ s)
    (f : SchwartzMap Space ℂ) :
    angularBoundedRepresentative s hs (angularDatum s f) =
      SchwartzMap.toBoundedContinuousFunctionCLM ℝ Space ℂ f := by
  change sobolevBoundedRepresentative s hs
      ((cyclesToAngular s).symm (cyclesToAngular s (weightedFourierLp s f))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply,
    sobolevBoundedRepresentative_weightedFourierLp]

/-- The spatial gradient of the canonical scalar representative, as one
bounded linear map from datum space to a bounded continuous field of linear
maps. -/
def angularRepresentativeGradient (s : ℝ) (hs : 3 ≤ s) :
    FourierData →L[ℝ] BoundedContinuousFunction Space (Space →L[ℝ] ℂ) :=
  ∑ i : Fin 3,
    ((ContinuousLinearMap.smulRightL ℝ Space ℂ
        (EuclideanSpace.proj i)).compLeftContinuousBounded Space).comp
      ((angularBoundedRepresentative (s - 1) (by linarith)).comp
        ((angularDirectionalDerivative s (coordinateVector i)).restrictScalars ℝ))

@[simp] theorem angularRepresentativeGradient_apply (s : ℝ) (hs : 3 ≤ s)
    (h : FourierData) (x v : Space) :
    angularRepresentativeGradient s hs h x v =
      ∑ i : Fin 3, v i •
        angularBoundedRepresentative (s - 1) (by linarith)
          (angularDirectionalDerivative s (coordinateVector i) h) x := by
  simp [angularRepresentativeGradient, ContinuousLinearMap.smulRight_apply]

/-- The spatial derivative formula for the canonical scalar representative.
It is proved on the dense Schwartz core and closed using uniform convergence
of both the representatives and their bounded gradient fields. -/
theorem angularBoundedRepresentative_hasFDerivAt (s : ℝ) (hs : 3 ≤ s)
    (h : FourierData) (x : Space) :
    HasFDerivAt (fun y => angularBoundedRepresentative s (by linarith) h y)
      (angularRepresentativeGradient s hs h x) x := by
  have hs2 : 2 ≤ s := by linarith
  let P : FourierData → Prop := fun k => ∀ x : Space,
    HasFDerivAt (fun y => angularBoundedRepresentative s hs2 k y)
      (angularRepresentativeGradient s hs k x) x
  apply (denseRange_angularDatum s).induction_on (p := P) h
  · apply isSeqClosed_iff_isClosed.mp
    intro u k hu huk x
    have hfun : TendstoUniformly
        (fun n y => angularBoundedRepresentative s hs2 (u n) y)
        (fun y => angularBoundedRepresentative s hs2 k y) atTop := by
      apply Metric.tendstoUniformly_iff.mpr
      intro ε hε
      have ht := ((angularBoundedRepresentative s hs2).continuous.tendsto k).comp huk
      filter_upwards [ht.eventually
        (Metric.ball_mem_nhds ((angularBoundedRepresentative s hs2) k) hε)]
        with n hn y
      apply (BoundedContinuousFunction.dist_coe_le_dist y).trans_lt
      rw [dist_comm]
      exact hn
    have hgrad : TendstoUniformly
        (fun n y => angularRepresentativeGradient s hs (u n) y)
        (fun y => angularRepresentativeGradient s hs k y) atTop := by
      apply Metric.tendstoUniformly_iff.mpr
      intro ε hε
      have ht := ((angularRepresentativeGradient s hs).continuous.tendsto k).comp huk
      filter_upwards [ht.eventually
        (Metric.ball_mem_nhds ((angularRepresentativeGradient s hs) k) hε)] with n hn y
      apply (BoundedContinuousFunction.dist_coe_le_dist y).trans_lt
      rw [dist_comm]
      exact hn
    exact hasFDerivAt_of_tendstoUniformly hgrad (fun n y => hu n y)
      (fun y => hfun.tendsto_at y) x
  · intro f x
    have hf : HasFDerivAt (fun y : Space => f y) (fderiv ℝ (⇑f) x) x :=
      f.differentiableAt.hasFDerivAt
    convert hf using 1
    · funext y
      rw [angularBoundedRepresentative_angularDatum]
      rfl
    · apply ContinuousLinearMap.ext
      intro v
      rw [angularRepresentativeGradient_apply]
      simp_rw [angularDirectionalDerivative_angularDatum,
        angularBoundedRepresentative_angularDatum]
      change (∑ i : Fin 3, v i • (∂_{coordinateVector i} f) x) =
        fderiv ℝ (⇑f) x v
      simp_rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
      simpa only [map_sum, map_smul] using
        congrArg (fderiv ℝ (⇑f) x)
          (NavierStokes.PeriodicUniqueness.sum_coordinates v)

/-- An order-`s` datum has a `C^n` canonical representative whenever
`n + 2 ≤ s`. -/
theorem angularBoundedRepresentative_contDiff (n : ℕ) (s : ℝ)
    (horder : (n : ℝ) + 2 ≤ s) (h : FourierData) :
    ContDiff ℝ n (fun x => angularBoundedRepresentative s (by linarith) h x) := by
  induction n generalizing s h with
  | zero =>
      exact contDiff_zero.mpr
        (angularBoundedRepresentative s (by linarith) h).continuous
  | succ n ih =>
      rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
      have hs3 : 3 ≤ s := by
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        push_cast at horder
        linarith
      refine ⟨fun x => (angularBoundedRepresentative_hasFDerivAt s hs3 h x).differentiableAt,
        by simp, ?_⟩
      have hfderiv : fderiv ℝ
          (fun x => angularBoundedRepresentative s (by linarith) h x) =
          fun x => angularRepresentativeGradient s hs3 h x := by
        funext x
        exact (angularBoundedRepresentative_hasFDerivAt s hs3 h x).fderiv
      rw [hfderiv]
      change ContDiff ℝ n (fun x => ∑ i : Fin 3,
        (EuclideanSpace.proj i).smulRight
          (angularBoundedRepresentative (s - 1) (by linarith)
            (angularDirectionalDerivative s (coordinateVector i) h) x))
      have hlo : (n : ℝ) + 2 ≤ s - 1 := by
        push_cast at horder
        linarith
      exact ContDiff.sum (fun i _ =>
        (ContinuousLinearMap.smulRightL ℝ Space ℂ
          (EuclideanSpace.proj i)).contDiff.comp
            (ih (s - 1) hlo
              (angularDirectionalDerivative s (coordinateVector i) h)))

/-! ## Joint scalar evaluation -/

/-- Point evaluation of the canonical order-`s` representative, as a uniformly
bounded continuous linear map on the angular datum carrier. -/
def angularEvaluation (s : ℝ) (hs : 2 ≤ s) (x : Space) :
    FourierData →L[ℝ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℝ x).comp
    (angularBoundedRepresentative s hs)

/-- Evaluation of a bounded continuous function is jointly continuous in the
function and the point. -/
theorem boundedContinuousEvaluation_continuous :
    Continuous (fun p : BoundedContinuousFunction Space ℂ × Space => p.1 p.2) := by
  apply continuous_prod_of_continuous_lipschitzWith _ 1
  · intro f
    exact f.continuous
  · intro x
    apply LipschitzWith.of_dist_le_mul
    intro f g
    simpa only [NNReal.coe_one, one_mul] using
      (BoundedContinuousFunction.dist_coe_le_dist (f := f) (g := g) x)

/-- The scalar joint representative associated with one Sobolev datum path. -/
def scalarJointRepresentative (s : ℝ) (hs : 2 ≤ s)
    (G : ℝ → FourierData) : ℝ × Space → ℂ :=
  fun z => angularBoundedRepresentative s hs (G z.1) z.2

/-- A `C^n` path of order-`s` scalar data, with `s ≥ n+2`, evaluates to a
jointly `C^n` scalar field on the closed slab. -/
theorem scalarJointRepresentative_contDiffOn (n : ℕ) (s S : ℝ) (hS : 0 < S)
    (horder : (n : ℝ) + 2 ≤ s) (G : ℝ → FourierData)
    (hG : ContDiffOn ℝ n G (Icc (0 : ℝ) S)) :
    ContDiffOn ℝ n (scalarJointRepresentative s (by linarith) G)
      (Icc (0 : ℝ) S ×ˢ (univ : Set Space)) := by
  induction n generalizing s G with
  | zero =>
      apply contDiffOn_zero.mpr
      have hrep : ContinuousOn
          (fun t => angularBoundedRepresentative s (by linarith) (G t))
          (Icc (0 : ℝ) S) :=
        (angularBoundedRepresentative s (by linarith)).continuous.comp_continuousOn
          hG.continuousOn
      exact boundedContinuousEvaluation_continuous.comp_continuousOn
        ((hrep.comp continuousOn_fst (fun _ hz => hz.1)).prodMk continuousOn_snd)
  | succ n ih =>
      have hs3 : 3 ≤ s := by
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        push_cast at horder
        linarith
      let I : Set ℝ := Icc (0 : ℝ) S
      let slab : Set (ℝ × Space) := I ×ˢ (univ : Set Space)
      let G' : ℝ → FourierData := derivWithin G I
      have hG' : ContDiffOn ℝ n G' I := by
        apply hG.derivWithin (uniqueDiffOn_Icc hS)
        rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp]
      have hscalarTime : ContDiffOn ℝ n
          (scalarJointRepresentative s (by linarith) G') slab := by
        apply ih s (by push_cast at horder; linarith) G' hG'
      have hscalarSpace (i : Fin 3) : ContDiffOn ℝ n
          (scalarJointRepresentative (s - 1) (by linarith)
            (fun t => angularDirectionalDerivative s (coordinateVector i) (G t))) slab := by
        apply ih (s - 1) (by push_cast at horder; linarith)
        exact ((angularDirectionalDerivative s (coordinateVector i)).restrictScalars ℝ).contDiff
          |>.comp_contDiffOn (hG.of_le (by simp))
      let D : ℝ × Space → (ℝ × Space) →L[ℝ] ℂ := fun z =>
        ((toSpanSingleton ℝ
            (angularBoundedRepresentative s (by linarith) (G' z.1) z.2)).comp
          (fst ℝ ℝ Space)) +
        (angularRepresentativeGradient s hs3 (G z.1) z.2).comp
          (snd ℝ ℝ Space)
      have hD : ContDiffOn ℝ n D slab := by
        have ht : ContDiffOn ℝ n (fun z => toSpanSingleton ℝ
            (angularBoundedRepresentative s (by linarith) (G' z.1) z.2)) slab :=
          (ContinuousLinearMap.toSpanSingletonLIE ℝ ℂ).contDiff.comp_contDiffOn hscalarTime
        have ht' : ContDiffOn ℝ n (fun z =>
            (toSpanSingleton ℝ
              (angularBoundedRepresentative s (by linarith) (G' z.1) z.2)).comp
              (fst ℝ ℝ Space)) slab := by
          exact ((ContinuousLinearMap.compL ℝ (ℝ × Space) ℝ ℂ).contDiff.comp_contDiffOn ht).clm_apply
            contDiffOn_const
        have hx : ContDiffOn ℝ n
            (fun z => angularRepresentativeGradient s hs3 (G z.1) z.2) slab := by
          have hsum : ContDiffOn ℝ n (fun z => ∑ i : Fin 3,
            (EuclideanSpace.proj i).smulRight
              (angularBoundedRepresentative (s - 1) (by linarith)
                (angularDirectionalDerivative s (coordinateVector i) (G z.1)) z.2)) slab
              := ContDiffOn.sum (fun i _ =>
            (ContinuousLinearMap.smulRightL ℝ Space ℂ
              (EuclideanSpace.proj i)).contDiff.comp_contDiffOn (hscalarSpace i))
          apply hsum.congr
          intro z _
          apply ContinuousLinearMap.ext
          intro v
          rw [angularRepresentativeGradient_apply]
          simp only [sum_apply, ContinuousLinearMap.smulRight_apply,
            EuclideanSpace.coe_proj]
        have hx' : ContDiffOn ℝ n (fun z =>
            (angularRepresentativeGradient s hs3 (G z.1) z.2).comp
              (snd ℝ ℝ Space)) slab := by
          exact ((ContinuousLinearMap.compL ℝ (ℝ × Space) Space ℂ).contDiff.comp_contDiffOn hx).clm_apply
            contDiffOn_const
        apply (ht'.add hx').congr
        intro z _
        rfl
      rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp]
      apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
        ((uniqueDiffOn_Icc hS).prod uniqueDiffOn_univ)).mpr
      refine ⟨by simp, D, hD, ?_⟩
      intro z hz
      have hderiv : HasDerivWithinAt G (G' z.1) I z.1 := by
        simpa only [G'] using
          (hG.differentiableOn (by simp) z.1 hz.1).hasDerivWithinAt
      have hEvalBound : ∀ x, ‖angularEvaluation s (by linarith) x‖ ≤
          ‖angularBoundedRepresentative s (by linarith)‖ := by
        intro x
        apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
        intro h
        exact (BoundedContinuousFunction.norm_coe_le_norm
          (angularBoundedRepresentative s (by linarith) h) x).trans
            ((angularBoundedRepresentative s (by linarith)).le_opNorm h)
      apply boundedEvaluation_hasFDerivWithinAt
        (angularEvaluation s (by linarith)) ‖angularBoundedRepresentative s (by linarith)‖
        hEvalBound G (G' z.1) I z.1 z.2 hderiv
        (angularRepresentativeGradient s hs3 (G z.1) z.2)
      · exact angularBoundedRepresentative_hasFDerivAt s hs3 (G z.1) z.2
      · exact (angularBoundedRepresentative s (by linarith) (G' z.1)).continuous.continuousAt

/-! ## Vector representatives and compatibility across orders -/

/-- The canonical real-vector representative obtained by taking real parts of
the three canonical scalar representatives. -/
def vectorRepresentative (s : ℝ) (hs : 2 ≤ s)
    (A : RealVectorSobolev s) (x : Space) : Space :=
  WithLp.toLp 2 (fun i =>
    (angularBoundedRepresentative s hs ((A i : RealSobolevHilbert s) : FourierData) x).re)

/-- The vector representative associated with one vector-valued datum path. -/
def vectorJointRepresentative (s : ℝ) (hs : 2 ≤ s)
    (G : ℝ → RealVectorSobolev s) : SpaceTimeField :=
  fun z => vectorRepresentative s hs (G z.1) z.2

/-- Vector reassembly preserves the finite joint regularity supplied by the
three scalar component paths. -/
theorem vectorJointRepresentative_contDiffOn (n : ℕ) (s S : ℝ) (hS : 0 < S)
    (horder : (n : ℝ) + 2 ≤ s) (G : ℝ → RealVectorSobolev s)
    (hG : ContDiffOn ℝ n G (Icc (0 : ℝ) S)) :
    ContDiffOn ℝ n (vectorJointRepresentative s (by linarith) G)
      (Icc (0 : ℝ) S ×ˢ (univ : Set Space)) := by
  apply (contDiffOn_piLp 2).mpr
  intro i
  let component : RealVectorSobolev s →L[ℝ] FourierData :=
    (RealSobolevHilbert s).subtypeL.comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => RealSobolevHilbert s) i)
  have hGi : ContDiffOn ℝ n (fun t => component (G t)) (Icc (0 : ℝ) S) :=
    component.contDiff.comp_contDiffOn hG
  have hi := scalarJointRepresentative_contDiffOn n s S hS horder
    (fun t => component (G t)) hGi
  exact Complex.reCLM.contDiff.comp_contDiffOn hi

/-- A vector datum's canonical representative is the original `L²` field
almost everywhere. -/
theorem vectorRepresentative_ae {s : ℝ} (hs : 2 ≤ s)
    {z : Space → Space} (hz : MemLp z 2 volume)
    {A : RealVectorSobolev s} (hA : IsSobolevDatum s z A) :
    (fun x => vectorRepresentative s hs A x) =ᵐ[volume] z := by
  have hcomponent : ∀ i : Fin 3, ∀ᵐ x ∂(volume : Measure Space),
      angularBoundedRepresentative s hs ((A i : RealSobolevHilbert s) : FourierData) x =
        ((z x i : ℝ) : ℂ) := by
    intro i
    exact representative_ae hs
      (locallyIntegrable_ofReal
        ((EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hz))
      ((isSobolevDatum_iff s z A).mp hA i)
  filter_upwards [ae_all_iff.mpr hcomponent] with x hx
  apply PiLp.ext
  intro i
  exact congrArg Complex.re (hx i)

/-- The spatial vector representative is continuous at every Sobolev order
`s ≥ 2`. -/
theorem vectorRepresentative_continuous (s : ℝ) (hs : 2 ≤ s)
    (A : RealVectorSobolev s) :
    Continuous (vectorRepresentative s hs A) := by
  exact ((contDiff_piLp 2).mpr (fun i =>
    Complex.reCLM.contDiff.comp
      (angularBoundedRepresentative_contDiff 0 s (by simpa using hs)
        ((A i : RealSobolevHilbert s) : FourierData)))).continuous

/-- Canonical representatives built from two different Sobolev orders agree
everywhere when their data realize the same `L²` field. -/
theorem vectorRepresentative_eq_of_datums {s r : ℝ} (hs : 2 ≤ s) (hr : 2 ≤ r)
    (z : Lp Space 2 (volume : Measure Space))
    {A : RealVectorSobolev s} {B : RealVectorSobolev r}
    (hA : IsSobolevDatum s (⇑z) A) (hB : IsSobolevDatum r (⇑z) B) :
    vectorRepresentative s hs A = vectorRepresentative r hr B := by
  apply (vectorRepresentative_continuous s hs A).ae_eq_iff_eq volume
    (vectorRepresentative_continuous r hr B) |>.mp
  exact (vectorRepresentative_ae hs (Lp.memLp z) hA).trans
    (vectorRepresentative_ae hr (Lp.memLp z) hB).symm

/-- Two datum paths representing the same `L²` path give identical canonical
joint representatives on the closed slab, even when their Sobolev orders
differ. -/
theorem vectorJointRepresentative_eqOn_of_datums {S s r : ℝ}
    (hs : 2 ≤ s) (hr : 2 ≤ r)
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (G : ℝ → RealVectorSobolev s) (H : ℝ → RealVectorSobolev r)
    (hG : ∀ t : Icc (0 : ℝ) S, IsSobolevDatum s (⇑(U t)) (G t.1))
    (hH : ∀ t : Icc (0 : ℝ) S, IsSobolevDatum r (⇑(U t)) (H t.1)) :
    EqOn (vectorJointRepresentative s hs G)
      (vectorJointRepresentative r hr H)
      (Icc (0 : ℝ) S ×ˢ (univ : Set Space)) := by
  intro z hz
  exact congrFun (vectorRepresentative_eq_of_datums hs hr
    (U ⟨z.1, hz.1⟩) (hG ⟨z.1, hz.1⟩) (hH ⟨z.1, hz.1⟩)) z.2

/-! ## One representative for all orders -/

/-- Fix the value of the final field using the canonical representative of the
order-two path supplied by `hpaths`.  Higher-order paths will only be used to
prove regularity of this fixed field. -/
def jointRepresentative {S : ℝ}
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hpaths : ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1)) :
    SpaceTimeField :=
  vectorJointRepresentative 2 (by norm_num) (Classical.choose (hpaths 0 2))

/-- Every closed-slab slice of `jointRepresentative` is the original ordinary
`L²` solution slice almost everywhere. -/
theorem jointRepresentative_slice {S : ℝ}
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hpaths : ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1))
    (t : Icc (0 : ℝ) S) :
    (fun x => jointRepresentative U hpaths (↑t, x)) =ᵐ[volume] ⇑(U t) := by
  change (fun x => vectorRepresentative 2 (by norm_num)
    (Classical.choose (hpaths 0 2) t.1) x) =ᵐ[volume] ⇑(U t)
  apply vectorRepresentative_ae (s := (2 : ℝ)) (by norm_num) (Lp.memLp (U t))
  exact (Classical.choose_spec (hpaths 0 2)).2 t

/-- A fixed order-two path inherits joint `C^n` regularity from a compatible
order-`n+2` path. -/
theorem vectorJointRepresentative_contDiffOn_of_compatible {S : ℝ} (hS : 0 < S)
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2)) (n : ℕ)
    (G₂ : ℝ → RealVectorSobolev (2 : ℝ))
    (Gₙ : ℝ → RealVectorSobolev ((n + 2 : ℕ) : ℝ))
    (hG₂d : ∀ t : Icc (0 : ℝ) S, IsSobolevDatum 2 (⇑(U t)) (G₂ t.1))
    (hGₙc : ContDiffOn ℝ n Gₙ (Icc (0 : ℝ) S))
    (hGₙd : ∀ t : Icc (0 : ℝ) S,
      IsSobolevDatum ((n + 2 : ℕ) : ℝ) (⇑(U t)) (Gₙ t.1)) :
    ContDiffOn ℝ n (vectorJointRepresentative 2 (by norm_num) G₂)
      (Icc (0 : ℝ) S ×ˢ (univ : Set Space)) := by
  have hsmooth := vectorJointRepresentative_contDiffOn n ((n + 2 : ℕ) : ℝ) S hS
    (by push_cast; linarith) Gₙ hGₙc
  apply hsmooth.congr
  intro z hz
  exact (vectorJointRepresentative_eqOn_of_datums (by norm_num) (by norm_num)
    U Gₙ G₂ hGₙd hG₂d hz).symm

/-- At finite order `n`, the order-`n+2` path proves regularity of the fixed
order-two representative. -/
theorem jointRepresentative_contDiffOn_nat {S : ℝ} (hS : 0 < S)
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hpaths : ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1))
    (n : ℕ) :
    ContDiffOn ℝ n (jointRepresentative U hpaths)
      (Icc (0 : ℝ) S ×ˢ (univ : Set Space)) := by
  change ContDiffOn ℝ n
    (vectorJointRepresentative 2 (by norm_num) (Classical.choose (hpaths 0 2)))
      (Icc (0 : ℝ) S ×ˢ (univ : Set Space))
  exact vectorJointRepresentative_contDiffOn_of_compatible hS U n
    (Classical.choose (hpaths 0 2)) (Classical.choose (hpaths n (n + 2)))
    (Classical.choose_spec (hpaths 0 2)).2
    (Classical.choose_spec (hpaths n (n + 2))).1
    (Classical.choose_spec (hpaths n (n + 2))).2

/-- The fixed order-two representative is jointly smooth on the stronger
closed slab.  Every finite order comes from
`jointRepresentative_contDiffOn_nat`. -/
theorem jointRepresentative_contDiffOn {S : ℝ} (hS : 0 < S)
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hpaths : ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1)) :
    ContDiffOn ℝ ∞ (jointRepresentative U hpaths)
      (Icc (0 : ℝ) S ×ˢ (univ : Set Space)) := by
  rw [contDiffOn_infty]
  exact jointRepresentative_contDiffOn_nat hS U hpaths

/-- **R4.**  The input `hS` is the standard positive-horizon restriction.
The path `U` is the ordinary `L²` solution restricted to `[0,S]`.  The input
`hpaths` is the standard all-order space-time Sobolev regularity of that same
solution, restricted to `[0,S]`; smooth nonzero solutions have this property. -/
theorem exists_joint_smooth_representative {S : ℝ} (hS : 0 < S)
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hpaths : ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1)) :
    ∃ u : SpaceTimeField,
      (∀ t : Icc (0 : ℝ) S,
        (fun x => u (↑t, x)) =ᵐ[volume] ⇑(U t)) ∧
      ContDiffOn ℝ ∞ u (Ico (0 : ℝ) S ×ˢ (univ : Set Space)) := by
  refine ⟨jointRepresentative U hpaths, jointRepresentative_slice U hpaths, ?_⟩
  exact (jointRepresentative_contDiffOn hS U hpaths).mono
    (prod_mono_left (Ico_subset_Icc_self : Ico (0 : ℝ) S ⊆ Icc 0 S))

/-- **R4 supplied by the cylinder construction.**  The input `hν` is the
ordinary positive-viscosity restriction, and `hS` is the ordinary
positive-horizon restriction.  The path `U` is the standard ordinary `L²`
solution restricted to `[0,S]`.  The input `hall` is the standard compatible
all-order smooth cylinder realization of that same solution on the common
horizon `[0,S]`; the smooth local theory supplies it for nonzero as well as
zero solutions. -/
theorem exists_joint_smooth_representative_of_hall {ν S : ℝ}
    (hν : 0 < ν) (hS : 0 < S)
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hall : ∀ (q : ℕ) (hq : 6 ≤ q),
      ∃ (u₀ : SobolevSpace 1 (q + 1))
        (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
        (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))),
        ContDiffOn ℝ ∞ (extendPath S hS.le f) (Icc (0 : ℝ) S) ∧
        (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
        (∀ (θ : AddCircle (1 : ℝ)) t,
          sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) ∧
        ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
          (coefficients 1 hq f) u₀ u t) :
    ∃ u : SpaceTimeField,
      (∀ t : Icc (0 : ℝ) S,
        (fun x => u (↑t, x)) =ᵐ[volume] ⇑(U t)) ∧
      ContDiffOn ℝ ∞ u (Ico (0 : ℝ) S ×ˢ (univ : Set Space)) :=
  exists_joint_smooth_representative hS U
    (datumPath_contDiffOn_all_orders hν hS U hall)

end NSFormalization.Section4.A01
