import NavierStokes.SpatialCurl
import Euler.CompactParameterIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-! The actual radial vector potential and its curl on Euclidean three-space. -/
noncomputable section
namespace NSFormalization.Paper1.RadialPotential
open NavierStokes.ProblemStatement NavierStokes.SpatialCurl
open Set MeasureTheory
open scoped ContDiff

def cross (a b : Space) : Space :=
  (a 1 * b 2 - a 2 * b 1) • coordinateVector 0 +
  (a 2 * b 0 - a 0 * b 2) • coordinateVector 1 +
  (a 0 * b 1 - a 1 * b 0) • coordinateVector 2

@[simp] theorem cross_zero (a b : Space) : (cross a b) 0 = a 1 * b 2 - a 2 * b 1 := by
  simp [cross, coordinateVector]
@[simp] theorem cross_one (a b : Space) : (cross a b) 1 = a 2 * b 0 - a 0 * b 2 := by
  simp [cross, coordinateVector]
@[simp] theorem cross_two (a b : Space) : (cross a b) 2 = a 0 * b 1 - a 1 * b 0 := by
  simp [cross, coordinateVector]

theorem cross_contDiff {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {a b : X → Space} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (fun x => cross (a x) (b x)) := by
  have ha' (i : Fin 3) : ContDiff ℝ ∞ (fun x => a x i) := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp ha
  have hb' (i : Fin 3) : ContDiff ℝ ∞ (fun x => b x i) := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hb
  have h0 := (((ha' 1).mul (hb' 2)).sub ((ha' 2).mul (hb' 1))).smul
    (contDiff_const (c := coordinateVector 0))
  have h1 := (((ha' 2).mul (hb' 0)).sub ((ha' 0).mul (hb' 2))).smul
    (contDiff_const (c := coordinateVector 1))
  have h2 := (((ha' 0).mul (hb' 1)).sub ((ha' 1).mul (hb' 0))).smul
    (contDiff_const (c := coordinateVector 2))
  exact (h0.add h1).add h2

theorem fderiv_cross_apply {a b : Space → Space} {x : Space}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) (h : Space) :
    fderiv ℝ (fun y => cross (a y) (b y)) x h =
      cross (fderiv ℝ a x h) (b x) + cross (a x) (fderiv ℝ b x h) := by
  have ha' (i : Fin 3) := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp x ha.hasFDerivAt
  have hb' (i : Fin 3) := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp x hb.hasFDerivAt
  have h0 := (((ha' 1).mul (hb' 2)).sub ((ha' 2).mul (hb' 1))).smul_const (coordinateVector 0)
  have h1 := (((ha' 2).mul (hb' 0)).sub ((ha' 0).mul (hb' 2))).smul_const (coordinateVector 1)
  have h2 := (((ha' 0).mul (hb' 1)).sub ((ha' 1).mul (hb' 0))).smul_const (coordinateVector 2)
  have hd := (h0.add h1).add h2
  change HasFDerivAt (fun y => cross (a y) (b y)) _ x at hd
  rw [hd.fderiv]
  ext i
  fin_cases i <;> simp [cross, coordinateVector, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply] <;> ring

def integrand (v : Space → Space) (p : Space × ℝ) : Space :=
  p.2 • cross (v (p.2 • p.1)) p.1

def potential (v : Space → Space) (x : Space) : Space :=
  ∫ r in (0 : ℝ)..1, integrand v (x, r)

theorem integrand_contDiff {v : Space → Space} (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (integrand v) :=
  contDiff_snd.smul (cross_contDiff (hv.comp (contDiff_snd.smul contDiff_fst)) contDiff_fst)

theorem potential_contDiff {v : Space → Space} (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (potential v) :=
  EulerCompactParameterIntegral.integral_contDiff 0 1 (by norm_num) _ (integrand_contDiff hv)

theorem integrand_fderiv_apply {v : Space → Space} (hv : ContDiff ℝ ∞ v)
    (r : ℝ) (x h : Space) :
    fderiv ℝ (fun y => integrand v (y, r)) x h =
      r • (cross (r • (fderiv ℝ v (r • x) h)) x + cross (v (r • x)) h) := by
  have hc : ContDiff ℝ ∞ (fun y : Space => v (r • y)) :=
    hv.comp (contDiff_id.const_smul r)
  have hcross := cross_contDiff hc contDiff_id
  have hd : DifferentiableAt ℝ (fun y : Space => cross (v (r • y)) y) x :=
    (hcross.differentiable (by simp)) x
  change fderiv ℝ (fun y => r • cross (v (r • y)) y) x h = _
  have hds := hd.hasFDerivAt.const_smul r
  change HasFDerivAt (fun y => r • cross (v (r • y)) y) _ x at hds
  rw [hds.fderiv]
  simp only [smul_apply]
  have hh := fderiv_cross_apply ((hc.differentiable (by simp)) x) differentiableAt_id h
  simp only [id_eq] at hh
  rw [hh]
  have hscale := ((hv.differentiable (by simp)) (r • x)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul r)
  change HasFDerivAt (fun y => v (r • y)) _ x at hscale
  rw [hscale.fderiv]
  simp

theorem linear_apply_coordinates (L : Space →L[ℝ] Space) (x : Space) :
    L x = x 0 • L (coordinateVector 0) + x 1 • L (coordinateVector 1) +
      x 2 • L (coordinateVector 2) := by
  have hx : x = x 0 • coordinateVector 0 + x 1 • coordinateVector 1 + x 2 • coordinateVector 2 := by
    ext i
    fin_cases i <;> simp [coordinateVector]
  conv_lhs => rw [hx]
  simp

/-- Algebraic curl of the radial integrand, including the divergence term. -/
theorem curl_integrand {v : Space → Space} (hv : ContDiff ℝ ∞ v)
    (r : ℝ) (x : Space)
    (hdiv : (∑ i : Fin 3, (fderiv ℝ v (r • x) (coordinateVector i)) i) = 0) :
    curl (fun y => integrand v (y, r)) x =
      (2 * r) • v (r • x) + (r ^ 2) • (fderiv ℝ v (r • x) x) := by
  have hlin := linear_apply_coordinates (fderiv ℝ v (r • x)) x
  rw [Fin.sum_univ_three] at hdiv
  have hd0 := congrArg (fun t : ℝ => r ^ 2 * x 0 * t) hdiv
  have hd1 := congrArg (fun t : ℝ => r ^ 2 * x 1 * t) hdiv
  have hd2 := congrArg (fun t : ℝ => r ^ 2 * x 2 * t) hdiv
  simp only [coordinateVector] at hd0 hd1 hd2
  ext i
  fin_cases i <;>
    simp [curl, curlLinear, derivativeEntry, integrand_fderiv_apply hv, cross,
      coordinateVector, hlin] <;> nlinarith [hd0, hd1, hd2]

/-- Curl commutes with this genuine compact parameter integral. -/
theorem curl_potential_integral {v : Space → Space} (hv : ContDiff ℝ ∞ v) (x : Space) :
    curl (potential v) x = ∫ r in (0 : ℝ)..1, curl (fun y => integrand v (y, r)) x := by
  have hF := integrand_contDiff hv
  have hd := EulerCompactParameterIntegral.integral_hasFDerivAt 0 1 (by norm_num)
    (integrand v) hF x
  have hparam : ∀ r : ℝ,
      EulerCompactParameterIntegral.parameterDerivative (integrand v) (x, r) =
      fderiv ℝ (fun y => integrand v (y, r)) x := by
    intro r
    have hin : HasFDerivAt (fun y : Space => (y, r))
        (ContinuousLinearMap.inl ℝ Space ℝ) x :=
      (hasFDerivAt_id x).prodMk (hasFDerivAt_const r x)
    exact (((hF.differentiable (by simp)) (x, r)).hasFDerivAt.comp x hin).fderiv.symm
  have hi : IntervalIntegrable
      (fun r => EulerCompactParameterIntegral.parameterDerivative (integrand v) (x, r))
      volume 0 1 :=
    ((EulerCompactParameterIntegral.parameterDerivative_contDiff _ hF).continuous.comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  change curlLinear (fderiv ℝ (potential v) x) = _
  rw [show fderiv ℝ (potential v) x = _ from hd.fderiv]
  rw [← curlLinear.intervalIntegral_comp_comm hi]
  apply intervalIntegral.integral_congr
  intro r _
  change curlLinear (EulerCompactParameterIntegral.parameterDerivative (integrand v) (x, r)) = _
  rw [hparam]
  rfl

theorem radial_derivative {v : Space → Space} (hv : ContDiff ℝ ∞ v) (x : Space) (r : ℝ) :
    HasDerivAt (fun t : ℝ => (t ^ 2) • v (t • x))
      ((2 * r) • v (r • x) + (r ^ 2) • (fderiv ℝ v (r • x) x)) r := by
  have hscale := (hasDerivAt_id r).smul_const x
  have hv' := ((hv.differentiable (by simp)) (r • x)).hasFDerivAt.comp_hasDerivAt r hscale
  have hd := ((hasDerivAt_id r).pow 2).smul hv'
  convert hd using 1 <;> first | rfl | simpa only [Pi.smul_apply, Pi.pow_apply, id_eq, one_smul, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, Function.comp_apply] using (add_comm ((2 * r) • v (r • x)) ((r ^ 2) • (fderiv ℝ v (r • x) x)))

/-- The radial vector potential has exactly the prescribed divergence-free curl. -/
theorem curl_potential {v : Space → Space} (hv : ContDiff ℝ ∞ v)
    (hdiv : ∀ x : Space, (∑ i : Fin 3, (fderiv ℝ v x (coordinateVector i)) i) = 0)
    (x : Space) : curl (potential v) x = v x := by
  rw [curl_potential_integral hv]
  have heq : (fun r => curl (fun y => integrand v (y, r)) x) =
      (fun r => (2 * r) • v (r • x) + (r ^ 2) • (fderiv ℝ v (r • x) x)) := by
    funext r
    exact curl_integrand hv r x (hdiv (r • x))
  rw [heq]
  have hc : Continuous (fun r : ℝ =>
      (2 * r) • v (r • x) + (r ^ 2) • (fderiv ℝ v (r • x) x)) := by
    have hvd : Continuous (fderiv ℝ v) := (hv.fderiv_right (m := ∞) (by simp)).continuous
    fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => radial_derivative hv x r) (hc.intervalIntegrable 0 1)
  simpa using hFTC

/-- Radial potential about an arbitrary spatial center. -/
def centeredPotential (v : Space → Space) (x₀ : Space) (x : Space) : Space :=
  potential (fun y => v (x₀ + y)) (x - x₀)

theorem centeredPotential_eq_integral (v : Space → Space) (x₀ x : Space) :
    centeredPotential v x₀ x =
      ∫ r in (0 : ℝ)..1, r • cross (v (x₀ + r • (x - x₀))) (x - x₀) := rfl

theorem centeredPotential_contDiff {v : Space → Space} (hv : ContDiff ℝ ∞ v) (x₀ : Space) :
    ContDiff ℝ ∞ (centeredPotential v x₀) :=
  (potential_contDiff (hv.comp (contDiff_const.add contDiff_id))).comp
    (contDiff_id.sub contDiff_const)

theorem curl_centeredPotential {v : Space → Space} (hv : ContDiff ℝ ∞ v)
    (hdiv : ∀ x : Space, (∑ i : Fin 3, (fderiv ℝ v x (coordinateVector i)) i) = 0)
    (x₀ x : Space) : curl (centeredPotential v x₀) x = v x := by
  have hw : ContDiff ℝ ∞ (fun y => v (x₀ + y)) := hv.comp (contDiff_const.add contDiff_id)
  have hwdiv : ∀ y : Space,
      (∑ i : Fin 3, (fderiv ℝ (fun z => v (x₀ + z)) y (coordinateVector i)) i) = 0 := by
    intro y
    rw [fderiv_comp_add_left]
    exact hdiv (x₀ + y)
  change curlLinear (fderiv ℝ (fun y => potential (fun z => v (x₀ + z)) (y - x₀)) x) = _
  rw [fderiv_comp_sub]
  have h := curl_potential hw hwdiv (x - x₀)
  have hx : x₀ + (x - x₀) = x := by abel
  simpa only [curl, hx] using h

/-- The radial potential with the physical time held fixed. -/
def timePotential (v : VelocityField) (x₀ : Space) : VelocityField :=
  fun z => centeredPotential (fun x => v (z.1, x)) x₀ z.2

theorem timePotential_contDiff {v : VelocityField} (hv : ContDiff ℝ ∞ v) (x₀ : Space) :
    ContDiff ℝ ∞ (timePotential v x₀) := by
  let F : SpaceTime × ℝ → Space := fun p =>
    p.2 • cross (v (p.1.1, x₀ + p.2 • (p.1.2 - x₀))) (p.1.2 - x₀)
  have harg : ContDiff ℝ ∞
      (fun p : SpaceTime × ℝ => (p.1.1, x₀ + p.2 • (p.1.2 - x₀))) := by
    fun_prop
  have hx : ContDiff ℝ ∞ (fun p : SpaceTime × ℝ => p.1.2 - x₀) := by fun_prop
  have hF : ContDiff ℝ ∞ F := contDiff_snd.smul (cross_contDiff (hv.comp harg) hx)
  exact EulerCompactParameterIntegral.integral_contDiff 0 1 (by norm_num) F hF

/-- Jointly smooth divergence-free velocity has a jointly smooth actual
potential whose spatial curl is that velocity, at every physical time. -/
theorem spatialCurl_timePotential {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (hdiv : ∀ t x, spatialDivergence v t x = 0) (x₀ : Space) :
    spatialCurl (timePotential v x₀) = v := by
  funext z
  have hs : ContDiff ℝ ∞ (fun x : Space => v (z.1, x)) :=
    hv.comp (contDiff_const.prodMk contDiff_id)
  exact curl_centeredPotential hs (hdiv z.1) x₀ z.2

end NSFormalization.Paper1.RadialPotential
