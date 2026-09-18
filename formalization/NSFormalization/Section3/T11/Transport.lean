import NSFormalization.Section3.T11.MeanIdentity
import NSFormalization.Section3.T10.ForcePaths
import NSFormalization.Section3.T10.DatumBasics

/-!
# T11/U6 — solution transport under a smooth change of variables

One shared constructor transports a `ClassicalSolutionT` along the change of
variables `(t, x) ↦ (α t, x + X t)` with an amplitude `α`, a `C^∞` moving
translation `X` and its two derivatives `c = X'`, `d = X''`:

```
v (t, x) = α • u (α t, x + X t) - c t
q (t, x) = α ^ 2 * p (α t, x + X t)
g (t, x) = α ^ 2 • f (α t, x + X t) - d t
```

at viscosity `α * ν` on the horizon `T'` with `α * T' = T`.  The three uses are
the Galilean mean reduction (`α = 1`, `X = galileanShiftT a f`) and the two
unit-viscosity rescalings (`X = 0`, `α = ν⁻¹` and `α = ν`).
-/

noncomputable section

namespace NSFormalization.Section3.T11

open Set MeasureTheory Filter Topology
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10
open scoped ContDiff ENNReal BigOperators

namespace Transport

/-! ## 1. Frozen-time chain rules

All spatial operators are `fderiv`s of the frozen-time slice, so each of them
only sees the spatial translation `y ↦ y + Y` and the amplitude `α`. -/

/-- The spatial Fréchet derivative of a transported slice. -/
theorem spatialDerivative_slice {v u : SpaceTimeField} {α s t : ℝ} {Y c x : Space}
    (hv : ∀ y : Space, v (t, y) = α • u (s, y + Y) - c)
    (hu : DifferentiableAt ℝ (fun y : Space ↦ u (s, y)) (x + Y)) :
    spatialDerivative v t x = α • spatialDerivative u s (x + Y) := by
  unfold spatialDerivative
  rw [show (fun y : Space ↦ v (t, y)) = fun y : Space ↦ α • u (s, y + Y) - c from
    funext hv, fderiv_sub_const,
    fderiv_fun_const_smul ((differentiableAt_comp_add_right Y).2 hu) α,
    fderiv_comp_add_right (𝕜 := ℝ) (f := fun y : Space ↦ u (s, y)) (x := x) Y]

/-- The spatial divergence of a transported slice. -/
theorem spatialDivergence_slice {v u : SpaceTimeField} {α s t : ℝ} {Y c x : Space}
    (hv : ∀ y : Space, v (t, y) = α • u (s, y + Y) - c)
    (hu : DifferentiableAt ℝ (fun y : Space ↦ u (s, y)) (x + Y)) :
    spatialDivergence v t x = α * spatialDivergence u s (x + Y) := by
  unfold spatialDivergence
  rw [spatialDerivative_slice hv hu]
  simp [Finset.mul_sum]

/-- The vector Laplacian of a transported slice. -/
theorem spatialLaplacian_slice {v u : SpaceTimeField} {α s t : ℝ} {Y c : Space} (x : Space)
    (hv : ∀ y : Space, v (t, y) = α • u (s, y + Y) - c)
    (hu : ContDiff ℝ 2 (fun y : Space ↦ u (s, y))) :
    spatialLaplacian v t x = α • spatialLaplacian u s (x + Y) := by
  have hd : ∀ y : Space, DifferentiableAt ℝ (fun z : Space ↦ u (s, z)) y :=
    hu.differentiable (by norm_num)
  have hslice : ∀ i : Fin 3, (fun y : Space ↦ spatialDerivative v t y (coordinateVector i)) =
      fun y : Space ↦ α • spatialDerivative u s (y + Y) (coordinateVector i) := by
    intro i
    funext y
    rw [spatialDerivative_slice hv (hd (y + Y))]
    rfl
  unfold spatialLaplacian
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [hslice i]
  have hdi : DifferentiableAt ℝ
      (fun y : Space ↦ spatialDerivative u s y (coordinateVector i)) (x + Y) :=
    NavierStokes.ResidualCalculus.differentiable_spatial_direction u s hu
      (coordinateVector i) (x + Y)
  rw [fderiv_fun_const_smul ((differentiableAt_comp_add_right Y).2 hdi) α,
    fderiv_comp_add_right (𝕜 := ℝ)
      (f := fun y : Space ↦ spatialDerivative u s y (coordinateVector i)) (x := x) Y]
  rfl

/-- The pressure gradient of a transported slice. -/
theorem pressureGradient_slice {q p : SpaceTimeScalar} {β s t : ℝ} {Y x : Space}
    (hq : ∀ y : Space, q (t, y) = β * p (s, y + Y))
    (hp : DifferentiableAt ℝ (fun y : Space ↦ p (s, y)) (x + Y)) :
    pressureGradient q t x = β • pressureGradient p s (x + Y) := by
  unfold pressureGradient
  rw [show (fun y : Space ↦ q (t, y)) = fun y : Space ↦ β • p (s, y + Y) from
    funext hq, fderiv_fun_const_smul ((differentiableAt_comp_add_right Y).2 hp) β,
    fderiv_comp_add_right (𝕜 := ℝ) (f := fun y : Space ↦ p (s, y)) (x := x) Y]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [smul_apply, smul_assoc]

/-! ## 2. The time derivative

Only the time derivative sees the moving translation: it produces the transport
term `-(Ẋ(t) · ∇)u`, which is exactly cancelled by the extra advection term of
the shifted velocity. -/

/-- Time slices of the total derivative. -/
theorem temporalDerivative_eq_fderiv {u : SpaceTimeField} {s : ℝ} {y : Space}
    (hu : DifferentiableAt ℝ u (s, y)) :
    temporalDerivative u s y = fderiv ℝ u (s, y) (1, 0) := by
  unfold temporalDerivative
  have h : HasFDerivAt (fun r : ℝ ↦ u (r, y))
      ((fderiv ℝ u (s, y)).comp (ContinuousLinearMap.inl ℝ ℝ Space)) s :=
    hu.hasFDerivAt.comp s (hasFDerivAt_prodMk_left s y)
  rw [h.fderiv]
  rfl

/-- Spatial slices of the total derivative. -/
theorem spatialDerivative_eq_fderiv {u : SpaceTimeField} {s : ℝ} {y : Space}
    (hu : DifferentiableAt ℝ u (s, y)) (e : Space) :
    spatialDerivative u s y e = fderiv ℝ u (s, y) (0, e) := by
  unfold spatialDerivative
  have h : HasFDerivAt (fun z : Space ↦ u (s, z))
      ((fderiv ℝ u (s, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) y :=
    hu.hasFDerivAt.comp y (hasFDerivAt_prodMk_right s y)
  rw [h.fderiv]
  rfl

/-- The time derivative of a transported time line. -/
theorem temporalDerivative_line {v u : SpaceTimeField} {α t : ℝ} {X c d : ℝ → Space}
    {x : Space}
    (hv : ∀ s : ℝ, v (s, x) = α • u (α * s, x + X s) - c s)
    (hX : HasDerivAt X (c t) t) (hc : HasDerivAt c (d t) t)
    (hu : DifferentiableAt ℝ u (α * t, x + X t)) :
    temporalDerivative v t x =
      (α * α) • temporalDerivative u (α * t) (x + X t) +
        α • spatialDerivative u (α * t) (x + X t) (c t) - d t := by
  have hpath : HasDerivAt (fun s : ℝ ↦ ((α * s : ℝ), x + X s)) ((α : ℝ), c t) t := by
    have h1 : HasDerivAt (fun s : ℝ ↦ α * s) α t := by
      simpa using (hasDerivAt_id t).const_mul α
    have h2 : HasDerivAt (fun s : ℝ ↦ x + X s) (c t) t := by
      simpa using hX.const_add x
    exact h1.prodMk h2
  have hcomp : HasDerivAt (fun s : ℝ ↦ u (α * s, x + X s))
      (fderiv ℝ u (α * t, x + X t) ((α : ℝ), c t)) t :=
    hu.hasFDerivAt.comp_hasDerivAt t hpath
  have hline : HasDerivAt (fun s : ℝ ↦ v (s, x))
      (α • fderiv ℝ u (α * t, x + X t) ((α : ℝ), c t) - d t) t := by
    apply HasDerivAt.congr_of_eventuallyEq (f := fun s : ℝ ↦
      α • u (α * s, x + X s) - c s)
    · exact (hcomp.const_smul α).sub hc
    · filter_upwards [] with s using hv s
  have hsplit : fderiv ℝ u (α * t, x + X t) ((α : ℝ), c t) =
      α • temporalDerivative u (α * t) (x + X t) +
        spatialDerivative u (α * t) (x + X t) (c t) := by
    rw [temporalDerivative_eq_fderiv hu, spatialDerivative_eq_fderiv hu,
      ← ContinuousLinearMap.map_smul, ← map_add]
    congr 1
    refine Prod.ext ?_ ?_
    · simp
    · simp
  have : temporalDerivative v t x = deriv (fun s : ℝ ↦ v (s, x)) t := rfl
  rw [this, hline.deriv, hsplit]
  rw [smul_add, smul_smul]

/-- The advection of a transported slice, including the transport correction. -/
theorem advection_slice {v u : SpaceTimeField} {α s t : ℝ} {Y c : Space} {x : Space}
    (hv : ∀ y : Space, v (t, y) = α • u (s, y + Y) - c)
    (hu : DifferentiableAt ℝ (fun y : Space ↦ u (s, y)) (x + Y)) :
    advection v t x =
      (α * α) • advection u s (x + Y) - α • spatialDerivative u s (x + Y) c := by
  unfold advection
  rw [spatialDerivative_slice hv hu, hv x]
  rw [map_sub, map_smul]
  rw [smul_apply, smul_apply, smul_smul]

/-! ## 3. The transported residual

Every term is collected: the transport term of the time derivative cancels the
extra advection term, the viscosity is rescaled to `α * ν`, and the whole
residual is `α ^ 2` times the original one, shifted by `X''`. -/

/-- The exact Navier--Stokes residual of a transported solution. -/
theorem navierStokesResidual_transport {v u : SpaceTimeField} {q p : SpaceTimeScalar}
    {ν α t : ℝ} {X c d : ℝ → Space} {x : Space}
    (hvline : ∀ s : ℝ, v (s, x) = α • u (α * s, x + X s) - c s)
    (hv : ∀ y : Space, v (t, y) = α • u (α * t, y + X t) - c t)
    (hq : ∀ y : Space, q (t, y) = α ^ 2 * p (α * t, y + X t))
    (hX : HasDerivAt X (c t) t) (hc : HasDerivAt c (d t) t)
    (hu : DifferentiableAt ℝ u (α * t, x + X t))
    (hu2 : ContDiff ℝ 2 (fun y : Space ↦ u (α * t, y)))
    (hp : DifferentiableAt ℝ (fun y : Space ↦ p (α * t, y)) (x + X t)) :
    NavierStokesR3.ProblemStatement.navierStokesResidual (α * ν) v q t x =
      α ^ 2 •
          NavierStokesR3.ProblemStatement.navierStokesResidual ν u p (α * t) (x + X t) -
        d t := by
  have hu1 : DifferentiableAt ℝ (fun y : Space ↦ u (α * t, y)) (x + X t) :=
    hu2.differentiable (by norm_num) (x + X t)
  unfold NavierStokesR3.ProblemStatement.navierStokesResidual
  rw [temporalDerivative_line hvline hX hc hu, advection_slice hv hu1,
    spatialLaplacian_slice x hv hu2, pressureGradient_slice hq hp]
  module

/-! ## 3b. Scalar Laplacian and tensor divergence under transport -/

/-- The scalar Laplacian of a transported pressure slice. -/
theorem scalarSpatialLaplacianT_slice {q p : SpaceTimeScalar} {β s t : ℝ} {Y : Space}
    (x : Space) (hq : ∀ y : Space, q (t, y) = β * p (s, y + Y))
    (hp : ContDiff ℝ 2 (fun y : Space ↦ p (s, y))) :
    scalarSpatialLaplacianT q t x = β * scalarSpatialLaplacianT p s (x + Y) := by
  have hd : ∀ y : Space, DifferentiableAt ℝ (fun z : Space ↦ p (s, z)) y :=
    hp.differentiable (by norm_num)
  have hinner : ∀ i : Fin 3,
      (fun y : Space ↦ fderiv ℝ (fun z : Space ↦ q (t, z)) y (coordinateVector i)) =
        fun y : Space ↦
          β • fderiv ℝ (fun z : Space ↦ p (s, z)) (y + Y) (coordinateVector i) := by
    intro i
    funext y
    rw [show (fun z : Space ↦ q (t, z)) = fun z : Space ↦ β • p (s, z + Y) from funext hq,
      fderiv_fun_const_smul ((differentiableAt_comp_add_right Y).2 (hd (y + Y))) β,
      fderiv_comp_add_right (𝕜 := ℝ) (f := fun z : Space ↦ p (s, z)) (x := y) Y]
    rfl
  unfold scalarSpatialLaplacianT
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [hinner i]
  have hdi : DifferentiableAt ℝ
      (fun y : Space ↦ fderiv ℝ (fun z : Space ↦ p (s, z)) y (coordinateVector i)) (x + Y) := by
    have hfd : ContDiff ℝ 1 (fderiv ℝ (fun z : Space ↦ p (s, z))) :=
      hp.fderiv_right (by norm_num)
    exact ((hfd.clm_apply contDiff_const).differentiable (by norm_num)) (x + Y)
  rw [fderiv_fun_const_smul ((differentiableAt_comp_add_right Y).2 hdi) β,
    fderiv_comp_add_right (𝕜 := ℝ)
      (f := fun y : Space ↦ fderiv ℝ (fun z : Space ↦ p (s, z)) y (coordinateVector i))
      (x := x) Y]
  rfl

/-- Smoothness of the tensor divergence on a smooth slice. -/
theorem contDiff_convectionDivergence_slice {u : SpaceTimeField} {s : ℝ}
    (hu : ContDiff ℝ ∞ (fun y : Space ↦ u (s, y))) :
    ContDiff ℝ ∞ (fun y : Space ↦ convectionDivergenceT u s y) := by
  unfold convectionDivergenceT NSFormalization.Section4.A01.convectionDivergence
  refine ContDiff.sum ?_
  intro j _
  have hprod : ContDiff ℝ ∞ (fun y : Space ↦ (u (s, y) j) • u (s, y)) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hu).smul hu
  have hfd : ContDiff ℝ ∞ (fderiv ℝ (fun y : Space ↦ (u (s, y) j) • u (s, y))) :=
    hprod.fderiv_right (by simp)
  exact hfd.clm_apply contDiff_const

/-- The tensor divergence of a purely rescaled slice. -/
theorem convectionDivergence_slice_smul {v u : SpaceTimeField} {α s t : ℝ} (x : Space)
    (hv : ∀ y : Space, v (t, y) = α • u (s, y))
    (hu : ContDiff ℝ ∞ (fun y : Space ↦ u (s, y))) :
    convectionDivergenceT v t x = (α * α) • convectionDivergenceT u s x := by
  unfold convectionDivergenceT NSFormalization.Section4.A01.convectionDivergence
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  have hfun : (fun y : Space ↦ (v (t, y) j) • v (t, y)) =
      fun y : Space ↦ (α * α) • ((u (s, y) j) • u (s, y)) := by
    funext y
    rw [hv y]
    change (α * u (s, y) j) • (α • u (s, y)) = _
    rw [smul_smul, smul_smul]
    ring_nf
  rw [hfun]
  have hprod : DifferentiableAt ℝ (fun y : Space ↦ (u (s, y) j) • u (s, y)) x :=
    (((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hu).smul hu).differentiable (by simp) x
  rw [fderiv_fun_const_smul hprod (α * α)]
  rfl

/-! ## 4. Transport of Fourier data

A spatial translation multiplies every coefficient by the unimodular character
`e^{2πi k·y}`; the amplitude is a scalar multiple, and the subtracted constant
only moves the zero mode.  The three operations are assembled into the datum of
one transported slice. -/

/-- The torus point represented by a spatial vector. -/
def torusPoint (y : Space) : PeriodicTorus := fun i ↦ (y i : UnitAddCircle)

/-- The unimodular translation multiplier `e^{2πi k·y}`. -/
def translateCoeff (y : Space) (k : PeriodicFrequency) : ℂ :=
  UnitAddTorus.mFourier k (torusPoint y)

theorem norm_translateCoeff (y : Space) (k : PeriodicFrequency) :
    ‖translateCoeff y k‖ = 1 := by
  simp only [translateCoeff, UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod,
    fourier_apply, Circle.norm_coe, Finset.prod_const_one]

theorem continuous_translateCoeff (k : PeriodicFrequency) :
    Continuous fun y : Space ↦ translateCoeff y k := by
  refine (UnitAddTorus.mFourier k).continuous.comp ?_
  refine continuous_pi fun i ↦ ?_
  exact (AddCircle.continuous_mk' (1 : ℝ)).comp ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous)

/-- Spatial translation of one scalar coefficient sequence. -/
def translateScalarData (y : Space) (A : PeriodicScalarData) : PeriodicScalarData :=
  ⟨fun k ↦ translateCoeff y k * A k, by
    apply memℓp_gen
    have hA := (lp.memℓp A).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_ofNat, norm_mul, Real.rpow_two,
      norm_translateCoeff, one_mul] using hA⟩

@[simp] theorem translateScalarData_apply (y : Space) (A : PeriodicScalarData)
    (k : PeriodicFrequency) : translateScalarData y A k = translateCoeff y k * A k := rfl

/-- Spatial translation of a full real vector datum. -/
def translatePeriodicDatum (s : ℝ) (y : Space) (A : PeriodicSobolev s) :
    PeriodicSobolev s := by
  refine ⟨WithLp.toLp 2 (fun i ↦ translateScalarData y (A.1 i)), ?_⟩
  intro i k
  change translateCoeff y (-k) * A.1 i (-k) = star (translateCoeff y k * A.1 i k)
  rw [A.2 i k]
  simp only [translateCoeff]
  rw [UnitAddTorus.mFourier_neg]
  exact (map_mul (starRingEnd ℂ) (UnitAddTorus.mFourier k (torusPoint y)) (A.1 i k)).symm

@[simp] theorem translatePeriodicDatum_apply (s : ℝ) (y : Space) (A : PeriodicSobolev s)
    (i : Fin 3) (k : PeriodicFrequency) :
    (translatePeriodicDatum s y A).1 i k = translateCoeff y k * A.1 i k := rfl

theorem torusLift_translate {E : Type*} [AddCommMonoid E] {z : Space → E}
    (hz : IsPeriodicSpatial z) (y : Space) (q : PeriodicTorus) :
    torusLift (fun x ↦ z (x + y)) q = torusLift z (q + torusPoint y) :=
  MeanIdentity.torusLift_translate hz y q

theorem isPeriodicSpatial_translate {E : Type*} [AddCommMonoid E] {z : Space → E}
    (hz : IsPeriodicSpatial z) (y : Space) :
    IsPeriodicSpatial (fun x ↦ z (x + y)) := by
  intro x i
  change z ((x + coordinateVector i) + y) = z (x + y)
  rw [show (x + coordinateVector i) + y = (x + y) + coordinateVector i by abel]
  exact hz (x + y) i

/-- Translating a periodic field multiplies its Fourier coefficients by the
unimodular character. -/
theorem periodicFourierCoeff_translate {z : Space → ℂ} (hz : IsPeriodicSpatial z)
    (y : Space) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ z (x + y)) k =
      translateCoeff y k * periodicFourierCoeff z k := by
  unfold periodicFourierCoeff NSFormalization.Paper1.periodicFourierCoeff
  unfold UnitAddTorus.mFourierCoeff
  simp_rw [torusLift_translate hz y]
  have hshift := integral_add_right_eq_self (μ := periodicTorusMeasure)
    (fun q : PeriodicTorus ↦
      UnitAddTorus.mFourier (-k) (q - torusPoint y) • torusLift z q)
    (torusPoint y)
  simp only [add_sub_cancel_right] at hshift
  rw [hshift]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with q
  change UnitAddTorus.mFourier (-k) (q - torusPoint y) * torusLift z q =
    translateCoeff y k * (UnitAddTorus.mFourier (-k) q * torusLift z q)
  simp only [translateCoeff]
  rw [show UnitAddTorus.mFourier (-k) (q - torusPoint y) =
      UnitAddTorus.mFourier (-k) q * UnitAddTorus.mFourier k (torusPoint y) by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply, Pi.sub_apply]
    rw [show (∏ i, fourier (-k i) (q i - torusPoint y i)) =
        ∏ i, (fourier (-k i) (q i) * fourier (-k i) (-torusPoint y i)) by
      apply Finset.prod_congr rfl
      intro i _
      rw [show q i - torusPoint y i = q i + -torusPoint y i by abel]
      simp only [fourier_apply]
      rw [zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]]
    rw [Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    simp [fourier_apply]]
  ring

/-- The translated datum is the datum of the translated field. -/
theorem isPeriodicDatum_translate {s : ℝ} {z : SpatialField} {A : PeriodicSobolev s}
    (hA : IsPeriodicDatum s z A) (y : Space) :
    IsPeriodicDatum s (fun x ↦ z (x + y)) (translatePeriodicDatum s y A) := by
  refine ⟨isPeriodicSpatial_translate hA.1 y,
    (MeanIdentity.integrable_torusLift_translate_iff hA.1 y).2 hA.2.1, ?_⟩
  intro i k
  rw [translatePeriodicDatum_apply]
  have hcoeff :
      periodicFourierCoeff (fun x ↦ ((z (x + y) i : ℝ) : ℂ)) k =
        translateCoeff y k * periodicFourierCoeff (fun x ↦ ((z x i : ℝ) : ℂ)) k := by
    apply periodicFourierCoeff_translate (z := fun x ↦ ((z x i : ℝ) : ℂ))
    intro x j
    exact congrArg (fun v : Space ↦ ((v i : ℝ) : ℂ)) (hA.1 x j)
  rw [hA.2.2 i k, hcoeff]
  exact mul_smul_comm _ _ _

theorem translateScalarData_norm (y : Space) (A : PeriodicScalarData) :
    ‖translateScalarData y A‖ = ‖A‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal),
    lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  congr 1
  apply tsum_congr
  intro k
  rw [translateScalarData_apply, norm_mul, norm_translateCoeff, one_mul]

theorem translatePeriodicDatum_norm (s : ℝ) (y : Space) (A : PeriodicSobolev s) :
    ‖translatePeriodicDatum s y A‖ = ‖A‖ := by
  change ‖(translatePeriodicDatum s y A).1‖ = ‖A.1‖
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [show (translatePeriodicDatum s y A).1 i = translateScalarData y (A.1 i) by
      simp only [translatePeriodicDatum, PiLp.toLp_apply],
    translateScalarData_norm]

theorem translatePeriodicDatum_sub (s : ℝ) (y : Space) (A B : PeriodicSobolev s) :
    translatePeriodicDatum s y A - translatePeriodicDatum s y B =
      translatePeriodicDatum s y (A - B) := by
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  funext i
  apply lp.ext
  funext k
  change translateCoeff y k * A.1 i k - translateCoeff y k * B.1 i k =
    translateCoeff y k * (A.1 i k - B.1 i k)
  ring

/-- The translation family is strongly continuous on one scalar datum. -/
theorem continuous_translateScalarData (A : PeriodicScalarData) :
    Continuous fun y : Space ↦ translateScalarData y A := by
  rw [continuous_iff_continuousAt]
  intro y₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hsq : ∀ y : Space, ‖translateScalarData y A - translateScalarData y₀ A‖ =
      (∑' k : PeriodicFrequency,
        ‖(translateCoeff y k - translateCoeff y₀ k) * A k‖ ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) := by
    intro y
    have hk : ∀ k : PeriodicFrequency,
        ((translateScalarData y A - translateScalarData y₀ A : PeriodicScalarData) k) =
          (translateCoeff y k - translateCoeff y₀ k) * A k := by
      intro k
      change translateCoeff y k * A k - translateCoeff y₀ k * A k = _
      ring
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    simp only [ENNReal.toReal_ofNat, hk]
    norm_num
  have hbound : Summable fun k : PeriodicFrequency ↦ (4 : ℝ) * ‖A k‖ ^ (2 : ℝ) := by
    have hA := (lp.memℓp A).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_ofNat] using hA.mul_left (4 : ℝ)
  have hterm : Tendsto (fun y : Space ↦
      ∑' k : PeriodicFrequency,
        ‖(translateCoeff y k - translateCoeff y₀ k) * A k‖ ^ (2 : ℝ)) (𝓝 y₀) (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝 y₀)
      (f := fun (y : Space) (k : PeriodicFrequency) ↦
        ‖(translateCoeff y k - translateCoeff y₀ k) * A k‖ ^ (2 : ℝ))
      (g := fun _ : PeriodicFrequency ↦ (0 : ℝ))
      (bound := fun k : PeriodicFrequency ↦ (4 : ℝ) * ‖A k‖ ^ (2 : ℝ)) hbound ?_ ?_
    · simpa using this
    · intro k
      have hc : Tendsto (fun y : Space ↦
          ‖(translateCoeff y k - translateCoeff y₀ k) * A k‖) (𝓝 y₀) (𝓝 0) := by
        have : Tendsto (fun y : Space ↦ (translateCoeff y k - translateCoeff y₀ k) * A k)
            (𝓝 y₀) (𝓝 ((translateCoeff y₀ k - translateCoeff y₀ k) * A k)) :=
          (((continuous_translateCoeff k).tendsto y₀).sub tendsto_const_nhds).mul
            tendsto_const_nhds
        simpa [Function.comp_def] using (tendsto_norm.comp this)
      have h0 : ((0 : ℝ)) ^ (2 : ℝ) = 0 := Real.zero_rpow (by norm_num)
      have := (Real.continuousAt_rpow_const (0 : ℝ) (2 : ℝ) (Or.inr (by norm_num))).tendsto.comp hc
      simpa [h0, Function.comp_def] using this
    · filter_upwards [] with y k
      have h1 : ‖(translateCoeff y k - translateCoeff y₀ k) * A k‖ ≤ 2 * ‖A k‖ := by
        rw [norm_mul]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        refine (norm_sub_le _ _).trans ?_
        rw [norm_translateCoeff, norm_translateCoeff]
        norm_num
      have h2 : ‖(translateCoeff y k - translateCoeff y₀ k) * A k‖ ^ (2 : ℝ) ≤
          (2 * ‖A k‖) ^ (2 : ℝ) :=
        Real.rpow_le_rpow (norm_nonneg _) h1 (by norm_num)
      have h3 : ((2 : ℝ) * ‖A k‖) ^ (2 : ℝ) = 4 * ‖A k‖ ^ (2 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) (norm_nonneg _)]
        norm_num
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      exact h2.trans_eq h3
  simp only [hsq]
  have h0 : ((0 : ℝ)) ^ ((2 : ℝ)⁻¹) = 0 := Real.zero_rpow (by norm_num)
  have := (Real.continuousAt_rpow_const (0 : ℝ) ((2 : ℝ)⁻¹)
    (Or.inr (by norm_num))).tendsto.comp hterm
  simpa [h0, Function.comp_def] using this

/-- The translation family is strongly continuous on one vector datum. -/
theorem continuous_translatePeriodicDatum (s : ℝ) (A : PeriodicSobolev s) :
    Continuous fun y : Space ↦ translatePeriodicDatum s y A := by
  apply Continuous.subtype_mk
  apply (PiLp.continuous_toLp 2 _).comp
  exact continuous_pi fun i ↦ continuous_translateScalarData (A.1 i)

/-- The order-`s` datum of a constant field: the zero mode carries it all. -/
def constantDatum (s : ℝ) (c : Space) : PeriodicSobolev s := by
  refine ⟨WithLp.toLp 2 (fun i ↦ lp.single 2 (0 : PeriodicFrequency) ((c i : ℝ) : ℂ)), ?_⟩
  intro i k
  change (lp.single 2 (0 : PeriodicFrequency) ((c i : ℝ) : ℂ) : PeriodicScalarData) (-k) =
    star ((lp.single 2 (0 : PeriodicFrequency) ((c i : ℝ) : ℂ) : PeriodicScalarData) k)
  by_cases hk : k = 0
  · subst k
    simp
  · simp [lp.single_apply, hk, neg_ne_zero.mpr hk]

@[simp] theorem constantDatum_apply (s : ℝ) (c : Space) (i : Fin 3)
    (k : PeriodicFrequency) :
    (constantDatum s c).1 i k =
      (lp.single 2 (0 : PeriodicFrequency) ((c i : ℝ) : ℂ) : PeriodicScalarData) k := rfl

theorem isPeriodicDatum_const (s : ℝ) (c : Space) :
    IsPeriodicDatum s (fun _ : Space ↦ c) (constantDatum s c) := by
  refine ⟨fun _ _ ↦ rfl, integrable_const c, ?_⟩
  intro i k
  rw [constantDatum_apply, periodicFourierCoeff_const]
  by_cases hk : k = 0
  · subst k
    simp [periodicFrequencyWeight]
  · simp [lp.single_apply, hk]

theorem constantDatum_sub (s : ℝ) (c c' : Space) :
    constantDatum s c - constantDatum s c' = constantDatum s (c - c') := by
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  funext i
  apply lp.ext
  funext k
  change (lp.single 2 (0 : PeriodicFrequency) ((c i : ℝ) : ℂ) : PeriodicScalarData) k -
      (lp.single 2 (0 : PeriodicFrequency) ((c' i : ℝ) : ℂ) : PeriodicScalarData) k =
    (lp.single 2 (0 : PeriodicFrequency) (((c - c') i : ℝ) : ℂ) : PeriodicScalarData) k
  by_cases hk : k = 0
  · subst k
    simp [Complex.ofReal_sub]
  · simp [lp.single_apply, hk]

theorem constantDatum_norm (s : ℝ) (c : Space) : ‖constantDatum s c‖ = ‖c‖ := by
  change ‖(constantDatum s c).1‖ = ‖c‖
  rw [PiLp.norm_eq_of_L2, EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [show (constantDatum s c).1 i =
      lp.single 2 (0 : PeriodicFrequency) ((c i : ℝ) : ℂ) by
    simp only [constantDatum, PiLp.toLp_apply],
    lp.norm_single (by norm_num), Complex.norm_real, Real.norm_eq_abs]

theorem continuous_constantDatum (s : ℝ) : Continuous (constantDatum s) := by
  refine LipschitzWith.continuous (K := 1) ?_
  intro c c'
  rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm, constantDatum_sub,
    constantDatum_norm]
  simp

theorem periodicFourierCoeff_const_mul (β : ℂ) (g : Space → ℂ) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ β * g x) k = β * periodicFourierCoeff g k := by
  unfold periodicFourierCoeff NSFormalization.Paper1.periodicFourierCoeff
    UnitAddTorus.mFourierCoeff
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with q
  change (UnitAddTorus.mFourier (-k) q : ℂ) • (β * torusLift g q) =
    β * ((UnitAddTorus.mFourier (-k) q : ℂ) • torusLift g q)
  simp only [smul_eq_mul]
  ring

/-- Scalar multiples of a datum. -/
theorem isPeriodicDatum_smul {s : ℝ} {z : SpatialField} {A : PeriodicSobolev s}
    (hA : IsPeriodicDatum s z A) (α : ℝ) :
    IsPeriodicDatum s (fun x ↦ α • z x) (α • A) := by
  refine ⟨fun x i ↦ congrArg (α • ·) (hA.1 x i), ?_, ?_⟩
  · have : torusLift (fun x ↦ α • z x) = fun q ↦ α • torusLift z q := rfl
    rw [this]
    exact hA.2.1.smul α
  · intro i k
    have hval : (α • A).1 i k = (α : ℂ) * A.1 i k := rfl
    rw [hval, hA.2.2 i k]
    have hz : (fun x ↦ (((α • z x) i : ℝ) : ℂ)) =
        fun x ↦ (α : ℂ) * ((z x i : ℝ) : ℂ) := by
      funext x
      simp [Complex.ofReal_mul]
    rw [hz, periodicFourierCoeff_const_mul]
    rw [Complex.real_smul, Complex.real_smul]
    ring

/-- The datum of one transported slice `x ↦ α • z (x + y) - c`. -/
theorem isPeriodicDatum_transport {s : ℝ} {z : SpatialField} {A : PeriodicSobolev s}
    (hA : IsPeriodicDatum s z A) (α : ℝ) (y c : Space) :
    IsPeriodicDatum s (fun x ↦ α • z (x + y) - c)
      (α • translatePeriodicDatum s y A - constantDatum s c) :=
  datum_sub (isPeriodicDatum_smul (isPeriodicDatum_translate hA y) α)
    (isPeriodicDatum_const s c)

/-- The translation family is jointly continuous in the shift and the datum. -/
theorem continuous_translate_pair (s : ℝ) :
    Continuous fun p : Space × PeriodicSobolev s ↦ translatePeriodicDatum s p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨y₀, A₀⟩
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hle : ∀ p : Space × PeriodicSobolev s,
      ‖translatePeriodicDatum s p.1 p.2 - translatePeriodicDatum s y₀ A₀‖ ≤
        ‖p.2 - A₀‖ + ‖translatePeriodicDatum s p.1 A₀ - translatePeriodicDatum s y₀ A₀‖ := by
    rintro ⟨y, A⟩
    have hsplit : translatePeriodicDatum s y A - translatePeriodicDatum s y₀ A₀ =
        (translatePeriodicDatum s y A - translatePeriodicDatum s y A₀) +
          (translatePeriodicDatum s y A₀ - translatePeriodicDatum s y₀ A₀) := by
      abel
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [translatePeriodicDatum_sub, translatePeriodicDatum_norm]
  have hb : Tendsto (fun p : Space × PeriodicSobolev s ↦
      ‖p.2 - A₀‖ + ‖translatePeriodicDatum s p.1 A₀ - translatePeriodicDatum s y₀ A₀‖)
      (𝓝 (y₀, A₀)) (𝓝 0) := by
    have h1 : Tendsto (fun p : Space × PeriodicSobolev s ↦ ‖p.2 - A₀‖)
        (𝓝 (y₀, A₀)) (𝓝 0) := by
      have hc : Continuous fun p : Space × PeriodicSobolev s ↦ ‖p.2 - A₀‖ :=
        (continuous_snd.sub continuous_const).norm
      have h0 : ‖A₀ - A₀‖ = 0 := by rw [sub_self, norm_zero]
      exact h0 ▸ hc.tendsto (y₀, A₀)
    have h2 : Tendsto (fun p : Space × PeriodicSobolev s ↦
        ‖translatePeriodicDatum s p.1 A₀ - translatePeriodicDatum s y₀ A₀‖)
        (𝓝 (y₀, A₀)) (𝓝 0) := by
      have hc : Continuous fun p : Space × PeriodicSobolev s ↦
          ‖translatePeriodicDatum s p.1 A₀ - translatePeriodicDatum s y₀ A₀‖ :=
        (((continuous_translatePeriodicDatum s A₀).comp continuous_fst).sub
          continuous_const).norm
      have h0 : ‖translatePeriodicDatum s y₀ A₀ - translatePeriodicDatum s y₀ A₀‖ = 0 := by
        rw [sub_self, norm_zero]
      exact h0 ▸ hc.tendsto (y₀, A₀)
    have hsum := h1.add h2
    rwa [add_zero] at hsum
  exact squeeze_zero (fun p ↦ norm_nonneg _) hle hb

/-! ## 5. Auxiliary slab facts -/

/-- A slab-smooth field has globally smooth spatial slices. -/
theorem slice_contDiff {u : SpaceTimeField} {T : ℝ}
    (hu : ContDiffOn ℝ ∞ u (Ico (0 : ℝ) T ×ˢ (univ : Set Space))) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) T) : ContDiff ℝ ∞ (fun y : Space ↦ u (s, y)) :=
  hu.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun y ↦ ⟨hs, mem_univ y⟩)

/-- A slab-smooth field is differentiable at every interior spacetime point. -/
theorem interior_differentiableAt {u : SpaceTimeField} {T : ℝ}
    (hu : ContDiffOn ℝ ∞ u (Ico (0 : ℝ) T ×ˢ (univ : Set Space))) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) T) (y : Space) : DifferentiableAt ℝ u (s, y) := by
  have hmem : Ico (0 : ℝ) T ×ˢ (univ : Set Space) ∈ nhds ((s, y) : SpaceTime) := by
    refine Filter.mem_of_superset
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hs, mem_univ y⟩) ?_
    exact Set.prod_mono Ioo_subset_Ico_self Subset.rfl
  exact (hu.contDiffAt hmem).differentiableAt (by simp)

/-- The scalar analogue of `slice_contDiff`. -/
theorem slice_contDiff_scalar {p : SpaceTimeScalar} {T : ℝ}
    (hp : ContDiffOn ℝ ∞ p (Ico (0 : ℝ) T ×ˢ (univ : Set Space))) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) T) : ContDiff ℝ ∞ (fun y : Space ↦ p (s, y)) :=
  hp.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun y ↦ ⟨hs, mem_univ y⟩)

/-- Continuity of a transported datum path. -/
theorem continuousOn_transport_datumPath {s α : ℝ} {X c : ℝ → Space}
    {G : ℝ → PeriodicSobolev s} {I J : Set ℝ} (hX : Continuous X) (hc : Continuous c)
    (hG : ContinuousOn G J) (hmap : MapsTo (fun t : ℝ ↦ α * t) I J) :
    ContinuousOn
      (fun t : ℝ ↦ α • translatePeriodicDatum s (X t) (G (α * t)) - constantDatum s (c t))
      I := by
  have hGcomp : ContinuousOn (fun t : ℝ ↦ G (α * t)) I :=
    hG.comp ((continuous_const.mul continuous_id).continuousOn) hmap
  have hpair : ContinuousOn (fun t : ℝ ↦ (X t, G (α * t))) I :=
    (hX.continuousOn).prodMk hGcomp
  have h2 := (continuous_translate_pair s).comp_continuousOn hpair
  exact (h2.const_smul α).sub ((continuous_constantDatum s).comp_continuousOn hc.continuousOn)

/-! ## 6. The transport constructor -/

/-- **Transport of a classical periodic solution.**  If `w` solves the periodic
problem at viscosity `ν` with datum `a` and force `f` on `[0, T)`, and
`X : ℝ → Space` is a `C^∞` moving translation with derivatives `c = X'`,
`d = X''`, then the fields
`v (t,x) = α • u (α t, x + X t) - c t`, `q (t,x) = α² p (α t, x + X t)`
solve the periodic problem at viscosity `α ν` with datum `a'` and force
`g (t,x) = α² f (α t, x + X t) - d t` on `[0, T')`, where `α T' = T`. -/
def classicalSolutionT_transport
    {ν ν' T α T' : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) (hα : 0 < α) (hT' : α * T' = T) (hν' : ν' = α * ν)
    {X c d : ℝ → Space} (hX : ContDiff ℝ ∞ X) (hcs : ContDiff ℝ ∞ c)
    (hXc : ∀ t : ℝ, HasDerivAt X (c t) t) (hcd : ∀ t : ℝ, HasDerivAt c (d t) t)
    {a' : SpatialField} {g v : SpaceTimeField} {q : SpaceTimeScalar}
    (hv : ∀ (t : ℝ) (x : Space), v (t, x) = α • w.velocity (α * t, x + X t) - c t)
    (hq : ∀ (t : ℝ) (x : Space), q (t, x) = α ^ 2 * w.pressure (α * t, x + X t))
    (hg : ∀ (t : ℝ) (x : Space), g (t, x) = α ^ 2 • f (α * t, x + X t) - d t)
    (ha' : ∀ x : Space, a' x = α • a (x + X 0) - c 0) :
    ClassicalSolutionT ν' a' g T' := by
  have hTpos := w.horizon_pos
  have hT'pos : 0 < T' := by
    rcases le_or_gt T' 0 with h | h
    · exfalso; nlinarith
    · exact h
  have hmap : ∀ t ∈ Ico (0 : ℝ) T', α * t ∈ Ico (0 : ℝ) T := by
    intro t ht
    refine ⟨mul_nonneg hα.le ht.1, ?_⟩
    rw [← hT']
    exact mul_lt_mul_of_pos_left ht.2 hα
  have hmapo : ∀ t ∈ Ioo (0 : ℝ) T', α * t ∈ Ioo (0 : ℝ) T := by
    intro t ht
    exact ⟨mul_pos hα ht.1, by rw [← hT']; exact mul_lt_mul_of_pos_left ht.2 hα⟩
  have hΦ : ContDiff ℝ ∞ (fun z : SpaceTime ↦ ((α * z.1 : ℝ), z.2 + X z.1)) :=
    (contDiff_const.mul contDiff_fst).prodMk (contDiff_snd.add (hX.comp contDiff_fst))
  have hmaps : MapsTo (fun z : SpaceTime ↦ ((α * z.1 : ℝ), z.2 + X z.1))
      (Ico (0 : ℝ) T' ×ˢ (univ : Set Space)) (Ico (0 : ℝ) T ×ˢ (univ : Set Space)) := by
    rintro z hz
    exact ⟨hmap z.1 hz.1, mem_univ _⟩
  have hvfun : v = fun z : SpaceTime ↦ α • w.velocity (α * z.1, z.2 + X z.1) - c z.1 :=
    funext fun z ↦ hv z.1 z.2
  have hqfun : q = fun z : SpaceTime ↦ α ^ 2 * w.pressure (α * z.1, z.2 + X z.1) :=
    funext fun z ↦ hq z.1 z.2
  refine
    { velocity := v
      pressure := q
      horizon_pos := hT'pos
      velocity_smooth := ?_
      pressure_smooth := ?_
      initial := ?_
      divergence := ?_
      momentum := ?_
      sobolev := ?_
      pressure_gradient := ?_
      velocity_periodic := ?_
      pressure_periodic := ?_
      pressure_gauge := ?_ }
  · rw [hvfun]
    exact ((w.velocity_smooth.comp hΦ.contDiffOn hmaps).const_smul α).sub
      (hcs.comp contDiff_fst).contDiffOn
  · rw [hqfun]
    exact (w.pressure_smooth.comp hΦ.contDiffOn hmaps).const_smul (α ^ 2)
  · intro x
    rw [hv 0 x, ha' x, mul_zero, w.initial (x + X 0)]
  · intro t ht x
    have hslice := slice_contDiff w.velocity_smooth (hmap t ht)
    rw [spatialDivergence_slice (fun y ↦ hv t y)
        (hslice.differentiable (by simp) (x + X t)),
      w.divergence (α * t) (hmap t ht) (x + X t), mul_zero]
  · subst hν'
    intro t ht x
    have ht' := hmapo t ht
    have htI : α * t ∈ Ico (0 : ℝ) T := ⟨ht'.1.le, ht'.2⟩
    have hu := interior_differentiableAt w.velocity_smooth ht' (x + X t)
    have hu2 : ContDiff ℝ 2 (fun y : Space ↦ w.velocity (α * t, y)) :=
      (slice_contDiff w.velocity_smooth htI).of_le (by simp)
    have hp := (slice_contDiff_scalar w.pressure_smooth htI).differentiable
      (by simp) (x + X t)
    rw [navierStokesResidual_transport (fun s ↦ hv s x) (fun y ↦ hv t y)
        (fun y ↦ hq t y) (hXc t) (hcd t) hu hu2 hp,
      w.momentum (α * t) ht' (x + X t), hg t x]
  · intro m
    obtain ⟨G, hGc, hGd⟩ := w.sobolev m
    refine ⟨fun t ↦ α • translatePeriodicDatum (m : ℝ) (X t) (G (α * t)) -
      constantDatum (m : ℝ) (c t), ?_, ?_⟩
    · exact continuousOn_transport_datumPath hX.continuous hcs.continuous hGc hmap
    · intro t ht
      rw [show (fun x : Space ↦ v (t, x)) =
          fun x : Space ↦ α • w.velocity (α * t, x + X t) - c t from funext (hv t)]
      exact isPeriodicDatum_transport (hGd (α * t) (hmap t ht)) α (X t) (c t)
  · intro t ht
    have hpslice := slice_contDiff_scalar w.pressure_smooth (hmap t ht)
    have heq : (fun x : Space ↦ pressureGradient q t x) =
        fun x : Space ↦ α ^ 2 • pressureGradient w.pressure (α * t) (x + X t) :=
      funext fun x ↦ pressureGradient_slice (fun y ↦ hq t y)
        (hpslice.differentiable (by simp) (x + X t))
    rw [heq]
    exact memLp_torusLift_vector
      (((NavierStokes.PeriodicUniqueness.pressureGradient_contDiff
        hpslice).continuous.comp (continuous_id.add continuous_const)).const_smul (α ^ 2)) 2
  · intro t ht x i
    rw [hv t (x + coordinateVector i), hv t x,
      show x + coordinateVector i + X t = (x + X t) + coordinateVector i by abel,
      w.velocity_periodic (α * t) (hmap t ht) (x + X t) i]
  · intro t ht x i
    rw [hq t (x + coordinateVector i), hq t x,
      show x + coordinateVector i + X t = (x + X t) + coordinateVector i by abel,
      w.pressure_periodic (α * t) (hmap t ht) (x + X t) i]
  · intro t ht
    have hper : IsPeriodicSpatial (fun x : Space ↦ w.pressure (α * t, x)) :=
      w.pressure_periodic (α * t) (hmap t ht)
    have h2 : ∀ y : PeriodicTorus,
        torusLift (fun x : Space ↦ q (t, x)) y =
          α ^ 2 * torusLift (fun x : Space ↦ w.pressure (α * t, x))
            (y + torusPoint (X t)) := by
      intro y
      rw [show (fun x : Space ↦ q (t, x)) =
          fun x : Space ↦ α ^ 2 * w.pressure (α * t, x + X t) from funext (hq t)]
      change α ^ 2 * torusLift (fun x : Space ↦ w.pressure (α * t, x + X t)) y = _
      rw [torusLift_translate hper (X t) y]
    change (∫ y : PeriodicTorus, torusLift (fun x : Space ↦ q (t, x)) y
      ∂periodicTorusMeasure) = 0
    simp_rw [h2]
    rw [integral_const_mul, integral_add_right_eq_self]
    change α ^ 2 * pressureMeanT w.pressure (α * t) = 0
    rw [w.pressure_gauge (α * t) (hmap t ht), mul_zero]

/-! ## 7. The two viscosity instances -/

/-- Unit-viscosity rescaling: `α = ν⁻¹`, no translation. -/
def classicalSolutionT_toUnit {ν T : ℝ} (hν : 0 < ν) {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) :
    ClassicalSolutionT 1 (unitViscosityInitialT ν a) (unitViscosityForceT ν f) (ν * T) := by
  have hν0 : ν ≠ 0 := ne_of_gt hν
  refine classicalSolutionT_transport (α := ν⁻¹) (X := fun _ ↦ (0 : Space))
    (c := fun _ ↦ (0 : Space)) (d := fun _ ↦ (0 : Space))
    (v := unitViscosityVelocityT ν w.velocity)
    (q := unitViscosityPressureT ν w.pressure)
    w (by positivity) ?_ ?_ contDiff_const contDiff_const
    (fun t ↦ hasDerivAt_const t 0) (fun t ↦ hasDerivAt_const t 0) ?_ ?_ ?_ ?_
  · field_simp
  · rw [inv_mul_cancel₀ hν0]
  · intro t x
    simp only [unitViscosityVelocityT, add_zero, sub_zero, div_eq_inv_mul]
  · intro t x
    simp only [unitViscosityPressureT, add_zero, div_eq_inv_mul, inv_pow]
  · intro t x
    simp only [unitViscosityForceT, add_zero, sub_zero, div_eq_inv_mul, inv_pow]
  · intro x
    simp only [unitViscosityInitialT, add_zero, sub_zero]

/-- Restoring the viscosity: `α = ν`, no translation. -/
def classicalSolutionT_fromUnit {ν T : ℝ} (hν : 0 < ν) {a : SpatialField} {f : SpaceTimeField}
    (v : ClassicalSolutionT 1 (unitViscosityInitialT ν a) (unitViscosityForceT ν f) (ν * T)) :
    ClassicalSolutionT ν a f T := by
  have hν0 : ν ≠ 0 := ne_of_gt hν
  refine classicalSolutionT_transport (α := ν) (X := fun _ ↦ (0 : Space))
    (c := fun _ ↦ (0 : Space)) (d := fun _ ↦ (0 : Space))
    (v := restoreViscosityVelocityT ν v.velocity)
    (q := restoreViscosityPressureT ν v.pressure)
    v hν rfl (mul_one ν).symm contDiff_const contDiff_const
    (fun t ↦ hasDerivAt_const t 0) (fun t ↦ hasDerivAt_const t 0) ?_ ?_ ?_ ?_
  · intro t x
    simp only [restoreViscosityVelocityT, add_zero, sub_zero]
  · intro t x
    simp only [restoreViscosityPressureT, add_zero]
  · intro t x
    simp only [unitViscosityForceT, add_zero, sub_zero, smul_smul]
    rw [mul_comm ν t, mul_div_assoc, div_self hν0, mul_one,
      mul_inv_cancel₀ (pow_ne_zero 2 hν0), one_smul]
  · intro x
    simp only [unitViscosityInitialT, add_zero, sub_zero, smul_smul,
      mul_inv_cancel₀ hν0, one_smul]

/-! ## 7a. The transported fields -/

@[simp] theorem classicalSolutionT_toUnit_velocity {ν T : ℝ} (hν : 0 < ν) {a : SpatialField}
    {f : SpaceTimeField} (w : ClassicalSolutionT ν a f T) :
    (classicalSolutionT_toUnit hν w).velocity = unitViscosityVelocityT ν w.velocity := rfl

@[simp] theorem classicalSolutionT_toUnit_pressure {ν T : ℝ} (hν : 0 < ν) {a : SpatialField}
    {f : SpaceTimeField} (w : ClassicalSolutionT ν a f T) :
    (classicalSolutionT_toUnit hν w).pressure = unitViscosityPressureT ν w.pressure := rfl

@[simp] theorem classicalSolutionT_fromUnit_velocity {ν T : ℝ} (hν : 0 < ν) {a : SpatialField}
    {f : SpaceTimeField}
    (v : ClassicalSolutionT 1 (unitViscosityInitialT ν a) (unitViscosityForceT ν f) (ν * T)) :
    (classicalSolutionT_fromUnit hν v).velocity = restoreViscosityVelocityT ν v.velocity := rfl

@[simp] theorem classicalSolutionT_fromUnit_pressure {ν T : ℝ} (hν : 0 < ν) {a : SpatialField}
    {f : SpaceTimeField}
    (v : ClassicalSolutionT 1 (unitViscosityInitialT ν a) (unitViscosityForceT ν f) (ν * T)) :
    (classicalSolutionT_fromUnit hν v).pressure = restoreViscosityPressureT ν v.pressure := rfl

/-! ## 7b. Regularity transport in the pure rescaling case -/

/-- `projected` holds for every classical periodic solution. -/
theorem classicalSolutionT_projected {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
      temporalDerivative w.velocity t x - ν • spatialLaplacian w.velocity t x =
        (f (t, x) - convectionDivergenceT w.velocity t x) -
          pressureGradient w.pressure t x := by
  intro t ht x
  have ht' : t ∈ Ico (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
  have hs : ContDiff ℝ ∞ (fun y : Space ↦ w.velocity (t, y)) :=
    slice_contDiff w.velocity_smooth ht'
  exact (NSFormalization.Section4.A01.navierStokesResidual_eq_iff_projected
    ν w.velocity w.pressure t x (f (t, x))
    (hs.differentiable (by simp) x) (w.divergence t ht' x)).mp (w.momentum t ht x)

/-- The pressure Poisson equation transports under a pure rescaling. -/
theorem pressure_poisson_rescale {u v f g : SpaceTimeField} {p q : SpaceTimeScalar}
    {α s t : ℝ} (x : Space)
    (hv : ∀ y : Space, v (t, y) = α • u (s, y))
    (hq : ∀ y : Space, q (t, y) = α ^ 2 * p (s, y))
    (hg : ∀ y : Space, g (t, y) = α ^ 2 • f (s, y))
    (hu : ContDiff ℝ ∞ (fun y : Space ↦ u (s, y)))
    (hp : ContDiff ℝ ∞ (fun y : Space ↦ p (s, y)))
    (hfs : ContDiff ℝ ∞ (fun y : Space ↦ f (s, y)))
    (hsrc : scalarSpatialLaplacianT p s x =
      spatialDivergence f s x -
        spatialDivergence (fun z : SpaceTime ↦ convectionDivergenceT u z.1 z.2) s x) :
    scalarSpatialLaplacianT q t x =
      spatialDivergence g t x -
        spatialDivergence (fun z : SpaceTime ↦ convectionDivergenceT v z.1 z.2) t x := by
  have h1 : scalarSpatialLaplacianT q t x = α ^ 2 * scalarSpatialLaplacianT p s x := by
    have h := scalarSpatialLaplacianT_slice (Y := 0) x
      (fun y ↦ by simpa using hq y) (hp.of_le (by simp))
    simpa using h
  have h2 : spatialDivergence g t x = α ^ 2 * spatialDivergence f s x := by
    have h := spatialDivergence_slice (α := α ^ 2) (Y := 0) (c := 0) (x := x)
      (fun y ↦ by simpa using hg y) (by simpa using hfs.differentiable (by simp) x)
    simpa using h
  have h3 : spatialDivergence (fun z : SpaceTime ↦ convectionDivergenceT v z.1 z.2) t x =
      α ^ 2 * spatialDivergence (fun z : SpaceTime ↦ convectionDivergenceT u z.1 z.2) s x := by
    have hconv : ∀ y : Space,
        convectionDivergenceT v t y = α ^ 2 • convectionDivergenceT u s y := by
      intro y
      rw [convectionDivergence_slice_smul y hv hu, sq]
    have h := spatialDivergence_slice (α := α ^ 2) (Y := 0) (c := 0) (x := x)
      (v := fun z : SpaceTime ↦ convectionDivergenceT v z.1 z.2)
      (u := fun z : SpaceTime ↦ convectionDivergenceT u z.1 z.2)
      (fun y ↦ by simpa using hconv y)
      (by simpa using (contDiff_convectionDivergence_slice hu).differentiable (by simp) x)
    simpa using h
  rw [h1, h2, h3, hsrc, mul_sub]

/-- Local regularity transports to the unit-viscosity rescaling. -/
theorem periodicLocalRegularity_toUnit {ν T : ℝ} (hν : 0 < ν) {a : SpatialField}
    {f : SpaceTimeField} (hf : ContDiff ℝ ∞ f) (w : ClassicalSolutionT ν a f T)
    (hreg : PeriodicLocalRegularity ν a f T w) :
    PeriodicLocalRegularity 1 (unitViscosityInitialT ν a) (unitViscosityForceT ν f) (ν * T)
      (classicalSolutionT_toUnit hν w) := by
  have hν0 : ν ≠ 0 := ne_of_gt hν
  have hmap : ∀ t ∈ Ico (0 : ℝ) (ν * T), t / ν ∈ Ico (0 : ℝ) T := by
    intro t ht
    refine ⟨div_nonneg ht.1 hν.le, ?_⟩
    rw [div_lt_iff₀ hν, mul_comm]
    exact ht.2
  refine ⟨?_, ?_, ?_⟩
  · intro m
    obtain ⟨G, hGpath, hGsmooth⟩ := hreg.sobolev_smooth m
    refine ⟨fun t ↦ ν⁻¹ • G (t / ν), ?_, ?_⟩
    · intro t ht
      rw [classicalSolutionT_toUnit_velocity]
      exact isPeriodicDatum_smul (hGpath (t / ν) (hmap t ht)) ν⁻¹
    · exact (hGsmooth.comp (contDiff_id.div_const ν).contDiffOn hmap).const_smul ν⁻¹
  · intro t ht x
    refine pressure_poisson_rescale (α := ν⁻¹) (s := t / ν) x (fun y ↦ rfl) (fun y ↦ ?_)
      (fun y ↦ ?_) (slice_contDiff w.velocity_smooth (hmap t ht))
      (slice_contDiff_scalar w.pressure_smooth (hmap t ht))
      (hf.comp (contDiff_const.prodMk contDiff_id)) (hreg.pressure_poisson (t / ν) (hmap t ht) x)
    · rw [classicalSolutionT_toUnit_pressure]
      simp only [unitViscosityPressureT, inv_pow]
    · simp only [unitViscosityForceT, inv_pow]
  · exact classicalSolutionT_projected (classicalSolutionT_toUnit hν w)

/-- Local regularity transports back from the unit-viscosity rescaling. -/
theorem periodicLocalRegularity_fromUnit {ν T : ℝ} (hν : 0 < ν) {a : SpatialField}
    {f : SpaceTimeField} (hf : ContDiff ℝ ∞ f)
    (v : ClassicalSolutionT 1 (unitViscosityInitialT ν a) (unitViscosityForceT ν f) (ν * T))
    (hreg : PeriodicLocalRegularity 1 (unitViscosityInitialT ν a) (unitViscosityForceT ν f)
      (ν * T) v) :
    PeriodicLocalRegularity ν a f T (classicalSolutionT_fromUnit hν v) := by
  have hν0 : ν ≠ 0 := ne_of_gt hν
  have hmap : ∀ t ∈ Ico (0 : ℝ) T, ν * t ∈ Ico (0 : ℝ) (ν * T) := by
    intro t ht
    exact ⟨mul_nonneg hν.le ht.1, mul_lt_mul_of_pos_left ht.2 hν⟩
  have hfu : ContDiff ℝ ∞ (unitViscosityForceT ν f) :=
    (hf.comp ((contDiff_fst.div_const ν).prodMk contDiff_snd)).const_smul (ν ^ 2)⁻¹
  refine ⟨?_, ?_, ?_⟩
  · intro m
    obtain ⟨G, hGpath, hGsmooth⟩ := hreg.sobolev_smooth m
    refine ⟨fun t ↦ ν • G (ν * t), ?_, ?_⟩
    · intro t ht
      rw [classicalSolutionT_fromUnit_velocity]
      exact isPeriodicDatum_smul (hGpath (ν * t) (hmap t ht)) ν
    · exact (hGsmooth.comp (contDiff_const.mul contDiff_id).contDiffOn hmap).const_smul ν
  · intro t ht x
    refine pressure_poisson_rescale (α := ν) (s := ν * t) x (fun y ↦ rfl) (fun y ↦ rfl)
      (fun y ↦ ?_) (slice_contDiff v.velocity_smooth (hmap t ht))
      (slice_contDiff_scalar v.pressure_smooth (hmap t ht))
      (hfu.comp (contDiff_const.prodMk contDiff_id))
      (hreg.pressure_poisson (ν * t) (hmap t ht) x)
    · simp only [unitViscosityForceT, smul_smul]
      rw [mul_comm ν t, mul_div_assoc, div_self hν0, mul_one,
        mul_inv_cancel₀ (pow_ne_zero 2 hν0), one_smul]
  · exact classicalSolutionT_projected (classicalSolutionT_fromUnit hν v)

/-! ## 7c. Commuting the divergence with a constant-direction derivative -/

/-- On a divergence-free smooth slice, the field `y ↦ (Du)(y) c` is itself
divergence free: its divergence is the `c`-directional derivative of `div u`.
This is the symmetry of the second derivative. -/
theorem spatialDivergence_directional_eq_zero {u : SpaceTimeField} {s : ℝ}
    (hu : ContDiff ℝ ∞ (fun y : Space ↦ u (s, y)))
    (hdiv : ∀ y : Space, spatialDivergence u s y = 0) (c : Space) (x : Space) :
    spatialDivergence (fun z : SpaceTime ↦ spatialDerivative u z.1 z.2 c) s x = 0 := by
  set F : Space → Space := fun y : Space ↦ u (s, y) with hF
  set F' : Space → (Space →L[ℝ] Space) := fderiv ℝ F with hF'def
  have hFd : ∀ y : Space, HasFDerivAt F (F' y) y :=
    fun y ↦ (hu.differentiable (by simp) y).hasFDerivAt
  have hF'smooth : ContDiff ℝ ∞ F' := hu.fderiv_right (by simp)
  set F'' : Space →L[ℝ] Space →L[ℝ] Space := fderiv ℝ F' x with hF''def
  have hF'd : HasFDerivAt F' F'' x := (hF'smooth.differentiable (by simp) x).hasFDerivAt
  have hsymm : ∀ v w : Space, F'' v w = F'' w v := second_derivative_symmetric hFd hF'd
  -- the derivative of the directional field
  have hdir : ∀ e : Space,
      fderiv ℝ (fun y : Space ↦ F' y c) x e = F'' e c := by
    intro e
    have h := (hF'd.clm_apply (hasFDerivAt_const c x)).fderiv
    rw [h]
    simp
  -- the derivative of the divergence
  have hsum : HasFDerivAt (fun y : Space ↦ ∑ i : Fin 3, (F' y (coordinateVector i)) i)
      (∑ i : Fin 3, (EuclideanSpace.proj (𝕜 := ℝ) i).comp
        (F''.flip (coordinateVector i))) x := by
    refine HasFDerivAt.fun_sum (u := Finset.univ)
      (A := fun (i : Fin 3) (y : Space) ↦ (F' y (coordinateVector i)) i)
      (A' := fun i : Fin 3 ↦ (EuclideanSpace.proj (𝕜 := ℝ) i).comp
        (F''.flip (coordinateVector i))) ?_
    intro i _
    have hi := hF'd.clm_apply (hasFDerivAt_const (coordinateVector i) x)
    have := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x hi
    simpa [Function.comp_def] using this
  have hzero : HasFDerivAt (fun y : Space ↦ ∑ i : Fin 3, (F' y (coordinateVector i)) i)
      (0 : Space →L[ℝ] ℝ) x := by
    have heq : (fun y : Space ↦ ∑ i : Fin 3, (F' y (coordinateVector i)) i) =
        fun _ : Space ↦ (0 : ℝ) := funext fun y ↦ hdiv y
    rw [heq]
    exact hasFDerivAt_const (0 : ℝ) x
  have hunique := hsum.unique hzero
  have happ := congrArg (fun L : Space →L[ℝ] ℝ ↦ L c) hunique
  simp only [sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, zero_apply] at happ
  change ∑ i : Fin 3, (fderiv ℝ (fun y : Space ↦ F' y c) x (coordinateVector i)) i = 0
  simp only [hdir]
  calc ∑ i : Fin 3, (F'' (coordinateVector i) c) i
      = ∑ i : Fin 3, (F'' c (coordinateVector i)) i := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [hsymm]
    _ = 0 := happ

/-- The pressure Poisson equation transports under a moving translation. -/
theorem pressure_poisson_translate {u v f g : SpaceTimeField} {p q : SpaceTimeScalar}
    {t : ℝ} {Y c₀ e₀ : Space} (x : Space)
    (hv : ∀ y : Space, v (t, y) = u (t, y + Y) - c₀)
    (hq : ∀ y : Space, q (t, y) = p (t, y + Y))
    (hg : ∀ y : Space, g (t, y) = f (t, y + Y) - e₀)
    (hu : ContDiff ℝ ∞ (fun y : Space ↦ u (t, y)))
    (hp : ContDiff ℝ ∞ (fun y : Space ↦ p (t, y)))
    (hfs : ContDiff ℝ ∞ (fun y : Space ↦ f (t, y)))
    (hdivu : ∀ y : Space, spatialDivergence u t y = 0)
    (hdivv : ∀ y : Space, spatialDivergence v t y = 0)
    (hsrc : scalarSpatialLaplacianT p t (x + Y) =
      spatialDivergence f t (x + Y) -
        spatialDivergence (fun z : SpaceTime ↦ convectionDivergenceT u z.1 z.2) t (x + Y)) :
    scalarSpatialLaplacianT q t x =
      spatialDivergence g t x -
        spatialDivergence (fun z : SpaceTime ↦ convectionDivergenceT v z.1 z.2) t x := by
  have hud : Differentiable ℝ (fun y : Space ↦ u (t, y)) := hu.differentiable (by simp)
  have h1 : scalarSpatialLaplacianT q t x = scalarSpatialLaplacianT p t (x + Y) := by
    have h := scalarSpatialLaplacianT_slice (β := 1) (Y := Y) x
      (fun y ↦ by simpa using hq y) (hp.of_le (by simp))
    simpa using h
  have h2 : spatialDivergence g t x = spatialDivergence f t (x + Y) := by
    have h := spatialDivergence_slice (α := 1) (Y := Y) (c := e₀) (x := x)
      (fun y ↦ by simpa using hg y) (hfs.differentiable (by simp) (x + Y))
    simpa using h
  have hDsmooth : ContDiff ℝ ∞ (fun y : Space ↦ spatialDerivative u t y c₀) := by
    have hfd : ContDiff ℝ ∞ (fderiv ℝ (fun y : Space ↦ u (t, y))) := hu.fderiv_right (by simp)
    exact hfd.clm_apply contDiff_const
  have hconvsmooth : ContDiff ℝ ∞ (fun y : Space ↦ convectionDivergenceT u t y) :=
    contDiff_convectionDivergence_slice hu
  have hconvv : ∀ y : Space, convectionDivergenceT v t y =
      convectionDivergenceT u t (y + Y) - spatialDerivative u t (y + Y) c₀ := by
    intro y
    have hvslice : (fun z : Space ↦ v (t, z)) = fun z : Space ↦ u (t, z + Y) - c₀ := funext hv
    have hvd : DifferentiableAt ℝ (fun z : Space ↦ v (t, z)) y := by
      rw [hvslice]
      exact (((differentiableAt_comp_add_right Y).2 (hud (y + Y))).sub_const c₀)
    have e1 : convectionDivergenceT v t y = advection v t y :=
      NSFormalization.Section4.A01.convectionDivergence_eq_advection v t y hvd (hdivv y)
    have e2 : convectionDivergenceT u t (y + Y) = advection u t (y + Y) :=
      NSFormalization.Section4.A01.convectionDivergence_eq_advection u t (y + Y)
        (hud (y + Y)) (hdivu (y + Y))
    rw [e1, e2, advection_slice (α := 1) (fun z ↦ by simpa using hv z) (hud (y + Y))]
    simp
  have h3 : spatialDivergence (fun z : SpaceTime ↦ convectionDivergenceT v z.1 z.2) t x =
      spatialDivergence (fun z : SpaceTime ↦ convectionDivergenceT u z.1 z.2) t (x + Y) := by
    have hK : ∀ y : Space,
        (fun z : SpaceTime ↦ convectionDivergenceT v z.1 z.2) (t, y) =
          (1 : ℝ) • ((fun z : SpaceTime ↦ convectionDivergenceT u z.1 z.2) -
            fun z : SpaceTime ↦ spatialDerivative u z.1 z.2 c₀) (t, y + Y) - 0 := by
      intro y
      simpa using hconvv y
    have hdiff : DifferentiableAt ℝ (fun y : Space ↦
        ((fun z : SpaceTime ↦ convectionDivergenceT u z.1 z.2) -
          fun z : SpaceTime ↦ spatialDerivative u z.1 z.2 c₀) (t, y)) (x + Y) :=
      (hconvsmooth.sub hDsmooth).differentiable (by simp) (x + Y)
    rw [spatialDivergence_slice hK hdiff, one_mul,
      NavierStokes.PeriodicUniqueness.spatialDivergence_sub hconvsmooth hDsmooth (x + Y),
      spatialDivergence_directional_eq_zero hu hdivu c₀ (x + Y), sub_zero]
  rw [h1, h2, h3, hsrc]

/-! ## 8. The Galilean instance -/

/-- The fundamental theorem of calculus for a continuous vector primitive. -/
theorem hasDerivAt_intervalPrimitive {h : ℝ → Space} (hh : Continuous h) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ ∫ r in (0 : ℝ)..s, h r) (h t) t :=
  intervalIntegral.integral_hasDerivAt_right (hh.intervalIntegrable 0 t)
    hh.aestronglyMeasurable.stronglyMeasurableAtFilter hh.continuousAt

/-- A smooth integrand has a smooth primitive. -/
theorem contDiff_intervalPrimitive {h : ℝ → Space} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun t : ℝ ↦ ∫ r in (0 : ℝ)..t, h r) := by
  apply contDiff_infty_iff_deriv.mpr
  constructor
  · intro t
    exact (hasDerivAt_intervalPrimitive hh.continuous t).differentiableAt
  · have hd : deriv (fun t : ℝ ↦ ∫ r in (0 : ℝ)..t, h r) = h :=
      funext fun t ↦ (hasDerivAt_intervalPrimitive hh.continuous t).deriv
    rw [hd]
    exact hh

theorem contDiff_galileanMeanT {a : SpatialField} {f : SpaceTimeField}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (galileanMeanT a f) :=
  contDiff_const.add (contDiff_intervalPrimitive (MeanIdentity.forceMeanT_contDiff hf))

theorem contDiff_galileanShiftT {a : SpatialField} {f : SpaceTimeField}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (galileanShiftT a f) :=
  contDiff_intervalPrimitive (contDiff_galileanMeanT hf)

theorem hasDerivAt_galileanShiftT {a : SpatialField} {f : SpaceTimeField}
    (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    HasDerivAt (galileanShiftT a f) (galileanMeanT a f t) t :=
  hasDerivAt_intervalPrimitive (contDiff_galileanMeanT hf).continuous t

theorem hasDerivAt_galileanMeanT {a : SpatialField} {f : SpaceTimeField}
    (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    HasDerivAt (galileanMeanT a f) (forceMeanT f t) t :=
  (hasDerivAt_intervalPrimitive
    (MeanIdentity.forceMeanT_contDiff hf).continuous t).const_add (meanT a)

@[simp] theorem galileanShiftT_zero (a : SpatialField) (f : SpaceTimeField) :
    galileanShiftT a f 0 = 0 := by
  simp [galileanShiftT]

@[simp] theorem galileanMeanT_zero (a : SpatialField) (f : SpaceTimeField) :
    galileanMeanT a f 0 = meanT a := by
  simp [galileanMeanT]

/-- Galilean mean reduction: `α = 1`, translation `X = galileanShiftT a f`. -/
def classicalSolutionT_galilean {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (hf : ContDiff ℝ ∞ f) (w : ClassicalSolutionT ν a f T) :
    ClassicalSolutionT ν (meanZeroPartT a) (galileanForceT a f) T := by
  refine classicalSolutionT_transport (α := 1) (X := galileanShiftT a f)
    (c := galileanMeanT a f) (d := forceMeanT f)
    (v := galileanVelocityT a f w.velocity) (q := galileanPressureT a f w.pressure)
    w one_pos (one_mul T) (one_mul ν).symm (contDiff_galileanShiftT hf)
    (contDiff_galileanMeanT hf) (hasDerivAt_galileanShiftT hf)
    (hasDerivAt_galileanMeanT hf) ?_ ?_ ?_ ?_
  · intro t x
    simp only [galileanVelocityT, one_smul, one_mul]
  · intro t x
    simp only [galileanPressureT, one_pow, one_mul]
  · intro t x
    simp only [galileanForceT, one_pow, one_smul, one_mul]
  · intro x
    simp only [meanZeroPartT, galileanShiftT_zero, galileanMeanT_zero, one_smul, add_zero]

@[simp] theorem classicalSolutionT_galilean_velocity {ν T : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (hf : ContDiff ℝ ∞ f) (w : ClassicalSolutionT ν a f T) :
    (classicalSolutionT_galilean (ν := ν) (T := T) hf w).velocity =
      galileanVelocityT a f w.velocity := rfl

@[simp] theorem classicalSolutionT_galilean_pressure {ν T : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (hf : ContDiff ℝ ∞ f) (w : ClassicalSolutionT ν a f T) :
    (classicalSolutionT_galilean (ν := ν) (T := T) hf w).pressure =
      galileanPressureT a f w.pressure := rfl

/-- The pressure Poisson clause for the Galilean-transformed solution. -/
theorem pressure_poisson_galilean {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (hf : ContDiff ℝ ∞ f) (w : ClassicalSolutionT ν a f T)
    (hreg : PeriodicLocalRegularity ν a f T w) :
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
      scalarSpatialLaplacianT (classicalSolutionT_galilean hf w).pressure t x =
        spatialDivergence (galileanForceT a f) t x -
          spatialDivergence (fun z : SpaceTime ↦
            convectionDivergenceT (classicalSolutionT_galilean hf w).velocity z.1 z.2) t x := by
  intro t ht x
  rw [classicalSolutionT_galilean_pressure, classicalSolutionT_galilean_velocity]
  refine pressure_poisson_translate (u := w.velocity) (p := w.pressure) (f := f)
    (Y := galileanShiftT a f t) (c₀ := galileanMeanT a f t) (e₀ := forceMeanT f t) x
    (fun y ↦ rfl) (fun y ↦ rfl) (fun y ↦ rfl)
    (slice_contDiff w.velocity_smooth ht) (slice_contDiff_scalar w.pressure_smooth ht)
    (hf.comp (contDiff_const.prodMk contDiff_id)) (fun y ↦ w.divergence t ht y) ?_
    (hreg.pressure_poisson t ht (x + galileanShiftT a f t))
  intro y
  exact (classicalSolutionT_galilean hf w).divergence t ht y

/-! ## 9. The API-shaped conclusions

The three target fields of `research/T11/probes/api_on_canonical.lean` are
`transformed_solution`, `to_unit` and `from_unit`.  The two rescaling fields are
proved verbatim *from the local regularity of the given solution* — the field
statements quantify over an arbitrary `ClassicalSolutionT`, which carries only a
`ContinuousOn` datum path, so no `PeriodicLocalRegularity` for the transported
solution can be produced without one for the source.  The Galilean field is
proved verbatim except for that same conjunct. -/

/-- `to_unit`, with the local regularity of the given solution as its input. -/
theorem to_unit_of_regularity : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          PeriodicLocalRegularity ν a f T w →
          ∃ v : ClassicalSolutionT 1 (unitViscosityInitialT ν a)
              (unitViscosityForceT ν f) (ν * T),
            v.velocity = unitViscosityVelocityT ν w.velocity ∧
            v.pressure = unitViscosityPressureT ν w.pressure ∧
            PeriodicLocalRegularity 1 (unitViscosityInitialT ν a)
              (unitViscosityForceT ν f) (ν * T) v := by
  intro ν hν a _ha f hf T w hreg
  exact ⟨classicalSolutionT_toUnit hν w, rfl, rfl,
    periodicLocalRegularity_toUnit hν hf.1 w hreg⟩

/-- `from_unit`, with the local regularity of the unit-viscosity solution as its input. -/
theorem from_unit_of_regularity : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ),
          ∀ v : ClassicalSolutionT 1 (unitViscosityInitialT ν a)
              (unitViscosityForceT ν f) (ν * T),
            PeriodicLocalRegularity 1 (unitViscosityInitialT ν a)
              (unitViscosityForceT ν f) (ν * T) v →
            ∃ w : ClassicalSolutionT ν a f T,
              w.velocity = restoreViscosityVelocityT ν v.velocity ∧
              w.pressure = restoreViscosityPressureT ν v.pressure ∧
              PeriodicLocalRegularity ν a f T w := by
  intro ν hν a _ha f hf T v hreg
  exact ⟨classicalSolutionT_fromUnit hν v, rfl, rfl,
    periodicLocalRegularity_fromUnit hν hf.1 v hreg⟩

/-- `transformed_solution` without its `PeriodicLocalRegularity` conjunct: the
Galilean-transformed fields are a classical solution for the centred datum and
the centred force, and they satisfy the `projected` clause. -/
theorem transformed_solution_fields : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          ∃ v : ClassicalSolutionT ν (meanZeroPartT a) (galileanForceT a f) T,
            v.velocity = galileanVelocityT a f w.velocity ∧
            v.pressure = galileanPressureT a f w.pressure ∧
            (∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
              temporalDerivative v.velocity t x - ν • spatialLaplacian v.velocity t x =
                (galileanForceT a f (t, x) - convectionDivergenceT v.velocity t x) -
                  pressureGradient v.pressure t x) := by
  intro ν _hν a _ha f hf T w
  exact ⟨classicalSolutionT_galilean hf.1 w, rfl, rfl,
    classicalSolutionT_projected (classicalSolutionT_galilean hf.1 w)⟩

/-- `transformed_solution` with its `PeriodicLocalRegularity` conjunct replaced by the two
clauses of that record which do transport: `pressure_poisson` and `projected`.  The third
clause, `sobolev_smooth`, is the residual recorded in `research/T11/REPORT_331.md`. -/
theorem transformed_solution_two_clauses : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          PeriodicLocalRegularity ν a f T w →
          ∃ v : ClassicalSolutionT ν (meanZeroPartT a) (galileanForceT a f) T,
            v.velocity = galileanVelocityT a f w.velocity ∧
            v.pressure = galileanPressureT a f w.pressure ∧
            (∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
              scalarSpatialLaplacianT v.pressure t x =
                spatialDivergence (galileanForceT a f) t x -
                  spatialDivergence
                    (fun z : SpaceTime ↦ convectionDivergenceT v.velocity z.1 z.2) t x) ∧
            (∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
              temporalDerivative v.velocity t x - ν • spatialLaplacian v.velocity t x =
                (galileanForceT a f (t, x) - convectionDivergenceT v.velocity t x) -
                  pressureGradient v.pressure t x) := by
  intro ν _hν a _ha f hf T w hreg
  exact ⟨classicalSolutionT_galilean hf.1 w, rfl, rfl,
    pressure_poisson_galilean hf.1 w hreg,
    classicalSolutionT_projected (classicalSolutionT_galilean hf.1 w)⟩

end Transport

end NSFormalization.Section3.T11
