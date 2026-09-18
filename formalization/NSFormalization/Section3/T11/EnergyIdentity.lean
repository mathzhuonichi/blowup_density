import NSFormalization.Section3.T11.HighOrder
import NSFormalization.Section3.T11.MildMomentum
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# T11 unit U12a — the periodic `H^m` energy identity of a classical solution

`paper/sections/appendix-a-local-theory.tex:127-141`.  This module closes
**missing fact A** of lane 322 (`research/T11/ATTEMPTS_HIGH_ORDER.md` §3.1): the
time differentiability of the Fourier coefficient path of a genuine
`ClassicalSolutionT`, the coefficient form of the momentum equation, and the
`H^m` energy identity that `higherOrderBound_of_energyInequality` consumes
through its `HasDerivAt … d t` component.

## The route

Nothing here goes through an `ℓ²`-valued datum path.  The whole argument lives
at the scalar Fourier coefficients

  `û ᵢ(t,k) = ∫_{T³} e^{−2πik·x} uᵢ(t,x) dx`   (`velocityCoeffT`)

and re-sums at the end:

1. **Differentiation under the integral sign** (`hasDerivAt_velocityCoeffT`).
   `periodicFourierCoeff` is the cube integral of `χ₋ₖ · uᵢ`
   (`Paper1.periodicFourierCoeff_eq_cube`), and on the open slab
   `Ioo 0 T ×ˢ univ` the integrand is jointly `C¹`, so
   `PeriodicIntegration.hasDerivAt_cubeIntegral_of_contDiffOn` applies verbatim:
   `d/dt û ᵢ(t,k) = (∂ₜuᵢ)^(t,k)`.  Only `velocity_smooth` is used.
2. **The momentum equation, coefficient by coefficient**
   (`velocityDerivCoeffT_momentum`).  Insert `w.momentum` pointwise and take
   coefficients of the four terms:
   `d/dt û ᵢ(k) = −ν|2πk|² û ᵢ(k) + (f̂ ᵢ(k) − Q̂ ᵢ(k)) − 2πikᵢ p̂(k)`,
   with `Q = (u·∇)u` (`convectionFieldT`).  The Laplacian symbol is lane 327's
   `periodicFourierCoeff_spatialLaplacian`; the gradient symbol is
   `periodicFourierCoeff_fderiv` of T10's Fourier calculus.
2'. **The projected form** (`velocityDerivCoeffT_momentum_projected`), the
   manuscript's spelling:
   `d/dt û(t)(k) = −ν·4π²|k|²·û(t)(k) + (P̂(f̂(t) − Q̂(t)))(k)`,
   with `P̂` the periodic Leray symbol at `k` — `T10.periodicLeray`, read on raw
   coefficients through the `rfl` bridge `MildMomentum.periodicLeray_eq_lerayAt`
   (exhibited in the probe).  It follows from 2 by applying `P̂`: `d/dt û` is
   solenoidal (`solenoidal_velocityDerivCoeffT`, the time derivative of the
   identically vanishing coefficient divergence) and so is `û`, so `P̂` fixes
   both (`lerayAt_of_solenoidal`), while the pressure gradient `2πikᵢ p̂(k)` is
   annihilated (`lerayAt_gradient`).  The energy identity itself uses only the
   unprojected form 2, because the gradient term is killed at step 3 anyway.
3. **The pressure drop** (`solenoidal_velocityCoeffT`,
   `torusPressureSymbol_drop_raw`).  `w.divergence` gives
   `∑ⱼ 2πikⱼ û ⱼ(k) = 0`, hence `∑ᵢ conj(û ᵢ(k)) · 2πikᵢ p̂(k) = 0` at **every**
   frequency: the pressure is gone before any summation, exactly as lane 322's
   datum-level `torusPressureDrop`.
4. **Termwise differentiation of the energy series**
   (`hasDerivAt_torusSobolevNormAt_sq`).  Vector Parseval writes
   `‖u(t)‖²_{H^m} = ∑ₖ W(k)^m ∑ᵢ |û ᵢ(t,k)|²` (`hasSum_freqEnergyT`), and the
   differentiated series is dominated on a compact time window by
   `6·M·D·W(k)⁻²`: the factor `|û ᵢ| ≤ M·W^{−(m+2)}` comes from the **continuous
   datum path at order `2m+4`** of `ClassicalSolutionT.sobolev`, and
   `|(∂ₜuᵢ)^(r,k)| ≤ D` from one sup bound of `∂ₜu` on a compact slab piece
   (`exists_velocityDerivCoeffT_bound`).  `hasDerivAt_tsum_of_isPreconnected`
   then differentiates the series term by term.  This is why no `ContDiffOn ℝ ∞ G`
   regularity predicate is needed — continuity of the datum path at one higher
   order is enough.
5. **The identity** (`energyIdentity_of_classical`):
   `d/dt ‖u(t)‖²_{H^m} = −2ν‖∇u‖²_{H^m} − 2⟪(u·∇)u, u⟫_{H^m} + 2⟪f, u⟫_{H^m}`,
   with `‖∇u‖_{H^m} = torusGradientNormAt m u t` and `⟪·,·⟫_{H^m}` lane 322's
   `torusRealPairing`.

## What is conditional

`hRhigh_of_pairingBound` takes **one explicit hypothesis**, U12b's tame pairing
estimate `|⟪(u·∇)u, u⟫_{H^m}| ≤ C_m ‖u‖_{H²}‖u‖_{H^m}‖∇u‖_{H^m}` — a theorem
argument, not a `def … : Prop` — and produces `eq:Rhigh` in exactly the binder
lane 322 consumes, instantiating its existential `g` at
`torusGradientNormAt m u t`.  `higherOrderBound_of_pairingBound` composes with
lane 322's Grönwall chain, so `PeriodicContinuationAPI.higherOrderBound` is now
conditional on the pairing bound alone (missing fact B of §3.2).

Non-vacuity: `research/T11/probes/energy_identity_closes.lean` evaluates the
identity at the spatially homogeneous forced solution `u(t,x) = eᵗc`, where the
right-hand side is the strictly positive number `2e^{2t}‖K‖²`.
-/

noncomputable section

namespace NSFormalization.Section3.T11

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NavierStokes.PeriodicIntegration (spatialPartial cubeIntegral Coords toSpace)
open NSFormalization.Section3.T10
open scoped ContDiff ENNReal BigOperators ComplexConjugate Topology

local instance energyIdentityNormedGroup (s : ℝ) : NormedAddCommGroup (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedAddCommGroup

local instance energyIdentityNormedSpace (s : ℝ) : NormedSpace ℝ (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedSpace

/-! ## 1. Elementary coefficient calculus -/

theorem periodicFrequencyWeight_pos (k : PeriodicFrequency) :
    0 < periodicFrequencyWeight k := by
  have h : (0 : ℝ) ≤ 4 * Real.pi ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2 := by positivity
  unfold periodicFrequencyWeight
  linarith

/-- Every torus lift value is a value of the field on the closed unit cube. -/
theorem torusLift_eq_cube_value {E : Type*} (g : Space → E) (z : PeriodicTorus) :
    ∃ y : Coords, y ∈ Icc (0 : Coords) 1 ∧ torusLift g z = g (toSpace y) := by
  refine ⟨(UnitAddTorus.measurableEquivPiIoc (0 : Coords) z).val, ?_, rfl⟩
  have h := (UnitAddTorus.measurableEquivPiIoc (0 : Coords) z).property
  exact ⟨fun i ↦ le_of_lt (by simpa using (h i).1), fun i ↦ by simpa using (h i).2⟩

/-- A cube-uniform bound on a continuous field bounds every Fourier coefficient. -/
theorem norm_periodicFourierCoeff_le_of_cube_bound {g : Space → ℂ} (hg : Continuous g)
    {C : ℝ} (hC : ∀ y ∈ Icc (0 : Coords) 1, ‖g (toSpace y)‖ ≤ C)
    (k : PeriodicFrequency) : ‖periodicFourierCoeff g k‖ ≤ C := by
  refine (norm_periodicFourierCoeff_le g k).trans ?_
  have hint : Integrable (fun z : PeriodicTorus ↦ ‖torusLift g z‖) periodicTorusMeasure :=
    ((NSFormalization.Paper1.memLp_torusLift hg 1).integrable le_rfl).norm
  have hle : ∀ z : PeriodicTorus, ‖torusLift g z‖ ≤ C := by
    intro z
    obtain ⟨y, hy, hz⟩ := torusLift_eq_cube_value g z
    rw [hz]
    exact hC y hy
  calc ∫ z, ‖torusLift g z‖ ∂periodicTorusMeasure
      ≤ ∫ _z : PeriodicTorus, C ∂periodicTorusMeasure :=
        integral_mono hint (integrable_const C) hle
    _ = C := by rw [integral_const]; simp

/-- Fourier coefficients are additive over finite sums of continuous fields. -/
theorem periodicFourierCoeff_finsetSum {ι : Type*} (s : Finset ι) (g : ι → Space → ℂ)
    (hg : ∀ j ∈ s, Continuous (g j)) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ ∑ j ∈ s, g j x) k =
      ∑ j ∈ s, periodicFourierCoeff (g j) k := by
  simp only [periodicFourierCoeff, NSFormalization.Paper1.periodicFourierCoeff_eq_cube,
    Finset.mul_sum, NavierStokes.PeriodicIntegration.cubeIntegral]
  apply integral_finsetSum
  intro j hj
  exact NavierStokes.PeriodicIntegration.integrable_cube
    ((NSFormalization.Paper1.periodicCharacter_smooth (-k)).continuous.mul (hg j hj))

/-- Continuity alone makes a torus lift integrable on the compact torus. -/
theorem integrable_torusLift_of_continuous {g : Space → ℂ} (hg : Continuous g) :
    Integrable (torusLift g) periodicTorusMeasure :=
  (NSFormalization.Paper1.memLp_torusLift hg 1).integrable le_rfl

/-- Fourier coefficients of a difference of continuous real fields. -/
theorem periodicFourierCoeff_sub_real {g h : Space → ℝ} (hg : Continuous g)
    (hh : Continuous h) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ ((g x - h x : ℝ) : ℂ)) k =
      periodicFourierCoeff (fun x ↦ ((g x : ℝ) : ℂ)) k -
        periodicFourierCoeff (fun x ↦ ((h x : ℝ) : ℂ)) k := by
  have hgc : Continuous (fun x ↦ ((g x : ℝ) : ℂ)) := Complex.continuous_ofReal.comp hg
  have hhc : Continuous (fun x ↦ ((h x : ℝ) : ℂ)) := Complex.continuous_ofReal.comp hh
  have := periodicFourierCoeff_sub (f := fun x ↦ ((g x : ℝ) : ℂ))
    (g := fun x ↦ ((h x : ℝ) : ℂ)) (integrable_torusLift_of_continuous hgc)
    (integrable_torusLift_of_continuous hhc) k
  simpa using this

/-- The derivative of the squared modulus of a complex path. -/
theorem hasDerivAt_norm_sq_complex {z : ℝ → ℂ} {z' : ℂ} {r : ℝ} (h : HasDerivAt z z' r) :
    HasDerivAt (fun s ↦ ‖z s‖ ^ 2) (2 * (conj (z r) * z').re) r := by
  have hre : HasDerivAt (fun s ↦ (z s).re) z'.re r :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt r h
  have him : HasDerivAt (fun s ↦ (z s).im) z'.im r :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt r h
  have h2 := (hre.pow 2).add (him.pow 2)
  have hfun : (fun s ↦ ‖z s‖ ^ 2) = fun s ↦ (z s).re ^ 2 + (z s).im ^ 2 := by
    funext s
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [hfun]
  refine h2.congr_deriv ?_
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  push_cast
  ring

/-- Cauchy–Schwarz for one real pairing term. -/
theorem abs_re_conj_mul_le (a b : ℂ) : |(conj a * b).re| ≤ ‖a‖ * ‖b‖ :=
  (Complex.abs_re_le_norm _).trans (by rw [norm_mul, RCLike.norm_conj])

/-! ## 2. The velocity coefficient path and its time derivative -/

/-- The unweighted Fourier coefficient path of one velocity component. -/
def velocityCoeffT (u : SpaceTimeField) (i : Fin 3) (k : PeriodicFrequency) (t : ℝ) : ℂ :=
  periodicFourierCoeff (fun x ↦ ((u (t, x) i : ℝ) : ℂ)) k

/-- The Fourier coefficient of the time derivative of one velocity component. -/
def velocityDerivCoeffT (u : SpaceTimeField) (i : Fin 3) (k : PeriodicFrequency) (t : ℝ) : ℂ :=
  periodicFourierCoeff (fun x ↦ ((temporalDerivative u t x i : ℝ) : ℂ)) k

/-- `(u·∇)u` as a space-time field, so that it carries coefficients and data in
exactly the same vocabulary as the velocity. -/
def convectionFieldT (u : SpaceTimeField) : SpaceTimeField := fun z ↦ advection u z.1 z.2

/-- The Fourier coefficient path of a pressure field. -/
def pressureCoeffT (p : SpaceTimeScalar) (k : PeriodicFrequency) (t : ℝ) : ℂ :=
  periodicFourierCoeff (fun x ↦ ((p (t, x) : ℝ) : ℂ)) k

/-- **Differentiation of the Fourier coefficient integral under the integral sign.**
On an open time domain where the field is jointly smooth, the coefficient path is
differentiable and its derivative is the coefficient of the time derivative. -/
theorem hasDerivAt_velocityCoeffT {u : SpaceTimeField} {I : Set ℝ} (hI : IsOpen I)
    (hu : ContDiffOn ℝ ∞ u (I ×ˢ (univ : Set Space))) {t : ℝ} (ht : t ∈ I)
    (i : Fin 3) (k : PeriodicFrequency) :
    HasDerivAt (velocityCoeffT u i k) (velocityDerivCoeffT u i k t) t := by
  classical
  set e : Space →L[ℝ] ℂ := Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) i) with he
  have hchar : ContDiff ℝ ∞ (fun z : SpaceTime ↦
      NSFormalization.Paper1.periodicCharacter (-k) z.2) :=
    (NSFormalization.Paper1.periodicCharacter_smooth (-k)).comp contDiff_snd
  have hcomp : ContDiffOn ℝ ∞ (fun z : SpaceTime ↦ e (u z)) (I ×ˢ (univ : Set Space)) :=
    e.contDiff.comp_contDiffOn hu
  have hF : ContDiffOn ℝ 1 (fun z : SpaceTime ↦
      NSFormalization.Paper1.periodicCharacter (-k) z.2 * e (u z))
      (I ×ˢ (univ : Set Space)) := (hchar.contDiffOn.mul hcomp).of_le (by simp)
  have hd := NavierStokes.PeriodicIntegration.hasDerivAt_cubeIntegral_of_contDiffOn
    (F := fun z : SpaceTime ↦ NSFormalization.Paper1.periodicCharacter (-k) z.2 * e (u z))
    hI hF ht
  have hslice : ∀ s : ℝ, cubeIntegral (fun x ↦
      NSFormalization.Paper1.periodicCharacter (-k) x * e (u (s, x))) =
      velocityCoeffT u i k s := fun s ↦
    (NSFormalization.Paper1.periodicFourierCoeff_eq_cube _ k).symm
  have hderiv : ∀ x : Space,
      deriv (fun s : ℝ ↦ NSFormalization.Paper1.periodicCharacter (-k) x * e (u (s, x))) t =
        NSFormalization.Paper1.periodicCharacter (-k) x *
          ((temporalDerivative u t x i : ℝ) : ℂ) := by
    intro x
    have hmem : ((t, x) : SpaceTime) ∈ I ×ˢ (univ : Set Space) := ⟨ht, mem_univ x⟩
    have hfd : DifferentiableAt ℝ u (t, x) :=
      (hu.contDiffAt ((hI.prod isOpen_univ).mem_nhds hmem)).differentiableAt (by simp)
    have hdiff : DifferentiableAt ℝ (fun s : ℝ ↦ u (s, x)) t :=
      hfd.comp t ((differentiableAt_id).prodMk (differentiableAt_const x))
    have hu2 : HasDerivAt (fun s : ℝ ↦ e (u (s, x))) (e (temporalDerivative u t x)) t :=
      e.hasFDerivAt.comp_hasDerivAt t hdiff.hasDerivAt
    rw [deriv_const_mul _ hu2.differentiableAt, hu2.deriv]
    rfl
  simp only [hslice] at hd
  have hrw : (fun x : Space ↦
      deriv (fun s : ℝ ↦ NSFormalization.Paper1.periodicCharacter (-k) x * e (u (s, x))) t) =
      fun x : Space ↦ NSFormalization.Paper1.periodicCharacter (-k) x *
        ((temporalDerivative u t x i : ℝ) : ℂ) := funext hderiv
  rw [hrw] at hd
  have heq : velocityDerivCoeffT u i k t =
      cubeIntegral (fun x ↦ NSFormalization.Paper1.periodicCharacter (-k) x *
        ((temporalDerivative u t x i : ℝ) : ℂ)) :=
    NSFormalization.Paper1.periodicFourierCoeff_eq_cube _ k
  rw [heq]
  exact hd

/-- One uniform bound for the time derivative over a compact time window. -/
theorem exists_temporalDerivative_cube_bound {u : SpaceTimeField} {I : Set ℝ} (hI : IsOpen I)
    (hu : ContDiffOn ℝ ∞ u (I ×ˢ (univ : Set Space))) {J : Set ℝ} (hJ : IsCompact J)
    (hJI : J ⊆ I) :
    ∃ C : ℝ, ∀ r ∈ J, ∀ y ∈ Icc (0 : Coords) 1,
      ‖temporalDerivative u r (toSpace y)‖ ≤ C := by
  have hopen : IsOpen (I ×ˢ (univ : Set Space)) := hI.prod isOpen_univ
  have hcont : ContinuousOn (fun z : SpaceTime ↦ temporalDerivative u z.1 z.2)
      (I ×ˢ (univ : Set Space)) :=
    (NavierStokes.ResidualRegularity.contDiffOn_temporalDerivative hopen hu).continuousOn
  have hK : IsCompact (J ×ˢ (toSpace '' (Icc (0 : Coords) 1))) :=
    hJ.prod (isCompact_Icc.image toSpace.continuous)
  have hsub : J ×ˢ (toSpace '' (Icc (0 : Coords) 1)) ⊆ I ×ˢ (univ : Set Space) :=
    fun z hz ↦ ⟨hJI hz.1, mem_univ _⟩
  obtain ⟨C, hCb⟩ := hK.exists_bound_of_continuousOn (hcont.mono hsub)
  exact ⟨C, fun r hr y hy ↦ hCb (r, toSpace y) ⟨hr, ⟨y, hy, rfl⟩⟩⟩

/-- **One uniform bound for every time-derivative coefficient** over a compact
time window inside the open smoothness domain. -/
theorem exists_velocityDerivCoeffT_bound {u : SpaceTimeField} {I : Set ℝ} (hI : IsOpen I)
    (hu : ContDiffOn ℝ ∞ u (I ×ˢ (univ : Set Space))) {J : Set ℝ} (hJ : IsCompact J)
    (hJI : J ⊆ I) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ r ∈ J, ∀ (i : Fin 3) (k : PeriodicFrequency),
      ‖velocityDerivCoeffT u i k r‖ ≤ D := by
  obtain ⟨C, hC⟩ := exists_temporalDerivative_cube_bound hI hu hJ hJI
  have hopen : IsOpen (I ×ˢ (univ : Set Space)) := hI.prod isOpen_univ
  have hslab := NavierStokes.ResidualRegularity.contDiffOn_temporalDerivative hopen hu
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro r hr i k
  have hsmooth : ContDiff ℝ ∞ (fun x : Space ↦ temporalDerivative u r x) :=
    hslab.comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun x ↦ ⟨hJI hr, mem_univ x⟩)
  have hcont : Continuous (fun x : Space ↦ ((temporalDerivative u r x i : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) i).comp hsmooth.continuous)
  refine norm_periodicFourierCoeff_le_of_cube_bound hcont (fun y hy ↦ ?_) k
  have h1 : ‖((temporalDerivative u r (toSpace y) i : ℝ) : ℂ)‖ ≤
      ‖temporalDerivative u r (toSpace y)‖ := by
    simpa using PiLp.norm_apply_le (temporalDerivative u r (toSpace y)) i
  exact h1.trans ((hC r hr y hy).trans (le_max_left _ _))

/-! ## 3. Frequency energies and vector Parseval -/

/-- The order-`s` energy of one frequency of a velocity slice. -/
def freqEnergyT (s : ℝ) (u : SpaceTimeField) (k : PeriodicFrequency) (t : ℝ) : ℝ :=
  periodicFrequencyWeight k ^ s * ∑ i : Fin 3, ‖velocityCoeffT u i k t‖ ^ 2

/-- The time derivative of `freqEnergyT`. -/
def freqEnergyDerivT (s : ℝ) (u : SpaceTimeField) (k : PeriodicFrequency) (t : ℝ) : ℝ :=
  periodicFrequencyWeight k ^ s *
    ∑ i : Fin 3, 2 * (conj (velocityCoeffT u i k t) * velocityDerivCoeffT u i k t).re

theorem freqEnergyT_nonneg (s : ℝ) (u : SpaceTimeField) (k : PeriodicFrequency) (t : ℝ) :
    0 ≤ freqEnergyT s u k t :=
  mul_nonneg (Real.rpow_nonneg (periodicFrequencyWeight_pos k).le _)
    (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

/-- The weighted datum entry in terms of the raw coefficient. -/
theorem datum_norm_sq_entry {s : ℝ} {z : SpatialField} {A : PeriodicSobolev s}
    (hA : IsPeriodicDatum s z A) (i : Fin 3) (k : PeriodicFrequency) :
    ‖A.1 i k‖ ^ 2 = periodicFrequencyWeight k ^ s *
      ‖periodicFourierCoeff (fun x ↦ ((z x i : ℝ) : ℂ)) k‖ ^ 2 := by
  have hw := periodicFrequencyWeight_pos k
  rw [hA.2.2 i k, norm_smul, mul_pow, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hw.le _)]
  congr 1
  rw [← Real.rpow_natCast (periodicFrequencyWeight k ^ (s / 2)) 2, ← Real.rpow_mul hw.le]
  norm_num

/-- **Vector Parseval**, in the form the energy identity differentiates. -/
theorem hasSum_freqEnergyT {s : ℝ} {u : SpaceTimeField} {t : ℝ} {A : PeriodicSobolev s}
    (hA : IsPeriodicDatum s (fun x ↦ u (t, x)) A) :
    HasSum (fun k ↦ freqEnergyT s u k t) (‖A‖ ^ 2) := by
  have hcomp : ∀ i : Fin 3, HasSum (fun k ↦ ‖A.1 i k‖ ^ 2) (‖A.1 i‖ ^ 2) := by
    intro i
    have h := lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (A.1 i)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  have hsum : HasSum (fun k ↦ ∑ i : Fin 3, ‖A.1 i k‖ ^ 2) (∑ i : Fin 3, ‖A.1 i‖ ^ 2) :=
    hasSum_sum fun i _ ↦ hcomp i
  have hnorm : ‖A‖ ^ 2 = ∑ i : Fin 3, ‖A.1 i‖ ^ 2 := by
    change ‖A.1‖ ^ 2 = _
    exact PiLp.norm_sq_eq_of_L2 _ _
  rw [hnorm]
  refine hsum.congr_fun fun k ↦ ?_
  rw [freqEnergyT, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ (datum_norm_sq_entry hA i k).symm

theorem torusSobolevNormAt_sq_eq_tsum {s : ℝ} {u : SpaceTimeField} {t : ℝ}
    {A : PeriodicSobolev s} (hA : IsPeriodicDatum s (fun x ↦ u (t, x)) A) :
    torusSobolevNormAt s u t ^ 2 = ∑' k, freqEnergyT s u k t := by
  rw [torusSobolevNormAt_eq hA, (hasSum_freqEnergyT hA).tsum_eq]

/-- The coefficient decay supplied by a datum. -/
theorem norm_velocityCoeffT_le {s : ℝ} {u : SpaceTimeField} {t : ℝ}
    {A : PeriodicSobolev s} (hA : IsPeriodicDatum s (fun x ↦ u (t, x)) A)
    (i : Fin 3) (k : PeriodicFrequency) :
    periodicFrequencyWeight k ^ (s / 2) * ‖velocityCoeffT u i k t‖ ≤ ‖A‖ := by
  have hw := periodicFrequencyWeight_pos k
  have hentry : ‖A.1 i k‖ =
      periodicFrequencyWeight k ^ (s / 2) * ‖velocityCoeffT u i k t‖ := by
    rw [hA.2.2 i k, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hw.le _)]
    rfl
  rw [← hentry]
  exact norm_coeff_le_norm A i k

/-! ## 4. Termwise differentiation of the energy series -/

theorem hasDerivAt_freqEnergyT {u : SpaceTimeField} {I : Set ℝ} (hI : IsOpen I)
    (hu : ContDiffOn ℝ ∞ u (I ×ˢ (univ : Set Space))) {t : ℝ} (ht : t ∈ I) (s : ℝ)
    (k : PeriodicFrequency) :
    HasDerivAt (freqEnergyT s u k) (freqEnergyDerivT s u k t) t := by
  have h : HasDerivAt (fun r ↦ ∑ i : Fin 3, ‖velocityCoeffT u i k r‖ ^ 2)
      (∑ i : Fin 3,
        2 * (conj (velocityCoeffT u i k t) * velocityDerivCoeffT u i k t).re) t :=
    HasDerivAt.fun_sum fun i _ ↦
      hasDerivAt_norm_sq_complex (hasDerivAt_velocityCoeffT hI hu ht i k)
  exact h.const_mul _

/-- **The domination bound.**  A datum two orders above `2m` and a uniform bound
on the time-derivative coefficients dominate the differentiated series by a
summable multiple of `(1+4π²|k|²)⁻²`. -/
theorem abs_freqEnergyDerivT_le {u : SpaceTimeField} {m : ℕ} {r : ℝ}
    {A : PeriodicSobolev ((2 * m + 4 : ℕ) : ℝ)}
    (hA : IsPeriodicDatum ((2 * m + 4 : ℕ) : ℝ) (fun x ↦ u (r, x)) A)
    {M D : ℝ} (hM : ‖A‖ ≤ M)
    (hD : ∀ (i : Fin 3) (k : PeriodicFrequency), ‖velocityDerivCoeffT u i k r‖ ≤ D)
    (k : PeriodicFrequency) :
    |freqEnergyDerivT (m : ℝ) u k r| ≤
      6 * M * D * (periodicFrequencyWeight k ^ 2)⁻¹ := by
  have hw := periodicFrequencyWeight_pos k
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) hM
  have hpos : 0 < periodicFrequencyWeight k ^ ((m : ℝ) + 2) := Real.rpow_pos_of_pos hw _
  have hhalf : ((2 * m + 4 : ℕ) : ℝ) / 2 = (m : ℝ) + 2 := by push_cast; ring
  have hcoeff : ∀ i : Fin 3, ‖velocityCoeffT u i k r‖ ≤
      M * (periodicFrequencyWeight k ^ ((m : ℝ) + 2))⁻¹ := by
    intro i
    have h := norm_velocityCoeffT_le hA i k
    rw [hhalf] at h
    have h' : ‖velocityCoeffT u i k r‖ * periodicFrequencyWeight k ^ ((m : ℝ) + 2) ≤ M := by
      rw [mul_comm]; exact h.trans hM
    rw [← le_div_iff₀ hpos] at h'
    rwa [div_eq_mul_inv] at h'
  have hterm : ∀ i : Fin 3,
      |2 * (conj (velocityCoeffT u i k r) * velocityDerivCoeffT u i k r).re| ≤
        2 * (M * (periodicFrequencyWeight k ^ ((m : ℝ) + 2))⁻¹) * D := by
    intro i
    rw [abs_mul, abs_two, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine (abs_re_conj_mul_le _ _).trans ?_
    exact mul_le_mul (hcoeff i) (hD i k) (norm_nonneg _)
      (mul_nonneg hM0 (le_of_lt (inv_pos.mpr hpos)))
  have hkey : periodicFrequencyWeight k ^ (m : ℝ) *
      (periodicFrequencyWeight k ^ ((m : ℝ) + 2))⁻¹ =
      (periodicFrequencyWeight k ^ 2)⁻¹ := by
    have h1 : (periodicFrequencyWeight k ^ ((m : ℝ) + 2))⁻¹ =
        periodicFrequencyWeight k ^ (-((m : ℝ) + 2)) := (Real.rpow_neg hw.le _).symm
    rw [h1, ← Real.rpow_add hw]
    have h2 : (m : ℝ) + -((m : ℝ) + 2) = -(2 : ℝ) := by ring
    rw [h2, Real.rpow_neg hw.le, Real.rpow_two]
  calc |freqEnergyDerivT (m : ℝ) u k r|
      = periodicFrequencyWeight k ^ (m : ℝ) *
          |∑ i : Fin 3,
            2 * (conj (velocityCoeffT u i k r) * velocityDerivCoeffT u i k r).re| := by
        rw [freqEnergyDerivT, abs_mul,
          abs_of_nonneg (Real.rpow_nonneg hw.le _)]
    _ ≤ periodicFrequencyWeight k ^ (m : ℝ) *
          ∑ i : Fin 3,
            2 * (M * (periodicFrequencyWeight k ^ ((m : ℝ) + 2))⁻¹) * D := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hw.le _)
        exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ ↦ hterm i)
    _ = 6 * M * D * (periodicFrequencyWeight k ^ (m : ℝ) *
          (periodicFrequencyWeight k ^ ((m : ℝ) + 2))⁻¹) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
    _ = 6 * M * D * (periodicFrequencyWeight k ^ 2)⁻¹ := by rw [hkey]

/-- **The `H^m` energy profile is differentiable at every interior time**, with
derivative the sum of the differentiated Fourier series. -/
theorem hasDerivAt_torusSobolevNormAt_sq {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) (m : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun r ↦ torusSobolevNormAt (m : ℝ) w.velocity r ^ 2)
      (∑' k, freqEnergyDerivT (m : ℝ) w.velocity k t) t := by
  classical
  have hI : IsOpen (Ioo (0 : ℝ) T) := isOpen_Ioo
  have hu : ContDiffOn ℝ ∞ w.velocity (Ioo (0 : ℝ) T ×ˢ (univ : Set Space)) :=
    w.velocity_smooth.mono (Set.prod_mono Ioo_subset_Ico_self Subset.rfl)
  obtain ⟨ht0, htT⟩ := ht
  set α : ℝ := t / 2 with hαdef
  set β : ℝ := (t + T) / 2 with hβdef
  have hα0 : 0 < α := by rw [hαdef]; linarith
  have hαt : α < t := by rw [hαdef]; linarith
  have htβ : t < β := by rw [hβdef]; linarith
  have hβT : β < T := by rw [hβdef]; linarith
  have hJI : Icc α β ⊆ Ioo (0 : ℝ) T := fun x hx ↦
    ⟨lt_of_lt_of_le hα0 hx.1, lt_of_le_of_lt hx.2 hβT⟩
  have hSJ : Ioo α β ⊆ Icc α β := Ioo_subset_Icc_self
  have hSI : Ioo α β ⊆ Ioo (0 : ℝ) T := hSJ.trans hJI
  have htS : t ∈ Ioo α β := ⟨hαt, htβ⟩
  obtain ⟨D, hD0, hD⟩ := exists_velocityDerivCoeffT_bound hI hu isCompact_Icc hJI
  obtain ⟨G, hGc, hGd⟩ := w.sobolev (2 * m + 4)
  have hGsub : Icc α β ⊆ Ico (0 : ℝ) T := fun x hx ↦
    ⟨le_of_lt (lt_of_lt_of_le hα0 hx.1), lt_of_le_of_lt hx.2 hβT⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hGc.mono hGsub)
  have hsummable : Summable fun k : PeriodicFrequency ↦
      6 * M * D * (periodicFrequencyWeight k ^ 2)⁻¹ :=
    summable_inverse_periodicFrequencyWeight.mul_left _
  obtain ⟨Gm, _, hGmd⟩ := w.sobolev m
  have hg0 : Summable fun k ↦ freqEnergyT (m : ℝ) w.velocity k t :=
    (hasSum_freqEnergyT (hGmd t ⟨le_of_lt ht0, htT⟩)).summable
  have hmain := hasDerivAt_tsum_of_isPreconnected (u := fun k : PeriodicFrequency ↦
      6 * M * D * (periodicFrequencyWeight k ^ 2)⁻¹)
    (g := fun k ↦ freqEnergyT (m : ℝ) w.velocity k)
    (g' := fun k r ↦ freqEnergyDerivT (m : ℝ) w.velocity k r)
    hsummable isOpen_Ioo isPreconnected_Ioo
    (fun k r hr ↦ hasDerivAt_freqEnergyT hI hu (hSI hr) (m : ℝ) k)
    (fun k r hr ↦ by
      rw [Real.norm_eq_abs]
      exact abs_freqEnergyDerivT_le (hGd r (hGsub (hSJ hr))) (hM r (hSJ hr))
        (fun i k' ↦ hD r (hSJ hr) i k') k)
    htS hg0 htS
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_Ioo (a := α) (b := β)).mem_nhds htS] with r hr
  exact torusSobolevNormAt_sq_eq_tsum (hGmd r ⟨le_of_lt (lt_trans hα0 hr.1), lt_trans hr.2 hβT⟩)

/-! ## 5. The coefficient form of the momentum equation -/

theorem classical_velocity_slice_contDiff {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    ContDiff ℝ ∞ (fun x : Space ↦ w.velocity (t, x)) :=
  w.velocity_smooth.comp_contDiff (contDiff_const.prodMk contDiff_id)
    (fun x ↦ ⟨ht, mem_univ x⟩)

theorem classical_pressure_slice_contDiff {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    ContDiff ℝ ∞ (fun x : Space ↦ w.pressure (t, x)) :=
  w.pressure_smooth.comp_contDiff (contDiff_const.prodMk contDiff_id)
    (fun x ↦ ⟨ht, mem_univ x⟩)

theorem advection_spatial_contDiff {v : SpaceTimeField} {t : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : Space ↦ v (t, x))) :
    ContDiff ℝ ∞ (fun x ↦ advection v t x) :=
  (hv.fderiv_right (by simp)).clm_apply hv

theorem advection_spatial_periodic {v : SpaceTimeField} {t : ℝ}
    (hp : IsPeriodicSpatial (fun x : Space ↦ v (t, x))) :
    IsPeriodicSpatial (fun x ↦ advection v t x) := by
  intro x l
  show (fderiv ℝ (fun y : Space ↦ v (t, y)) (x + coordinateVector l))
      (v (t, x + coordinateVector l)) =
    (fderiv ℝ (fun y : Space ↦ v (t, y)) x) (v (t, x))
  have h1 : v (t, x + coordinateVector l) = v (t, x) := hp x l
  rw [h1, NavierStokes.PeriodicUniqueness.periodic_fderiv (fun y q ↦ hp y q) x l]

/-- The Fourier coefficient of a component of the pressure gradient. -/
theorem periodicFourierCoeff_pressureGradient {p : SpaceTimeScalar} {t : ℝ}
    (hp : ContDiff ℝ ∞ (fun y : Space ↦ p (t, y)))
    (hpp : IsPeriodicSpatial (fun y : Space ↦ p (t, y))) (i : Fin 3) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ ((pressureGradient p t x i : ℝ) : ℂ)) k =
      periodicDerivativeSymbol i k *
        periodicFourierCoeff (fun x ↦ ((p (t, x) : ℝ) : ℂ)) k := by
  have hc : ContDiff ℝ ∞ (fun y : Space ↦ ((p (t, y) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hp
  have hcp : IsPeriodicSpatial (fun y : Space ↦ ((p (t, y) : ℝ) : ℂ)) :=
    fun y l ↦ congrArg (fun r : ℝ ↦ (r : ℂ)) (hpp y l)
  have hrw : (fun x : Space ↦ ((pressureGradient p t x i : ℝ) : ℂ)) =
      fun x : Space ↦
        fderiv ℝ (fun y : Space ↦ ((p (t, y) : ℝ) : ℂ)) x (coordinateVector i) := by
    funext x
    rw [pressureGradient_component]
    exact (congrFun (spatialPartial_complexify (hp.of_le (by norm_num)) i) x).symm
  rw [hrw]
  exact periodicFourierCoeff_fderiv hcp (hc.of_le (by simp)) i k

/-- **The momentum equation, coefficient by coefficient.**  Differentiating the
Fourier coefficient integral of a genuine classical solution and inserting the
pointwise equation gives the scalar forced linear ODE at every frequency. -/
theorem velocityDerivCoeffT_momentum {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) (hf : ContDiff ℝ ∞ f) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    (i : Fin 3) (k : PeriodicFrequency) :
    velocityDerivCoeffT w.velocity i k t =
      ((-(ν * periodicAngularFrequencySq k) : ℝ) : ℂ) * velocityCoeffT w.velocity i k t +
        (velocityCoeffT f i k t - velocityCoeffT (convectionFieldT w.velocity) i k t) -
        periodicDerivativeSymbol i k * pressureCoeffT w.pressure k t := by
  simp only [velocityCoeffT, convectionFieldT, pressureCoeffT]
  have htI : t ∈ Ico (0 : ℝ) T := ⟨le_of_lt ht.1, ht.2⟩
  have hv : ContDiff ℝ ∞ (fun x : Space ↦ w.velocity (t, x)) :=
    classical_velocity_slice_contDiff w htI
  have hvp : IsPeriodicSpatial (fun x : Space ↦ w.velocity (t, x)) := w.velocity_periodic t htI
  have hpr : ContDiff ℝ ∞ (fun x : Space ↦ w.pressure (t, x)) :=
    classical_pressure_slice_contDiff w htI
  have hprp : IsPeriodicSpatial (fun x : Space ↦ w.pressure (t, x)) := w.pressure_periodic t htI
  -- the four continuous real fields appearing in the equation
  have hcf : Continuous (fun x : Space ↦ f (t, x) i) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) i).comp
      (hf.continuous.comp (continuous_const.prodMk continuous_id))
  have hcadv : Continuous (fun x : Space ↦ advection w.velocity t x i) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) i).comp
      (advection_spatial_contDiff hv).continuous
  have hclap : Continuous (fun x : Space ↦ ν * spatialLaplacian w.velocity t x i) :=
    continuous_const.mul (spatialLaplacian_component_contDiff hv i).continuous
  have hcgrad : Continuous (fun x : Space ↦ pressureGradient w.pressure t x i) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) i).comp
      (pressureGradient_continuous hpr)
  -- the pointwise equation, component `i`
  have hpt : ∀ x : Space, temporalDerivative w.velocity t x i =
      (f (t, x) i - advection w.velocity t x i) -
        (pressureGradient w.pressure t x i - ν * spatialLaplacian w.velocity t x i) := by
    intro x
    have h := congrArg (fun z : Space ↦ z i) (w.momentum t ht x)
    simp only [NavierStokesR3.ProblemStatement.navierStokesResidual] at h
    have h' : temporalDerivative w.velocity t x i + advection w.velocity t x i -
        ν * spatialLaplacian w.velocity t x i + pressureGradient w.pressure t x i =
        f (t, x) i := by
      simpa using h
    linarith
  rw [velocityDerivCoeffT]
  rw [show (fun x : Space ↦ ((temporalDerivative w.velocity t x i : ℝ) : ℂ)) =
      fun x : Space ↦ (((f (t, x) i - advection w.velocity t x i) -
        (pressureGradient w.pressure t x i - ν * spatialLaplacian w.velocity t x i) : ℝ) : ℂ) from
    funext fun x ↦ congrArg (fun r : ℝ ↦ (r : ℂ)) (hpt x)]
  rw [periodicFourierCoeff_sub_real
      (g := fun x : Space ↦ f (t, x) i - advection w.velocity t x i)
      (h := fun x : Space ↦
        pressureGradient w.pressure t x i - ν * spatialLaplacian w.velocity t x i)
      (hcf.sub hcadv) (hcgrad.sub hclap) k,
    periodicFourierCoeff_sub_real (g := fun x : Space ↦ f (t, x) i)
      (h := fun x : Space ↦ advection w.velocity t x i) hcf hcadv k,
    periodicFourierCoeff_sub_real (g := fun x : Space ↦ pressureGradient w.pressure t x i)
      (h := fun x : Space ↦ ν * spatialLaplacian w.velocity t x i) hcgrad hclap k,
    periodicFourierCoeff_pressureGradient hpr hprp i k]
  have hlapc : periodicFourierCoeff (fun x ↦ ((ν * spatialLaplacian w.velocity t x i : ℝ) : ℂ)) k =
      ((-(ν * periodicAngularFrequencySq k) : ℝ) : ℂ) *
        periodicFourierCoeff (fun x ↦ ((w.velocity (t, x) i : ℝ) : ℂ)) k := by
    have hstep : (fun x : Space ↦ ((ν * spatialLaplacian w.velocity t x i : ℝ) : ℂ)) =
        fun x : Space ↦ (ν : ℂ) * ((spatialLaplacian w.velocity t x i : ℝ) : ℂ) := by
      funext x; push_cast; ring
    rw [hstep, periodicFourierCoeff_const_mul,
      periodicFourierCoeff_spatialLaplacian hv hvp i k]
    push_cast
    ring
  rw [hlapc]
  ring

/-! ## 6. Solenoidality and the pressure drop at the raw coefficients -/

/-- **Coefficient-side solenoidality of a classical velocity slice.** -/
theorem solenoidal_velocityCoeffT {u : SpaceTimeField} {t : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : Space ↦ u (t, x)))
    (hvp : IsPeriodicSpatial (fun x : Space ↦ u (t, x)))
    (hdiv : ∀ x : Space, spatialDivergence u t x = 0) (k : PeriodicFrequency) :
    ∑ j : Fin 3, periodicDerivativeSymbol j k * velocityCoeffT u j k t = 0 := by
  have hcj : ∀ j : Fin 3, ContDiff ℝ ∞ (fun y : Space ↦ u (t, y) j) := fun j ↦
    (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hv
  have hcpj : ∀ j : Fin 3, IsPeriodicSpatial (fun y : Space ↦ ((u (t, y) j : ℝ) : ℂ)) :=
    fun j y l ↦ congrArg (fun z : Space ↦ ((z j : ℝ) : ℂ)) (hvp y l)
  have hzero : (fun x : Space ↦ ((spatialDivergence u t x : ℝ) : ℂ)) =
      fun x : Space ↦ ∑ j : Fin 3,
        fderiv ℝ (fun y : Space ↦ ((u (t, y) j : ℝ) : ℂ)) x (coordinateVector j) := by
    funext x
    rw [spatialDivergence_eq_sum hv x, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    exact (congrFun (spatialPartial_complexify ((hcj j).of_le (by norm_num)) j) x).symm
  have hlhs : periodicFourierCoeff (fun x : Space ↦ ((spatialDivergence u t x : ℝ) : ℂ)) k = 0 := by
    rw [show (fun x : Space ↦ ((spatialDivergence u t x : ℝ) : ℂ)) = fun _ : Space ↦ (0 : ℂ) from
      funext fun x ↦ by rw [hdiv x]; norm_num]
    rw [periodicFourierCoeff_const]
    simp
  rw [hzero] at hlhs
  rw [periodicFourierCoeff_finsetSum Finset.univ
      (fun j x ↦ fderiv ℝ (fun y : Space ↦ ((u (t, y) j : ℝ) : ℂ)) x (coordinateVector j))
      (fun j _ ↦ NavierStokes.PeriodicIntegration.continuous_partial
        ((Complex.ofRealCLM.contDiff.comp (hcj j)).of_le (by norm_num)) j) k] at hlhs
  rw [← hlhs]
  exact Finset.sum_congr rfl fun j _ ↦
    (periodicFourierCoeff_fderiv (hcpj j)
      ((Complex.ofRealCLM.contDiff.comp (hcj j)).of_le (by simp)) j k).symm

/-- **The pressure term drops, frequency by frequency, at the raw coefficients.**
The datum-level statement is `HighOrder.torusPressureSymbol_drop`; the same three
lines work without a weight. -/
theorem torusPressureSymbol_drop_raw {c : Fin 3 → ℂ} {k : PeriodicFrequency}
    (hc : ∑ j : Fin 3, periodicDerivativeSymbol j k * c j = 0) (q : ℂ) :
    ∑ i : Fin 3, conj (c i) * (periodicDerivativeSymbol i k * q) = 0 := by
  have hconj : ∀ j : Fin 3,
      conj (periodicDerivativeSymbol j k) = -periodicDerivativeSymbol j k :=
    fun j ↦ periodicDerivativeSymbol_conj j k
  have hcc : ∑ j : Fin 3, periodicDerivativeSymbol j k * conj (c j) = 0 := by
    have h0 : conj (∑ j : Fin 3, periodicDerivativeSymbol j k * c j) = 0 := by
      rw [hc, map_zero]
    rw [map_sum] at h0
    have h1 : ∑ j : Fin 3, conj (periodicDerivativeSymbol j k * c j) =
        -∑ j : Fin 3, periodicDerivativeSymbol j k * conj (c j) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [map_mul, hconj j]
      ring
    rw [h1] at h0
    exact neg_eq_zero.mp h0
  calc ∑ i : Fin 3, conj (c i) * (periodicDerivativeSymbol i k * q)
      = q * ∑ i : Fin 3, periodicDerivativeSymbol i k * conj (c i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
    _ = 0 := by rw [hcc, mul_zero]

/-! ### 6a. The projected (Leray) form of the coefficient equation

`lerayAt` (`MildMomentum.lean:346`) is `T10.Leray`'s `periodicLeray` symbol read
on a bare vector of three coefficients at one frequency; the identification is
the `rfl` lemma `periodicLeray_eq_lerayAt` (`MildMomentum.lean:350`), exhibited
in the probe.  The two facts below are its raw-coefficient fixed-point and
annihilation properties, matching `T10.Leray.periodicLeray_of_solenoidal`. -/

/-- A solenoidal raw coefficient vector is fixed by the periodic Leray symbol.
Raw-coefficient form of `T10.Leray.periodicLeray_of_solenoidal`. -/
theorem lerayAt_of_solenoidal {c : Fin 3 → ℂ} {k : PeriodicFrequency}
    (hc : ∑ j : Fin 3, periodicDerivativeSymbol j k * c j = 0) (i : Fin 3) :
    lerayAt k c i = c i := by
  have hconst : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have heq : (∑ j : Fin 3, periodicDerivativeSymbol j k * c j) =
      (2 * Real.pi * Complex.I : ℂ) * ∑ j : Fin 3, (k j : ℂ) * c j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [periodicDerivativeSymbol]
    ring
  rw [heq] at hc
  have hdot : ∑ j : Fin 3, (k j : ℂ) * c j = 0 := (mul_eq_zero.mp hc).resolve_left hconst
  unfold lerayAt
  split_ifs with hk
  · rfl
  · rw [hdot, mul_zero, sub_zero]

/-- **The periodic Leray symbol annihilates a gradient.**  A datum with scalar
symbol `q`, i.e. `2πikᵢ q`, is projected to zero at every frequency. -/
theorem lerayAt_gradient (k : PeriodicFrequency) (q : ℂ) (i : Fin 3) :
    lerayAt k (fun j ↦ periodicDerivativeSymbol j k * q) i = 0 := by
  unfold lerayAt
  split_ifs with hk
  · rw [hk]
    simp [periodicDerivativeSymbol]
  · have hD : ((∑ j : Fin 3, (k j : ℝ) ^ 2 : ℝ) : ℂ) ≠ 0 := by
      have h1 : (1 : ℝ) ≤ ∑ j : Fin 3, (k j : ℝ) ^ 2 := mildPressure_one_le_sq_sum hk
      exact Complex.ofReal_ne_zero.mpr (by linarith)
    have hsum : (∑ j : Fin 3, (k j : ℂ) * (periodicDerivativeSymbol j k * q)) =
        ((2 * Real.pi * Complex.I : ℂ) * q) * ((∑ j : Fin 3, (k j : ℝ) ^ 2 : ℝ) : ℂ) := by
      simp only [periodicDerivativeSymbol]
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    have hcancel : ((k i : ℂ) / ((∑ j : Fin 3, (k j : ℝ) ^ 2 : ℝ) : ℂ)) *
        (((2 * Real.pi * Complex.I : ℂ) * q) * ((∑ j : Fin 3, (k j : ℝ) ^ 2 : ℝ) : ℂ)) =
        periodicDerivativeSymbol i k * q := by
      simp only [periodicDerivativeSymbol]
      field_simp
    rw [hsum, hcancel, sub_self]

/-- **The time derivative of the coefficient path is solenoidal.**  The
coefficient-side divergence is identically zero on the open lifespan, so its time
derivative vanishes at every interior time. -/
theorem solenoidal_velocityDerivCoeffT {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (k : PeriodicFrequency) :
    ∑ j : Fin 3, periodicDerivativeSymbol j k * velocityDerivCoeffT w.velocity j k t = 0 := by
  have hI : IsOpen (Ioo (0 : ℝ) T) := isOpen_Ioo
  have hu : ContDiffOn ℝ ∞ w.velocity (Ioo (0 : ℝ) T ×ˢ (univ : Set Space)) :=
    w.velocity_smooth.mono (Set.prod_mono Ioo_subset_Ico_self Subset.rfl)
  have hd : HasDerivAt
      (fun r ↦ ∑ j : Fin 3, periodicDerivativeSymbol j k * velocityCoeffT w.velocity j k r)
      (∑ j : Fin 3, periodicDerivativeSymbol j k * velocityDerivCoeffT w.velocity j k t) t :=
    HasDerivAt.fun_sum fun j _ ↦ (hasDerivAt_velocityCoeffT hI hu ht j k).const_mul _
  have hz : HasDerivAt
      (fun r ↦ ∑ j : Fin 3, periodicDerivativeSymbol j k * velocityCoeffT w.velocity j k r)
      0 t := by
    refine (hasDerivAt_const t (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [hI.mem_nhds ht] with r hr
    have hrI : r ∈ Ico (0 : ℝ) T := ⟨le_of_lt hr.1, hr.2⟩
    exact solenoidal_velocityCoeffT (classical_velocity_slice_contDiff w hrI)
      (w.velocity_periodic r hrI) (w.divergence r hrI) k
  exact hd.unique hz

/-- **The momentum equation in the projected (Leray) form**, as the brief states
it: `d/dt û(t)(k) = −ν·4π²|k|²·û(t)(k) + (P̂(f̂(t) − Q̂(t)))(k)` with
`Q = (u·∇)u = convectionFieldT u` and `P̂` the periodic Leray symbol at `k`
(`T10.periodicLeray`, read on raw coefficients through `periodicLeray_eq_lerayAt`).

The pressure-explicit `velocityDerivCoeffT_momentum` is the auxiliary form.
Applying `P̂` to it: `d/dt û` is solenoidal (`solenoidal_velocityDerivCoeffT`) so
`P̂` fixes it, `û` is solenoidal so `P̂` fixes it, and the pressure gradient
`2πikᵢp̂(k)` is annihilated (`lerayAt_gradient`). -/
theorem velocityDerivCoeffT_momentum_projected {ν T : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (w : ClassicalSolutionT ν a f T) (hf : ContDiff ℝ ∞ f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (i : Fin 3) (k : PeriodicFrequency) :
    velocityDerivCoeffT w.velocity i k t =
      ((-(ν * periodicAngularFrequencySq k) : ℝ) : ℂ) * velocityCoeffT w.velocity i k t +
        lerayAt k (fun j ↦ velocityCoeffT f j k t -
          velocityCoeffT (convectionFieldT w.velocity) j k t) i := by
  have htI : t ∈ Ico (0 : ℝ) T := ⟨le_of_lt ht.1, ht.2⟩
  have hsolu : ∑ j : Fin 3, periodicDerivativeSymbol j k * velocityCoeffT w.velocity j k t = 0 :=
    solenoidal_velocityCoeffT (classical_velocity_slice_contDiff w htI)
      (w.velocity_periodic t htI) (w.divergence t htI) k
  have hsold := solenoidal_velocityDerivCoeffT w ht k
  have hvec : (fun j ↦ velocityDerivCoeffT w.velocity j k t) =
      fun j ↦ (((-(ν * periodicAngularFrequencySq k) : ℝ) : ℂ) *
            velocityCoeffT w.velocity j k t) -
        ((periodicDerivativeSymbol j k * pressureCoeffT w.pressure k t) -
          (velocityCoeffT f j k t - velocityCoeffT (convectionFieldT w.velocity) j k t)) := by
    funext j
    rw [velocityDerivCoeffT_momentum w hf ht j k]
    ring
  calc velocityDerivCoeffT w.velocity i k t
      = lerayAt k (fun j ↦ velocityDerivCoeffT w.velocity j k t) i :=
        (lerayAt_of_solenoidal hsold i).symm
    _ = lerayAt k (fun j ↦ (((-(ν * periodicAngularFrequencySq k) : ℝ) : ℂ) *
              velocityCoeffT w.velocity j k t) -
            ((periodicDerivativeSymbol j k * pressureCoeffT w.pressure k t) -
              (velocityCoeffT f j k t -
                velocityCoeffT (convectionFieldT w.velocity) j k t))) i := by
        rw [hvec]
    _ = lerayAt k (fun j ↦ ((-(ν * periodicAngularFrequencySq k) : ℝ) : ℂ) *
            velocityCoeffT w.velocity j k t) i -
          lerayAt k (fun j ↦ (periodicDerivativeSymbol j k * pressureCoeffT w.pressure k t) -
            (velocityCoeffT f j k t -
              velocityCoeffT (convectionFieldT w.velocity) j k t)) i :=
        lerayAt_sub k _ _ i
    _ = ((-(ν * periodicAngularFrequencySq k) : ℝ) : ℂ) *
            lerayAt k (fun j ↦ velocityCoeffT w.velocity j k t) i -
          (lerayAt k (fun j ↦ periodicDerivativeSymbol j k * pressureCoeffT w.pressure k t) i -
            lerayAt k (fun j ↦ velocityCoeffT f j k t -
              velocityCoeffT (convectionFieldT w.velocity) j k t) i) := by
        rw [lerayAt_const_mul, lerayAt_sub]
    _ = ((-(ν * periodicAngularFrequencySq k) : ℝ) : ℂ) * velocityCoeffT w.velocity i k t +
          lerayAt k (fun j ↦ velocityCoeffT f j k t -
            velocityCoeffT (convectionFieldT w.velocity) j k t) i := by
        rw [lerayAt_of_solenoidal hsolu i,
          lerayAt_gradient k (pressureCoeffT w.pressure k t) i]
        ring

/-! ## 7. The three sums of the energy identity -/

theorem weight_half_sq (s : ℝ) (k : PeriodicFrequency) :
    periodicFrequencyWeight k ^ (s / 2) * periodicFrequencyWeight k ^ (s / 2) =
      periodicFrequencyWeight k ^ s := by
  rw [← Real.rpow_add (periodicFrequencyWeight_pos k)]
  congr 1
  ring

/-- One frequency of the `H^s` pairing, in terms of the raw coefficients. -/
theorem datum_pair_entry {s : ℝ} {u v : SpaceTimeField} {t : ℝ} {A B : PeriodicSobolev s}
    (hA : IsPeriodicDatum s (fun x ↦ u (t, x)) A)
    (hB : IsPeriodicDatum s (fun x ↦ v (t, x)) B) (k : PeriodicFrequency) :
    (∑ i : Fin 3, conj (A.1 i k) * B.1 i k) =
      ((periodicFrequencyWeight k ^ s : ℝ) : ℂ) *
        ∑ i : Fin 3, conj (velocityCoeffT u i k t) * velocityCoeffT v i k t := by
  simp only [velocityCoeffT]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hA.2.2 i k, hB.2.2 i k, Complex.real_smul, Complex.real_smul, map_mul,
    Complex.conj_ofReal, ← weight_half_sq s k]
  push_cast
  ring

/-- **The `H^s` pairing is the sum of its frequency terms.** -/
theorem hasSum_datum_pair {s : ℝ} (A B : PeriodicSobolev s) :
    HasSum (fun k ↦ (∑ i : Fin 3, conj (A.1 i k) * B.1 i k).re) (torusRealPairing A B) := by
  have hcomp : ∀ i : Fin 3,
      HasSum (fun k ↦ conj (A.1 i k) * B.1 i k) (inner ℂ (A.1 i) (B.1 i) : ℂ) := by
    intro i
    have hsum : Summable fun k ↦ conj (A.1 i k) * B.1 i k := by
      have hsi := lp.summable_inner (𝕜 := ℂ) (A.1 i) (B.1 i)
      exact hsi.congr fun k ↦ RCLike.inner_apply' _ _
    have heq : (inner ℂ (A.1 i) (B.1 i) : ℂ) = ∑' k, conj (A.1 i k) * B.1 i k := by
      rw [lp.inner_eq_tsum]
      exact tsum_congr fun k ↦ RCLike.inner_apply' _ _
    rw [heq]
    exact hsum.hasSum
  have hsum : HasSum (fun k ↦ ∑ i : Fin 3, conj (A.1 i k) * B.1 i k)
      (∑ i : Fin 3, (inner ℂ (A.1 i) (B.1 i) : ℂ)) := hasSum_sum fun i _ ↦ hcomp i
  have htot : (∑ i : Fin 3, (inner ℂ (A.1 i) (B.1 i) : ℂ)) = (inner ℂ A.1 B.1 : ℂ) :=
    (PiLp.inner_apply _ _).symm
  rw [htot] at hsum
  exact hsum.map (Complex.reCLM.toLinearMap.toAddMonoidHom) Complex.reCLM.continuous

/-- The `H^s` norm of the full spatial gradient of a velocity slice, squared. -/
def torusGradientEnergyT (s : ℝ) (u : SpaceTimeField) (t : ℝ) : ℝ :=
  ∑' k, periodicFrequencyWeight k ^ s * periodicAngularFrequencySq k *
    ∑ i : Fin 3, ‖velocityCoeffT u i k t‖ ^ 2

/-- `‖∇u(t)‖_{H^s}`, the dissipation norm of `eq:Rhigh`. -/
def torusGradientNormAt (s : ℝ) (u : SpaceTimeField) (t : ℝ) : ℝ :=
  Real.sqrt (torusGradientEnergyT s u t)

theorem torusGradientNormAt_nonneg (s : ℝ) (u : SpaceTimeField) (t : ℝ) :
    0 ≤ torusGradientNormAt s u t := Real.sqrt_nonneg _

theorem gradEnergy_term_nonneg (s : ℝ) (u : SpaceTimeField) (k : PeriodicFrequency) (t : ℝ) :
    0 ≤ periodicFrequencyWeight k ^ s * periodicAngularFrequencySq k *
      ∑ i : Fin 3, ‖velocityCoeffT u i k t‖ ^ 2 :=
  mul_nonneg (mul_nonneg (Real.rpow_nonneg (periodicFrequencyWeight_pos k).le _)
    (periodicAngularFrequencySq_nonneg k)) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

/-- The dissipation series converges, dominated by the order-`s+1` energy. -/
theorem hasSum_gradEnergy {s : ℝ} {u : SpaceTimeField} {t : ℝ}
    {A : PeriodicSobolev (s + 1)} (hA : IsPeriodicDatum (s + 1) (fun x ↦ u (t, x)) A) :
    HasSum (fun k ↦ periodicFrequencyWeight k ^ s * periodicAngularFrequencySq k *
        ∑ i : Fin 3, ‖velocityCoeffT u i k t‖ ^ 2) (torusGradientEnergyT s u t) := by
  have hle : ∀ k : PeriodicFrequency,
      periodicFrequencyWeight k ^ s * periodicAngularFrequencySq k *
        ∑ i : Fin 3, ‖velocityCoeffT u i k t‖ ^ 2 ≤ freqEnergyT (s + 1) u k t := by
    intro k
    have hw := periodicFrequencyWeight_pos k
    have hlam : periodicAngularFrequencySq k ≤ periodicFrequencyWeight k := by
      unfold periodicFrequencyWeight periodicAngularFrequencySq
      linarith
    have hX : 0 ≤ ∑ i : Fin 3, ‖velocityCoeffT u i k t‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    have hsplit : periodicFrequencyWeight k ^ (s + 1) =
        periodicFrequencyWeight k ^ s * periodicFrequencyWeight k := by
      rw [Real.rpow_add hw, Real.rpow_one]
    rw [freqEnergyT, hsplit]
    have hmul : periodicFrequencyWeight k ^ s * periodicAngularFrequencySq k ≤
        periodicFrequencyWeight k ^ s * periodicFrequencyWeight k :=
      mul_le_mul_of_nonneg_left hlam (Real.rpow_nonneg hw.le _)
    exact mul_le_mul_of_nonneg_right hmul hX
  have hsummable : Summable fun k ↦ periodicFrequencyWeight k ^ s *
      periodicAngularFrequencySq k * ∑ i : Fin 3, ‖velocityCoeffT u i k t‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun k ↦ gradEnergy_term_nonneg s u k t) hle
      (hasSum_freqEnergyT hA).summable
  exact hsummable.hasSum

/-! ## 8. The frequency identity -/

/-- **The differentiated frequency energy, after the pressure drop.**  At every
frequency the derivative splits into the dissipation, the force pairing and the
convection pairing; the pressure term vanishes by coefficient-side
solenoidality. -/
theorem freqEnergyDerivT_split {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) (hf : ContDiff ℝ ∞ f) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    (m : ℕ) {Gm Fm Nm : PeriodicSobolev (m : ℝ)}
    (hGm : IsPeriodicDatum (m : ℝ) (fun x ↦ w.velocity (t, x)) Gm)
    (hFm : IsPeriodicDatum (m : ℝ) (fun x ↦ f (t, x)) Fm)
    (hNm : IsPeriodicDatum (m : ℝ) (fun x ↦ convectionFieldT w.velocity (t, x)) Nm)
    (k : PeriodicFrequency) :
    freqEnergyDerivT (m : ℝ) w.velocity k t =
      -2 * ν * (periodicFrequencyWeight k ^ (m : ℝ) * periodicAngularFrequencySq k *
          ∑ i : Fin 3, ‖velocityCoeffT w.velocity i k t‖ ^ 2) +
        2 * (∑ i : Fin 3, conj (Gm.1 i k) * Fm.1 i k).re -
        2 * (∑ i : Fin 3, conj (Gm.1 i k) * Nm.1 i k).re := by
  have htI : t ∈ Ico (0 : ℝ) T := ⟨le_of_lt ht.1, ht.2⟩
  have hv : ContDiff ℝ ∞ (fun x : Space ↦ w.velocity (t, x)) :=
    classical_velocity_slice_contDiff w htI
  have hvp : IsPeriodicSpatial (fun x : Space ↦ w.velocity (t, x)) := w.velocity_periodic t htI
  have hmom : ∀ i : Fin 3, velocityDerivCoeffT w.velocity i k t =
      ((-(ν * periodicAngularFrequencySq k) : ℝ) : ℂ) * velocityCoeffT w.velocity i k t +
        (velocityCoeffT f i k t - velocityCoeffT (convectionFieldT w.velocity) i k t) -
        periodicDerivativeSymbol i k * pressureCoeffT w.pressure k t :=
    fun i ↦ velocityDerivCoeffT_momentum w hf ht i k
  have hsol : ∑ j : Fin 3, periodicDerivativeSymbol j k * velocityCoeffT w.velocity j k t = 0 :=
    solenoidal_velocityCoeffT hv hvp (w.divergence t htI) k
  have hdrop : ∑ i : Fin 3, conj (velocityCoeffT w.velocity i k t) *
      (periodicDerivativeSymbol i k * pressureCoeffT w.pressure k t) = 0 :=
    torusPressureSymbol_drop_raw hsol _
  have hmc : ∀ i : Fin 3, conj (velocityCoeffT w.velocity i k t) * velocityCoeffT w.velocity i k t =
      ((‖velocityCoeffT w.velocity i k t‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [Complex.conj_mul']
    norm_cast
  have hL : ∑ i : Fin 3,
      conj (velocityCoeffT w.velocity i k t) * velocityDerivCoeffT w.velocity i k t =
      ∑ i : Fin 3, (((-(ν * periodicAngularFrequencySq k) : ℝ) : ℂ) *
          ((‖velocityCoeffT w.velocity i k t‖ ^ 2 : ℝ) : ℂ) +
          conj (velocityCoeffT w.velocity i k t) * velocityCoeffT f i k t -
          conj (velocityCoeffT w.velocity i k t) *
            velocityCoeffT (convectionFieldT w.velocity) i k t -
          conj (velocityCoeffT w.velocity i k t) *
            (periodicDerivativeSymbol i k * pressureCoeffT w.pressure k t)) :=
    Finset.sum_congr rfl fun i _ ↦ by rw [hmom i, ← hmc i]; ring
  have hcsum : ∑ i : Fin 3,
      conj (velocityCoeffT w.velocity i k t) * velocityDerivCoeffT w.velocity i k t =
      ((-(ν * periodicAngularFrequencySq k) : ℝ) : ℂ) *
          (∑ i : Fin 3, ((‖velocityCoeffT w.velocity i k t‖ ^ 2 : ℝ) : ℂ)) +
        (∑ i : Fin 3, conj (velocityCoeffT w.velocity i k t) * velocityCoeffT f i k t) -
        (∑ i : Fin 3, conj (velocityCoeffT w.velocity i k t) *
          velocityCoeffT (convectionFieldT w.velocity) i k t) := by
    rw [hL, Finset.sum_sub_distrib, hdrop, sub_zero, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum]
  have hXreal : (∑ i : Fin 3, ((‖velocityCoeffT w.velocity i k t‖ ^ 2 : ℝ) : ℂ)) =
      ((∑ i : Fin 3, ‖velocityCoeffT w.velocity i k t‖ ^ 2 : ℝ) : ℂ) :=
    (Complex.ofReal_sum _ _).symm
  have hcsumre : (∑ i : Fin 3,
      conj (velocityCoeffT w.velocity i k t) * velocityDerivCoeffT w.velocity i k t).re =
      -(ν * periodicAngularFrequencySq k) *
          (∑ i : Fin 3, ‖velocityCoeffT w.velocity i k t‖ ^ 2) +
        (∑ i : Fin 3, conj (velocityCoeffT w.velocity i k t) * velocityCoeffT f i k t).re -
        (∑ i : Fin 3, conj (velocityCoeffT w.velocity i k t) *
          velocityCoeffT (convectionFieldT w.velocity) i k t).re := by
    rw [hcsum, hXreal]
    simp only [Complex.sub_re, Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re]
  have hsumre : ∑ i : Fin 3,
      2 * (conj (velocityCoeffT w.velocity i k t) * velocityDerivCoeffT w.velocity i k t).re =
      2 * (∑ i : Fin 3,
        conj (velocityCoeffT w.velocity i k t) * velocityDerivCoeffT w.velocity i k t).re := by
    rw [Complex.re_sum, Finset.mul_sum]
  have hGF : (∑ i : Fin 3, conj (Gm.1 i k) * Fm.1 i k).re =
      periodicFrequencyWeight k ^ (m : ℝ) *
        (∑ i : Fin 3, conj (velocityCoeffT w.velocity i k t) * velocityCoeffT f i k t).re := by
    rw [datum_pair_entry hGm hFm k, Complex.re_ofReal_mul]
  have hGN : (∑ i : Fin 3, conj (Gm.1 i k) * Nm.1 i k).re =
      periodicFrequencyWeight k ^ (m : ℝ) *
        (∑ i : Fin 3, conj (velocityCoeffT w.velocity i k t) *
          velocityCoeffT (convectionFieldT w.velocity) i k t).re := by
    rw [datum_pair_entry hGm hNm k, Complex.re_ofReal_mul]
  rw [freqEnergyDerivT, hsumre, hcsumre, hGF, hGN]
  ring

/-! ## 9. The energy identity -/

theorem torusGradientEnergyT_nonneg (s : ℝ) (u : SpaceTimeField) (t : ℝ) :
    0 ≤ torusGradientEnergyT s u t :=
  tsum_nonneg fun k ↦ gradEnergy_term_nonneg s u k t

theorem torusGradientNormAt_sq (s : ℝ) (u : SpaceTimeField) (t : ℝ) :
    torusGradientNormAt s u t ^ 2 = torusGradientEnergyT s u t :=
  Real.sq_sqrt (torusGradientEnergyT_nonneg s u t)

/-- The convection slice of a classical solution has a datum at every order. -/
theorem exists_convection_datum {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) (s : ℝ) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    ∃ Nm : PeriodicSobolev s,
      IsPeriodicDatum s (fun x ↦ convectionFieldT w.velocity (t, x)) Nm :=
  exists_periodicDatum_smooth s
    (advection_spatial_contDiff (classical_velocity_slice_contDiff w ht))
    (advection_spatial_periodic (w.velocity_periodic t ht))

/-- A smooth periodic force slice has a datum at every order. -/
theorem exists_force_datum {f : SpaceTimeField} (hf : ContDiff ℝ ∞ f)
    (hfp : IsPeriodicOn univ f) (s : ℝ) (t : ℝ) :
    ∃ Fm : PeriodicSobolev s, IsPeriodicDatum s (fun x ↦ f (t, x)) Fm :=
  exists_periodicDatum_smooth s (hf.comp (contDiff_const.prodMk contDiff_id))
    (hfp t (mem_univ t))

/-- **The `H^m` energy identity of a classical periodic solution.**
`appendix-a-local-theory.tex:127-141`.  The squared `H^m` profile is
differentiable at every interior time with derivative
`−2ν‖∇u‖²_{H^m} − 2⟪(u·∇)u, u⟫_{H^m} + 2⟪f, u⟫_{H^m}`.  The pressure term is
absent: it vanished frequency by frequency by solenoidality
(`freqEnergyDerivT_split`). -/
theorem energyIdentity_of_classical {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) (hf : ContDiff ℝ ∞ f) (m : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) T) {Gm Fm Nm : PeriodicSobolev (m : ℝ)}
    (hGm : IsPeriodicDatum (m : ℝ) (fun x ↦ w.velocity (t, x)) Gm)
    (hFm : IsPeriodicDatum (m : ℝ) (fun x ↦ f (t, x)) Fm)
    (hNm : IsPeriodicDatum (m : ℝ) (fun x ↦ convectionFieldT w.velocity (t, x)) Nm) :
    HasDerivAt (fun r ↦ torusSobolevNormAt (m : ℝ) w.velocity r ^ 2)
      (-2 * ν * torusGradientNormAt (m : ℝ) w.velocity t ^ 2 +
        2 * torusRealPairing Gm Fm - 2 * torusRealPairing Gm Nm) t := by
  have htI : t ∈ Ico (0 : ℝ) T := ⟨le_of_lt ht.1, ht.2⟩
  obtain ⟨G1, _, hG1d⟩ := w.sobolev (m + 1)
  have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  have hG1 : IsPeriodicDatum ((m : ℝ) + 1) (fun x ↦ w.velocity (t, x)) (G1 t) := by
    rw [← hcast]
    exact hG1d t htI
  have hdiss := hasSum_gradEnergy (u := w.velocity) hG1
  have hFsum := hasSum_datum_pair Gm Fm
  have hNsum := hasSum_datum_pair Gm Nm
  have hcomb := ((hdiss.mul_left (-2 * ν)).add (hFsum.mul_left 2)).sub (hNsum.mul_left 2)
  have hsum : HasSum (fun k ↦ freqEnergyDerivT (m : ℝ) w.velocity k t)
      (-2 * ν * torusGradientEnergyT (m : ℝ) w.velocity t +
        2 * torusRealPairing Gm Fm - 2 * torusRealPairing Gm Nm) :=
    hcomb.congr_fun fun k ↦ freqEnergyDerivT_split w hf ht m hGm hFm hNm k
  have hval : (∑' k, freqEnergyDerivT (m : ℝ) w.velocity k t) =
      -2 * ν * torusGradientNormAt (m : ℝ) w.velocity t ^ 2 +
        2 * torusRealPairing Gm Fm - 2 * torusRealPairing Gm Nm := by
    rw [hsum.tsum_eq, torusGradientNormAt_sq]
  rw [← hval]
  exact hasDerivAt_torusSobolevNormAt_sq w m ht

/-! ## 10. `eq:Rhigh` from the U12b pairing estimate -/

/-- **`eq:Rhigh` from the tame pairing bound.**  The hypothesis `hpair` is U12b's
estimate `|⟪(u·∇)u, u⟫_{H^m}| ≤ C_m ‖u‖_{H²} ‖u‖_{H^m} ‖∇u‖_{H^m}`, taken as an
explicit theorem argument; everything else is the energy identity, Cauchy–Schwarz
for the force term, and arithmetic.  The conclusion is `hRhigh` exactly as
`higherOrderBound_of_energyInequality` consumes it, with the existential `g`
instantiated at `torusGradientNormAt m u t`. -/
theorem hRhigh_of_pairingBound (Chigh : ℕ → ℝ)
    (hpair : ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T) (m : ℕ), 3 ≤ m →
          ∀ t ∈ Ioo (0 : ℝ) T, ∀ Gm Nm : PeriodicSobolev (m : ℝ),
            IsPeriodicDatum (m : ℝ) (fun x ↦ w.velocity (t, x)) Gm →
            IsPeriodicDatum (m : ℝ) (fun x ↦ convectionFieldT w.velocity (t, x)) Nm →
            |torusRealPairing Gm Nm| ≤
              Chigh m * torusSobolevNormAt 2 w.velocity t *
                torusSobolevNormAt (m : ℝ) w.velocity t *
                torusGradientNormAt (m : ℝ) w.velocity t) :
    ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T) (m : ℕ), 3 ≤ m →
          ∀ t ∈ Ioo (0 : ℝ) T, ∃ d g : ℝ, 0 ≤ g ∧
            HasDerivAt (fun r ↦ torusSobolevNormAt (m : ℝ) w.velocity r ^ 2) d t ∧
            (1 / 2) * d + ν * g ^ 2 ≤
              Chigh m * torusSobolevNormAt 2 w.velocity t *
                  torusSobolevNormAt (m : ℝ) w.velocity t * g +
                torusSobolevNormAt (m : ℝ) f t * torusSobolevNormAt (m : ℝ) w.velocity t := by
  intro ν hν a ha f hfmem T w m hm t ht
  have htI : t ∈ Ico (0 : ℝ) T := ⟨le_of_lt ht.1, ht.2⟩
  have hfm : MemForceT f := hfmem
  obtain ⟨Gm, _, hGmd⟩ := w.sobolev m
  have hGm : IsPeriodicDatum (m : ℝ) (fun x ↦ w.velocity (t, x)) (Gm t) := hGmd t htI
  obtain ⟨Fm, hFm⟩ := exists_force_datum hfm.1 hfm.2.1 (m : ℝ) t
  obtain ⟨Nm, hNm⟩ := exists_convection_datum w (m : ℝ) htI
  set g : ℝ := torusGradientNormAt (m : ℝ) w.velocity t with hgdef
  refine ⟨-2 * ν * g ^ 2 + 2 * torusRealPairing (Gm t) Fm - 2 * torusRealPairing (Gm t) Nm,
    g, torusGradientNormAt_nonneg _ _ _,
    energyIdentity_of_classical w hfm.1 m ht hGm hFm hNm, ?_⟩
  have hGnorm : torusSobolevNormAt (m : ℝ) w.velocity t = ‖Gm t‖ := torusSobolevNormAt_eq hGm
  have hFnorm : torusSobolevNormAt (m : ℝ) f t = ‖Fm‖ := torusSobolevNormAt_eq hFm
  have hforce : torusRealPairing (Gm t) Fm ≤
      torusSobolevNormAt (m : ℝ) f t * torusSobolevNormAt (m : ℝ) w.velocity t := by
    rw [hGnorm, hFnorm, mul_comm]
    exact torusRealPairing_le (Gm t) Fm
  have hconv : -torusRealPairing (Gm t) Nm ≤
      Chigh m * torusSobolevNormAt 2 w.velocity t *
        torusSobolevNormAt (m : ℝ) w.velocity t * g :=
    (neg_le_abs _).trans (hpair ν hν a ha f hfmem T w m hm t ht (Gm t) Nm hGm hNm)
  linarith

/-- **The periodic higher-order bound from the U12b pairing estimate.**  Composing
this lane's `eq:Rhigh` with lane 322's Grönwall chain discharges the
`higherOrderBound` field of `PeriodicContinuationAPI` from the pairing bound
alone. -/
theorem higherOrderBound_of_pairingBound (Chigh : ℕ → ℝ)
    (hpair : ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T) (m : ℕ), 3 ≤ m →
          ∀ t ∈ Ioo (0 : ℝ) T, ∀ Gm Nm : PeriodicSobolev (m : ℝ),
            IsPeriodicDatum (m : ℝ) (fun x ↦ w.velocity (t, x)) Gm →
            IsPeriodicDatum (m : ℝ) (fun x ↦ convectionFieldT w.velocity (t, x)) Nm →
            |torusRealPairing Gm Nm| ≤
              Chigh m * torusSobolevNormAt 2 w.velocity t *
                torusSobolevNormAt (m : ℝ) w.velocity t *
                torusGradientNormAt (m : ℝ) w.velocity t) :
    ∀ (ν : ℝ), 0 < ν →
      ∀ (a : SpatialField), a ∈ initialClassT →
        ∀ (f : SpaceTimeField), f ∈ forceClassT →
          ∀ (S : ℝ), 0 < S →
            ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
              SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
                ∀ m : ℕ, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
                  ∀ t ∈ Ico (0 : ℝ) S,
                    periodicSobolevENorm (m : ℝ) (fun x ↦ u (t, x)) ≤ M :=
  higherOrderBound_of_energyInequality Chigh (hRhigh_of_pairingBound Chigh hpair)

/-! ## 11. Non-vacuity -/

/-- The coefficient derivative is not vacuous: for the spatially homogeneous
field `u(t,x) = eᵗc` the zero-mode coefficient path is `eᵗcᵢ`, and its derivative
is nonzero whenever `cᵢ ≠ 0`. -/
example (c : Space) (i : Fin 3) (hci : c i ≠ 0) {t : ℝ} (ht : (0 : ℝ) < t) :
    HasDerivAt (velocityCoeffT (fun z : SpaceTime ↦ Real.exp z.1 • c) i 0)
        (((Real.exp t * c i : ℝ) : ℂ)) t ∧ ((Real.exp t * c i : ℝ) : ℂ) ≠ 0 := by
  have hu : ContDiffOn ℝ ∞ (fun z : SpaceTime ↦ Real.exp z.1 • c)
      (Ioi (0 : ℝ) ×ˢ (univ : Set Space)) :=
    ((Real.contDiff_exp.comp contDiff_fst).smul contDiff_const).contDiffOn
  have hd : ∀ x : Space, temporalDerivative (fun z : SpaceTime ↦ Real.exp z.1 • c) t x =
      Real.exp t • c := fun x ↦ ((Real.hasDerivAt_exp t).smul_const c).deriv
  have hcoeff : velocityDerivCoeffT (fun z : SpaceTime ↦ Real.exp z.1 • c) i 0 t =
      ((Real.exp t * c i : ℝ) : ℂ) := by
    rw [velocityDerivCoeffT,
      show (fun x : Space ↦
          ((temporalDerivative (fun z : SpaceTime ↦ Real.exp z.1 • c) t x i : ℝ) : ℂ)) =
        fun _ : Space ↦ ((Real.exp t * c i : ℝ) : ℂ) from
        funext fun x ↦ by rw [hd x]; rfl,
      periodicFourierCoeff_const]
    simp
  refine ⟨?_, ?_⟩
  · have := hasDerivAt_velocityCoeffT isOpen_Ioi hu ht i 0
    rwa [hcoeff] at this
  · simpa using mul_ne_zero (Real.exp_ne_zero t) hci

end NSFormalization.Section3.T11
