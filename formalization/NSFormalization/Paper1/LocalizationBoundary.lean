import NSFormalization.Paper1.PeriodicBridge
import NSFormalization.Paper1.PeriodicSobolevHilbert
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Endpoint localization and interior-domain energy interfaces

This file records the endpoint statements used alongside the manuscript's
fractional localization lemma.  The periodization equalities are inherited
from the explicit fundamental-domain argument in `PeriodicBridge`; the
bounded-domain inequalities are direct instances of Mathlib's monotonicity of
set integrals.  The final theorem adds the genuinely proved spectral
interpolation bound for `0 ≤ s ≤ 1`; it does not assert a Gagliardo norm
equivalence or the critical `H^(1/2) → L^3` embedding.

Source anchors:
* `final/paper_1_theory.tex`, Lemma `localization` (equation (localization))
  states the missing fractional comparison and its `s = 0,1` endpoints.
* Mathlib `MeasureTheory.Integral.Bochner.Set`, theorem
  `setIntegral_le_integral`, supplies restriction monotonicity for a
  nonnegative integrable real integrand.
* Mathlib `Analysis.Calculus.FDeriv.Congr`, theorem
  `Filter.EventuallyEq.fderiv_eq`, supplies the derivative locality used for
  scalar support and periodization.
-/

noncomputable section
namespace NSFormalization.Paper1.LocalizationBoundary

open Set MeasureTheory NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Paper1.PeriodicBridge
open NavierStokes.PeriodicLocalization NavierStokes.PeriodicIntegration
open Filter
open scoped ContDiff Topology

/-- The endpoint `s = 0` identity in the manuscript's localization lemma,
for any normed-valued compact field supported strictly inside the fundamental
cube.  This is an actual integral equality, not a formal norm convention. -/
theorem l2_endpoint_periodization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ} {u : SpaceTime → E} (hu : SupportedInCube r u) (hr : r < 1 / 2)
    {t : ℝ} (hi : Integrable (fun x => ‖u (t, x)‖ ^ 2)) :
    cubeIntegral (fun x => ‖periodize u (t, x)‖ ^ 2) =
      ∫ x : Space, ‖u (t, x)‖ ^ 2 := by
  exact cubeIntegral_periodize_norm_sq hu hr hi

/-- The endpoint `s = 1` identity for the velocity gradient energy.  The
hypothesis is exactly the smoothness needed by the existing compact-energy
integrability theorem; support and `r < 1/2` prevent copy overlap. -/
theorem gradient_endpoint_periodization
    {r : ℝ} {u : VelocityField} (hu : SupportedInCube r u) (hr : r < 1 / 2)
    {t : ℝ} (hs : ContDiff ℝ ∞ (fun x => u (t, x))) :
    PeriodicUniqueness.dissipation (periodize u) t =
      NavierStokesR3.CompactEnergy.dissipation u t := by
  exact dissipation_periodize hu hr hs

/-- A bounded-domain spatial `L²` energy never exceeds the whole-space one.
The conclusion is valid for any measurable set; it does not encode a trace or
no-slip condition. -/
def domainL2Sq {E : Type*} [NormedAddCommGroup E] (Ω : Set Space)
    (u : SpaceTime → E) (t : ℝ) : ℝ :=
  ∫ x in Ω, ‖u (t, x)‖ ^ 2

theorem domainL2Sq_le_whole
    {E : Type*} [NormedAddCommGroup E] {Ω : Set Space}
    (_hΩ : MeasurableSet Ω) {u : SpaceTime → E} {t : ℝ}
    (hi : Integrable (fun x => ‖u (t, x)‖ ^ 2)) :
    domainL2Sq Ω u t ≤ ∫ x : Space, ‖u (t, x)‖ ^ 2 := by
  unfold domainL2Sq
  exact setIntegral_le_integral hi (Filter.Eventually.of_forall
    (fun x => sq_nonneg ‖u (t, x)‖))

theorem domainL2Sq_eq_whole_of_compl_eq_zero
    {E : Type*} [NormedAddCommGroup E] {Ω : Set Space}
    (_hΩ : MeasurableSet Ω) {u : SpaceTime → E} {t : ℝ}
    (hzero : ∀ x, x ∉ Ω → u (t, x) = 0)
    (_hi : Integrable (fun x => ‖u (t, x)‖ ^ 2)) :
    domainL2Sq Ω u t = ∫ x : Space, ‖u (t, x)‖ ^ 2 := by
  unfold domainL2Sq
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  simp [hzero x hx]

/-- The same restriction monotonicity applied to each directional gradient.
This is the quantitative domain-energy part of the interior boundary adapter;
no boundary integration by parts is hidden in the statement. -/
def domainDissipation (Ω : Set Space) (u : VelocityField) (t : ℝ) : ℝ :=
  ∑ i : Fin 3, ∫ x in Ω,
    ‖PeriodicIntegration.spatialPartial i (fun y => u (t, y)) x‖ ^ 2

theorem domainDissipation_le_whole
    {Ω : Set Space} (_hΩ : MeasurableSet Ω) {u : VelocityField} {t : ℝ}
    (hi : ∀ i : Fin 3,
      Integrable (fun x =>
        ‖PeriodicIntegration.spatialPartial i (fun y => u (t, y)) x‖ ^ 2)) :
    domainDissipation Ω u t ≤
      NavierStokesR3.CompactEnergy.dissipation u t := by
  unfold domainDissipation NavierStokesR3.CompactEnergy.dissipation
  apply Finset.sum_le_sum
  intro i hiFin
  exact setIntegral_le_integral (hi i)
    (Filter.Eventually.of_forall (fun x => sq_nonneg
      ‖PeriodicIntegration.spatialPartial i (fun y => u (t, y)) x‖))

theorem domainDissipation_eq_whole_of_compl_eq_zero
    {Ω : Set Space} (_hΩ : MeasurableSet Ω) {u : VelocityField} {t : ℝ}
    (hzero : ∀ x ∉ Ω, ∀ i : Fin 3,
      PeriodicIntegration.spatialPartial i (fun y => u (t, y)) x = 0)
    (_hi : ∀ i : Fin 3,
      Integrable (fun x =>
        ‖PeriodicIntegration.spatialPartial i (fun y => u (t, y)) x‖ ^ 2)) :
    domainDissipation Ω u t =
      NavierStokesR3.CompactEnergy.dissipation u t := by
  unfold domainDissipation NavierStokesR3.CompactEnergy.dissipation
  apply Finset.sum_congr rfl
  intro i hiFin
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  simp [hzero x hx i]


/-- A scalar derivative of a supported spacetime field has the same support
bound.  The proof uses the zero germ outside the support cube and the
locality of the Fréchet derivative; no regularity or unproved extension is
inserted. -/
theorem supported_spatialPartial_complex {r : ℝ} {f : SpaceTime → ℂ}
    (hf : SupportedInCube r f) (i : Fin 3) :
    SupportedInCube r
      (fun z => spatialPartial i (fun y => f (z.1, y)) z.2) := by
  intro z hz j
  by_contra hnot
  have hgt : r < |z.2 j| := lt_of_not_ge hnot
  have hzero := zero_germ_outside_cube hf (z := z) (i := j) hgt
  have hslice : (fun y : Space => f (z.1, y)) =ᶠ[𝓝 z.2]
      (fun _ => (0 : ℂ)) := by
    have hmap : Tendsto (fun y : Space => (z.1, y)) (𝓝 z.2) (𝓝 z) :=
      tendsto_const_nhds.prodMk_nhds tendsto_id
    have hc := hzero.comp_tendsto hmap
    filter_upwards [hc] with y hy
    simpa only [Function.comp_apply] using hy
  have hderiv : fderiv ℝ (fun y : Space => f (z.1, y)) z.2 =
      fderiv ℝ (fun _ : Space => (0 : ℂ)) z.2 := hslice.fderiv_eq
  apply hz
  change (fderiv ℝ (fun y : Space => f (z.1, y)) z.2) (coordinateVector i) = 0
  rw [hderiv]
  simp

/-- Local derivative commutation for a scalar complex field. -/
theorem spatialPartial_periodize_local_complex {r : ℝ} {f : SpaceTime → ℂ}
    (hf : SupportedInCube r f) {z : SpaceTime} (hz : z.2 ∈ innerCube r)
    (i : Fin 3) :
    spatialPartial i (fun y => periodize f (z.1, y)) z.2 =
      spatialPartial i (fun y => f (z.1, y)) z.2 := by
  have hU : innerCube r ∈ 𝓝 z.2 := (isOpen_innerCube r).mem_nhds hz
  have hslice : (fun y : Space => periodize f (z.1, y)) =ᶠ[𝓝 z.2]
      (fun y => f (z.1, y)) := by
    filter_upwards [hU] with y hy
    exact periodize_eq_on_innerCube hf hy z.1
  have hderiv : fderiv ℝ (fun y : Space => periodize f (z.1, y)) z.2 =
      fderiv ℝ (fun y : Space => f (z.1, y)) z.2 := hslice.fderiv_eq
  unfold spatialPartial
  exact congrArg (fun A : Space →L[ℝ] ℂ => A (coordinateVector i)) hderiv

/-- The actual scalar spatial derivative commutes with periodization on all of
space.  Periodicity is used only to pass from the centered fundamental cube;
the local identity is the preceding germ argument. -/
theorem spatialPartial_periodize_complex {r : ℝ} {f : SpaceTime → ℂ}
    (hf : SupportedInCube r f) (hr : r < 1 / 2) (i : Fin 3) :
    (fun z => spatialPartial i (fun y => periodize f (z.1, y)) z.2) =
      periodize (fun z => spatialPartial i (fun y => f (z.1, y)) z.2) := by
  apply periodic_eq_of_unitCube
  · intro t _ x j
    have hp : UnitPeriods (fun y : Space => periodize f (t, y)) := by
      intro y k
      exact unitSpatialPeriodsOn_periodize f (univ : Set ℝ) t (mem_univ _) y k
    exact (NavierStokes.PeriodicUniqueness.spatial_partial_periodic hp i) x j
  · exact unitSpatialPeriodsOn_periodize _ (univ : Set ℝ)
  · intro t x hx
    exact (spatialPartial_periodize_local_complex hf (z := (t, x))
      (innerCube_of_unitCube hr hx) i).trans
      (periodize_eq_on_unitCube (supported_spatialPartial_complex hf i) hr hx t).symm

/-- Fractional-order localization interface actually proved by the available
periodic Fourier calculus.  For every `0 ≤ s ≤ 1`, a compactly supported
complex field periodized into the unit torus obeys the usual spectral
interpolation bound, with the endpoint energies written in their genuine
whole-space form.  The two integrability hypotheses are explicit so this
lemma does not hide a fractional Sobolev or critical embedding assertion. -/
theorem periodicSobolevNorm_periodize_interpolation_complex
    {r : ℝ} {f : SpaceTime → ℂ} (hf : SupportedInCube r f)
    (hr : r < 1 / 2) (hreg : ContDiff ℝ 1 f) {t : ℝ}
    (h0 : Integrable (fun x : Space => ‖f (t, x)‖ ^ 2))
    (h1 : ∀ i : Fin 3,
      Integrable (fun x : Space =>
        ‖spatialPartial i (fun y => f (t, y)) x‖ ^ 2))
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    periodicSobolevNorm s (fun x => periodize f (t, x)) ≤
      (Real.sqrt (∫ x : Space, ‖f (t, x)‖ ^ 2)) ^ (1 - s) *
        (Real.sqrt ((∫ x : Space, ‖f (t, x)‖ ^ 2) +
          ∑ i : Fin 3, ∫ x : Space,
            ‖spatialPartial i (fun y => f (t, y)) x‖ ^ 2)) ^ s := by
  let g : Space → ℂ := fun x => periodize f (t, x)
  have hg : ContDiff ℝ 1 g := by
    have hp := contDiff_periodize hf hreg
    exact hp.comp (contDiff_const.prodMk contDiff_id)
  have hgp : UnitPeriods g := by
    intro x i
    exact unitSpatialPeriodsOn_periodize f (univ : Set ℝ) t (mem_univ _) x i
  have hinterp := periodicSobolevNorm_interpolation hg hgp hs0 hs1
  have h0eq : cubeIntegral (fun x => ‖g x‖ ^ 2) =
      ∫ x : Space, ‖f (t, x)‖ ^ 2 := by
    exact cubeIntegral_periodize_norm_sq hf hr h0
  have hderiv_support (i : Fin 3) :
      SupportedInCube r
        (fun z => spatialPartial i (fun y => f (z.1, y)) z.2) :=
    supported_spatialPartial_complex hf i
  have h1eq (i : Fin 3) :
      cubeIntegral (fun x => ‖spatialPartial i g x‖ ^ 2) =
        ∫ x : Space, ‖spatialPartial i (fun y => f (t, y)) x‖ ^ 2 := by
    have hi := cubeIntegral_periodize_norm_sq (hderiv_support i) hr (h1 i)
    have heqfun : (fun x => spatialPartial i g x) =
        (fun x => periodize
          (fun z => spatialPartial i (fun y => f (z.1, y)) z.2) (t, x)) := by
      funext x
      exact congrFun (spatialPartial_periodize_complex hf hr i) (t, x)
    have hnormfun : (fun x => ‖spatialPartial i g x‖ ^ 2) =
        (fun x => ‖periodize
          (fun z => spatialPartial i (fun y => f (z.1, y)) z.2) (t, x)‖ ^ 2) := by
      funext x
      exact congrArg (fun z : ℂ => ‖z‖ ^ 2) (congrFun heqfun x)
    rw [hnormfun]
    simpa only [Prod.fst, Prod.snd] using hi
  have h1sum : periodicH1Energy g =
      (∫ x : Space, ‖f (t, x)‖ ^ 2) +
        ∑ i : Fin 3, ∫ x : Space,
          ‖spatialPartial i (fun y => f (t, y)) x‖ ^ 2 := by
    unfold periodicH1Energy
    rw [h0eq]
    simp_rw [h1eq]
  rw [h0eq, h1sum] at hinterp
  simpa only [g] using hinterp


/-- The (inhomogeneous-free) Gagliardo kernel used for a fractional order
`0 < s < 1`.  Its diagonal value is set to zero explicitly, avoiding any
unstated convention for the singular denominator. -/
def fractionalKernel (s : ℝ) (f : Space → ℂ) (x y : Space) : ℝ :=
  if x = y then 0 else
    ‖f x - f y‖ ^ 2 / ‖x - y‖ ^ (3 + 2 * s)

/-- Near-field part of the Gagliardo kernel (the unit interaction ball). -/
def fractionalKernelNear (s : ℝ) (f : Space → ℂ) (x y : Space) : ℝ :=
  if ‖x - y‖ ≤ 1 then fractionalKernel s f x y else 0

/-- Far-field part of the Gagliardo kernel. -/
def fractionalKernelFar (s : ℝ) (f : Space → ℂ) (x y : Space) : ℝ :=
  if 1 < ‖x - y‖ then fractionalKernel s f x y else 0


/-- The kernel is pointwise nonnegative. -/
theorem fractionalKernel_nonneg (s : ℝ) (f : Space → ℂ)
    (x y : Space) : 0 ≤ fractionalKernel s f x y := by
  by_cases hxy : x = y
  · simp [fractionalKernel, hxy]
  · rw [fractionalKernel, ite_eq_right hxy]
    exact div_nonneg (sq_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)

/-- Both pieces in the near/far decomposition are pointwise nonnegative. -/
theorem fractionalKernelNear_nonneg (s : ℝ) (f : Space → ℂ)
    (x y : Space) : 0 ≤ fractionalKernelNear s f x y := by
  by_cases h : ‖x - y‖ ≤ 1 <;>
    simp [fractionalKernelNear, h, fractionalKernel_nonneg]

theorem fractionalKernelFar_nonneg (s : ℝ) (f : Space → ℂ)
    (x y : Space) : 0 ≤ fractionalKernelFar s f x y := by
  by_cases h : 1 < ‖x - y‖ <;>
    simp [fractionalKernelFar, h, fractionalKernel_nonneg]

/-- Exact near/far decomposition of the Gagliardo kernel, including the
singular diagonal convention. -/
theorem fractionalKernel_eq_near_add_far (s : ℝ) (f : Space → ℂ)
    (x y : Space) :
    fractionalKernel s f x y =
      fractionalKernelNear s f x y + fractionalKernelFar s f x y := by
  by_cases h : ‖x - y‖ ≤ 1
  · simp [fractionalKernelNear, fractionalKernelFar, h]
  · have h' : 1 < ‖x - y‖ := lt_of_not_ge h
    simp [fractionalKernelNear, fractionalKernelFar, h, h']

/-- Integral form of the exact near/far split.  Only integrability of the two
pieces is assumed; no fractional Sobolev norm equivalence is folded into this
statement. -/
theorem integral_fractionalKernel_eq_near_add_far
    (s : ℝ) (f : Space → ℂ)
    (hnear : Integrable (fun z : Space × Space =>
      fractionalKernelNear s f z.1 z.2))
    (hfar : Integrable (fun z : Space × Space =>
      fractionalKernelFar s f z.1 z.2)) :
    (∫ z : Space × Space, fractionalKernel s f z.1 z.2) =
      (∫ z : Space × Space, fractionalKernelNear s f z.1 z.2) +
        ∫ z : Space × Space, fractionalKernelFar s f z.1 z.2 := by
  have hpoint : (fun z : Space × Space => fractionalKernel s f z.1 z.2) =
      (fun z => fractionalKernelNear s f z.1 z.2 +
        fractionalKernelFar s f z.1 z.2) := by
    funext z
    exact fractionalKernel_eq_near_add_far s f z.1 z.2

  rw [hpoint, integral_add hnear hfar]

/-- Under the same explicit integrability assumptions, the near-field part is
bounded by the complete Gagliardo kernel integral. -/
theorem integral_fractionalKernelNear_le
    (s : ℝ) (f : Space → ℂ)
    (hnear : Integrable (fun z : Space × Space =>
      fractionalKernelNear s f z.1 z.2))
    (hfar : Integrable (fun z : Space × Space =>
      fractionalKernelFar s f z.1 z.2)) :
    (∫ z : Space × Space, fractionalKernelNear s f z.1 z.2) ≤
      ∫ z : Space × Space, fractionalKernel s f z.1 z.2 := by
  have hpoint : (fun z : Space × Space => fractionalKernel s f z.1 z.2) =
      (fun z => fractionalKernelNear s f z.1 z.2 +
        fractionalKernelFar s f z.1 z.2) := by
    funext z
    exact fractionalKernel_eq_near_add_far s f z.1 z.2
  have hkernel : Integrable (fun z : Space × Space =>
      fractionalKernel s f z.1 z.2) := by
    rw [hpoint]
    exact hnear.add hfar
  apply integral_mono hnear hkernel
  intro z
  rw [hpoint]
  exact le_add_of_nonneg_right
    (fractionalKernelFar_nonneg s f z.1 z.2)


/-- Pointwise far-field domination by the two endpoint `L²` densities.  This
is the exact estimate used to control the nonzero-lattice (far) terms in the
periodization comparison; it is independent of the support radius. -/
theorem fractionalKernelFar_le_l2_density
    (s : ℝ) (f : Space → ℂ) (hs : 0 ≤ s) (x y : Space) :
    fractionalKernelFar s f x y ≤
      2 * (‖f x‖ ^ 2 + ‖f y‖ ^ 2) := by
  by_cases hdist : 1 < ‖x - y‖
  · have hsq : ‖f x - f y‖ ^ 2 ≤
        (‖f x‖ + ‖f y‖) ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg (f x - f y))
        (by positivity)).2 (norm_sub_le _ _)
    have hsum : (‖f x‖ + ‖f y‖) ^ 2 ≤
        2 * (‖f x‖ ^ 2 + ‖f y‖ ^ 2) := by
      nlinarith [sq_nonneg (‖f x‖ - ‖f y‖)]
    have hpow : 1 ≤ ‖x - y‖ ^ (3 + 2 * s) := by
      exact Real.one_le_rpow (le_of_lt hdist) (by linarith)
    have hden : 0 < ‖x - y‖ ^ (3 + 2 * s) := by
      exact Real.rpow_pos_of_pos (lt_trans zero_lt_one hdist) _
    simp only [fractionalKernelFar, if_pos hdist, fractionalKernel]
    have hxy : x ≠ y := by
      intro h
      subst y
      have hcontra : ¬ (1 : ℝ) < ‖x - x‖ := by simp
      exact (hcontra hdist).elim
    rw [if_neg hxy]
    exact (div_le_iff₀ hden).2 (by nlinarith [hsq, hsum, hpow])
  · simp [fractionalKernelFar, hdist]
    positivity

/-- Integrated far-field bound on a measurable support window.  The endpoint
integrability assumptions are explicit, so this theorem is a genuine
`L²` estimate and does not encode a fractional Sobolev equivalence. -/
theorem integral_fractionalKernelFar_restrict_le_l2
    {s : ℝ} {f : Space → ℂ} {K : Set Space}
    (hfar : IntegrableOn
      (fun z : Space × Space => fractionalKernelFar s f z.1 z.2)
      (K ×ˢ K))
    (h1 : IntegrableOn (fun z : Space × Space => ‖f z.1‖ ^ 2)
      (K ×ˢ K))
    (h2 : IntegrableOn (fun z : Space × Space => ‖f z.2‖ ^ 2)
      (K ×ˢ K))
    (hs : 0 ≤ s) :
    (∫ z in K ×ˢ K, fractionalKernelFar s f z.1 z.2) ≤
      2 * (∫ z in K ×ˢ K, ‖f z.1‖ ^ 2) +
        2 * (∫ z in K ×ˢ K, ‖f z.2‖ ^ 2) := by
  have hmajor : IntegrableOn
      (fun z : Space × Space =>
        2 * (‖f z.1‖ ^ 2 + ‖f z.2‖ ^ 2)) (K ×ˢ K) := by
    have hadd : IntegrableOn
        (fun z : Space × Space => ‖f z.1‖ ^ 2 + ‖f z.2‖ ^ 2)
        (K ×ˢ K) := h1.add h2
    exact hadd.const_mul 2
  have hmono := integral_mono hfar hmajor (by
    intro z
    exact fractionalKernelFar_le_l2_density s f hs z.1 z.2)
  calc
    (∫ z in K ×ˢ K, fractionalKernelFar s f z.1 z.2) ≤
        ∫ z in K ×ˢ K, 2 * (‖f z.1‖ ^ 2 + ‖f z.2‖ ^ 2) := hmono
    _ = ∫ z in K ×ˢ K, (2 * ‖f z.1‖ ^ 2 + 2 * ‖f z.2‖ ^ 2) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by ring)
    _ = (∫ z in K ×ˢ K, 2 * ‖f z.1‖ ^ 2) +
        (∫ z in K ×ˢ K, 2 * ‖f z.2‖ ^ 2) := by
      apply integral_add (h1.const_mul 2) (h2.const_mul 2)
    _ = 2 * (∫ z in K ×ˢ K, ‖f z.1‖ ^ 2) +
        2 * (∫ z in K ×ˢ K, ‖f z.2‖ ^ 2) := by
      rw [integral_const_mul, integral_const_mul]

end NSFormalization.Paper1.LocalizationBoundary
