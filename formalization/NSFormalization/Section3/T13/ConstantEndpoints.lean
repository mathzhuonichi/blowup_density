import NSFormalization.Section3.T13.Localization
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# T13: the explicit Gagliardo constant and the two endpoint identities

This module proves three of the six fields of `LocalizationAPI`
(`research/T13/probes/api_on_canonical.lean`), verbatim, for the canonical
vocabulary of `NSFormalization.Section3.T13.Localization`:

* `constant_pos_finite` (`paper/sections/03-torus.tex:35-39`): the explicit
  constant `c_s = ∫_{ℝ³} |e^{i h₁} - 1|² |h|^{-3-2s} dh` is strictly positive
  and finite for `0 < s < 1`.  Finiteness follows the paper: near the origin
  the numerator is at most `|h|²`, which leaves the radial integral
  `∫₀¹ r^{1-2s} dr`; away from the origin the numerator is at most `4`, which
  leaves `∫₁^∞ r^{-1-2s} dr`.  Both are realized through Mathlib's radial
  reduction `MeasureTheory.integrable_fun_norm_addHaar` applied to the radial
  majorant `cFracRadial`.  Positivity is the observation that the integrand is
  nonzero on the nonempty open slab `0 < h₁ < 1`.
* `endpoint_zero` and `endpoint_one` (`paper/sections/03-torus.tex:29,96-98`):
  "integration over the single copy of the support" for the `L²` norm and for
  the `L²` gradient norm.  Both rest on the single-copy lemma
  `periodize_eq_of_mem_cube`: for a field whose topological support lies in a
  ball with closure inside `interior fundamentalCube`, every nonzero lattice
  translate vanishes on the whole closed cube `[0,1]³`, so the periodization
  agrees with the zero extension there.  For the gradient the agreement is
  upgraded to a neighbourhood statement on `interior fundamentalCube`, whose
  complement inside the cube is the frontier of a convex set and hence null.

No named input is used; every declaration below is proved outright.  The three
remaining `LocalizationAPI` fields (`wholeSpace_identity`, `torus_identity`,
`localization`) are out of scope for this module.
-/

noncomputable section

namespace NSFormalization.Section3.T13

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section3.T10
open scoped ContDiff ENNReal BigOperators Topology

/-! ## §0  Coordinate helpers on `Space` -/

/-- Every Euclidean coordinate functional on `Space` is continuous. -/
theorem continuous_spaceCoord (i : Fin 3) : Continuous fun x : Space => x i :=
  (EuclideanSpace.proj i).continuous

/-- A single coordinate never exceeds the Euclidean norm. -/
theorem abs_spaceCoord_le_norm (x : Space) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i

/-- A natural power absorbed into a real power, at a positive base. -/
theorem npow_mul_rpow_of_pos {y : ℝ} (hy : 0 < y) (n : ℕ) (a : ℝ) :
    y ^ n * y ^ a = y ^ ((n : ℝ) + a) := by
  rw [Real.rpow_add hy, Real.rpow_natCast]

/-! ## §1  The explicit constant `cFrac`

`03-torus.tex:35-39`.  All three bounds on the numerator `|e^{i t} - 1|²` come
from Mathlib's exact evaluation `‖exp (I t) - 1‖ = ‖2 sin (t/2)‖`. -/

/-- Near the origin the `cFrac` numerator is at most `t²`. -/
theorem norm_exp_sub_one_sq_le_sq (t : ℝ) :
    ‖Complex.exp (Complex.I * (t : ℂ)) - 1‖ ^ 2 ≤ t ^ 2 := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := t)
  rw [Real.norm_eq_abs] at h
  calc ‖Complex.exp (Complex.I * (t : ℂ)) - 1‖ ^ 2 ≤ |t| ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = t ^ 2 := sq_abs t

/-- Globally the `cFrac` numerator is at most `4`. -/
theorem norm_exp_sub_one_sq_le_four (t : ℝ) :
    ‖Complex.exp (Complex.I * (t : ℂ)) - 1‖ ^ 2 ≤ 4 := by
  have h : ‖Complex.exp (Complex.I * (t : ℂ)) - 1‖ ≤ 2 := by
    rw [Complex.norm_exp_I_mul_ofReal_sub_one t, Real.norm_eq_abs, abs_mul]
    have hs := Real.abs_sin_le_one (t / 2)
    have h2 : |(2:ℝ)| = 2 := by norm_num
    rw [h2]; nlinarith
  nlinarith [norm_nonneg (Complex.exp (Complex.I * (t : ℂ)) - 1)]

/-- On `0 < t < 1` the `cFrac` numerator is strictly positive. -/
theorem norm_exp_sub_one_sq_pos {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    0 < ‖Complex.exp (Complex.I * (t : ℂ)) - 1‖ ^ 2 := by
  have hsin : 0 < Real.sin (t / 2) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by linarith) ?_
    have hpi := Real.pi_gt_three
    linarith
  have heq : ‖Complex.exp (Complex.I * (t : ℂ)) - 1‖ = |2 * Real.sin (t / 2)| := by
    rw [Complex.norm_exp_I_mul_ofReal_sub_one t, Real.norm_eq_abs]
  rw [heq]
  have habs : 0 < |2 * Real.sin (t / 2)| := abs_pos.mpr (by positivity)
  positivity

/-- The radial majorant of the `cFrac` integrand: `min(r², 4) · r^{-3-2s}`.
It encodes exactly the paper's two-regime bound on `|e^{i h₁} - 1|²`. -/
def cFracRadial (s y : ℝ) : ℝ := min (y ^ 2) 4 * y ^ (-(3 + 2 * s))

theorem cFracRadial_nonneg (s : ℝ) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ cFracRadial s y :=
  mul_nonneg (le_min (sq_nonneg y) (by norm_num)) (Real.rpow_nonneg hy _)

/-- Near-origin regime: `r² · cFracRadial s r = r^{1-2s}` is integrable on
`(0,1)` exactly when `s < 1`. -/
theorem integrableOn_cFracRadial_Ioo (s : ℝ) (hs1 : s < 1) :
    IntegrableOn (fun y : ℝ => y ^ 2 * cFracRadial s y) (Ioo 0 1) volume := by
  have h1 : IntegrableOn (fun y : ℝ => y ^ (1 - 2 * s)) (Ioo 0 1) volume :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).mpr (by linarith)
  refine h1.congr_fun ?_ measurableSet_Ioo
  rintro y ⟨hy0, hy1⟩
  have hmin : min (y ^ 2) 4 = y ^ 2 := min_eq_left (by nlinarith)
  simp only [cFracRadial, hmin]
  rw [← mul_assoc, show y ^ 2 * y ^ 2 = y ^ (4:ℕ) by ring, npow_mul_rpow_of_pos hy0 4]
  congr 1
  push_cast
  ring

/-- Far-field regime: `r² · cFracRadial s r ≤ 4 r^{-1-2s}` is integrable on
`[1,∞)` exactly when `0 < s`. -/
theorem integrableOn_cFracRadial_Ici (s : ℝ) (hs0 : 0 < s) :
    IntegrableOn (fun y : ℝ => y ^ 2 * cFracRadial s y) (Ici 1) volume := by
  have h2 : IntegrableOn (fun y : ℝ => (4:ℝ) * y ^ (-1 - 2 * s)) (Ici 1) volume := by
    refine IntegrableOn.congr_set_ae ?_ Ioi_ae_eq_Ici.symm
    exact ((integrableOn_Ioi_rpow_iff one_pos).mpr (by linarith)).const_mul 4
  refine Integrable.mono' h2 ?_ ?_
  · exact (by unfold cFracRadial; fun_prop : Measurable _).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ici ?_
    intro y hy
    have hy0 : (0:ℝ) < y := lt_of_lt_of_le one_pos hy
    have hr : (0:ℝ) ≤ y ^ (-(3 + 2 * s)) := Real.rpow_nonneg hy0.le _
    have hmin : min (y ^ 2) 4 ≤ 4 := min_le_right _ _
    have hmin0 : (0:ℝ) ≤ min (y ^ 2) 4 := le_min (sq_nonneg y) (by norm_num)
    have hkey : y ^ 2 * (min (y ^ 2) 4 * y ^ (-(3 + 2 * s))) ≤ 4 * y ^ (-1 - 2 * s) := by
      have hstep : y ^ 2 * (min (y ^ 2) 4 * y ^ (-(3 + 2 * s)))
          ≤ y ^ 2 * (4 * y ^ (-(3 + 2 * s))) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg y)
        exact mul_le_mul_of_nonneg_right hmin hr
      refine hstep.trans_eq ?_
      rw [show y ^ 2 * (4 * y ^ (-(3 + 2 * s))) = 4 * (y ^ (2:ℕ) * y ^ (-(3 + 2 * s))) by ring,
        npow_mul_rpow_of_pos hy0 2]
      congr 2
      push_cast
      ring
    have hnn : (0:ℝ) ≤ y ^ 2 * (min (y ^ 2) 4 * y ^ (-(3 + 2 * s))) :=
      mul_nonneg (sq_nonneg y) (mul_nonneg hmin0 hr)
    simp only [cFracRadial]
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hkey

/-- The radial majorant is integrable on `ℝ³` for `0 < s < 1`. -/
theorem integrable_cFracRadial (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    Integrable (fun h : Space => cFracRadial s ‖h‖) volume := by
  have hfr : Module.finrank ℝ Space = 3 := by simp
  rw [integrable_fun_norm_addHaar (volume : Measure Space) (f := cFracRadial s), hfr]
  norm_num only
  have hunion : Ioo (0:ℝ) 1 ∪ Ici 1 = Ioi 0 := Ioo_union_Ici_eq_Ioi one_pos
  rw [← hunion]
  simp only [smul_eq_mul]
  exact (integrableOn_cFracRadial_Ioo s hs1).union (integrableOn_cFracRadial_Ici s hs0)

theorem measurable_cFrac_integrand (s : ℝ) : Measurable (fun h : Space =>
    ENNReal.ofReal (‖Complex.exp (Complex.I * (h 0 : ℂ)) - 1‖ ^ 2) *
      fractionalRadialKernel s h) := by
  unfold fractionalRadialKernel
  fun_prop

/-- Pointwise domination of the `cFrac` integrand by the radial majorant. -/
theorem cFrac_integrand_le (s : ℝ) (h : Space) :
    ENNReal.ofReal (‖Complex.exp (Complex.I * (h 0 : ℂ)) - 1‖ ^ 2) *
        fractionalRadialKernel s h ≤ ENNReal.ofReal (cFracRadial s ‖h‖) := by
  rcases eq_or_ne h 0 with rfl | hne
  · simp
  · have hpos : (0:ℝ) < ‖h‖ := norm_pos_iff.mpr hne
    have hnum : (0:ℝ) ≤ ‖Complex.exp (Complex.I * (h 0 : ℂ)) - 1‖ ^ 2 := sq_nonneg _
    have hker : fractionalRadialKernel s h = ENNReal.ofReal (‖h‖ ^ (-(3 + 2 * s))) := by
      rw [fractionalRadialKernel, ENNReal.ofReal_rpow_of_pos hpos]
    rw [hker, ← ENNReal.ofReal_mul hnum]
    refine ENNReal.ofReal_le_ofReal ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hpos.le _)
    refine le_min ?_ (norm_exp_sub_one_sq_le_four _)
    refine (norm_exp_sub_one_sq_le_sq (h 0)).trans ?_
    have hc := abs_spaceCoord_le_norm h 0
    nlinarith [abs_nonneg (h 0), sq_abs (h 0)]

/-- `03-torus.tex:37-39`: the explicit constant is finite. -/
theorem cFrac_lt_top (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) : cFrac s < ⊤ := by
  have hfin : ∫⁻ h : Space, ‖cFracRadial s ‖h‖‖ₑ < ⊤ :=
    (integrable_cFracRadial s hs0 hs1).hasFiniteIntegral
  refine lt_of_le_of_lt (lintegral_mono (cFrac_integrand_le s)) ?_
  refine lt_of_le_of_lt (lintegral_mono fun h => ?_) hfin
  rw [Real.enorm_eq_ofReal (cFracRadial_nonneg s (norm_nonneg h))]

/-- `03-torus.tex:37-39`: the explicit constant is strictly positive. -/
theorem cFrac_pos (s : ℝ) (hs0 : 0 < s) : 0 < cFrac s := by
  set F : Space → ℝ≥0∞ := fun h =>
    ENNReal.ofReal (‖Complex.exp (Complex.I * (h 0 : ℂ)) - 1‖ ^ 2) *
      fractionalRadialKernel s h with hF
  have hU : IsOpen {h : Space | 0 < h 0 ∧ h 0 < 1} :=
    (isOpen_lt continuous_const (continuous_spaceCoord 0)).inter
      (isOpen_lt (continuous_spaceCoord 0) continuous_const)
  have hUne : {h : Space | 0 < h 0 ∧ h 0 < 1}.Nonempty := by
    refine ⟨EuclideanSpace.single (0 : Fin 3) (1/2 : ℝ), ?_, ?_⟩ <;>
      · show _ < _
        rw [PiLp.single_apply]
        norm_num
  have hsub : {h : Space | 0 < h 0 ∧ h 0 < 1} ⊆ {h : Space | ¬ F h = 0} := by
    rintro h ⟨h1, h2⟩
    simp only [Set.mem_ofPred_eq, hF]
    refine mul_ne_zero ?_ ?_
    · exact (ENNReal.ofReal_pos.mpr (norm_exp_sub_one_sq_pos h1 h2)).ne'
    · rw [fractionalRadialKernel]
      intro hcon
      rcases ENNReal.rpow_eq_zero_iff.mp hcon with ⟨_, hp⟩ | ⟨htop, _⟩
      · linarith
      · exact ENNReal.ofReal_ne_top htop
  rw [pos_iff_ne_zero]
  intro hzero
  have hae := (lintegral_eq_zero_iff' (measurable_cFrac_integrand s).aemeasurable).mp hzero
  have h0 : volume {h : Space | ¬ F h = 0} = 0 := by
    simpa only [Pi.zero_apply] using ae_iff.mp hae
  exact absurd (measure_mono_null hsub h0) (hU.measure_pos volume hUne).ne'

/-! ## §2  The fixed fundamental cube `[0,1]³` -/

/-- The open coordinate cube `(0,1)³`; it is exactly `interior fundamentalCube`. -/
def fundamentalCubeInterior : Set Space := {x | ∀ i : Fin 3, 0 < x i ∧ x i < 1}

theorem isOpen_fundamentalCubeInterior : IsOpen fundamentalCubeInterior := by
  have hEq : fundamentalCubeInterior =
      (⋂ i : Fin 3, {x : Space | 0 < x i}) ∩ (⋂ i : Fin 3, {x : Space | x i < 1}) := by
    ext x
    simp only [fundamentalCubeInterior, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩, fun h i => ⟨h.1 i, h.2 i⟩⟩
  rw [hEq]
  exact (isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const (continuous_spaceCoord i)).inter
    (isOpen_iInter_of_finite fun i => isOpen_lt (continuous_spaceCoord i) continuous_const)

theorem isClosed_fundamentalCube : IsClosed fundamentalCube := by
  have hEq : fundamentalCube =
      (⋂ i : Fin 3, {x : Space | 0 ≤ x i}) ∩ (⋂ i : Fin 3, {x : Space | x i ≤ 1}) := by
    ext x
    simp only [fundamentalCube, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩, fun h i => ⟨h.1 i, h.2 i⟩⟩
  rw [hEq]
  exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_spaceCoord i)).inter
    (isClosed_iInter fun i => isClosed_le (continuous_spaceCoord i) continuous_const)

theorem measurableSet_fundamentalCube : MeasurableSet fundamentalCube :=
  isClosed_fundamentalCube.measurableSet

theorem convex_fundamentalCube : Convex ℝ fundamentalCube := by
  intro x hx y hy a b ha hb hab i
  have hco : (a • x + b • y) i = a * x i + b * y i := rfl
  rw [hco]
  have hxi := hx i
  have hyi := hy i
  constructor <;> nlinarith [hxi.1, hxi.2, hyi.1, hyi.2]

/-- The cube is convex, so its frontier is Lebesgue null. -/
theorem volume_frontier_fundamentalCube : volume (frontier fundamentalCube) = 0 :=
  convex_fundamentalCube.addHaar_frontier volume

theorem fundamentalCubeInterior_subset_interior :
    fundamentalCubeInterior ⊆ interior fundamentalCube :=
  interior_maximal (fun _ hx i => ⟨(hx i).1.le, (hx i).2.le⟩) isOpen_fundamentalCubeInterior

theorem interior_subset_fundamentalCubeInterior :
    interior fundamentalCube ⊆ fundamentalCubeInterior := by
  intro x hx i
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  have hsub : Metric.ball x ε ⊆ fundamentalCube := hball.trans interior_subset
  have hnorm : ‖EuclideanSpace.single i (ε / 2 : ℝ)‖ = ε / 2 := by
    have h : ‖EuclideanSpace.single i (ε / 2 : ℝ)‖ = |ε| / 2 := by simp
    rw [h, abs_of_pos hε]
  have hlo : x - EuclideanSpace.single i (ε / 2 : ℝ) ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [sub_sub_cancel_left, norm_neg, hnorm]
    linarith
  have hhi : x + EuclideanSpace.single i (ε / 2 : ℝ) ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [add_sub_cancel_left, hnorm]
    linarith
  have h1 := hsub hlo i
  have h2 := hsub hhi i
  have e1 : (x - EuclideanSpace.single i (ε / 2 : ℝ)) i = x i - ε / 2 := by simp
  have e2 : (x + EuclideanSpace.single i (ε / 2 : ℝ)) i = x i + ε / 2 := by simp
  rw [e1] at h1
  rw [e2] at h2
  exact ⟨by linarith [h1.1], by linarith [h2.2]⟩

/-- `03-torus.tex:23`: the interior of the fixed closed cube is the open cube. -/
theorem interior_fundamentalCube : interior fundamentalCube = fundamentalCubeInterior :=
  Subset.antisymm interior_subset_fundamentalCubeInterior fundamentalCubeInterior_subset_interior

/-! ## §3  Single-copy periodization

`03-torus.tex:23,96-98`: on the closed cube the lattice sum has exactly one
nonvanishing term. -/

@[simp] theorem latticeVector_zero : latticeVector 0 = 0 := by
  ext i
  simp [latticeVector]

/-- Every nonzero lattice translate of an admissibly supported field vanishes
on the whole closed fundamental cube. -/
theorem eq_zero_of_mem_cube {c : Space} {r : ℝ} {f : SpatialField}
    (hball : closure (Metric.ball c r) ⊆ interior fundamentalCube)
    (hsupp : tsupport f ⊆ Metric.ball c r)
    {x : Space} (hx : x ∈ fundamentalCube) {n : PeriodicFrequency} (hn : n ≠ 0) :
    f (x - latticeVector n) = 0 := by
  by_contra hne
  have hmem : x - latticeVector n ∈ interior fundamentalCube :=
    hball (subset_closure (hsupp (subset_tsupport f hne)))
  have hI := interior_subset_fundamentalCubeInterior hmem
  obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := Function.ne_iff.mp hn
  have hxi := hx i
  have hIi := hI i
  have hcoord : (x - latticeVector n) i = x i - (n i : ℝ) := rfl
  rw [hcoord] at hIi
  rcases lt_or_gt_of_ne hi with hneg | hpos
  · have hz : (1:ℤ) ≤ -n i := by omega
    have hz' : (1:ℝ) ≤ -(n i : ℝ) := by exact_mod_cast hz
    linarith [hxi.2, hIi.2]
  · have hz : (1:ℤ) ≤ n i := by omega
    have hz' : (1:ℝ) ≤ (n i : ℝ) := by exact_mod_cast hz
    linarith [hxi.1, hIi.1]

/-- `03-torus.tex:23,96-98`: on the closed fundamental cube the periodization
is the zero extension itself. -/
theorem periodize_eq_of_mem_cube {c : Space} {r : ℝ} {f : SpatialField}
    (hball : closure (Metric.ball c r) ⊆ interior fundamentalCube)
    (hsupp : tsupport f ⊆ Metric.ball c r)
    {x : Space} (hx : x ∈ fundamentalCube) : periodize f x = f x := by
  have h := tsum_eq_single (L := SummationFilter.unconditional PeriodicFrequency)
    (0 : PeriodicFrequency) (fun n hn => eq_zero_of_mem_cube hball hsupp hx hn)
  simpa only [periodize, latticeVector_zero, sub_zero] using h

/-- The same agreement holds on a whole neighbourhood of every interior point,
so all local derivatives agree there. -/
theorem periodize_eventuallyEq {c : Space} {r : ℝ} {f : SpatialField}
    (hball : closure (Metric.ball c r) ⊆ interior fundamentalCube)
    (hsupp : tsupport f ⊆ Metric.ball c r)
    {x : Space} (hx : x ∈ interior fundamentalCube) : periodize f =ᶠ[nhds x] f := by
  filter_upwards [isOpen_interior.mem_nhds hx] with y hy
  exact periodize_eq_of_mem_cube hball hsupp (interior_subset hy)

theorem tsupport_subset_cube {c : Space} {r : ℝ} {f : SpatialField}
    (hball : closure (Metric.ball c r) ⊆ interior fundamentalCube)
    (hsupp : tsupport f ⊆ Metric.ball c r) : tsupport f ⊆ fundamentalCube :=
  fun _ hx => interior_subset (hball (subset_closure (hsupp hx)))

theorem fderiv_eq_zero_of_notMem_tsupport {f : SpatialField} {x : Space}
    (hx : x ∉ tsupport f) : fderiv ℝ f x = 0 := by
  have h : f =ᶠ[nhds x] fun _ : Space => (0 : Space) :=
    notMem_tsupport_iff_eventuallyEq.mp hx
  rw [h.fderiv_eq]
  simp

/-! ## §4  The two endpoint identities -/

/-- `03-torus.tex:29,96-98`, order zero. -/
theorem endpoint_zero_eq {c : Space} {r : ℝ} {f : SpatialField}
    (hball : closure (Metric.ball c r) ⊆ interior fundamentalCube)
    (hsupp : tsupport f ⊆ Metric.ball c r) :
    eLpNorm (periodize f) 2 (volume.restrict fundamentalCube) = eLpNorm f 2 volume := by
  have hae : periodize f =ᵐ[volume.restrict fundamentalCube] f :=
    ae_restrict_of_forall_mem measurableSet_fundamentalCube
      (fun x hx => periodize_eq_of_mem_cube hball hsupp hx)
  rw [eLpNorm_congr_ae hae,
    ← eLpNorm_indicator_eq_eLpNorm_restrict (p := 2) (μ := volume) measurableSet_fundamentalCube]
  congr 1
  exact Set.indicator_eq_self.mpr ((subset_tsupport f).trans (tsupport_subset_cube hball hsupp))

/-- `03-torus.tex:29,96-98`, order one. -/
theorem endpoint_one_eq {c : Space} {r : ℝ} {f : SpatialField}
    (hball : closure (Metric.ball c r) ⊆ interior fundamentalCube)
    (hsupp : tsupport f ⊆ Metric.ball c r) :
    gradientENorm (periodize f) (volume.restrict fundamentalCube) = gradientENorm f volume := by
  have hcube := tsupport_subset_cube hball hsupp
  unfold gradientENorm
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hae : ∀ᵐ x ∂(volume.restrict fundamentalCube),
      ENNReal.ofReal (‖fderiv ℝ (periodize f) x (coordinateVector i)‖ ^ 2)
        = ENNReal.ofReal (‖fderiv ℝ f x (coordinateVector i)‖ ^ 2) := by
    rw [ae_iff, Measure.restrict_apply' measurableSet_fundamentalCube]
    refine measure_mono_null ?_ volume_frontier_fundamentalCube
    rintro x ⟨hx1, hx2⟩
    refine ⟨subset_closure hx2, fun hint => hx1 ?_⟩
    rw [(periodize_eventuallyEq hball hsupp hint).fderiv_eq]
  rw [lintegral_congr_ae hae, ← lintegral_indicator measurableSet_fundamentalCube]
  congr 1
  refine Set.indicator_eq_self.mpr (Function.support_subset_iff'.mpr (fun x hx => ?_))
  rw [fderiv_eq_zero_of_notMem_tsupport (fun hc => hx (hcube hc))]
  simp

/-! ## §5  The three `LocalizationAPI` fields, verbatim -/

/-- `LocalizationAPI.constant_pos_finite`, `03-torus.tex:35-39`. -/
theorem constant_pos_finite :
    ∀ (s : ℝ), 0 < s → s < 1 → 0 < cFrac s ∧ cFrac s < ⊤ :=
  fun s hs0 hs1 => ⟨cFrac_pos s hs0, cFrac_lt_top s hs0 hs1⟩

/-- `LocalizationAPI.endpoint_zero`, `03-torus.tex:29,96-98`. -/
theorem endpoint_zero :
    ∀ (c : Space) (r : ℝ),
      0 < r → closure (Metric.ball c r) ⊆ interior fundamentalCube →
        ∀ f : SpatialField, (ContDiff ℝ ∞ f ∧ SupportedInBall c r f) →
          eLpNorm (periodize f) 2 (volume.restrict fundamentalCube) =
            eLpNorm f 2 volume :=
  fun _ _ _ hball _ hf => endpoint_zero_eq hball hf.2

/-- `LocalizationAPI.endpoint_one`, `03-torus.tex:29,96-98`. -/
theorem endpoint_one :
    ∀ (c : Space) (r : ℝ),
      0 < r → closure (Metric.ball c r) ⊆ interior fundamentalCube →
        ∀ f : SpatialField, (ContDiff ℝ ∞ f ∧ SupportedInBall c r f) →
          gradientENorm (periodize f) (volume.restrict fundamentalCube) =
            gradientENorm f volume :=
  fun _ _ _ hball _ hf => endpoint_one_eq hball hf.2

end NSFormalization.Section3.T13
