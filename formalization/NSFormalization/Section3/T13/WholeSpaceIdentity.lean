import NSFormalization.Section3.T13.ConstantEndpoints
import NSFormalization.Section4.D01.HomogeneousNorm
import NSFormalization.Source.FourierTranslation
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# T13: the whole-space Gagliardo/Fourier identity `wholeSpace_identity`

`paper/sections/03-torus.tex:40-51`.  For a smooth compactly supported real
vector field `f` on `ℝ³`,
`IReal s f = cFrac s * dotHomogeneousENorm s f ^ 2` and `IReal s f < ⊤`
for `0 < s < 1`.

The proof follows the manuscript: the datum-infimum norm agrees with the
manuscript Fourier quantity (`dotHomogeneousENorm_eq_homogeneousFourierENorm`),
componentwise Plancherel for the unitary angular transform
(`lintegral_angularFourier_sq`) together with the translation phase
(`angularFourier_translate`), Tonelli, and the rotation+dilation evaluation of
the phase kernel (`lintegral_kernel_smul`).
-/

noncomputable section

namespace NSFormalization.Section3.T13

open Set MeasureTheory FourierTransform
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section4.D01 (dotHomogeneousENorm)
open NSFormalization.Section4.D01.Homogeneous hiding SpatialField
open NSFormalization.Source
open NSFormalization.Paper3 (schwartzAngularDilation schwartzAngularDilation_norm_toLp)
open scoped ContDiff ENNReal BigOperators Topology RealInnerProductSpace SchwartzMap

/-! ## §1  The infimum bridge and finiteness -/

/-- For a smooth compactly supported field the datum-infimum homogeneous norm is
the manuscript's pointwise Fourier quantity. -/
theorem dotHomogeneousENorm_eq_homogeneousFourierENorm {s : ℝ} (hs : -3 / 2 < s)
    {f : SpatialField} (hzs : ContDiff ℝ ∞ f) (hzc : HasCompactSupport f) :
    dotHomogeneousENorm s f = homogeneousFourierENorm s f := by
  obtain ⟨⟨A, hA⟩, hval⟩ := isHomogeneousSliceDatum_compact hs hzs hzc
  refine le_antisymm ?_ ?_
  · rw [dotHomogeneousENorm]
    exact iInf_le_of_le ⟨A, hA⟩ (le_of_eq (hval A hA))
  · rw [dotHomogeneousENorm]
    exact le_iInf fun G => le_of_eq (hval G.1 G.2).symm

/-- A smooth compactly supported field has finite homogeneous Fourier energy. -/
theorem homogeneousFourierENorm_lt_top {s : ℝ} (hs : -3 / 2 < s)
    {f : SpatialField} (hzs : ContDiff ℝ ∞ f) (hzc : HasCompactSupport f) :
    homogeneousFourierENorm s f < ⊤ := by
  obtain ⟨⟨A, hA⟩, hval⟩ := isHomogeneousSliceDatum_compact hs hzs hzc
  rw [← hval A hA, ← ofReal_norm]
  exact ENNReal.ofReal_lt_top

/-- The square of the homogeneous Fourier quantity is the summed weighted
frequency energy. -/
theorem homogeneousFourierENorm_sq {s : ℝ} (z : SpatialField) :
    homogeneousFourierENorm s z ^ (2 : ℕ) =
      ∑ i : Fin 3, ∫⁻ ξ : Space,
        ENNReal.ofReal (‖ξ‖ ^ (2 * s) *
          ‖angularFourier (fun x => ((z x i : ℝ) : ℂ)) ξ‖ ^ 2) := by
  set S : ℝ≥0∞ := ∑ i : Fin 3, ∫⁻ ξ : Space,
      ENNReal.ofReal (‖ξ‖ ^ (2 * s) *
        ‖angularFourier (fun x => ((z x i : ℝ) : ℂ)) ξ‖ ^ 2) with hS
  have h1 : homogeneousFourierENorm s z = S ^ ((2 : ℝ)⁻¹) := rfl
  rw [h1, ← ENNReal.rpow_natCast (S ^ ((2 : ℝ)⁻¹)) 2, ← ENNReal.rpow_mul]
  norm_num

/-! ## §2  Angular Plancherel (unitary transform) -/

/-- `∫⁻ ofReal ‖ψ‖² = ofReal ‖ψ.toLp 2‖²` for a Schwartz function. -/
theorem schwartz_lintegral_normSq (ψ : SchwartzMap Space ℂ) :
    (∫⁻ x : Space, ENNReal.ofReal (‖ψ x‖ ^ 2))
      = ENNReal.ofReal (‖ψ.toLp 2 volume‖ ^ 2) := by
  set E : ℝ≥0∞ := eLpNorm (ψ : Space → ℂ) 2 volume with hE
  have hElt : E < ⊤ := (ψ.memLp 2 volume).2
  have hRHS : ENNReal.ofReal (‖ψ.toLp 2 volume‖ ^ 2) = E ^ 2 := by
    rw [SchwartzMap.norm_toLp (f := ψ) (p := 2) (μ := volume)]
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_toReal hElt.ne]
  have hLHS : (∫⁻ x : Space, ENNReal.ofReal (‖ψ x‖ ^ 2)) = E ^ 2 := by
    rw [hE, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, one_div]
    rw [← ENNReal.rpow_natCast (_ ^ ((2 : ℝ)⁻¹)) 2, ← ENNReal.rpow_mul]
    norm_num
  rw [hLHS, hRHS]

/-- Plancherel for the manuscript unitary angular transform, in `ℝ≥0∞` form. -/
theorem lintegral_angularFourier_sq (φ : SchwartzMap Space ℂ) :
    (∫⁻ ξ : Space, ENNReal.ofReal (‖angularFourier (φ : Space → ℂ) ξ‖ ^ 2))
      = ∫⁻ x : Space, ENNReal.ofReal (‖(φ : Space → ℂ) x‖ ^ 2) := by
  calc (∫⁻ ξ : Space, ENNReal.ofReal (‖angularFourier (φ : Space → ℂ) ξ‖ ^ 2))
      = ∫⁻ ξ : Space, ENNReal.ofReal (‖(schwartzAngularFourier φ) ξ‖ ^ 2) := by
        simp_rw [schwartzAngularFourier_apply]
    _ = ENNReal.ofReal (‖(schwartzAngularFourier φ).toLp 2 volume‖ ^ 2) :=
        schwartz_lintegral_normSq _
    _ = ENNReal.ofReal (‖φ.toLp 2 volume‖ ^ 2) := by
        congr 2
        show ‖(schwartzAngularDilation (𝓕 φ)).toLp 2 volume‖ = ‖φ.toLp 2 volume‖
        rw [schwartzAngularDilation_norm_toLp, ← SchwartzMap.toLp_fourier_eq φ,
          MeasureTheory.Lp.norm_fourier_eq]
    _ = ∫⁻ x : Space, ENNReal.ofReal (‖(φ : Space → ℂ) x‖ ^ 2) :=
        (schwartz_lintegral_normSq _).symm

/-! ## §3  Translation phase and additivity of the angular transform -/

theorem angularFourier_translate (g : Space → ℂ) (h ξ : Space) :
    angularFourier (fun x => g (x + h)) ξ
      = Complex.exp (Complex.I * ((inner ℝ h ξ : ℝ) : ℂ)) * angularFourier g ξ := by
  have hsub : (fun x => g (x + h)) = (fun x => g (x - (-h))) := by
    funext x; rw [sub_neg_eq_add]
  have hP : (2 * Real.pi * -(inner ℝ (-h) (frequencyUnit⁻¹ • ξ)) : ℝ) = inner ℝ h ξ := by
    rw [inner_neg_left, inner_smul_right]
    unfold frequencyUnit
    field_simp [Real.pi_ne_zero]
  unfold angularFourier
  rw [hsub, fourier_translate, Circle.smul_def, Real.fourierChar_apply]
  simp only [smul_eq_mul, Complex.real_smul]
  rw [show ((2 * Real.pi * -(inner ℝ (-h) (frequencyUnit⁻¹ • ξ)) : ℝ) : ℂ)
        = ((inner ℝ h ξ : ℝ) : ℂ) from by rw [hP],
    mul_comm ((inner ℝ h ξ : ℝ) : ℂ) Complex.I]
  ring

theorem measurable_phase (ξ : Space) :
    Measurable (fun x : Space => Complex.exp (-((inner ℝ x ξ : ℝ) : ℂ) * Complex.I)) := by
  have : Measurable (fun x : Space => (inner ℝ x ξ : ℝ)) := (continuous_inner.comp
    (Continuous.prodMk continuous_id continuous_const)).measurable
  fun_prop

theorem norm_phase_le (ξ x : Space) :
    ‖Complex.exp (-((inner ℝ x ξ : ℝ) : ℂ) * Complex.I)‖ ≤ 1 := by
  rw [show -((inner ℝ x ξ : ℝ) : ℂ) * Complex.I = ((-(inner ℝ x ξ) : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.norm_exp_ofReal_mul_I]

theorem integrable_phase_mul {g : Space → ℂ} (hg : Integrable g) (ξ : Space) :
    Integrable (fun x => Complex.exp (-((inner ℝ x ξ : ℝ) : ℂ) * Complex.I) * g x) :=
  hg.bdd_mul (c := 1) (measurable_phase ξ).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => norm_phase_le ξ x))

theorem angularFourier_sub (g g' : Space → ℂ)
    (hg : Integrable g) (hg' : Integrable g') (ξ : Space) :
    angularFourier (fun x => g x - g' x) ξ
      = angularFourier g ξ - angularFourier g' ξ := by
  simp only [angularFourier_eq_integral, smul_eq_mul]
  rw [← smul_sub]
  congr 1
  rw [← integral_sub (integrable_phase_mul hg ξ) (integrable_phase_mul hg' ξ)]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

/-! ## §4  Componentwise per-shift Plancherel expansion -/

theorem contDiff_translate {f : SpatialField} (hzs : ContDiff ℝ ∞ f) (i : Fin 3) (h : Space) :
    ContDiff ℝ ∞ (fun x => ((f (x + h) i : ℝ) : ℂ)) :=
  (contDiff_component hzs i).comp (contDiff_id.add contDiff_const)

theorem hasCompactSupport_translate {f : SpatialField} (hzc : HasCompactSupport f) (i : Fin 3)
    (h : Space) : HasCompactSupport (fun x => ((f (x + h) i : ℝ) : ℂ)) :=
  (hasCompactSupport_component hzc i).comp_homeomorph (Homeomorph.addRight h)

theorem contDiff_diff {f : SpatialField} (hzs : ContDiff ℝ ∞ f) (i : Fin 3) (h : Space) :
    ContDiff ℝ ∞ (fun x => ((f (x + h) i : ℝ) : ℂ) - ((f x i : ℝ) : ℂ)) :=
  (contDiff_translate hzs i h).sub (contDiff_component hzs i)

theorem hasCompactSupport_diff {f : SpatialField} (hzc : HasCompactSupport f) (i : Fin 3)
    (h : Space) : HasCompactSupport (fun x => ((f (x + h) i : ℝ) : ℂ) - ((f x i : ℝ) : ℂ)) :=
  (hasCompactSupport_translate hzc i h).sub (hasCompactSupport_component hzc i)

/-- The angular transform of the shifted difference factors through the phase. -/
theorem angularFourier_diff {f : SpatialField} (hzs : ContDiff ℝ ∞ f) (hzc : HasCompactSupport f)
    (i : Fin 3) (h ξ : Space) :
    angularFourier (fun x => ((f (x + h) i : ℝ) : ℂ) - ((f x i : ℝ) : ℂ)) ξ
      = (Complex.exp (Complex.I * ((inner ℝ h ξ : ℝ) : ℂ)) - 1) *
          angularFourier (fun x => ((f x i : ℝ) : ℂ)) ξ := by
  rw [angularFourier_sub _ _
      ((contDiff_translate hzs i h).continuous.integrable_of_hasCompactSupport
        (hasCompactSupport_translate hzc i h))
      ((contDiff_component hzs i).continuous.integrable_of_hasCompactSupport
        (hasCompactSupport_component hzc i)) ξ,
    angularFourier_translate (fun x => ((f x i : ℝ) : ℂ)) h ξ]
  ring

/-- For each component and shift `h`, the physical square integral equals the
frequency-side phase-weighted energy (componentwise Plancherel). -/
theorem per_h_component {f : SpatialField} (hzs : ContDiff ℝ ∞ f) (hzc : HasCompactSupport f)
    (i : Fin 3) (h : Space) :
    (∫⁻ x : Space, ENNReal.ofReal (‖((f (x + h) i : ℝ) : ℂ) - ((f x i : ℝ) : ℂ)‖ ^ 2))
      = ∫⁻ ξ : Space, ENNReal.ofReal (
          ‖Complex.exp (Complex.I * ((inner ℝ h ξ : ℝ) : ℂ)) - 1‖ ^ 2 *
            ‖angularFourier (fun x => ((f x i : ℝ) : ℂ)) ξ‖ ^ 2) := by
  set φ : SchwartzMap Space ℂ :=
    NavierStokesR3.CompactSchwartz.ofCompactSupport
      (fun x => ((f (x + h) i : ℝ) : ℂ) - ((f x i : ℝ) : ℂ))
      (contDiff_diff hzs i h) (hasCompactSupport_diff hzc i h) with hφ
  have hcoe : (φ : Space → ℂ) = fun x => ((f (x + h) i : ℝ) : ℂ) - ((f x i : ℝ) : ℂ) := rfl
  calc (∫⁻ x : Space, ENNReal.ofReal (‖((f (x + h) i : ℝ) : ℂ) - ((f x i : ℝ) : ℂ)‖ ^ 2))
      = ∫⁻ x : Space, ENNReal.ofReal (‖(φ : Space → ℂ) x‖ ^ 2) := by rw [hcoe]
    _ = ∫⁻ ξ : Space, ENNReal.ofReal (‖angularFourier (φ : Space → ℂ) ξ‖ ^ 2) :=
        (lintegral_angularFourier_sq φ).symm
    _ = ∫⁻ ξ : Space, ENNReal.ofReal (
          ‖Complex.exp (Complex.I * ((inner ℝ h ξ : ℝ) : ℂ)) - 1‖ ^ 2 *
            ‖angularFourier (fun x => ((f x i : ℝ) : ℂ)) ξ‖ ^ 2) := by
        apply lintegral_congr
        intro ξ
        rw [hcoe, angularFourier_diff hzs hzc i h ξ, norm_mul, mul_pow]

/-! ## §5  Rotation + dilation evaluation of the phase kernel -/

/-- A measure-preserving rotation of `Space` sending `e₀` to a prescribed unit
vector `u`. -/
private theorem exists_rotation {u : Space} (hu : ‖u‖ = 1) :
    ∃ R : Space ≃ₗᵢ[ℝ] Space,
      R (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) = u ∧
      MeasurePreserving R volume volume := by
  classical
  have card_eq : Module.finrank ℝ Space = Fintype.card (Fin 3) := finrank_euclideanSpace
  have hon : Orthonormal ℝ (({0} : Set (Fin 3)).domRestrict (fun _ : Fin 3 => u)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subtype.ext (i.2.trans j.2.symm)
    subst hij
    have hval : (({0} : Set (Fin 3)).domRestrict (fun _ : Fin 3 => u)) i = u := rfl
    rw [hval, real_inner_self_eq_norm_sq, hu]
    simp
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq card_eq hon
  have hb0 : b 0 = u := hb 0 rfl
  refine ⟨b.repr.symm, ?_, b.measurePreserving_repr_symm⟩
  have hru : b.repr u = EuclideanSpace.single (0 : Fin 3) (1 : ℝ) := by
    rw [← hb0]; exact b.repr_self 0
  rw [← hru, LinearIsometryEquiv.symm_apply_apply]

/-- `paper/sections/03-torus.tex:49`: rotation and dilation identify the inner
phase integral with `c_s · ‖ξ‖^{2s}` for `ξ ≠ 0`. -/
theorem lintegral_kernel_smul (s : ℝ) {ξ : Space} (hξ : ξ ≠ 0) :
    (∫⁻ h : Space,
        ENNReal.ofReal (‖Complex.exp (Complex.I * ((inner ℝ h ξ : ℝ) : ℂ)) - 1‖ ^ 2) *
          fractionalRadialKernel s h)
      = cFrac s * ENNReal.ofReal (‖ξ‖ ^ (2 * s)) := by
  set r : ℝ := ‖ξ‖ with hr_def
  have hr : 0 < r := by rw [hr_def]; exact norm_pos_iff.mpr hξ
  set u : Space := r⁻¹ • ξ with hu_def
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), ← hr_def,
      inv_mul_cancel₀ hr.ne']
  have hξu : ξ = r • u := by
    rw [hu_def, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  obtain ⟨R, hR0, hRmp⟩ := exists_rotation hu
  have hinner : ∀ k : Space, (inner ℝ (R k) ξ : ℝ) = r * k 0 := by
    intro k
    rw [hξu, real_inner_smul_right, ← hR0, LinearIsometryEquiv.inner_map_map,
      EuclideanSpace.inner_single_right]
    simp
  have hnorm : ∀ k : Space, ‖R k‖ = ‖k‖ := fun k => R.norm_map k
  have hker : ∀ k : Space, fractionalRadialKernel s (R k) = fractionalRadialKernel s k := by
    intro k; unfold fractionalRadialKernel; rw [hnorm]
  have hkerscale : ∀ k : Space,
      fractionalRadialKernel s k
        = (ENNReal.ofReal r) ^ (3 + 2 * s) * fractionalRadialKernel s (r • k) := by
    intro k
    unfold fractionalRadialKernel
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, ENNReal.ofReal_mul hr.le,
      ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top, ← mul_assoc,
      ← ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top,
      add_neg_cancel, ENNReal.rpow_zero, one_mul]
  have hcoord : ∀ k : Space, (r • k) 0 = r * k 0 := by
    intro k; rw [PiLp.smul_apply, smul_eq_mul]
  set F : Space → ℝ≥0∞ := fun h =>
    ENNReal.ofReal (‖Complex.exp (Complex.I * ((inner ℝ h ξ : ℝ) : ℂ)) - 1‖ ^ 2) *
      fractionalRadialKernel s h with hF_def
  set Φ : Space → ℝ≥0∞ := fun m =>
    ENNReal.ofReal (‖Complex.exp (Complex.I * (m 0 : ℂ)) - 1‖ ^ 2) *
      fractionalRadialKernel s m with hΦ_def
  have hcFrac : cFrac s = ∫⁻ m, Φ m := rfl
  have hΦmeas : Measurable Φ := by
    rw [hΦ_def]; unfold fractionalRadialKernel; fun_prop
  have hAmeas : Measurable F := by
    rw [hF_def]; unfold fractionalRadialKernel; fun_prop
  have hfmeas : Measurable (fun k : Space => Φ (r • k)) :=
    hΦmeas.comp (measurable_const_smul r)
  have hpt : ∀ k : Space, F (R k) = (ENNReal.ofReal r) ^ (3 + 2 * s) * Φ (r • k) := by
    intro k
    simp only [hF_def]
    rw [hinner k, hker k, hkerscale k]
    simp only [hΦ_def, hcoord]
    ring
  have hmap : (∫⁻ k, Φ (r • k)) = ENNReal.ofReal ((r ^ 3)⁻¹) * ∫⁻ m, Φ m := by
    have h1 : (∫⁻ k, Φ (r • k) ∂volume)
        = ∫⁻ m, Φ m ∂(Measure.map (fun x : Space => r • x) volume) := by
      rw [lintegral_map hΦmeas (measurable_const_smul r)]
    rw [h1, Measure.map_addHaar_smul volume hr.ne', lintegral_smul_measure, smul_eq_mul]
    congr 2
    have hfr : Module.finrank ℝ Space = 3 := by simp [Space]
    rw [hfr, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (r ^ 3)⁻¹)]
  have hconst : (ENNReal.ofReal r) ^ (3 + 2 * s) * ENNReal.ofReal ((r ^ 3)⁻¹)
      = ENNReal.ofReal (r ^ (2 * s)) := by
    rw [ENNReal.ofReal_rpow_of_pos hr, ← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)]
    congr 1
    rw [← Real.rpow_natCast r 3, ← Real.rpow_neg hr.le, ← Real.rpow_add hr]
    norm_num
  calc (∫⁻ h, F h)
      = ∫⁻ k, F (R k) := (hRmp.lintegral_comp hAmeas).symm
    _ = ∫⁻ k, (ENNReal.ofReal r) ^ (3 + 2 * s) * Φ (r • k) := lintegral_congr hpt
    _ = (ENNReal.ofReal r) ^ (3 + 2 * s) * ∫⁻ k, Φ (r • k) := lintegral_const_mul _ hfmeas
    _ = (ENNReal.ofReal r) ^ (3 + 2 * s) * (ENNReal.ofReal ((r ^ 3)⁻¹) * ∫⁻ m, Φ m) := by
          rw [hmap]
    _ = (ENNReal.ofReal r) ^ (3 + 2 * s) * (ENNReal.ofReal ((r ^ 3)⁻¹) * cFrac s) := by
          rw [← hcFrac]
    _ = ((ENNReal.ofReal r) ^ (3 + 2 * s) * ENNReal.ofReal ((r ^ 3)⁻¹)) * cFrac s := by
          rw [← mul_assoc]
    _ = ENNReal.ofReal (r ^ (2 * s)) * cFrac s := by rw [hconst]
    _ = cFrac s * ENNReal.ofReal (r ^ (2 * s)) := mul_comm _ _

/-! ## §6  Assembling the whole-space Gagliardo/Fourier identity -/

theorem measurable_kernel (s : ℝ) : Measurable (fractionalRadialKernel s) := by
  unfold fractionalRadialKernel; fun_prop

/-- Continuity of `a ↦ exp(i·p a) - 1` from a continuous real slot `p`. -/
theorem continuous_phase {α : Type*} [TopologicalSpace α]
    {p : α → ℝ} (hp : Continuous p) :
    Continuous (fun a : α => Complex.exp (Complex.I * ((p a : ℝ) : ℂ)) - 1) :=
  (Complex.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_ofReal.comp hp))).sub continuous_const

theorem measurable_weightedSq (s : ℝ) {g : Space → ℂ} (hg : Continuous g) :
    Measurable (fun ξ : Space => ENNReal.ofReal (‖ξ‖ ^ (2 * s) * ‖g ξ‖ ^ 2)) := by
  have hm : Measurable (fun ξ : Space => ‖ξ‖ ^ (2 * s) * ‖g ξ‖ ^ 2) := by fun_prop
  exact ENNReal.measurable_ofReal.comp hm

/-- Continuity of `ξ ↦ angularFourier fᵢ ξ` for a smooth compactly supported field. -/
theorem continuous_angularFourier_component {f : SpatialField} (hzs : ContDiff ℝ ∞ f)
    (hzc : HasCompactSupport f) (i : Fin 3) :
    Continuous (fun ξ => angularFourier (fun x => ((f x i : ℝ) : ℂ)) ξ) := by
  have heq : (fun ξ => angularFourier (fun x => ((f x i : ℝ) : ℂ)) ξ)
      = ⇑(schwartzAngularFourier (compactSchwartzComponents hzs hzc i)) := by
    funext ξ
    exact (schwartzAngularFourier_apply (compactSchwartzComponents hzs hzc i) ξ).symm
  rw [heq]
  exact (schwartzAngularFourier (compactSchwartzComponents hzs hzc i)).continuous

/-- The Euclidean square-norm as a sum of the three component square-norms. -/
theorem ofReal_normSq_eq_sum (u v : Space) :
    ENNReal.ofReal (‖u - v‖ ^ 2)
      = ∑ i : Fin 3, ENNReal.ofReal (‖((u i : ℝ) : ℂ) - ((v i : ℝ) : ℂ)‖ ^ 2) := by
  have hn : ‖u - v‖ ^ 2 = ∑ i : Fin 3, ‖((u i : ℝ) : ℂ) - ((v i : ℝ) : ℂ)‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have : (u - v) i = u i - v i := rfl
    rw [this, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hn, ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]

/-- The per-component double integral evaluates to `c_s` times the weighted
frequency energy of that component. -/
theorem component_integral_eq
    {s : ℝ} {f : SpatialField} (hzs : ContDiff ℝ ∞ f) (hzc : HasCompactSupport f) (i : Fin 3) :
    (∫⁻ h : Space, ∫⁻ x : Space,
        ENNReal.ofReal (‖((f (x + h) i : ℝ) : ℂ) - ((f x i : ℝ) : ℂ)‖ ^ 2)
          * fractionalRadialKernel s h)
      = cFrac s * ∫⁻ ξ : Space, ENNReal.ofReal (‖ξ‖ ^ (2 * s) *
          ‖angularFourier (fun x => ((f x i : ℝ) : ℂ)) ξ‖ ^ 2) := by
  have hKm : Measurable (fractionalRadialKernel s) := measurable_kernel s
  have hfc : Continuous f := hzs.continuous
  obtain ⟨aF, haFc, haF⟩ :
      ∃ aF : Space → ℂ, Continuous aF ∧
        ∀ ξ, angularFourier (fun x => ((f x i : ℝ) : ℂ)) ξ = aF ξ :=
    ⟨_, continuous_angularFourier_component hzs hzc i, fun _ => rfl⟩
  have hmx : ∀ h : Space, Measurable (fun x : Space =>
      ENNReal.ofReal (‖((f (x + h) i : ℝ) : ℂ) - ((f x i : ℝ) : ℂ)‖ ^ 2)) := by
    intro h
    have hc1 : Continuous (fun x : Space => f (x + h)) :=
      hfc.comp (continuous_id.add continuous_const)
    have hcΔ : Continuous (fun x : Space => ((f (x + h) i : ℝ) : ℂ) - ((f x i : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.comp ((EuclideanSpace.proj i).continuous.comp hc1)).sub
        (Complex.continuous_ofReal.comp ((EuclideanSpace.proj i).continuous.comp hfc))
    exact ENNReal.measurable_ofReal.comp (hcΔ.norm.pow 2).measurable
  have hmξ : ∀ h : Space, Measurable (fun ξ : Space =>
      ENNReal.ofReal (‖Complex.exp (Complex.I * ((inner ℝ h ξ : ℝ) : ℂ)) - 1‖ ^ 2 *
        ‖aF ξ‖ ^ 2)) := by
    intro h
    have hin : Continuous (fun ξ : Space => (inner ℝ h ξ : ℝ)) :=
      continuous_const.inner continuous_id
    exact ENNReal.measurable_ofReal.comp
      (((continuous_phase hin).norm.pow 2).mul (haFc.norm.pow 2)).measurable
  have hJ2 : Measurable (Function.uncurry (fun h ξ : Space =>
      ENNReal.ofReal (‖Complex.exp (Complex.I * ((inner ℝ h ξ : ℝ) : ℂ)) - 1‖ ^ 2 *
        ‖aF ξ‖ ^ 2) * fractionalRadialKernel s h)) := by
    have hin : Continuous (fun p : Space × Space => (inner ℝ p.1 p.2 : ℝ)) := continuous_inner
    have haFsnd : Continuous (fun p : Space × Space => aF p.2) := haFc.comp continuous_snd
    have hnum : Continuous (fun p : Space × Space =>
        ‖Complex.exp (Complex.I * ((inner ℝ p.1 p.2 : ℝ) : ℂ)) - 1‖ ^ 2 * ‖aF p.2‖ ^ 2) :=
      ((continuous_phase hin).norm.pow 2).mul (haFsnd.norm.pow 2)
    exact (ENNReal.measurable_ofReal.comp hnum.measurable).mul (hKm.comp measurable_fst)
  have hM4 : ∀ ξ : Space, Measurable (fun h : Space =>
      ENNReal.ofReal (‖Complex.exp (Complex.I * ((inner ℝ h ξ : ℝ) : ℂ)) - 1‖ ^ 2)
        * fractionalRadialKernel s h) := by
    intro ξ
    have hin : Continuous (fun h : Space => (inner ℝ h ξ : ℝ)) :=
      continuous_id.inner continuous_const
    exact (ENNReal.measurable_ofReal.comp ((continuous_phase hin).norm.pow 2).measurable).mul hKm
  have hMfinal : Measurable (fun ξ : Space => ENNReal.ofReal (‖ξ‖ ^ (2 * s) * ‖aF ξ‖ ^ 2)) :=
    measurable_weightedSq s haFc
  simp only [haF]
  calc (∫⁻ h : Space, ∫⁻ x : Space,
        ENNReal.ofReal (‖((f (x + h) i : ℝ) : ℂ) - ((f x i : ℝ) : ℂ)‖ ^ 2)
          * fractionalRadialKernel s h)
      = ∫⁻ h : Space, (∫⁻ x : Space,
          ENNReal.ofReal (‖((f (x + h) i : ℝ) : ℂ) - ((f x i : ℝ) : ℂ)‖ ^ 2))
            * fractionalRadialKernel s h := by
        apply lintegral_congr; intro h; rw [lintegral_mul_const _ (hmx h)]
    _ = ∫⁻ h : Space, (∫⁻ ξ : Space,
          ENNReal.ofReal (‖Complex.exp (Complex.I * ((inner ℝ h ξ : ℝ) : ℂ)) - 1‖ ^ 2 *
            ‖aF ξ‖ ^ 2)) * fractionalRadialKernel s h := by
        apply lintegral_congr; intro h
        rw [per_h_component hzs hzc i h]; simp only [haF]
    _ = ∫⁻ h : Space, ∫⁻ ξ : Space,
          ENNReal.ofReal (‖Complex.exp (Complex.I * ((inner ℝ h ξ : ℝ) : ℂ)) - 1‖ ^ 2 *
            ‖aF ξ‖ ^ 2) * fractionalRadialKernel s h := by
        apply lintegral_congr; intro h; rw [lintegral_mul_const _ (hmξ h)]
    _ = ∫⁻ ξ : Space, ∫⁻ h : Space,
          ENNReal.ofReal (‖Complex.exp (Complex.I * ((inner ℝ h ξ : ℝ) : ℂ)) - 1‖ ^ 2 *
            ‖aF ξ‖ ^ 2) * fractionalRadialKernel s h :=
        lintegral_lintegral_swap hJ2.aemeasurable
    _ = ∫⁻ ξ : Space, cFrac s * ENNReal.ofReal (‖ξ‖ ^ (2 * s) * ‖aF ξ‖ ^ 2) := by
        apply lintegral_congr_ae
        filter_upwards [ae_ne_zero] with ξ hξ
        have hsplit : ∀ h : Space,
            ENNReal.ofReal (‖Complex.exp (Complex.I * ((inner ℝ h ξ : ℝ) : ℂ)) - 1‖ ^ 2 *
              ‖aF ξ‖ ^ 2) * fractionalRadialKernel s h
              = (ENNReal.ofReal (‖Complex.exp (Complex.I * ((inner ℝ h ξ : ℝ) : ℂ)) - 1‖ ^ 2)
                  * fractionalRadialKernel s h) * ENNReal.ofReal (‖aF ξ‖ ^ 2) := by
          intro h; rw [ENNReal.ofReal_mul (by positivity)]; ring
        simp_rw [hsplit]
        rw [lintegral_mul_const _ (hM4 ξ), lintegral_kernel_smul s hξ,
          ENNReal.ofReal_mul (by positivity), mul_assoc]
    _ = cFrac s * ∫⁻ ξ : Space, ENNReal.ofReal (‖ξ‖ ^ (2 * s) * ‖aF ξ‖ ^ 2) :=
        lintegral_const_mul _ hMfinal

/-- The whole-space Gagliardo integral decomposes over the three components. -/
theorem IReal_decomp {s : ℝ} {f : SpatialField} (hzs : ContDiff ℝ ∞ f) :
    IReal s f = ∑ i : Fin 3, ∫⁻ h : Space, ∫⁻ x : Space,
        ENNReal.ofReal (‖((f (x + h) i : ℝ) : ℂ) - ((f x i : ℝ) : ℂ)‖ ^ 2)
          * fractionalRadialKernel s h := by
  have hfc : Continuous f := hzs.continuous
  have hKm : Measurable (fractionalRadialKernel s) := measurable_kernel s
  have hJ1 : ∀ i : Fin 3, Measurable (Function.uncurry (fun h x : Space =>
      ENNReal.ofReal (‖((f (x + h) i : ℝ) : ℂ) - ((f x i : ℝ) : ℂ)‖ ^ 2)
        * fractionalRadialKernel s h)) := by
    intro i
    have hcphx : Continuous (fun p : Space × Space => f (p.2 + p.1)) :=
      hfc.comp (continuous_snd.add continuous_fst)
    have hcpx : Continuous (fun p : Space × Space => f p.2) := hfc.comp continuous_snd
    have hcΔp : Continuous (fun p : Space × Space =>
        ((f (p.2 + p.1) i : ℝ) : ℂ) - ((f p.2 i : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.comp ((EuclideanSpace.proj i).continuous.comp hcphx)).sub
        (Complex.continuous_ofReal.comp ((EuclideanSpace.proj i).continuous.comp hcpx))
    exact (ENNReal.measurable_ofReal.comp (hcΔp.norm.pow 2).measurable).mul
      (hKm.comp measurable_fst)
  have hmx : ∀ (h : Space) (i : Fin 3), Measurable (fun x : Space =>
      ENNReal.ofReal (‖((f (x + h) i : ℝ) : ℂ) - ((f x i : ℝ) : ℂ)‖ ^ 2)
        * fractionalRadialKernel s h) := by
    intro h i
    have hc1 : Continuous (fun x : Space => f (x + h)) :=
      hfc.comp (continuous_id.add continuous_const)
    have hcΔ : Continuous (fun x : Space => ((f (x + h) i : ℝ) : ℂ) - ((f x i : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.comp ((EuclideanSpace.proj i).continuous.comp hc1)).sub
        (Complex.continuous_ofReal.comp ((EuclideanSpace.proj i).continuous.comp hfc))
    exact (ENNReal.measurable_ofReal.comp (hcΔ.norm.pow 2).measurable).mul measurable_const
  calc IReal s f
      = ∫⁻ h : Space, ∫⁻ x : Space, ∑ i : Fin 3,
          ENNReal.ofReal (‖((f (x + h) i : ℝ) : ℂ) - ((f x i : ℝ) : ℂ)‖ ^ 2)
            * fractionalRadialKernel s h := by
        unfold IReal
        apply lintegral_congr; intro h; apply lintegral_congr; intro x
        rw [ofReal_normSq_eq_sum (f (x + h)) (f x), Finset.sum_mul]
    _ = ∫⁻ h : Space, ∑ i : Fin 3, ∫⁻ x : Space,
          ENNReal.ofReal (‖((f (x + h) i : ℝ) : ℂ) - ((f x i : ℝ) : ℂ)‖ ^ 2)
            * fractionalRadialKernel s h := by
        apply lintegral_congr; intro h
        rw [lintegral_finsetSum _ (fun i _ => hmx h i)]
    _ = ∑ i : Fin 3, ∫⁻ h : Space, ∫⁻ x : Space,
          ENNReal.ofReal (‖((f (x + h) i : ℝ) : ℂ) - ((f x i : ℝ) : ℂ)‖ ^ 2)
            * fractionalRadialKernel s h :=
        lintegral_finsetSum _ (fun i _ => (hJ1 i).lintegral_prod_right)

set_option maxHeartbeats 400000 in
/-- The whole-space Gagliardo integral equals `c_s` times the squared homogeneous
Fourier quantity, for smooth compactly supported fields. -/
theorem IReal_eq_cFrac_mul_homogeneousFourierENorm_sq
    {s : ℝ} {f : SpatialField} (hzs : ContDiff ℝ ∞ f) (hzc : HasCompactSupport f) :
    IReal s f = cFrac s * homogeneousFourierENorm s f ^ (2 : ℕ) := by
  have hstep : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      (∫⁻ h : Space, ∫⁻ x : Space,
          ENNReal.ofReal (‖((f (x + h) i : ℝ) : ℂ) - ((f x i : ℝ) : ℂ)‖ ^ 2)
            * fractionalRadialKernel s h)
        = cFrac s * ∫⁻ ξ : Space, ENNReal.ofReal (‖ξ‖ ^ (2 * s) *
            ‖angularFourier (fun x => ((f x i : ℝ) : ℂ)) ξ‖ ^ 2) :=
    fun i _ => component_integral_eq hzs hzc i
  rw [IReal_decomp hzs, Finset.sum_congr rfl hstep, ← Finset.mul_sum,
    ← homogeneousFourierENorm_sq]

/-! ## §7  The `LocalizationAPI.wholeSpace_identity` field, verbatim -/

/-- `LocalizationAPI.wholeSpace_identity`, `03-torus.tex:40-51`. -/
theorem wholeSpace_identity :
    ∀ (s : ℝ), 0 < s → s < 1 → ∀ f : SpatialField,
      ContDiff ℝ ∞ f → HasCompactSupport f →
        IReal s f < ⊤ ∧
          IReal s f = cFrac s * dotHomogeneousENorm s f ^ (2 : ℕ) := by
  intro s hs0 hs1 f hzs hzc
  have hs : -3 / 2 < s := by linarith
  have hdot : dotHomogeneousENorm s f = homogeneousFourierENorm s f :=
    dotHomogeneousENorm_eq_homogeneousFourierENorm hs hzs hzc
  have hEq : IReal s f = cFrac s * homogeneousFourierENorm s f ^ (2 : ℕ) :=
    IReal_eq_cFrac_mul_homogeneousFourierENorm_sq hzs hzc
  refine ⟨?_, ?_⟩
  · rw [hEq]
    have hc : cFrac s < ⊤ := (constant_pos_finite s hs0 hs1).2
    have hn : homogeneousFourierENorm s f < ⊤ := homogeneousFourierENorm_lt_top hs hzs hzc
    exact ENNReal.mul_lt_top hc (lt_top_iff_ne_top.mpr (ENNReal.pow_ne_top hn.ne))
  · rw [hEq, hdot]

end NSFormalization.Section3.T13
