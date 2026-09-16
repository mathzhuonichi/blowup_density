import NSFormalization.Source.AngularForceNorms
import NSFormalization.Paper1.CorrectionForceNorms
import NSFormalization.Source.VectorForceNorms
import NSFormalization.Source.TimeNormScaling
import NSFormalization.Paper3.HomogeneousTime
import NSFormalization.Section4.D01.HomogeneousNorm

/-!
# Exact homogeneous force scaling

The scalar Fourier identities use Mathlib's cycles convention. They hold for
all real orders as identities of totalized integrals; finiteness is supplied
separately for compact smooth profiles at `-3/2 < s ≤ 0`.
The physical amplitude is `k³`, with `k = ε⁻¹`.
-/
noncomputable section
namespace NSFormalization.Section4.I03
open NavierStokes.ProblemStatement MeasureTheory
open NSFormalization.Source
open scoped FourierTransform ENNReal ContDiff

/-- Exact change of frequency variables for the homogeneous squared norm. -/
theorem homogeneous_integral_concentrated (s : ℝ) (f : Space → ℂ)
    {k : ℝ} (hk : 0 < k) :
    (∫ ξ : Space, ‖ξ‖ ^ (2 * s) * ‖𝓕 (concentratedForce k f) ξ‖ ^ 2) =
      k ^ (3 + 2 * s) * (∫ ξ : Space, ‖ξ‖ ^ (2 * s) * ‖𝓕 f ξ‖ ^ 2) := by
  simp_rw [fourier_concentratedForce f k hk]
  let G : Space → ℝ := fun ξ => ‖k • ξ‖ ^ (2 * s) * ‖𝓕 f ξ‖ ^ 2
  have he (ξ : Space) : G (k⁻¹ • ξ) =
      ‖ξ‖ ^ (2 * s) * ‖𝓕 f (k⁻¹ • ξ)‖ ^ 2 := by
    simp [G, smul_smul, hk.ne']
  simp_rw [← he]
  rw [Measure.integral_comp_smul_of_nonneg volume G k⁻¹ (hR := (inv_pos.mpr hk).le)]
  simp only [finrank_euclideanSpace, Fintype.card_fin, inv_pow, inv_inv, smul_eq_mul]
  have hG : G = fun ξ => k ^ (2 * s) * (‖ξ‖ ^ (2 * s) * ‖𝓕 f ξ‖ ^ 2) := by
    funext ξ
    dsimp [G]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hk,
      Real.mul_rpow hk.le (norm_nonneg ξ), mul_assoc]
  rw [hG, integral_const_mul, ← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hk]
  norm_num

/-- Spatial homogeneous scaling, including negative orders. -/
theorem homogeneous_norm_concentrated (s : ℝ) (f : Space → ℂ)
    {k : ℝ} (hk : 0 < k) :
    homogeneousFourierNorm s (concentratedForce k f) =
      k ^ (3 / 2 + s) * homogeneousFourierNorm s f := by
  unfold homogeneousFourierNorm
  rw [homogeneous_integral_concentrated s f hk, sqrt_rpow_energy hk]

/-- Exact time scaling on the whole real axis, for every `q`, including infinity. -/
theorem homogeneous_time_scaling (s : ℝ) (f : ℝ → Space → ℂ)
    {k : ℝ} (hk : 0 < k) (t₀ : ℝ) (q : ℝ≥0∞)
    (ht : StronglyMeasurable (fun t => homogeneousFourierNorm s (f t))) :
    eLpNorm (fun t => homogeneousFourierNorm s (parabolicComplexForce k t₀ f t)) q volume =
      ENNReal.ofReal (k ^ (3 / 2 + s - 2 / q.toReal)) *
        eLpNorm (fun t => homogeneousFourierNorm s (f t)) q volume := by
  simp_rw [parabolicComplexForce, homogeneous_norm_concentrated s _ hk]
  rw [show (fun t => k ^ (3 / 2 + s) * homogeneousFourierNorm s (f (k ^ 2 * (t - t₀)))) =
    k ^ (3 / 2 + s) • (fun t => homogeneousFourierNorm s (f (k ^ 2 * (t - t₀)))) from rfl,
    eLpNorm_const_smul, eLpNorm_parabolic_time _ ht q hk t₀]
  rw [← mul_assoc, Real.enorm_eq_ofReal_abs,
    abs_of_pos (Real.rpow_pos_of_pos hk _),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hk.le _), ← Real.rpow_add hk]
  congr 3
  ring

/-- The paper's packet exponent `β(q,s) = 2/q - 3/2 - s`. -/
theorem homogeneous_time_scaling_epsilon (s : ℝ) (f : ℝ → Space → ℂ)
    {ε : ℝ} (hε : 0 < ε) (t₀ : ℝ) (q : ℝ≥0∞)
    (ht : StronglyMeasurable (fun t => homogeneousFourierNorm s (f t))) :
    eLpNorm (fun t => homogeneousFourierNorm s (parabolicComplexForce ε⁻¹ t₀ f t)) q volume =
      ENNReal.ofReal (ε ^ (2 / q.toReal - 3 / 2 - s)) *
        eLpNorm (fun t => homogeneousFourierNorm s (f t)) q volume := by
  rw [homogeneous_time_scaling s f (inv_pos.mpr hε) t₀ q ht]
  congr 2
  rw [Real.inv_rpow hε.le, ← Real.rpow_neg hε.le]
  congr 1
  ring

/-- The constant on the right of the exact identity is finite for compact
smooth spacetime profiles in the negative-order finiteness range. -/
theorem homogeneous_profile_finite {s : ℝ} (hs : -3 / 2 < s) (hs0 : s ≤ 0)
    {F : ℝ × Space → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (q : ℝ≥0∞) :
    eLpNorm (fun t => homogeneousFourierNorm s (fun x => F (t, x))) q volume ≠ ⊤ :=
  (NSFormalization.Paper3.memLp_homogeneousFourier_time hs hs0 hF hc q).eLpNorm_ne_top

/-- Homogeneous norms respect real nonnegative amplitudes. -/
theorem homogeneous_norm_smul (s : ℝ) (f : Space → ℂ) {a : ℝ} (ha : 0 ≤ a) :
    homogeneousFourierNorm s (fun x => a • f x) = a * homogeneousFourierNorm s f := by
  have hF (ξ : Space) : 𝓕 (fun x => a • f x) ξ = a • 𝓕 f ξ := by
    simp only [Real.fourier_eq, smul_comm _ a, integral_smul]
  unfold homogeneousFourierNorm
  simp_rw [hF, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, mul_pow]
  have he : (∫ ξ : Space, ‖ξ‖ ^ (2 * s) * (a ^ 2 * ‖𝓕 f ξ‖ ^ 2)) =
      a ^ 2 * ∫ ξ : Space, ‖ξ‖ ^ (2 * s) * ‖𝓕 f ξ‖ ^ 2 := by
    rw [← integral_const_mul]
    congr 1
    funext ξ
    ring
  rw [he, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]

open Set NSFormalization.Paper1.CorrectionForceNorms

/-- The actual correction force, with a uniform finite homogeneous profile
constant. This is the homogeneous counterpart of the existing inhomogeneous
`scalarPhysicalForce_uniform_negative_time`. -/
theorem correction_scalar_homogeneous (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (i : Fin 3)
    {s : ℝ} (hs : -3 / 2 < s) (hs0 : s ≤ 0) (q : ℝ≥0∞) :
    ∃ C : ℝ≥0∞, C < (⊤ : ℝ≥0∞) ∧ ∀ ε ∈ Ioc (0 : ℝ) 1,
      eLpNorm (fun t => homogeneousFourierNorm s
        (fun x => scalarPhysicalForce ν v x₀ T θ η i ε (t, x))) q volume ≤
      ENNReal.ofReal (ε ^ (2 / q.toReal - 1 / 2 - s)) * C := by
  obtain ⟨C, hC, hb⟩ := scalarProfile_uniform_homogeneous_time ν hv x₀ T hθ hη hθc hηc i hs hs0 q
  refine ⟨C, hC, ?_⟩
  intro ε hε
  let F : SpaceTime → ℂ := fun z => scalarProfile ν v x₀ T θ η i (ε, z)
  have hF : ContDiff ℝ ∞ F :=
    (scalarProfile_smooth ν hv x₀ T hθ hη i).comp (contDiff_const.prodMk contDiff_id)
  have hscale := homogeneous_time_scaling_epsilon s (fun t x => F (t, x)) hε.1 T q
    (Paper3.stronglyMeasurable_homogeneousFourier_time s hF.continuous)
  have heq : (fun t => homogeneousFourierNorm s
      (fun x => scalarPhysicalForce ν v x₀ T θ η i ε (t, x))) =
      ε • (fun t => homogeneousFourierNorm s
        (parabolicComplexForce ε⁻¹ T (fun σ z => F (σ, z)) t)) := by
    funext t
    rw [scalarPhysicalForce_eq ν hv x₀ T ε hε.1 hθ hη i t,
      homogeneous_norm_smul s _ hε.1.le, homogeneousFourierNorm_translate]
    rfl
  rw [heq, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_pos hε.1, hscale]
  calc
    _ ≤ ENNReal.ofReal ε * (ENNReal.ofReal (ε ^ (2 / q.toReal - 3 / 2 - s)) * C) :=
      mul_le_mul_right (mul_le_mul_right (hb ε ⟨hε.1.le, hε.2⟩).2 _) _
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hε.1.le]
      congr 2
      conv_lhs => arg 1; rw [← Real.rpow_one ε]
      rw [← Real.rpow_add hε.1]
      congr 1
      ring

/-- Sum of the three component profile time norms; a finite explicit constant. -/
def componentTimeNorm (q : ℝ≥0∞) (s : ℝ) (F : VelocityField) : ℝ≥0∞ :=
  ∑ i : Fin 3, eLpNorm (fun t => homogeneousFourierNorm s
    (fun x => coordinateForce F i (t, x))) q volume

/-- Translation does not affect any component homogeneous norm. -/
theorem componentTimeNorm_packet (q : ℝ≥0∞) (s : ℝ) {F : VelocityField}
    (hF : ContDiff ℝ ∞ F) {ε : ℝ} (hε : 0 < ε) (t₀ : ℝ) (x₀ : Space) :
    componentTimeNorm q s (parabolicForce ε⁻¹ t₀ x₀ F) =
      ENNReal.ofReal (ε ^ (2 / q.toReal - 3 / 2 - s)) * componentTimeNorm q s F := by
  unfold componentTimeNorm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [coordinate_parabolicForce, homogeneousFourierNorm_translate]
  exact homogeneous_time_scaling_epsilon s _ hε t₀ q
    (Paper3.stronglyMeasurable_homogeneousFourier_time s (coordinateForce_smooth hF i).continuous)

/-- Finiteness holds for the actual packet as soon as its recorded smoothness
and compact support are supplied. -/
theorem componentTimeNorm_finite (q : ℝ≥0∞) {s : ℝ} (hs : -3 / 2 < s) (hs0 : s ≤ 0)
    {F : VelocityField} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    componentTimeNorm q s F ≠ ⊤ :=
  ENNReal.sum_ne_top.mpr fun i _ => homogeneous_profile_finite hs hs0
    (coordinateForce_smooth hF i) (coordinateForce_compact hc i) q

/-- Summing the actual correction components keeps the extra power of epsilon. -/
theorem correction_componentTimeNorm (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    {s : ℝ} (hs : -3 / 2 < s) (hs0 : s ≤ 0) (q : ℝ≥0∞) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ ε ∈ Ioc (0 : ℝ) 1,
      componentTimeNorm q s (Source.correctionForce ν v
        (Paper1.CorrectionProfile.physicalCorrection v x₀ T θ η ε)) ≤
      ENNReal.ofReal (ε ^ (2 / q.toReal - 1 / 2 - s)) * C := by
  have hi (i : Fin 3) := correction_scalar_homogeneous ν hv x₀ T hθ hη hθc hηc i hs hs0 q
  choose C hC hb using hi
  refine ⟨∑ i, C i, ENNReal.sum_ne_top.mpr (fun i _ => (hC i).ne), ?_⟩
  intro ε hε
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => hb i ε hε)

/-- Exact conversion from cycles to unitary angular homogeneous energy. -/
theorem angular_homogeneous_integral (s : ℝ) (f : Space → ℂ) :
    (∫ ξ : Space, ‖ξ‖ ^ (2 * s) * ‖angularFourier f ξ‖ ^ 2) =
      frequencyUnit ^ (2 * s) * (∫ ξ : Space, ‖ξ‖ ^ (2 * s) * ‖𝓕 f ξ‖ ^ 2) := by
  have hfirst : (∫ ξ : Space, ‖ξ‖ ^ (2 * s) * ‖angularFourier f ξ‖ ^ 2) =
      (frequencyUnit ^ (-3 / 2 : ℝ)) ^ 2 *
        (∫ ξ : Space, ‖ξ‖ ^ (2 * s) * ‖𝓕 (concentratedForce frequencyUnit f) ξ‖ ^ 2) := by
    unfold angularFourier
    simp_rw [fourier_concentratedForce f frequencyUnit frequencyUnit_pos,
      norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [← integral_const_mul]
    congr 1
    funext ξ
    ring
  rw [hfirst, homogeneous_integral_concentrated s f frequencyUnit_pos, ← mul_assoc]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul frequencyUnit_pos.le,
    ← Real.rpow_add frequencyUnit_pos]
  congr 1
  ring

open D01.Homogeneous

/-- The homogeneous datum has exactly the angular component norm. -/
theorem norm_homogeneousDatum_cycles {s : ℝ} (hs : -3 / 2 < s)
    (φ : SchwartzMap Space ℂ) :
    ‖homogeneousDatum hs φ‖ = frequencyUnit ^ s * homogeneousFourierNorm s (φ : Space → ℂ) := by
  have hint : Integrable (fun ξ : Space => ‖ξ‖ ^ (2 * s) *
      ‖angularFourier (φ : Space → ℂ) ξ‖ ^ 2) :=
    integrable_homogeneous_schwartz hs (schwartzAngularFourier φ)
  have he := enorm_homogeneousDatum_sq hs φ
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall
    (fun ξ => mul_nonneg (Real.rpow_nonneg (norm_nonneg ξ) _) (sq_nonneg _)))] at he
  have he' := congrArg ENNReal.toReal he
  simp only [← ENNReal.toReal_rpow, toReal_enorm,
    ENNReal.toReal_ofReal (integral_nonneg (fun ξ =>
      mul_nonneg (Real.rpow_nonneg (norm_nonneg ξ) _) (sq_nonneg _)))] at he'
  rw [angular_homogeneous_integral] at he'
  have hn := congrArg Real.sqrt he'
  rw [Real.rpow_two, Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_mul (Real.rpow_nonneg frequencyUnit_pos.le _), Real.sqrt_eq_rpow,
    ← Real.rpow_mul frequencyUnit_pos.le] at hn
  convert hn using 1
  congr 2
  ring

/-- Exact spatial scaling at the level of homogeneous vector data. `A` and `B`
are genuine data of the two physical slices, not inhomogeneous substitutes. -/
theorem homogeneous_vector_datum_scaling {s : ℝ} (hs : -3 / 2 < s)
    {F : VelocityField} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    {k : ℝ} (hk : 0 < k) (t₀ : ℝ) (x₀ : Space) (t : ℝ)
    (A B : Paper3.RealVectorSobolev s)
    (hA : IsHomogeneousSliceDatum s (fun x => parabolicForce k t₀ x₀ F (t, x)) A)
    (hB : IsHomogeneousSliceDatum s (fun x => F (k ^ 2 * (t - t₀), x)) B) :
    ‖A‖ = k ^ (3 / 2 + s) * ‖B‖ := by
  let Fs := parabolicForce k t₀ x₀ F
  have hFs := Source.parabolicForce_smooth k t₀ x₀ hF
  have hFcs := Source.parabolicForce_compact k t₀ x₀ hc
  let As := compactHomogeneousPath hs hFs hFcs t
  let Bs := compactHomogeneousPath hs hF hc (k ^ 2 * (t - t₀))
  have hAs : IsHomogeneousSliceDatum s (fun x => Fs (t, x)) As :=
    isHomogeneousSliceDatum_schwartz hs _ _ (fun _ _ => rfl) _
  have hBs : IsHomogeneousSliceDatum s (fun x => F (k ^ 2 * (t - t₀), x)) Bs :=
    isHomogeneousSliceDatum_schwartz hs _ _ (fun _ _ => rfl) _
  have heA := isHomogeneousSliceDatum_unique hA hAs
  have heB := isHomogeneousSliceDatum_unique hB hBs
  rw [heA, heB]
  have hcomp (i : Fin 3) : ‖As i‖ = k ^ (3 / 2 + s) * ‖Bs i‖ := by
    have ha : ‖As i‖ = frequencyUnit ^ s *
        homogeneousFourierNorm s (fun x => coordinateForce Fs i (t, x)) :=
      norm_homogeneousDatum_cycles hs _
    have hb : ‖Bs i‖ = frequencyUnit ^ s * homogeneousFourierNorm s
        (fun x => coordinateForce F i (k ^ 2 * (t - t₀), x)) :=
      norm_homogeneousDatum_cycles hs _
    rw [ha, hb]
    dsimp [Fs]
    rw [coordinate_parabolicForce, homogeneousFourierNorm_translate]
    rw [parabolicComplexForce, homogeneous_norm_concentrated s _ hk]
    ring
  have hsqA := PiLp.norm_sq_eq_of_L2
    (fun _ : Fin 3 => Source.RealSobolev.RealSobolevHilbert s) As
  have hsqB := PiLp.norm_sq_eq_of_L2
    (fun _ : Fin 3 => Source.RealSobolev.RealSobolevHilbert s) Bs
  simp_rw [hcomp, mul_pow] at hsqA
  rw [← Finset.mul_sum, ← hsqB] at hsqA
  apply (sq_eq_sq₀ (norm_nonneg As)
    (mul_nonneg (Real.rpow_nonneg hk.le _) (norm_nonneg Bs))).mp
  simpa only [mul_pow] using hsqA

/-- A pointwise component bound for the concrete compact homogeneous path.
Only measurability of this path remains to lift it to the time infimum. -/
theorem compactHomogeneousPath_norm_le {s : ℝ} (hs : -3 / 2 < s) {F : VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (t : ℝ) :
    ‖compactHomogeneousPath hs hF hc t‖ ≤ frequencyUnit ^ s *
      ∑ i : Fin 3, homogeneousFourierNorm s (fun x => coordinateForce F i (t, x)) := by
  let A := compactHomogeneousPath hs hF hc t
  have hcomp (i : Fin 3) : ‖A i‖ = frequencyUnit ^ s *
      homogeneousFourierNorm s (fun x => coordinateForce F i (t, x)) :=
    norm_homogeneousDatum_cycles hs _
  have hsq := PiLp.norm_sq_eq_of_L2
    (fun _ : Fin 3 => Source.RealSobolev.RealSobolevHilbert s) A
  have hsum := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    (f := fun i : Fin 3 => ‖A i‖) (fun i _ => norm_nonneg _)
  have hle : ‖A‖ ≤ ∑ i : Fin 3, ‖A i‖ := by
    nlinarith [norm_nonneg A, Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => norm_nonneg (A i))]
  simpa only [hcomp, ← Finset.mul_sum] using hle

/-- Slice validity holds at every time, including the inactive past. -/
theorem compactHomogeneousPath_slice {s : ℝ} (hs : -3 / 2 < s) {F : VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (t : ℝ) :
    IsHomogeneousSliceDatum s (fun x => F (t, x)) (compactHomogeneousPath hs hF hc t) :=
  isHomogeneousSliceDatum_schwartz hs _ _ (fun _ _ => rfl) _

/-- Norm measurability is weaker than datum-path measurability and is already
available from the component Fourier integrals. -/
theorem compactHomogeneousPath_norm_stronglyMeasurable {s : ℝ} (hs : -3 / 2 < s)
    {F : VelocityField} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    StronglyMeasurable (fun t => ‖compactHomogeneousPath hs hF hc t‖) := by
  have he : (fun t => ‖compactHomogeneousPath hs hF hc t‖) = fun t =>
      Real.sqrt (∑ i : Fin 3, (frequencyUnit ^ s *
        homogeneousFourierNorm s (fun x => coordinateForce F i (t, x))) ^ 2) := by
    funext t
    have hh := PiLp.norm_sq_eq_of_L2
      (fun _ : Fin 3 => Source.RealSobolev.RealSobolevHilbert s)
      (compactHomogeneousPath hs hF hc t)
    have hi (i : Fin 3) : ‖compactHomogeneousPath hs hF hc t i‖ = frequencyUnit ^ s *
        homogeneousFourierNorm s (fun x => coordinateForce F i (t, x)) :=
      norm_homogeneousDatum_cycles hs _
    simp_rw [← hi]
    rw [← hh, Real.sqrt_sq (norm_nonneg _)]
  rw [he]
  apply Real.continuous_sqrt.comp_stronglyMeasurable
  have hm (i : Fin 3) : StronglyMeasurable (fun t => (frequencyUnit ^ s *
      homogeneousFourierNorm s (fun x => coordinateForce F i (t, x))) ^ 2) :=
    (stronglyMeasurable_const.mul (Paper3.stronglyMeasurable_homogeneousFourier_time s
      (coordinateForce_smooth hF i).continuous)).pow 2
  convert Finset.stronglyMeasurable_sum Finset.univ (fun i _ => hm i) using 1
  ext t
  simp only [Finset.sum_apply]

/-- Exact vector-datum time scaling on the entire real axis. -/
theorem homogeneous_datum_time_scaling {s : ℝ} (hs : -3 / 2 < s)
    {F : VelocityField} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    {k : ℝ} (hk : 0 < k) (t₀ : ℝ) (x₀ : Space) (q : ℝ≥0∞) :
    eLpNorm (compactHomogeneousPath hs (Source.parabolicForce_smooth k t₀ x₀ hF)
      (Source.parabolicForce_compact k t₀ x₀ hc)) q volume =
      ENNReal.ofReal (k ^ (3 / 2 + s - 2 / q.toReal)) *
        eLpNorm (compactHomogeneousPath hs hF hc) q volume := by
  let G := compactHomogeneousPath hs hF hc
  let H := compactHomogeneousPath hs (Source.parabolicForce_smooth k t₀ x₀ hF)
    (Source.parabolicForce_compact k t₀ x₀ hc)
  have he : (fun t => ‖H t‖) = k ^ (3 / 2 + s) •
      (fun t => ‖G (k ^ 2 * (t - t₀))‖) := by
    funext t
    exact homogeneous_vector_datum_scaling hs hF hc hk t₀ x₀ t _ _
      (compactHomogeneousPath_slice hs _ _ t) (compactHomogeneousPath_slice hs hF hc _)
  change eLpNorm H q volume = _ * eLpNorm G q volume
  rw [← eLpNorm_norm H, he, eLpNorm_const_smul,
    eLpNorm_parabolic_time _ (compactHomogeneousPath_norm_stronglyMeasurable hs hF hc) q hk t₀,
    eLpNorm_norm]
  rw [← mul_assoc, Real.enorm_eq_ofReal_abs,
    abs_of_pos (Real.rpow_pos_of_pos hk _),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hk.le _), ← Real.rpow_add hk]
  congr 3
  ring

/-- For a force zero in the past, restriction to positive time loses no norm. -/
theorem homogeneous_datum_positive_eq_volume {s : ℝ} (hs : -3 / 2 < s)
    {F : VelocityField} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hzero : ∀ t : ℝ, t ≤ 0 → ∀ x : Space, F (t, x) = 0) (q : ℝ≥0∞) :
    eLpNorm (compactHomogeneousPath hs hF hc) q forceTimeMeasure =
      eLpNorm (compactHomogeneousPath hs hF hc) q volume := by
  have hind : (Ioi (0 : ℝ)).indicator (compactHomogeneousPath hs hF hc) =
      compactHomogeneousPath hs hF hc := by
    funext t
    by_cases ht : 0 < t
    · exact Set.indicator_of_mem ht _
    · rw [Set.indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht)]
      symm
      apply norm_eq_zero.mp
      have h := compactHomogeneousPath_norm_le hs hF hc t
      have hz : ∀ x : Space, F (t, x) = 0 := hzero t (not_lt.mp ht)
      simpa [coordinateForce, hz, homogeneousFourierNorm, Real.fourier_eq] using h
  change eLpNorm _ q (volume.restrict (Ioi 0)) = _
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioi, hind]

end NSFormalization.Section4.I03
