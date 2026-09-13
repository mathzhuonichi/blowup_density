import NavierStokes.R3RieszApproximation

/-!
# Weighted whole-space pressure

A sixth-power spatial cutoff turns the pressure of an integrable stress
into an `L²` function. The proof combines the `L²` Fourier bound with the
absolutely convergent kernel commutator; no integrability hypothesis is
imposed on an arbitrary physical pressure.
-/

noncomputable section
namespace NavierStokes.R3PressureCutoff

open Set Filter MeasureTheory ProblemStatement FourierTransform TemperedDistribution
open R3PressureFourier R3RieszKernel R3RieszApproximation R3PressureCommutator
open scoped Topology ENNReal SchwartzMap

def powerCutoff (φ : Space → ℝ) (x : Space) : ℂ := (φ x ^ 6 : ℝ)

theorem powerCutoff_temperate {φ : Space → ℝ} (hφ : φ.HasTemperateGrowth) :
    (powerCutoff φ).HasTemperateGrowth := by
  unfold powerCutoff
  fun_prop

theorem powerCutoff_measurable {R L : ℝ} {φ : Space → ℝ} (hφ : Cutoff R L φ) :
    Measurable (powerCutoff φ) := by
  have hm := hφ.measurable
  unfold powerCutoff
  fun_prop

theorem norm_powerCutoff_le {R L : ℝ} {φ : Space → ℝ} (hφ : Cutoff R L φ) (x : Space) :
    ‖powerCutoff φ x‖ ≤ 1 := by
  rw [powerCutoff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hφ.range x).1 6)]
  exact pow_le_one₀ (hφ.range x).1 (hφ.range x).2

theorem powerCutoff_memLp {R L : ℝ} {φ : Space → ℝ} (hφ : Cutoff R L φ) :
    MemLp (powerCutoff φ) ⊤ :=
  memLp_top_of_bound (powerCutoff_measurable hφ).aestronglyMeasurable 1
    (Eventually.of_forall (norm_powerCutoff_le hφ))

def cutoffLp {R L : ℝ} {φ : Space → ℝ} (hφ : Cutoff R L φ) : Lp ℂ ⊤ (volume : Measure Space) :=
  (powerCutoff_memLp hφ).toLp (powerCutoff φ)

def weightedLp {R L : ℝ} {φ : Space → ℝ} (hφ : Cutoff R L φ)
    (g : Lp ℂ 1 (volume : Measure Space)) : Lp ℂ 1 (volume : Measure Space) := cutoffLp hφ • g

theorem weightedLp_ae {R L : ℝ} {φ : Space → ℝ} (hφ : Cutoff R L φ)
    (g : Lp ℂ 1 (volume : Measure Space)) :
    weightedLp hφ g =ᵐ[volume] fun x => powerCutoff φ x * g x := by
  filter_upwards [Lp.coeFn_lpSMul (r := 1) (cutoffLp hφ) g,
    (powerCutoff_memLp hφ).coeFn_toLp] with x hm hc
  change cutoffLp hφ x = powerCutoff φ x at hc
  change weightedLp hφ g x = _ at hm ⊢
  simpa only [Pi.smul_apply', smul_eq_mul, hc] using hm

theorem weighted_integrable {R L : ℝ} {φ : Space → ℝ} (hφ : Cutoff R L φ)
    (g : Lp ℂ 1 (volume : Measure Space)) : Integrable (fun x => powerCutoff φ x * g x) :=
  (L1.integrable_coeFn (weightedLp hφ g)).congr (weightedLp_ae hφ g)

theorem regularized_commutator_ae {R L : ℝ} {φ : Space → ℝ} (hφ : Cutoff R L φ)
    (n : ℕ) (i j : Fin 3) (g : Lp ℂ 1 (volume : Measure Space)) :
    ∀ᵐ x ∂volume, powerCutoff φ x * regularized n i j g x -
      regularized n i j (fun y => powerCutoff φ y * g y) x =
        R3PressureCommutator.commutator φ (truncatedKernel n i j) g x := by
  filter_upwards [regularized_ae_integrable n i j (L1.integrable_coeFn g),
    regularized_ae_integrable n i j (weighted_integrable hφ g)] with x hg hw
  unfold regularized R3ConvolutionYoung.scalarConvolution R3PressureCommutator.commutator
  rw [← integral_const_mul, ← integral_sub (hg.const_mul _) hw]
  apply integral_congr_ae
  filter_upwards with z
  unfold integrand powerCutoff
  push_cast
  ring

def commutatorLp {R L : ℝ} {φ : Space → ℝ} (hφ : Cutoff R L φ)
    (i j : Fin 3) (g : Lp ℂ 1 (volume : Measure Space))
    (hw : MemLp (weightedNorm φ g) (3 / 2)) : Lp ℂ 2 (volume : Measure Space) :=
  (commutator_memLp hφ (limitingKernel_kernelBound i j) (Lp.stronglyMeasurable g).measurable
    (Lp.memLp g) hw).toLp (R3PressureCommutator.commutator φ (limitingKernel i j) g)

def regularizedCommutatorLp {R L : ℝ} {φ : Space → ℝ} (hφ : Cutoff R L φ)
    (n : ℕ) (i j : Fin 3) (g : Lp ℂ 1 (volume : Measure Space))
    (hw : MemLp (weightedNorm φ g) (3 / 2)) : Lp ℂ 2 (volume : Measure Space) :=
  (commutator_memLp hφ (truncatedKernel_kernelBound n i j) (Lp.stronglyMeasurable g).measurable
    (Lp.memLp g) hw).toLp (R3PressureCommutator.commutator φ (truncatedKernel n i j) g)

theorem regularizedCommutatorLp_ae {R L : ℝ} {φ : Space → ℝ} (hφ : Cutoff R L φ)
    (n : ℕ) (i j : Fin 3) (g : Lp ℂ 1 (volume : Measure Space))
    (hw : MemLp (weightedNorm φ g) (3 / 2)) :
    regularizedCommutatorLp hφ n i j g hw =ᵐ[volume] R3PressureCommutator.commutator φ (truncatedKernel n i j) g :=
  (commutator_memLp hφ (truncatedKernel_kernelBound n i j) (Lp.stronglyMeasurable g).measurable
    (Lp.memLp g) hw).coeFn_toLp

/-- The finite-scale commutator identity holds in distributions, allowing
its two terms to belong to different `Lp` spaces. -/
theorem regularized_cutoff_identity {R L : ℝ} {φ : Space → ℝ} (hφ : Cutoff R L φ)
    (hφg : φ.HasTemperateGrowth) (n : ℕ) (i j : Fin 3) (g : Lp ℂ 1 (volume : Measure Space))
    (hw : MemLp (weightedNorm φ g) (3 / 2)) :
    smulLeftCLM ℂ (powerCutoff φ) (operatorL1 n i j g) =
      operatorL1 n i j (weightedLp hφ g) +
        (regularizedCommutatorLp hφ n i j g hw : 𝓢'(Space, ℂ)) := by
  let A : Lp ℂ 1 (volume : Measure Space) :=
    cutoffLp hφ • regularizedLp n i j g - regularizedLp n i j (weightedLp hφ g)
  have hA : A =ᵐ[volume] R3PressureCommutator.commutator φ (truncatedKernel n i j) g := by
    have he := regularized_congr_ae n i j (weightedLp_ae hφ g)
    filter_upwards [Lp.coeFn_sub (cutoffLp hφ • regularizedLp n i j g : Lp ℂ 1 volume)
        (regularizedLp n i j (weightedLp hφ g)),
      Lp.coeFn_lpSMul (r := 1) (cutoffLp hφ) (regularizedLp n i j g),
      (powerCutoff_memLp hφ).coeFn_toLp,
      regularizedLp_ae n i j g, regularizedLp_ae n i j (weightedLp hφ g),
      regularized_commutator_ae hφ n i j g] with x hsub hmul hc hg hw hcmt
    change cutoffLp hφ x = powerCutoff φ x at hc
    change A x = _ at hsub ⊢
    rw [hsub]
    simp only [Pi.sub_apply, hmul, Pi.smul_apply', smul_eq_mul, hc, hg, hw, he]
    exact hcmt
  have hAd : (A : 𝓢'(Space, ℂ)) =
      (regularizedCommutatorLp hφ n i j g hw : 𝓢'(Space, ℂ)) :=
    lp_distribution_eq_of_ae (hA.trans (regularizedCommutatorLp_ae hφ n i j g hw).symm)
  have hsub := (Lp.toTemperedDistributionCLM ℂ (volume : Measure Space) 1).map_sub
    (cutoffLp hφ • regularizedLp n i j g : Lp ℂ 1 volume)
    (regularizedLp n i j (weightedLp hφ g))
  change (A : 𝓢'(Space, ℂ)) = _ at hsub
  rw [hAd] at hsub
  have hprod := Lp.toTemperedDistribution_smul_eq (p := ⊤) (q := 1) (r := 1)
    (powerCutoff_temperate hφg) (powerCutoff_memLp hφ) (regularizedLp n i j g)
  rw [operatorL1_eq_regularizedLp, operatorL1_eq_regularizedLp]
  rw [← hprod]
  have hh := hsub.symm
  exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)

theorem regularizedCommutatorLp_tendsto {R L : ℝ} {φ : Space → ℝ} (hφ : Cutoff R L φ)
    (i j : Fin 3) (g : Lp ℂ 1 (volume : Measure Space))
    (hw : MemLp (weightedNorm φ g) (3 / 2)) :
    Tendsto (fun n => regularizedCommutatorLp hφ n i j g hw) atTop (𝓝 (commutatorLp hφ i j g hw)) := by
  apply tendsto_toLp_two_of_lpNorm
  exact commutator_tendsto_lpNorm hφ (fun n => truncatedKernel_kernelBound n i j)
    (limitingKernel_kernelBound i j) (Lp.stronglyMeasurable g).measurable (Lp.memLp g) hw
    (truncatedKernel_tendsto i j)

/-- The sixth-power commutator identity for the normalized pressure. -/
theorem pressure_cutoff_identity {R L : ℝ} {φ : Space → ℝ} (hφ : Cutoff R L φ)
    (hφg : φ.HasTemperateGrowth) (i j : Fin 3) (g : Lp ℂ 1 (volume : Measure Space))
    (hw : MemLp (weightedNorm φ g) (3 / 2)) :
    smulLeftCLM ℂ (powerCutoff φ) (pressureL1 i j g) =
      pressureL1 i j (weightedLp hφ g) + (commutatorLp hφ i j g hw : 𝓢'(Space, ℂ)) := by
  have hl := ((smulLeftCLM ℂ (powerCutoff φ)).continuous.tendsto (pressureL1 i j g)).comp
    (operatorL1_tendsto i j g)
  have hc := ((Lp.toTemperedDistributionCLM ℂ (volume : Measure Space) 2).continuous.tendsto
    (commutatorLp hφ i j g hw)).comp (regularizedCommutatorLp_tendsto hφ i j g hw)
  have hr := (operatorL1_tendsto i j (weightedLp hφ g)).add hc
  apply tendsto_nhds_unique hl
  exact hr.congr' (Eventually.of_forall fun n => (regularized_cutoff_identity hφ hφg n i j g hw).symm)


/-- The two radius-decaying contributions to the weighted pressure. -/
def errorBound (R L : ℝ) (φ : Space → ℝ) (g : Space → ℂ) : ℝ :=
  (kernelConstant * (96 * L ^ 6)) *
    (R ^ (-1 / 2 : ℝ) * lpNorm R3PressureNearKernel.nearBase (6 / 5) volume *
        lpNorm (weightedNorm φ g) (3 / 2) volume +
      R ^ (-3 / 2 : ℝ) * lpNorm R3PressureNearKernel.remainderBase 2 volume * lpNorm g 1 volume)

theorem norm_commutatorLp_le {R L : ℝ} {φ : Space → ℝ} (hφ : Cutoff R L φ)
    (i j : Fin 3) (g : Lp ℂ 1 (volume : Measure Space))
    (hw : MemLp (weightedNorm φ g) (3 / 2)) :
    ‖commutatorLp hφ i j g hw‖ ≤ errorBound R L φ g := by
  unfold commutatorLp
  rw [Lp.norm_toLp, toReal_eLpNorm (commutator_aestronglyMeasurable hφ
    (limitingKernel_kernelBound i j) (Lp.stronglyMeasurable g).measurable)]
  exact commutator_lpNorm hφ (limitingKernel_kernelBound i j) (Lp.stronglyMeasurable g).measurable
    (Lp.memLp g) hw

theorem norm_regularizedCommutatorLp_le {R L : ℝ} {φ : Space → ℝ} (hφ : Cutoff R L φ)
    (n : ℕ) (i j : Fin 3) (g : Lp ℂ 1 (volume : Measure Space))
    (hw : MemLp (weightedNorm φ g) (3 / 2)) :
    ‖regularizedCommutatorLp hφ n i j g hw‖ ≤ errorBound R L φ g := by
  unfold regularizedCommutatorLp
  rw [Lp.norm_toLp, toReal_eLpNorm (commutator_aestronglyMeasurable hφ
    (truncatedKernel_kernelBound n i j) (Lp.stronglyMeasurable g).measurable)]
  exact commutator_lpNorm hφ (truncatedKernel_kernelBound n i j) (Lp.stronglyMeasurable g).measurable
    (Lp.memLp g) hw

def weightedPressure {R L : ℝ} {φ : Space → ℝ} (hφ : Cutoff R L φ)
    (i j : Fin 3) (g : Lp ℂ 1 (volume : Measure Space))
    (hw : MemLp (weightedNorm φ g) (3 / 2))
    (hg₂ : MemLp (fun x => powerCutoff φ x * g x) 2) : Lp ℂ 2 (volume : Measure Space) :=
  pressureL2 i j (hg₂.toLp (fun x => powerCutoff φ x * g x)) + commutatorLp hφ i j g hw

def regularizedWeightedPressure {R L : ℝ} {φ : Space → ℝ} (hφ : Cutoff R L φ)
    (n : ℕ) (i j : Fin 3) (g : Lp ℂ 1 (volume : Measure Space))
    (hw : MemLp (weightedNorm φ g) (3 / 2))
    (hg₂ : MemLp (fun x => powerCutoff φ x * g x) 2) : Lp ℂ 2 (volume : Measure Space) :=
  operatorL2 n i j (hg₂.toLp (fun x => powerCutoff φ x * g x)) +
    regularizedCommutatorLp hφ n i j g hw

theorem weightedPressure_distribution {R L : ℝ} {φ : Space → ℝ} (hφ : Cutoff R L φ)
    (hφg : φ.HasTemperateGrowth) (i j : Fin 3) (g : Lp ℂ 1 (volume : Measure Space))
    (hw : MemLp (weightedNorm φ g) (3 / 2)) (hg₂ : MemLp (fun x => powerCutoff φ x * g x) 2) :
    smulLeftCLM ℂ (powerCutoff φ) (pressureL1 i j g) =
      (weightedPressure hφ i j g hw hg₂ : 𝓢'(Space, ℂ)) := by
  rw [pressure_cutoff_identity hφ hφg]
  rw [pressureL1_eq_pressureL2 i j ((weightedLp_ae hφ g).trans hg₂.coeFn_toLp.symm)]
  exact ((Lp.toTemperedDistributionCLM ℂ (volume : Measure Space) 2).map_add _ _).symm

theorem regularizedWeightedPressure_distribution {R L : ℝ} {φ : Space → ℝ} (hφ : Cutoff R L φ)
    (hφg : φ.HasTemperateGrowth) (n : ℕ) (i j : Fin 3) (g : Lp ℂ 1 (volume : Measure Space))
    (hw : MemLp (weightedNorm φ g) (3 / 2)) (hg₂ : MemLp (fun x => powerCutoff φ x * g x) 2) :
    smulLeftCLM ℂ (powerCutoff φ) (operatorL1 n i j g) =
      (regularizedWeightedPressure hφ n i j g hw hg₂ : 𝓢'(Space, ℂ)) := by
  rw [regularized_cutoff_identity hφ hφg]
  rw [operatorL1_eq_operatorL2 n i j ((weightedLp_ae hφ g).trans hg₂.coeFn_toLp.symm)]
  exact ((Lp.toTemperedDistributionCLM ℂ (volume : Measure Space) 2).map_add _ _).symm

theorem norm_weightedPressure_le {R L : ℝ} {φ : Space → ℝ} (hφ : Cutoff R L φ)
    (i j : Fin 3) (g : Lp ℂ 1 (volume : Measure Space))
    (hw : MemLp (weightedNorm φ g) (3 / 2)) (hg₂ : MemLp (fun x => powerCutoff φ x * g x) 2) :
    ‖weightedPressure hφ i j g hw hg₂‖ ≤
      lpNorm (fun x => powerCutoff φ x * g x) 2 volume + errorBound R L φ g := by
  unfold weightedPressure
  apply (norm_add_le _ _).trans
  have hn := norm_pressureL2_le i j (hg₂.toLp (fun x => powerCutoff φ x * g x))
  rw [Lp.norm_toLp, toReal_eLpNorm hg₂.1] at hn
  exact add_le_add hn (norm_commutatorLp_le hφ i j g hw)

theorem norm_regularizedWeightedPressure_le {R L : ℝ} {φ : Space → ℝ} (hφ : Cutoff R L φ)
    (n : ℕ) (i j : Fin 3) (g : Lp ℂ 1 (volume : Measure Space))
    (hw : MemLp (weightedNorm φ g) (3 / 2)) (hg₂ : MemLp (fun x => powerCutoff φ x * g x) 2) :
    ‖regularizedWeightedPressure hφ n i j g hw hg₂‖ ≤
      lpNorm (fun x => powerCutoff φ x * g x) 2 volume + errorBound R L φ g := by
  unfold regularizedWeightedPressure
  apply (norm_add_le _ _).trans
  have hn := norm_operatorL2_le n i j (hg₂.toLp (fun x => powerCutoff φ x * g x))
  rw [Lp.norm_toLp, toReal_eLpNorm hg₂.1] at hn
  exact add_le_add hn (norm_regularizedCommutatorLp_le hφ n i j g hw)

theorem regularizedWeightedPressure_ae {R L : ℝ} {φ : Space → ℝ} (hφ : Cutoff R L φ)
    (hφg : φ.HasTemperateGrowth) (n : ℕ) (i j : Fin 3) (g : Lp ℂ 1 (volume : Measure Space))
    (hw : MemLp (weightedNorm φ g) (3 / 2)) (hg₂ : MemLp (fun x => powerCutoff φ x * g x) 2) :
    regularizedWeightedPressure hφ n i j g hw hg₂ =ᵐ[volume]
      fun x => powerCutoff φ x * regularized n i j g x := by
  have hd := regularizedWeightedPressure_distribution hφ hφg n i j g hw hg₂
  rw [operatorL1_eq_regularizedLp] at hd
  have he := Lp.toTemperedDistribution_smul_eq (p := ⊤) (q := 1) (r := 1)
    (powerCutoff_temperate hφg) (powerCutoff_memLp hφ) (regularizedLp n i j g)
  rw [← he] at hd
  have hh := lp_ae_of_distribution_eq hd.symm
  filter_upwards [hh, Lp.coeFn_lpSMul (r := 1) (cutoffLp hφ) (regularizedLp n i j g),
    (powerCutoff_memLp hφ).coeFn_toLp, regularizedLp_ae n i j g] with x hx hm hc hg
  change cutoffLp hφ x = powerCutoff φ x at hc
  rw [hx]
  change (cutoffLp hφ • regularizedLp n i j g : Lp ℂ 1 volume) x = _
  rw [hm]
  simp only [Pi.smul_apply', smul_eq_mul, hc, hg]

/-- A bound on the actual finite-scale pressure functions, uniform in the
regularization parameter. This is suitable for subsequent time integration. -/
theorem regularized_weighted_lpNorm_le {R L : ℝ} {φ : Space → ℝ} (hφ : Cutoff R L φ)
    (hφg : φ.HasTemperateGrowth) (n : ℕ) (i j : Fin 3) (g : Lp ℂ 1 (volume : Measure Space))
    (hw : MemLp (weightedNorm φ g) (3 / 2)) (hg₂ : MemLp (fun x => powerCutoff φ x * g x) 2) :
    lpNorm (fun x => powerCutoff φ x * regularized n i j g x) 2 volume ≤
      lpNorm (fun x => powerCutoff φ x * g x) 2 volume + errorBound R L φ g := by
  have ha := regularizedWeightedPressure_ae hφ hφg n i j g hw hg₂
  have hm := (memLp_congr_ae ha).mp (Lp.memLp (regularizedWeightedPressure hφ n i j g hw hg₂))
  have hn : lpNorm (fun x => powerCutoff φ x * regularized n i j g x) 2 volume =
      ‖regularizedWeightedPressure hφ n i j g hw hg₂‖ := by
    rw [← toReal_eLpNorm hm.1, ← eLpNorm_congr_ae ha, Lp.norm_def]
  rw [hn]
  exact norm_regularizedWeightedPressure_le hφ n i j g hw hg₂

end NavierStokes.R3PressureCutoff
