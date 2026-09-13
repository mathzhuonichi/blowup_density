import Formal.R3CoordinateIncompressibility

/-!
# Classical incompressibility of the explicit physical representative (Clay edge 1b)

Edge 1a proved the distributional physical-coordinate divergence-free property of a
Fourier-side solenoidal `L²` velocity. This file closes the classical half: the physical
representative is exhibited **explicitly** as an inverse Fourier integral
`x ↦ 𝓕⁻ g x = ∫ ξ, 𝐞 ⟪ξ, x⟫ • g ξ`, and under explicit frequency-side `L¹` hypotheses
(`Integrable g` and `Integrable (fun ξ => ‖ξ‖ * ‖g ξ‖)`) it is proved to be `C¹`,
differentiable at every point with an explicit Fourier-integral derivative, and its
classical divergence `∑ i, (fderiv ℝ U x (eᵢ)) i` vanishes at every point whenever the
raw frequency divergence of `g` vanishes a.e. — in particular whenever `g` is an a.e.
representative of `𝓕 u` for `u` in the solenoidal submodule.

The definitional equality `R3HsVelocity s = R3L2Velocity` is nowhere used as a physical
Sobolev embedding: every regularity input is an explicit integrability hypothesis on the
frequency side. The bridge from the Bessel decoder to these hypotheses (and the a.e.
identification of the representative with `u` itself, which for `L²` data needs an
`L¹ ∩ L²` inversion layer that mathlib does not currently provide) is deliberately left
to the initial-data-class edge (edge 3).
-/

namespace MNS2

open MeasureTheory FourierTransform Real VectorFourier
open scoped FourierTransform SchwartzMap ENNReal

noncomputable section

/-- The explicit physical representative of a frequency-side velocity `g`: the inverse
Fourier integral `x ↦ ∫ ξ, 𝐞 ⟪ξ, x⟫ • g ξ`. -/
def r3PhysicalRepresentative (g : R3 → R3C) : R3 → R3C := 𝓕⁻ g

theorem r3PhysicalRepresentative_eq_fourier_comp_neg (g : R3 → R3C) :
    r3PhysicalRepresentative g = 𝓕 (fun ξ : R3 => g (-ξ)) :=
  fourierInv_eq_fourier_comp_neg g

/-- The classical (pointwise) divergence of a vector field on `R3`: the sum over
coordinates of the `i`-th component of the Fréchet derivative applied to the `i`-th
standard basis vector. -/
def r3ClassicalDivergence (U : R3 → R3C) (x : R3) : ℂ :=
  ∑ i : Fin 3, fderiv ℝ U x (r3StdBasis i) i

/-- Reflection transfer for the plain `L¹` hypothesis. -/
theorem r3Integrable_comp_neg {g : R3 → R3C} (hg : Integrable g volume) :
    Integrable (fun ξ : R3 => g (-ξ)) volume :=
  hg.comp_neg

/-- Reflection transfer for the weighted `L¹` hypothesis. -/
theorem r3WeightedIntegrable_comp_neg {g : R3 → R3C}
    (hg : Integrable (fun ξ : R3 => ‖ξ‖ * ‖g ξ‖) volume) :
    Integrable (fun ξ : R3 => ‖ξ‖ * ‖g (-ξ)‖) volume := by
  have h := hg.comp_neg
  simpa [norm_neg] using h

/-- Under the explicit frequency-side `L¹` hypotheses, the physical representative is `C¹`. -/
theorem contDiff_one_r3PhysicalRepresentative {g : R3 → R3C}
    (hg₁ : Integrable g volume)
    (hg₂ : Integrable (fun ξ : R3 => ‖ξ‖ * ‖g ξ‖) volume) :
    ContDiff ℝ 1 (r3PhysicalRepresentative g) := by
  rw [r3PhysicalRepresentative_eq_fourier_comp_neg]
  refine Real.contDiff_fourier fun n hn => ?_
  have hn' : n ≤ 1 := by exact_mod_cast hn
  interval_cases n
  · simpa using (r3Integrable_comp_neg hg₁).norm
  · simpa using r3WeightedIntegrable_comp_neg hg₂

/-- The explicit derivative of the physical representative at `x`: the forward Fourier
integral of the multiplier `fourierSMulRight` of the reflected frequency data. -/
def r3RepresentativeDeriv (g : R3 → R3C) (x : R3) : R3 →L[ℝ] R3C :=
  𝓕 (fourierSMulRight (innerSL ℝ) (fun ξ : R3 => g (-ξ))) x

/-- Under the explicit `L¹` hypotheses the representative is differentiable at every point,
with the explicit Fourier-integral derivative. -/
theorem hasFDerivAt_r3PhysicalRepresentative {g : R3 → R3C}
    (hg₁ : Integrable g volume)
    (hg₂ : Integrable (fun ξ : R3 => ‖ξ‖ * ‖g ξ‖) volume) (x : R3) :
    HasFDerivAt (r3PhysicalRepresentative g) (r3RepresentativeDeriv g x) x := by
  rw [r3PhysicalRepresentative_eq_fourier_comp_neg]
  exact Real.hasFDerivAt_fourier (r3Integrable_comp_neg hg₁)
    (r3WeightedIntegrable_comp_neg hg₂) x

theorem r3RawDivergencePointwise_neg_left (ξ : R3) (v : R3C) :
    r3RawDivergencePointwise (-ξ) v = -(r3RawDivergencePointwise ξ v) := by
  unfold r3RawDivergencePointwise
  have h0 : ((-ξ) 0 : ℝ) = -(ξ 0) := rfl
  have h1 : ((-ξ) 1 : ℝ) = -(ξ 1) := rfl
  have h2 : ((-ξ) 2 : ℝ) = -(ξ 2) := rfl
  rw [h0, h1, h2]
  push_cast
  ring

/-- The a.e. vanishing of the raw frequency divergence transfers to the reflected data. -/
theorem r3RawDivergence_ae_zero_comp_neg {g : R3 → R3C}
    (hraw : ∀ᵐ ξ : R3 ∂(volume : Measure R3), r3RawDivergencePointwise ξ (g ξ) = 0) :
    ∀ᵐ ξ : R3 ∂(volume : Measure R3), r3RawDivergencePointwise ξ (g (-ξ)) = 0 := by
  have hqmp : Measure.QuasiMeasurePreserving (fun ξ : R3 => -ξ) volume volume :=
    ⟨measurable_neg, (Measure.map_neg_eq_self (volume : Measure R3)).absolutelyContinuous⟩
  filter_upwards [hqmp.ae hraw] with ξ hξ
  have hneg := r3RawDivergencePointwise_neg_left ξ (g (-ξ))
  have hzero : -(r3RawDivergencePointwise ξ (g (-ξ))) = 0 := by
    rw [← hneg]
    exact hξ
  exact neg_eq_zero.mp hzero

/-- Membership in the solenoidal submodule gives the a.e. vanishing of the raw frequency
divergence of any a.e. representative of `𝓕 u`. -/
theorem r3RawDivergence_ae_zero_of_mem_solenoidal {u : R3L2Velocity} {g : R3 → R3C}
    (hu : u ∈ r3L2SolenoidalSubmodule)
    (hrep : g =ᵐ[volume] ((𝓕 u : R3L2Velocity) : R3 → R3C)) :
    ∀ᵐ ξ : R3 ∂(volume : Measure R3), r3RawDivergencePointwise ξ (g ξ) = 0 := by
  have hker : r3NormalizedDivergenceFrequencyAux (𝓕 u) = 0 := by
    have h := LinearMap.mem_ker.mp hu
    simpa [r3NormalizedDivergenceL2OperatorAux] using h
  have hae := r3NormalizedDivergenceFrequencyAux_ae (𝓕 u)
  have hzero : (r3NormalizedDivergenceFrequencyAux (𝓕 u) : R3 → ℂ) =ᵐ[volume] 0 := by
    rw [hker]
    exact Lp.coeFn_zero ℂ 2 volume
  filter_upwards [hae, hzero, hrep] with ξ h1 h2 h3
  have hnorm : r3NormalizedDivergencePointwise ξ (((𝓕 u : R3L2Velocity) : R3 → R3C) ξ) = 0 := by
    rw [← h1]
    simpa using h2
  have hrawU := (r3NormalizedDivergencePointwise_eq_zero_iff ξ _).mp hnorm
  rw [h3]
  exact hrawU

/-- **The divergence of the explicit derivative vanishes.** -/
theorem r3RepresentativeDeriv_div_eq_zero {g : R3 → R3C}
    (hg₁ : Integrable g volume)
    (hg₂ : Integrable (fun ξ : R3 => ‖ξ‖ * ‖g ξ‖) volume)
    (hraw : ∀ᵐ ξ : R3 ∂(volume : Measure R3), r3RawDivergencePointwise ξ (g ξ) = 0)
    (x : R3) :
    ∑ i : Fin 3, r3RepresentativeDeriv g x (r3StdBasis i) i = 0 := by
  set h : R3 → R3C := fun ξ => g (-ξ) with hhdef
  have hh₁ : Integrable h volume := r3Integrable_comp_neg hg₁
  have hh₂ : Integrable (fun ξ : R3 => ‖ξ‖ * ‖h ξ‖) volume := r3WeightedIntegrable_comp_neg hg₂
  have hhraw : ∀ᵐ ξ : R3 ∂(volume : Measure R3), r3RawDivergencePointwise ξ (h ξ) = 0 :=
    r3RawDivergence_ae_zero_comp_neg hraw
  have hF : Integrable (fun ξ : R3 => fourierSMulRight (innerSL ℝ) h ξ) volume := by
    refine Integrable.mono'
      (hh₂.const_mul (2 * π * ‖(innerSL ℝ : R3 →L[ℝ] R3 →L[ℝ] ℝ)‖))
      hh₁.aestronglyMeasurable.fourierSMulRight
      (Filter.Eventually.of_forall fun ξ => ?_)
    calc ‖fourierSMulRight (innerSL ℝ) h ξ‖
        ≤ 2 * π * ‖(innerSL ℝ : R3 →L[ℝ] R3 →L[ℝ] ℝ)‖ * ‖ξ‖ * ‖h ξ‖ :=
          norm_fourierSMulRight_le _ _ _
      _ = 2 * π * ‖(innerSL ℝ : R3 →L[ℝ] R3 →L[ℝ] ℝ)‖ * (‖ξ‖ * ‖h ξ‖) := by ring
  have hΦ : ∀ i : Fin 3,
      Integrable (fun ξ : R3 =>
        𝐞 (-(inner ℝ ξ x)) • fourierSMulRight (innerSL ℝ) h ξ (r3StdBasis i)) volume := by
    intro i
    have hG : Integrable
        (fun ξ : R3 => fourierSMulRight (innerSL ℝ) h ξ (r3StdBasis i)) volume :=
      (ContinuousLinearMap.apply ℝ R3C (r3StdBasis i)).integrable_comp hF
    refine Integrable.mono' hG.norm
      (((continuous_fourierChar.comp (by fun_prop)).aestronglyMeasurable).smul
        hG.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Circle.norm_smul]
  have key : ∑ i : Fin 3, r3RepresentativeDeriv g x (r3StdBasis i) i =
      ∫ ξ : R3, ∑ i : Fin 3,
        (EuclideanSpace.proj i : R3C →L[ℂ] ℂ)
          (𝐞 (-(inner ℝ ξ x)) • fourierSMulRight (innerSL ℝ) h ξ (r3StdBasis i)) := by
    rw [MeasureTheory.integral_finsetSum _
      (fun i _ => ((EuclideanSpace.proj i : R3C →L[ℂ] ℂ)).integrable_comp (hΦ i))]
    refine Finset.sum_congr rfl fun i _ => ?_
    have heval : r3RepresentativeDeriv g x (r3StdBasis i) =
        𝓕 (fun ξ : R3 => fourierSMulRight (innerSL ℝ) h ξ (r3StdBasis i)) x :=
      Real.fourier_continuousLinearMap_apply hF
    have hproj : (𝓕 (fun ξ : R3 => fourierSMulRight (innerSL ℝ) h ξ (r3StdBasis i)) x) i =
        (EuclideanSpace.proj i : R3C →L[ℂ] ℂ)
          (𝓕 (fun ξ : R3 => fourierSMulRight (innerSL ℝ) h ξ (r3StdBasis i)) x) := rfl
    rw [heval, hproj, Real.fourier_eq,
      ← ContinuousLinearMap.integral_comp_comm _ (hΦ i)]
  rw [key]
  have hzero : (fun ξ : R3 => ∑ i : Fin 3,
      (EuclideanSpace.proj i : R3C →L[ℂ] ℂ)
        (𝐞 (-(inner ℝ ξ x)) • fourierSMulRight (innerSL ℝ) h ξ (r3StdBasis i)))
      =ᵐ[volume] fun _ => (0 : ℂ) := by
    filter_upwards [hhraw] with ξ hξ
    have hraw' : r3RawDivergencePointwise ξ (h ξ) = 0 := hξ
    unfold r3RawDivergencePointwise at hraw'
    have hinner : ∀ i : Fin 3, (innerSL ℝ) ξ (r3StdBasis i) = ξ i := fun i => by
      simpa using inner_r3StdBasis ξ i
    simp only [fourierSMulRight_apply, Fin.sum_univ_three, map_smul,
      ContinuousLinearMap.map_smul_of_tower, PiLp.proj_apply, hinner, Circle.smul_def,
      smul_eq_mul, Complex.real_smul]
    linear_combination
      ((𝐞 (-(inner ℝ ξ x)) : ℂ) * (-(2 * (π : ℂ) * Complex.I))) * hraw'
  rw [MeasureTheory.integral_congr_ae hzero, MeasureTheory.integral_zero]

/-- **Classical incompressibility of the explicit physical representative**
(Clay semantic-promotion edge 1b, explicit-hypothesis form).

Under the explicit frequency-side `L¹` conditions, the classical divergence of the
representative vanishes at every point (its `fderiv` being genuine by
`hasFDerivAt_r3PhysicalRepresentative`). -/
theorem r3ClassicalDivergence_r3PhysicalRepresentative {g : R3 → R3C}
    (hg₁ : Integrable g volume)
    (hg₂ : Integrable (fun ξ : R3 => ‖ξ‖ * ‖g ξ‖) volume)
    (hraw : ∀ᵐ ξ : R3 ∂(volume : Measure R3), r3RawDivergencePointwise ξ (g ξ) = 0)
    (x : R3) :
    r3ClassicalDivergence (r3PhysicalRepresentative g) x = 0 := by
  unfold r3ClassicalDivergence
  rw [(hasFDerivAt_r3PhysicalRepresentative hg₁ hg₂ x).fderiv]
  exact r3RepresentativeDeriv_div_eq_zero hg₁ hg₂ hraw x

/-- **Edge 1b, membership form**: a Fourier-side solenoidal `L²` velocity whose Fourier
image admits an integrable representative with integrable first moment has an explicit
`C¹` physical representative with vanishing classical divergence at every point. -/
theorem r3PhysicalRepresentative_incompressible_of_mem_solenoidal
    {u : R3L2Velocity} {g : R3 → R3C}
    (hu : u ∈ r3L2SolenoidalSubmodule)
    (hrep : g =ᵐ[volume] ((𝓕 u : R3L2Velocity) : R3 → R3C))
    (hg₁ : Integrable g volume)
    (hg₂ : Integrable (fun ξ : R3 => ‖ξ‖ * ‖g ξ‖) volume) :
    ContDiff ℝ 1 (r3PhysicalRepresentative g) ∧
      ∀ x : R3, r3ClassicalDivergence (r3PhysicalRepresentative g) x = 0 :=
  ⟨contDiff_one_r3PhysicalRepresentative hg₁ hg₂, fun x =>
    r3ClassicalDivergence_r3PhysicalRepresentative hg₁ hg₂
      (r3RawDivergence_ae_zero_of_mem_solenoidal hu hrep) x⟩

/-- Non-vacuity witness: every Schwartz frequency profile satisfies both explicit `L¹`
hypotheses. -/
theorem r3PhysicalRepresentative_hypotheses_nonvacuous (φ : 𝓢(R3, R3C)) :
    Integrable (⇑φ) volume ∧ Integrable (fun ξ : R3 => ‖ξ‖ * ‖φ ξ‖) volume :=
  ⟨φ.integrable, by simpa using φ.integrable_pow_mul (volume : Measure R3) 1⟩

end

end MNS2
