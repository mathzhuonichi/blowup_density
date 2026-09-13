import Formal.R3ClosedSolenoidalCarrier

/-!
# Coordinate incompressibility semantics (Clay semantic-promotion edge 1)

The frozen chain's solenoidal condition is a Fourier-side statement: membership in
`r3L2SolenoidalSubmodule`, i.e. the normalized frequency divergence of `𝓕 u` vanishes in `L²`.
This file proves the physical-coordinate meaning of that condition: the physical tempered
distribution represented by `u` (through the honest `L² → 𝓢'` embedding `r3L2ToTemperedCLM`,
no Bessel weight consumed) is divergence-free in physical coordinates, where the divergence is
the sum over coordinates of mathlib's distributional partial derivative `∂_{eᵢ}` — defined by
physical-coordinate duality against Schwartz test functions — of the `i`-th component.

No phantom Sobolev order is used as a physical inclusion: the statement is at the `L²` level,
and the proof uses only the embedding, mathlib's distributional calculus, and Plancherel
(`MeasureTheory.Lp.fourier_toTemperedDistribution_eq`).
-/

namespace MNS2

open MeasureTheory FourierTransform LineDeriv Real
open scoped FourierTransform SchwartzMap ENNReal

noncomputable section

/-- The `i`-th standard basis vector of the physical space `R3`. -/
def r3StdBasis (i : Fin 3) : R3 := EuclideanSpace.single i 1

/-- Physical-coordinate divergence of an `R3C`-valued tempered distribution: the sum over
coordinates of the distributional partial derivative in the `i`-th coordinate direction of the
`i`-th component. -/
def r3TemperedDivergence (T : 𝓢'(R3, R3C)) : 𝓢'(R3, ℂ) :=
  ∑ i : Fin 3,
    PointwiseConvergenceCLM.postcomp 𝓢(R3, ℂ)
      (EuclideanSpace.proj i : R3C →L[ℂ] ℂ) (∂_{r3StdBasis i} T)

theorem r3TemperedDivergence_apply (T : 𝓢'(R3, R3C)) (φ : 𝓢(R3, ℂ)) :
    r3TemperedDivergence T φ =
      ∑ i : Fin 3, (EuclideanSpace.proj i : R3C →L[ℂ] ℂ) (T (-(∂_{r3StdBasis i} φ))) := by
  unfold r3TemperedDivergence
  rw [sum_apply]
  rfl

/-- The multiplier Schwartz function produced by pulling one coordinate derivative through the
Fourier transform: `ξ ↦ -(2πI) ⬝ ξᵢ ⬝ ψ ξ`. -/
def r3DerivMultiplier (ψ : 𝓢(R3, ℂ)) (i : Fin 3) : 𝓢(R3, ℂ) :=
  -(2 * π * Complex.I) • SchwartzMap.smulLeftCLM ℂ (inner ℝ · (r3StdBasis i)) ψ

theorem lineDerivOp_eq_fourier_r3DerivMultiplier (ψ : 𝓢(R3, ℂ)) (i : Fin 3) :
    ∂_{r3StdBasis i} (𝓕 ψ) = 𝓕 (r3DerivMultiplier ψ i) :=
  SchwartzMap.lineDerivOp_fourier_eq ψ (r3StdBasis i)

theorem inner_r3StdBasis (ξ : R3) (i : Fin 3) : inner ℝ ξ (r3StdBasis i) = ξ i := by
  unfold r3StdBasis
  simp [EuclideanSpace.inner_single_right]

theorem hasTemperateGrowth_inner_r3StdBasis (i : Fin 3) :
    Function.HasTemperateGrowth (inner ℝ · (r3StdBasis i)) :=
  ((innerSL ℝ).flip (r3StdBasis i)).hasTemperateGrowth

theorem r3DerivMultiplier_apply (ψ : 𝓢(R3, ℂ)) (i : Fin 3) (ξ : R3) :
    r3DerivMultiplier ψ i ξ = -(2 * π * Complex.I) * ((ξ i : ℝ) : ℂ) * ψ ξ := by
  unfold r3DerivMultiplier
  rw [smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_inner_r3StdBasis i) ψ ξ,
    inner_r3StdBasis, Complex.real_smul, smul_eq_mul]
  ring

/-- **Coordinate incompressibility semantics** (Clay semantic-promotion edge 1, `L²` level).

If `u` lies in the Fourier-side solenoidal submodule, then the physical tempered distribution
it represents through the plain `L²` embedding is divergence-free in physical coordinates:
the sum of the distributional coordinate partial derivatives of its components vanishes. -/
theorem r3TemperedDivergence_eq_zero_of_mem_solenoidal
    (u : R3L2Velocity) (hu : u ∈ r3L2SolenoidalSubmodule) :
    r3TemperedDivergence (r3L2ToTemperedCLM u) = 0 := by
  -- The Fourier image of `u` and the a.e. vanishing of its raw frequency divergence.
  have hker : r3NormalizedDivergenceFrequencyAux (𝓕 u) = 0 := by
    have h := LinearMap.mem_ker.mp hu
    simpa [r3NormalizedDivergenceL2OperatorAux] using h
  have hraw : ∀ᵐ ξ : R3 ∂(volume : Measure R3),
      r3RawDivergencePointwise ξ (((𝓕 u : R3L2Velocity) : R3 → R3C) ξ) = 0 := by
    have hae := r3NormalizedDivergenceFrequencyAux_ae (𝓕 u)
    have hzero : (r3NormalizedDivergenceFrequencyAux (𝓕 u) : R3 → ℂ) =ᵐ[volume] 0 := by
      rw [hker]
      exact Lp.coeFn_zero ℂ 2 volume
    filter_upwards [hae, hzero] with ξ h1 h2
    have hnorm : r3NormalizedDivergencePointwise ξ (((𝓕 u : R3L2Velocity) : R3 → R3C) ξ) = 0 := by
      rw [← h1]
      simpa using h2
    exact (r3NormalizedDivergencePointwise_eq_zero_iff ξ (((𝓕 u : R3L2Velocity) : R3 → R3C) ξ)).mp hnorm
  -- Test against an arbitrary Schwartz function.
  ext φ
  set ψ : 𝓢(R3, ℂ) := 𝓕⁻ φ with hψdef
  have hφ : 𝓕 ψ = φ := fourier_fourierInv_eq φ
  -- Each derivative pairing becomes a frequency-side integral against the multiplier.
  have hpair : ∀ i : Fin 3,
      (r3L2ToTemperedCLM u) (∂_{r3StdBasis i} φ) =
        ∫ ξ : R3, r3DerivMultiplier ψ i ξ • ((𝓕 u : R3L2Velocity) : R3 → R3C) ξ := by
    intro i
    have hderiv : ∂_{r3StdBasis i} φ = 𝓕 (r3DerivMultiplier ψ i) := by
      rw [← hφ]
      exact lineDerivOp_eq_fourier_r3DerivMultiplier ψ i
    calc (r3L2ToTemperedCLM u) (∂_{r3StdBasis i} φ)
        = (u : 𝓢'(R3, R3C)) (𝓕 (r3DerivMultiplier ψ i)) := by rw [hderiv]; rfl
      _ = (𝓕 (u : 𝓢'(R3, R3C))) (r3DerivMultiplier ψ i) :=
          (TemperedDistribution.fourier_apply (u : 𝓢'(R3, R3C)) (r3DerivMultiplier ψ i)).symm
      _ = ((𝓕 u : R3L2Velocity) : 𝓢'(R3, R3C)) (r3DerivMultiplier ψ i) := by
          rw [MeasureTheory.Lp.fourier_toTemperedDistribution_eq]
      _ = ∫ ξ : R3, r3DerivMultiplier ψ i ξ • ((𝓕 u : R3L2Velocity) : R3 → R3C) ξ :=
          MeasureTheory.Lp.toTemperedDistribution_apply (𝓕 u) (r3DerivMultiplier ψ i)
  -- Integrability of each frequency-side integrand (`Schwartz × L² ⊆ L¹`).
  have hint : ∀ i : Fin 3,
      Integrable (fun ξ : R3 => r3DerivMultiplier ψ i ξ • ((𝓕 u : R3L2Velocity) : R3 → R3C) ξ) volume := by
    intro i
    have hUmem : MemLp ((𝓕 u : R3L2Velocity) : R3 → R3C) 2 volume := Lp.memLp (𝓕 u)
    have hχmem : MemLp (fun ξ : R3 => r3DerivMultiplier ψ i ξ) 2 volume :=
      (r3DerivMultiplier ψ i).memLp 2
    have hone : MemLp
        (fun ξ : R3 => r3DerivMultiplier ψ i ξ • ((𝓕 u : R3L2Velocity) : R3 → R3C) ξ) 1 volume :=
      hUmem.smul hχmem
    exact memLp_one_iff_integrable.mp hone
  have hintscalar : ∀ i : Fin 3,
      Integrable (fun ξ : R3 => r3DerivMultiplier ψ i ξ * ((𝓕 u : R3L2Velocity) : R3 → R3C) ξ i) volume := by
    intro i
    have h := ContinuousLinearMap.integrable_comp
      (EuclideanSpace.proj i : R3C →L[ℂ] ℂ) (hint i)
    simpa [smul_eq_mul] using h
  -- Collapse each projected pairing to a scalar frequency-side integral.
  have hproj : ∀ i : Fin 3,
      (EuclideanSpace.proj i : R3C →L[ℂ] ℂ)
          ((r3L2ToTemperedCLM u) (∂_{r3StdBasis i} φ)) =
        ∫ ξ : R3, r3DerivMultiplier ψ i ξ * ((𝓕 u : R3L2Velocity) : R3 → R3C) ξ i := by
    intro i
    rw [hpair i, ← ContinuousLinearMap.integral_comp_comm _ (hint i)]
    congr 1
  -- Assemble the sum and pass to a single integral of the raw frequency divergence.
  have hsum :
      ∑ i : Fin 3, (EuclideanSpace.proj i : R3C →L[ℂ] ℂ)
          ((r3L2ToTemperedCLM u) (-(∂_{r3StdBasis i} φ))) =
        -∫ ξ : R3, ∑ i : Fin 3, r3DerivMultiplier ψ i ξ * ((𝓕 u : R3L2Velocity) : R3 → R3C) ξ i := by
    rw [MeasureTheory.integral_finsetSum _ (fun i _ => hintscalar i),
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_neg (r3L2ToTemperedCLM u), map_neg, hproj i]
  -- The pointwise sum is a multiple of the raw frequency divergence.
  have hpt : ∀ ξ : R3,
      ∑ i : Fin 3, r3DerivMultiplier ψ i ξ * ((𝓕 u : R3L2Velocity) : R3 → R3C) ξ i =
        -(2 * π * Complex.I) * ψ ξ *
          r3RawDivergencePointwise ξ (((𝓕 u : R3L2Velocity) : R3 → R3C) ξ) := by
    intro ξ
    unfold r3RawDivergencePointwise
    rw [Fin.sum_univ_three, r3DerivMultiplier_apply, r3DerivMultiplier_apply,
      r3DerivMultiplier_apply]
    ring
  -- Conclude: the integrand vanishes a.e., so the pairing vanishes.
  have hzero :
      (∫ ξ : R3, ∑ i : Fin 3, r3DerivMultiplier ψ i ξ * ((𝓕 u : R3L2Velocity) : R3 → R3C) ξ i) = 0 := by
    have hae : (fun ξ : R3 => ∑ i : Fin 3, r3DerivMultiplier ψ i ξ * ((𝓕 u : R3L2Velocity) : R3 → R3C) ξ i)
        =ᵐ[volume] (fun _ => (0 : ℂ)) := by
      filter_upwards [hraw] with ξ hξ
      rw [hpt ξ, hξ]
      ring
    rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_zero]
  have hLHS : r3TemperedDivergence (r3L2ToTemperedCLM u) φ = 0 := by
    rw [r3TemperedDivergence_apply, hsum, hzero, neg_zero]
  rw [hLHS]
  rfl

end

end MNS2
