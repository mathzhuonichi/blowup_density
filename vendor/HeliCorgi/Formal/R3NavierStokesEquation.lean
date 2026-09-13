import Formal.R3ProjectedMomentumEquation

/-!
# The incompressible Navier–Stokes equation along a mild solution
(Clay semantic-promotion edge 2b-ii.b — closing edge 2b)

This file is a **composition pass**: no new analysis is built (the only new mathematical
content is the algebraic propagation of solenoidality along the mild identity).  It
combines

* the projected momentum equation of edge 2b-ii.a
  (`r3EndpointSafeProjectedMild_momentum`: `∂ₜU = νΔU − P((U·∇)U)` with a strong
  `L²`-valued time derivative at interior times),
* the edge-2a Helmholtz pressure witness (`r3HelmholtzPressure`,
  `r3HelmholtzPressure_gradient`: `∇p = −(I−P)F` componentwise in `𝓢'`), **consumed** at
  the edge-2b-i identified convection source, and
* the repository's solenoidal machinery (Stokes and smoothing preservation, the closed
  kernel description of `r3L2SolenoidalSubmodule`, the edge-3a decode preservation, and
  the edge-1a distributional divergence theorem)

into the **incompressible Navier–Stokes equation** for the decoded physical velocity
`U t = r3H3ToL2Operator (u t)` of a mild solution with solenoidal initial coordinate:

`∂ₜU − νΔU + (U·∇)U + ∇p = 0` (componentwise in `𝓢'`, with the strong `L²` time
derivative and the explicit pressure `p = r3HelmholtzPressure ((U·∇)U)`), and

`∇·U = 0` (the distributional physical-coordinate divergence, edge 1a).

Capstone: `r3EndpointSafeProjectedMild_navierStokes`; existence composition:
`exists_r3EndpointSafeProjectedMild_navierStokes`.

Honest scope: the equation is componentwise in `𝓢'(R3, ℂ)` in space with a strong
`L²`-valued derivative in time, at interior times only, on the complex carrier; the
pressure is the explicit edge-2a witness (determined up to additive harmonic terms, as
recorded there); realness of the solution is neither used nor asserted here — for real
data the *coordinate* trajectory is unconditionally real
(`IsR3EndpointSafeProjectedMildSolutionOn.isR3RealVelocity`), but realness of the
*decoded* field is not transported in this file.  No claim of global smoothness,
blow-up, or any Clay-level result is made.
-/

namespace MNS2

open MeasureTheory FourierTransform Real LineDeriv intervalIntegral
open scoped FourierTransform SchwartzMap ContDiff NNReal

noncomputable section

variable {ν T : ℝ} {u₀ : R3HsVelocity 3} {u : ℝ → R3HsVelocity 3}

/-! ## Solenoidality propagates along a mild solution -/

/-- The endpoint-safe Duhamel integrand kills the normalized divergence at every time
(for slice times before the horizon it is a flowed projected convection, hence
solenoidal; at and beyond the horizon it vanishes). -/
theorem r3NormalizedDivergence_duhamelIntegrand (hnu : 0 < ν)
    (u : ℝ → R3HsVelocity 3) (σ : ℝ) (s : ℝ) :
    r3NormalizedDivergenceL2OperatorAux
      (r3EndpointSafeProjectedDuhamelIntegrand hnu σ u s) = 0 := by
  rcases lt_or_ge s σ with hs | hs
  · have hmem : r3EndpointSafeProjectedDuhamelIntegrand hnu σ u s ∈
        r3L2SolenoidalSubmodule := by
      rw [r3EndpointSafeProjectedDuhamelIntegrand_of_lt hnu σ u hs]
      exact r3StokesH2ToH3Operator_mem_solenoidal hnu (sub_pos.mpr hs)
        (r3ProjectedConvectionH3ToH2 (u s) (u s))
        (r3ProjectedConvectionH3ToH2_mem_solenoidal (u s) (u s))
    exact hmem
  · rw [r3EndpointSafeProjectedDuhamelIntegrand_of_le hnu σ u hs, map_zero]

/-- **Solenoidality propagates**: a mild solution with solenoidal initial coordinate
stays in the solenoidal submodule at every certified time. -/
theorem r3EndpointSafeProjectedMild_mem_solenoidal (hnu : 0 < ν)
    (hu : IsR3EndpointSafeProjectedMildSolutionOn hnu T u₀ u)
    (hsol : u₀ ∈ r3L2SolenoidalSubmodule) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    u t ∈ r3L2SolenoidalSubmodule := by
  obtain ⟨hint, heq⟩ := r3EndpointSafeProjectedMild_equation_at_time hnu hu ht
  have hlin : r3NormalizedDivergenceL2OperatorAux
      (r3StokesH3Evolution hnu.le ⟨t, ht.1⟩ u₀) = 0 := by
    have hmem : r3StokesH3Evolution hnu.le ⟨t, ht.1⟩ u₀ ∈ r3L2SolenoidalSubmodule := by
      exact r3StokesL2Operator_mem_solenoidal hnu.le ht.1 u₀ hsol
    exact hmem
  have hduh : r3NormalizedDivergenceL2OperatorAux
      (∫ s in (0 : ℝ)..t, r3EndpointSafeProjectedDuhamelIntegrand hnu t u s) = 0 := by
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm
      r3NormalizedDivergenceL2OperatorAux hint]
    rw [intervalIntegral.integral_congr
      (g := fun _ : ℝ => (0 : R3L2ScalarAux))
      (fun s _ => r3NormalizedDivergence_duhamelIntegrand hnu u t s)]
    exact intervalIntegral.integral_zero
  show u t ∈ r3L2SolenoidalSubmodule
  have hval : r3NormalizedDivergenceL2OperatorAux (u t) = 0 := by
    rw [heq, map_sub, hlin, hduh, sub_zero]
  exact LinearMap.mem_ker.mpr hval

/-- The order-three decode preserves solenoidality (edge-3a machinery, restated for the
bounded multiplier decoder). -/
theorem r3H3ToL2Operator_mem_solenoidal_of_mem {f : R3HsVelocity 3}
    (hf : f ∈ r3L2SolenoidalSubmodule) :
    r3H3ToL2Operator f ∈ r3L2SolenoidalSubmodule := by
  rw [← r3Decoded3PhysicalVelocity_eq]
  exact r3Decoded3PhysicalVelocity_mem_solenoidal hf

/-! ## The pressure completes the projection -/

/-- **The Helmholtz completion of the Leray projection** (edge-2a consumption): for every
`L²` source, the embedded projection is the embedded source plus the pressure gradient,
componentwise in `𝓢'`. -/
theorem postcomp_r3LerayL2Operator_eq (F : R3L2Velocity) (j : Fin 3) :
    PointwiseConvergenceCLM.postcomp 𝓢(R3, ℂ) (EuclideanSpace.proj j : R3C →L[ℂ] ℂ)
        ((r3LerayL2Operator F : R3L2Velocity) : 𝓢'(R3, R3C)) =
      PointwiseConvergenceCLM.postcomp 𝓢(R3, ℂ) (EuclideanSpace.proj j : R3C →L[ℂ] ℂ)
          ((F : R3L2Velocity) : 𝓢'(R3, R3C)) +
        ∂_{r3StdBasis j} (r3HelmholtzPressure F) := by
  have hgrad := r3HelmholtzPressure_gradient F j
  have hsplit : (r3LerayL2Operator F : R3L2Velocity) = F - r3LerayComplementL2 F := by
    unfold r3LerayComplementL2
    abel
  rw [hsplit]
  rw [show ((F - r3LerayComplementL2 F : R3L2Velocity) : 𝓢'(R3, R3C)) =
      ((F : R3L2Velocity) : 𝓢'(R3, R3C)) -
        ((r3LerayComplementL2 F : R3L2Velocity) : 𝓢'(R3, R3C)) from
    map_sub r3L2ToTemperedCLM F (r3LerayComplementL2 F)]
  rw [map_sub, hgrad]
  abel

/-! ## The incompressible Navier–Stokes equation -/

set_option maxHeartbeats 1000000 in
/-- **Clay semantic-promotion edge 2b-ii.b: the incompressible Navier–Stokes equation
along a mild solution.**

For a mild solution with solenoidal initial coordinate, at every interior time the
decoded physical velocity `U s = r3H3ToL2Operator (u s)`:

1. has the strong `L²`-valued time derivative
   `∂ₜU = νΔU − P((U·∇)U)` (edge 2b-ii.a);
2. satisfies, componentwise in `𝓢'` with the explicit edge-2a pressure
   `p = r3HelmholtzPressure ((U·∇)U)`, the **unprojected momentum equation**
   `∂ₜU = νΔU − (U·∇)U − ∇p`, i.e. `∂ₜU − νΔU + (U·∇)U + ∇p = 0`;
3. is **incompressible**: the distributional physical-coordinate divergence of `U t`
   vanishes (edge 1a). -/
theorem r3EndpointSafeProjectedMild_navierStokes (hnu : 0 < ν)
    (hu : IsR3EndpointSafeProjectedMildSolutionOn hnu T u₀ u)
    (hsol : u₀ ∈ r3L2SolenoidalSubmodule) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun s : ℝ => r3H3ToL2Operator (u s))
        (ν • r3H3LaplacianL2Operator (u t) -
          r3LerayL2Operator (r3DecodedConvectionL2 (u t) (u t))) t ∧
      (∀ j : Fin 3,
        PointwiseConvergenceCLM.postcomp 𝓢(R3, ℂ) (EuclideanSpace.proj j : R3C →L[ℂ] ℂ)
            ((ν • r3H3LaplacianL2Operator (u t) -
              r3LerayL2Operator (r3DecodedConvectionL2 (u t) (u t)) :
                R3L2Velocity) : 𝓢'(R3, R3C)) =
          PointwiseConvergenceCLM.postcomp 𝓢(R3, ℂ)
              (EuclideanSpace.proj j : R3C →L[ℂ] ℂ)
              ((ν • r3H3LaplacianL2Operator (u t) : R3L2Velocity) : 𝓢'(R3, R3C)) -
            PointwiseConvergenceCLM.postcomp 𝓢(R3, ℂ)
              (EuclideanSpace.proj j : R3C →L[ℂ] ℂ)
              ((r3DecodedConvectionL2 (u t) (u t) : R3L2Velocity) : 𝓢'(R3, R3C)) -
            ∂_{r3StdBasis j}
              (r3HelmholtzPressure (r3DecodedConvectionL2 (u t) (u t)))) ∧
      r3TemperedDivergence (r3L2ToTemperedCLM (r3H3ToL2Operator (u t))) = 0 := by
  refine ⟨r3EndpointSafeProjectedMild_momentum hnu hu ht, fun j => ?_, ?_⟩
  · rw [show ((ν • r3H3LaplacianL2Operator (u t) -
        r3LerayL2Operator (r3DecodedConvectionL2 (u t) (u t)) : R3L2Velocity) :
          𝓢'(R3, R3C)) =
        ((ν • r3H3LaplacianL2Operator (u t) : R3L2Velocity) : 𝓢'(R3, R3C)) -
          ((r3LerayL2Operator (r3DecodedConvectionL2 (u t) (u t)) : R3L2Velocity) :
            𝓢'(R3, R3C)) from
      map_sub r3L2ToTemperedCLM _ _]
    rw [map_sub, postcomp_r3LerayL2Operator_eq]
    abel
  · exact r3TemperedDivergence_eq_zero_of_mem_solenoidal _
      (r3H3ToL2Operator_mem_solenoidal_of_mem
        (r3EndpointSafeProjectedMild_mem_solenoidal hnu hu hsol ⟨ht.1.le, ht.2.le⟩))

/-- **Non-vacuity by composition with local existence**: for every viscosity and every
solenoidal initial coordinate there is a certified positive horizon and a mild solution
along which the full conclusion of the capstone — the strong `L²` time derivative, the
unprojected momentum equation with the explicit pressure, and incompressibility — holds
at every interior time.  (Solenoidal data exist in abundance: every Leray projection
qualifies, `r3LerayL2Operator_mem_solenoidal`.) -/
theorem exists_r3EndpointSafeProjectedMild_navierStokes {ν : ℝ} (hnu : 0 < ν)
    (u₀ : R3HsVelocity 3) (hsol : u₀ ∈ r3L2SolenoidalSubmodule) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → R3HsVelocity 3,
      IsR3EndpointSafeProjectedMildSolutionOn hnu T u₀ u ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) T,
        HasDerivAt (fun s : ℝ => r3H3ToL2Operator (u s))
            (ν • r3H3LaplacianL2Operator (u t) -
              r3LerayL2Operator (r3DecodedConvectionL2 (u t) (u t))) t ∧
        (∀ j : Fin 3,
          PointwiseConvergenceCLM.postcomp 𝓢(R3, ℂ)
              (EuclideanSpace.proj j : R3C →L[ℂ] ℂ)
              ((ν • r3H3LaplacianL2Operator (u t) -
                r3LerayL2Operator (r3DecodedConvectionL2 (u t) (u t)) :
                  R3L2Velocity) : 𝓢'(R3, R3C)) =
            PointwiseConvergenceCLM.postcomp 𝓢(R3, ℂ)
                (EuclideanSpace.proj j : R3C →L[ℂ] ℂ)
                ((ν • r3H3LaplacianL2Operator (u t) : R3L2Velocity) : 𝓢'(R3, R3C)) -
              PointwiseConvergenceCLM.postcomp 𝓢(R3, ℂ)
                (EuclideanSpace.proj j : R3C →L[ℂ] ℂ)
                ((r3DecodedConvectionL2 (u t) (u t) : R3L2Velocity) : 𝓢'(R3, R3C)) -
              ∂_{r3StdBasis j}
                (r3HelmholtzPressure (r3DecodedConvectionL2 (u t) (u t)))) ∧
        r3TemperedDivergence (r3L2ToTemperedCLM (r3H3ToL2Operator (u t))) = 0 := by
  obtain ⟨T, hT, -, u, hu, -⟩ :=
    r3EndpointSafeProjected_exists_localMildSolution hnu u₀
  exact ⟨T, hT, u, hu, fun t ht =>
    r3EndpointSafeProjectedMild_navierStokes hnu hu hsol ht⟩

end

end MNS2
