import Formal.R3ConvectionSourceIdentification
import Formal.R3ConvectionConjugationEquivariance
import Formal.R3DecodedVelocityRealness
import Formal.R3FiniteEnergy
import Formal.R3MildContinuation
import Formal.R3SchwartzDivergence

/-!
# Admissible Schwartz initial data (Clay semantic edge 3, adapter form)

Stage-9 readiness pass, Task B: the smallest concrete initial-data bridge into the
certified local Navier–Stokes theory.  No arbitrary-`H³` characterization is attempted
(`H³ ⇒ C^∞` is false and is not claimed); instead one concrete admissible class is
certified: **real, divergence-free Schwartz velocity fields**.

* `IsR3AdmissibleSchwartzDatum` — the interface predicate: the Schwartz field is a fixed
  point of conjugation (physically real) and its Fourier transform has vanishing raw
  frequency divergence `ξ · 𝓕φ(ξ) = 0` at every frequency.  The frequency-side condition
  is the *defining* one; the classical pointwise divergence-free property of the field
  itself is derived below as a theorem, not assumed.
* `r3SchwartzConjCLM_eq_self_iff` — the realness hypothesis is exactly pointwise
  vanishing of every imaginary part.
* `r3H3ToL2Operator_r3SchwartzToHsCLM` — **decode ∘ encode = identity** on the Schwartz
  core at order three: the bounded `J⁻³` decoder returns the literal physical `L²` field
  of the canonical coordinate (transposition of the proved order-two identity
  `r3H2ToL2Operator_r3SchwartzToHsCLM`; the `𝓢'` version
  `r3HsToTempered_r3SchwartzToHsCLM` already exists, and the pointwise-everywhere version
  for the explicit representative is `r3DecodedRepresentative_schwartz`).
* `IsR3AdmissibleSchwartzDatum.encode_mem_solenoidal` — the encoded coordinate lies in
  the closed solenoidal submodule consumed by the Navier–Stokes capstone.
* `IsR3AdmissibleSchwartzDatum.classicalDivergence` — the admissible field itself is
  classically divergence-free at every point (derived by decoding: the explicit physical
  representative of the encoded coordinate is the field itself, and solenoidal
  coordinates decode to everywhere divergence-free representatives).
* `isR3AdmissibleSchwartzDatum_iff` — the interface is *exactly* "real and classically
  divergence-free" (`Formal/R3SchwartzDivergence.lean` supplies the equivalence of the two
  divergence formulations on the Schwartz core, in both directions).  This gives a second,
  independent derivation of the previous item — the decoding route and the
  Fourier-multiplier route agree.
* `IsR3AdmissibleSchwartzDatum.isR3RealVelocity_encode` — the encoded coordinate is
  physically real, feeding the realness half of the local theory.
* `r3Schwartz_finiteEnergy` — the literal field has finite kinetic energy.
* `r3AdmissibleSchwartzDatum_navierStokes` — **Stage-9 entry capstone**: from a real
  divergence-free Schwartz datum, a certified local mild solution whose decoded physical
  velocity starts at the literal datum, is physically real at every certified time, has
  finite kinetic energy at every time, and satisfies the incompressible Navier–Stokes
  equations (strong `L²` time derivative, componentwise `𝓢'` momentum equation with the
  explicit Helmholtz pressure, distributional incompressibility) at every interior time.
* `r3AdmissibleSchwartzDatum_blowup_dichotomy` — the same datum entering the already-proved
  continuation machinery, so the readiness audit's Gate C is consumed rather than claimed.
* `exists_isR3AdmissibleSchwartzDatum_ne_zero` — **non-vacuity**: an explicit nonzero real
  divergence-free Schwartz field, built on the frequency side from the existing plateau
  bump, so the entry capstone is neither an empty implication nor a statement about the
  trivial datum only.

Scope guards: the semantics are exactly those of
`r3EndpointSafeProjectedMild_navierStokes` — local horizon, interior times, spatial
distributions, pressure up to harmonic terms.  Smoothness (`ContDiff ℝ ∞`) and rapid
decay of the datum are the Schwartz-class properties of `φ` itself (mathlib's
`SchwartzMap.smooth` / `SchwartzMap.decay`); they are *not* claimed for the solution at
positive times.  No Clay-level claim.
-/

namespace MNS2

open MeasureTheory FourierTransform Real LineDeriv intervalIntegral
open scoped FourierTransform SchwartzMap ContDiff ENNReal NNReal ComplexConjugate

noncomputable section

/-! ## The admissible-datum interface -/

/-- A concrete admissible initial datum: a Schwartz velocity field that is physically
real (fixed point of conjugation) and divergence-free in the raw frequency sense
`ξ · 𝓕φ(ξ) = 0` for every `ξ`.  The classical pointwise divergence-free property is
derived in `IsR3AdmissibleSchwartzDatum.classicalDivergence`. -/
def IsR3AdmissibleSchwartzDatum (φ : R3SchwartzVelocity) : Prop :=
  r3SchwartzConjCLM φ = φ ∧
    ∀ ξ : R3, r3RawDivergencePointwise ξ ((𝓕 φ : R3SchwartzVelocity) ξ) = 0

/-- The realness half of the interface is exactly pointwise vanishing of every imaginary
part of the field. -/
theorem r3SchwartzConjCLM_eq_self_iff (φ : R3SchwartzVelocity) :
    r3SchwartzConjCLM φ = φ ↔ ∀ x : R3, ∀ i : Fin 3, (φ x i).im = 0 := by
  constructor
  · intro h x
    have hx : r3SchwartzConjCLM φ x = φ x := by rw [h]
    rw [r3SchwartzConjCLM_apply] at hx
    exact (r3CConj_eq_self_iff (φ x)).mp hx
  · intro h
    ext x
    rw [r3SchwartzConjCLM_apply]
    exact congrFun (congrArg _ ((r3CConj_eq_self_iff (φ x)).mpr (h x))) _

/-! ## Decode ∘ encode on the order-three Schwartz core -/

/-- Canonical order-three Schwartz coordinates decode to their literal physical `L²`
field: the bounded `J⁻³` decoder inverts the canonical encoder on the Schwartz core. -/
@[simp]
theorem r3H3ToL2Operator_r3SchwartzToHsCLM (f : R3SchwartzVelocity) :
    r3H3ToL2Operator (r3SchwartzToHsCLM 3 f) = f.toLp 2 := by
  apply (MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C).injective
  change 𝓕 (r3H3ToL2Operator (r3SchwartzToHsCLM 3 f)) = 𝓕 (f.toLp 2)
  rw [fourier_r3H3ToL2Operator, r3SchwartzToHsCLM_apply,
    SchwartzMap.toLp_fourier_eq, fourier_r3SchwartzBesselCoordinate,
    SchwartzMap.toLp_fourier_eq]
  letI : ENNReal.HolderTriple (⊤ : ℝ≥0∞) (2 : ℝ≥0∞) (2 : ℝ≥0∞) := ⟨by simp⟩
  change r3H3InverseBesselWeightLpTop •
      (r3SchwartzSobolevFrequencyCoordinate 3 f).toLp 2 =
    (𝓕 f).toLp 2
  apply Lp.ext
  filter_upwards
    [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) r3H3InverseBesselWeightLpTop
      ((r3SchwartzSobolevFrequencyCoordinate 3 f).toLp 2),
      r3H3InverseBesselWeightLpTop_ae,
      (r3SchwartzSobolevFrequencyCoordinate 3 f).coeFn_toLp 2
        (volume : Measure R3),
      (𝓕 f).coeFn_toLp 2 (volume : Measure R3)]
    with ξ hmul hinv hweighted hfourier
  rw [hmul, Pi.smul_apply', hinv, hweighted, hfourier]
  unfold r3SchwartzSobolevFrequencyCoordinate
  rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop), smul_smul]
  change
    (r3H3InverseBesselWeightComplex ξ * r3SobolevWeightComplex 3 ξ) •
      (𝓕 f) ξ = (𝓕 f) ξ
  rw [r3H3InverseBesselWeightComplex_mul_weight_three, one_smul]

/-! ## The encoded coordinate is solenoidal -/

/-- The normalized frequency divergence is `ℂ`-homogeneous in the fiber. -/
theorem r3NormalizedDivergencePointwise_smul (ξ : R3) (c : ℂ) (v : R3C) :
    r3NormalizedDivergencePointwise ξ (c • v) =
      c * r3NormalizedDivergencePointwise ξ v := by
  unfold r3NormalizedDivergencePointwise
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

/-- The canonical order-three coordinate of an admissible Schwartz datum lies in the
closed solenoidal submodule — the exact hypothesis of the Navier–Stokes capstone. -/
theorem IsR3AdmissibleSchwartzDatum.encode_mem_solenoidal {φ : R3SchwartzVelocity}
    (hφ : IsR3AdmissibleSchwartzDatum φ) :
    r3SchwartzToHsCLM 3 φ ∈ r3L2SolenoidalSubmodule := by
  have hfourier : 𝓕 (r3SchwartzToHsCLM 3 φ : R3L2Velocity) =
      (r3SchwartzSobolevFrequencyCoordinate 3 φ).toLp 2 := by
    rw [r3SchwartzToHsCLM_apply, SchwartzMap.toLp_fourier_eq,
      fourier_r3SchwartzBesselCoordinate]
  rw [mem_r3L2SolenoidalSubmodule_iff]
  have hcomp : r3NormalizedDivergenceL2OperatorAux (r3SchwartzToHsCLM 3 φ) =
      r3NormalizedDivergenceFrequencyAux
        ((r3SchwartzSobolevFrequencyCoordinate 3 φ).toLp 2) := by
    simp only [r3NormalizedDivergenceL2OperatorAux, ContinuousLinearMap.comp_apply]
    rw [FourierTransform.fourierCLM_apply, hfourier]
  rw [hcomp, MeasureTheory.Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards
    [r3NormalizedDivergenceFrequencyAux_ae
      ((r3SchwartzSobolevFrequencyCoordinate 3 φ).toLp 2),
      (r3SchwartzSobolevFrequencyCoordinate 3 φ).coeFn_toLp 2 (volume : Measure R3)]
    with ξ h1 h2
  rw [h1, h2]
  have hsingle : r3SchwartzSobolevFrequencyCoordinate 3 φ ξ =
      Complex.ofReal ((1 + ‖ξ‖ ^ 2) ^ ((3 : ℝ) / 2)) •
        (𝓕 φ : R3SchwartzVelocity) ξ := by
    unfold r3SchwartzSobolevFrequencyCoordinate
    rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
  rw [hsingle, r3NormalizedDivergencePointwise_smul,
    (r3NormalizedDivergencePointwise_eq_zero_iff ξ _).mpr (hφ.2 ξ), mul_zero]
  rfl

/-! ## Certificates for the literal datum -/

/-- The admissible field itself is classically divergence-free at every point: decoding
the encoded coordinate returns the field (`r3DecodedRepresentative_schwartz`), and
solenoidal coordinates decode to everywhere divergence-free `C¹` representatives. -/
theorem IsR3AdmissibleSchwartzDatum.classicalDivergence {φ : R3SchwartzVelocity}
    (hφ : IsR3AdmissibleSchwartzDatum φ) (x : R3) :
    r3ClassicalDivergence (⇑φ) x = 0 := by
  have h := (r3DecodedFrequency_incompressible hφ.encode_mem_solenoidal).2 x
  rwa [r3DecodedRepresentative_schwartz] at h

/-- **Honest characterization of the interface.**  The admissible class is *exactly* the class
of real, classically divergence-free Schwartz velocity fields: the frequency-side condition in
the definition is equivalent to the standard pointwise one
(`r3Schwartz_rawDivergence_fourier_iff_classical`), and the conjugation fixed-point condition is
equivalent to pointwise vanishing of every imaginary part.  So nothing convenient was smuggled
into the definition. -/
theorem isR3AdmissibleSchwartzDatum_iff (φ : R3SchwartzVelocity) :
    IsR3AdmissibleSchwartzDatum φ ↔
      ((∀ x : R3, ∀ i : Fin 3, (φ x i).im = 0) ∧
        ∀ x : R3, r3ClassicalDivergence (⇑φ) x = 0) := by
  unfold IsR3AdmissibleSchwartzDatum
  rw [r3SchwartzConjCLM_eq_self_iff, r3Schwartz_rawDivergence_fourier_iff_classical]

/-- The encoded coordinate of an admissible Schwartz datum is physically real. -/
theorem IsR3AdmissibleSchwartzDatum.isR3RealVelocity_encode {φ : R3SchwartzVelocity}
    (hφ : IsR3AdmissibleSchwartzDatum φ) :
    IsR3RealVelocity (r3SchwartzToHsCLM 3 φ) := by
  unfold IsR3RealVelocity
  rw [r3L2Conj_r3SchwartzToHsCLM, hφ.1]

/-- Smoothness certificate: every admissible datum is `C^∞` (Schwartz class). -/
theorem IsR3AdmissibleSchwartzDatum.smooth {φ : R3SchwartzVelocity}
    (_hφ : IsR3AdmissibleSchwartzDatum φ) : ContDiff ℝ ∞ (⇑φ) :=
  φ.smooth'

/-- Rapid-decay certificate: every admissible datum decays faster than any polynomial,
together with all its derivatives (Schwartz class). -/
theorem IsR3AdmissibleSchwartzDatum.decay {φ : R3SchwartzVelocity}
    (_hφ : IsR3AdmissibleSchwartzDatum φ) :
    ∀ k n : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ x : R3, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑φ) x‖ ≤ C :=
  φ.decay

/-- Finite kinetic energy of the literal Schwartz field. -/
theorem r3Schwartz_finiteEnergy (φ : R3SchwartzVelocity) :
    Integrable (fun x : R3 => ‖φ x‖ ^ 2) volume ∧
      (∫ x : R3, ‖φ x‖ ^ 2) = ‖(φ.toLp 2 : R3L2Velocity)‖ ^ 2 := by
  set g : R3L2Velocity := φ.toLp 2 with hg
  have hae : (fun x : R3 => ‖(g : R3 → R3C) x‖ ^ 2)
      =ᵐ[volume] fun x : R3 => ‖φ x‖ ^ 2 := by
    filter_upwards [φ.coeFn_toLp 2 (volume : Measure R3)] with x hx
    rw [hg, hx]
  refine ⟨(integrable_norm_sq_r3L2 g).congr hae, ?_⟩
  rw [← integral_congr_ae hae, integral_norm_sq_r3L2 g]

/-! ## Stage-9 entry capstone -/

/-- **Stage-9 entry capstone.**  From a real divergence-free Schwartz datum: a certified
local mild solution whose decoded physical velocity starts at the literal datum, is
physically real at every certified time, has finite kinetic energy at every time, and
satisfies the incompressible Navier–Stokes equations — strong `L²` time derivative,
componentwise `𝓢'` unprojected momentum equation with the explicit Helmholtz pressure,
and distributional incompressibility — at every interior time of the horizon. -/
theorem r3AdmissibleSchwartzDatum_navierStokes {ν : ℝ} (hnu : 0 < ν)
    {φ : R3SchwartzVelocity} (hφ : IsR3AdmissibleSchwartzDatum φ) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → R3HsVelocity 3,
      IsR3EndpointSafeProjectedMildSolutionOn hnu T (r3SchwartzToHsCLM 3 φ) u ∧
      r3H3ToL2Operator (u 0) = φ.toLp 2 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, IsR3RealVelocity (r3H3ToL2Operator (u t))) ∧
      (∀ t : ℝ,
        Integrable (fun x : R3 =>
          ‖((r3H3ToL2Operator (u t) : R3L2Velocity) : R3 → R3C) x‖ ^ 2) volume ∧
        (∫ x : R3, ‖((r3H3ToL2Operator (u t) : R3L2Velocity) : R3 → R3C) x‖ ^ 2) =
          ‖r3H3ToL2Operator (u t)‖ ^ 2) ∧
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
  obtain ⟨T, hT, u, hu, hns⟩ :=
    exists_r3EndpointSafeProjectedMild_navierStokes hnu (r3SchwartzToHsCLM 3 φ)
      hφ.encode_mem_solenoidal
  refine ⟨T, hT, u, hu, ?_, ?_, ?_, hns⟩
  · rw [hu.2.2.1, r3H3ToL2Operator_r3SchwartzToHsCLM]
  · exact r3EndpointSafeProjectedMild_isR3RealVelocity_decoded hu
      hφ.isR3RealVelocity_encode
  · exact fun t => r3DecodedVelocity_finiteEnergy (u t)

/-! ## Entry into the continuation machinery -/

/-- **Gate C, consumed**: the admissible Schwartz datum enters the already-proved
continuation theory verbatim — either arbitrarily long horizons carry certified mild
solutions from this datum, or the certified solution norms escape every ball.  This is the
existing `r3EndpointSafeProjected_blowup_dichotomy` instantiated at the encoded datum; no
new continuation packaging, and in particular no canonical maximal trajectory, is built. -/
theorem r3AdmissibleSchwartzDatum_blowup_dichotomy {ν : ℝ} (hnu : 0 < ν)
    {φ : R3SchwartzVelocity} (_hφ : IsR3AdmissibleSchwartzDatum φ) :
    (∀ M : ℝ, ∃ T ∈ r3MildHorizons hnu (r3SchwartzToHsCLM 3 φ), M ≤ T) ∨
      ∀ R : ℝ, 0 ≤ R →
        ∃ T ∈ r3MildHorizons hnu (r3SchwartzToHsCLM 3 φ), ∃ u : ℝ → R3HsVelocity 3,
          IsR3EndpointSafeProjectedMildSolutionOn hnu T (r3SchwartzToHsCLM 3 φ) u ∧
          ∃ t ∈ Set.Icc (0 : ℝ) T, R < ‖u t‖ :=
  r3EndpointSafeProjected_blowup_dichotomy hnu (r3SchwartzToHsCLM 3 φ)

/-! ## Non-vacuity witness

The admissible class is not the empty class, and the capstone is not applied to the trivial
datum `0`.  The witness is built on the **frequency** side, where both halves of
`IsR3AdmissibleSchwartzDatum` are elementary.  Write `b := r3ConvectionWitnessBump` for the
real, even, compactly supported plateau bump already used as the convection witness, and set

`F ξ := i ⬝ b ξ ⬝ (ξ₁ e₀ - ξ₀ e₁)`.

Then `ξ · F ξ = i ⬝ b ξ ⬝ (ξ₀ξ₁ - ξ₁ξ₀) = 0` identically, and `F` is fixed by reflected
conjugation (`b` is real and even; the vector factor is odd with real entries), which is the
frequency-side form of physical realness.  The datum is `φ := 𝓕⁻ F`.  Fourier inversion on
Schwartz space is an exact continuous linear equivalence, so `𝓕 φ = F` holds literally — no
almost-everywhere, `L²` or density argument is consumed anywhere in this section. -/

/-- The raw frequency-coordinate symbol `ξ ↦ ξⱼ`, complexified. -/
def r3SchwartzWitnessCoordinate (j : Fin 3) : R3 → ℂ := fun ξ => ((ξ j : ℝ) : ℂ)

/-- The frequency-coordinate symbol has temperate growth: it is a continuous linear map. -/
theorem hasTemperateGrowth_r3SchwartzWitnessCoordinate (j : Fin 3) :
    Function.HasTemperateGrowth (r3SchwartzWitnessCoordinate j) := by
  have hcoe : r3SchwartzWitnessCoordinate j =
      ⇑(Complex.ofRealCLM ∘L (EuclideanSpace.proj j : R3 →L[ℝ] ℝ)) := rfl
  rw [hcoe]
  exact ContinuousLinearMap.hasTemperateGrowth _

/-- The building block `ξ ↦ ξⱼ ⬝ b ξ ⬝ e_k` of the frequency profile, as a Schwartz map: the
complexified bump pushed into the `e_k` fiber direction, then multiplied by the `j`-th
frequency coordinate (a temperate-growth symbol). -/
def r3SchwartzWitnessBlock (k j : Fin 3) : R3SchwartzVelocity :=
  SchwartzMap.smulLeftCLM R3C (r3SchwartzWitnessCoordinate j)
    (SchwartzMap.postcompCLM
      (ContinuousLinearMap.toSpanSingleton ℂ (EuclideanSpace.single k (1 : ℂ) : R3C))
      r3ConvectionWitnessScalar)

/-- Pointwise value of a building block. -/
theorem r3SchwartzWitnessBlock_apply (k j : Fin 3) (ξ : R3) :
    r3SchwartzWitnessBlock k j ξ =
      (((ξ j : ℝ) : ℂ) * ((r3ConvectionWitnessBump ξ : ℝ) : ℂ)) •
        (EuclideanSpace.single k (1 : ℂ) : R3C) := by
  rw [r3SchwartzWitnessBlock,
    SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_r3SchwartzWitnessCoordinate j)]
  show ((ξ j : ℝ) : ℂ) • (((r3ConvectionWitnessBump ξ : ℝ) : ℂ) •
    (EuclideanSpace.single k (1 : ℂ) : R3C)) = _
  rw [smul_smul]

/-- The frequency profile of the witness: `F ξ = i ⬝ b ξ ⬝ (ξ₁ e₀ - ξ₀ e₁)`, a Schwartz map
because it is a fixed linear combination of the temperate-growth-weighted bump blocks. -/
def r3SchwartzWitnessFrequency : R3SchwartzVelocity :=
  Complex.I • (r3SchwartzWitnessBlock 0 1 - r3SchwartzWitnessBlock 1 0)

/-- First component of the frequency profile: `i ⬝ ξ₁ ⬝ b ξ`. -/
theorem r3SchwartzWitnessFrequency_apply_zero (ξ : R3) :
    r3SchwartzWitnessFrequency ξ 0 =
      Complex.I * (((ξ 1 : ℝ) * (r3ConvectionWitnessBump ξ : ℝ) : ℝ) : ℂ) := by
  simp [r3SchwartzWitnessFrequency, r3SchwartzWitnessBlock_apply]

/-- Second component of the frequency profile: `-(i ⬝ ξ₀ ⬝ b ξ)`. -/
theorem r3SchwartzWitnessFrequency_apply_one (ξ : R3) :
    r3SchwartzWitnessFrequency ξ 1 =
      -(Complex.I * (((ξ 0 : ℝ) * (r3ConvectionWitnessBump ξ : ℝ) : ℝ) : ℂ)) := by
  simp [r3SchwartzWitnessFrequency, r3SchwartzWitnessBlock_apply]

/-- Third component of the frequency profile: the profile is planar. -/
theorem r3SchwartzWitnessFrequency_apply_two (ξ : R3) :
    r3SchwartzWitnessFrequency ξ 2 = 0 := by
  simp [r3SchwartzWitnessFrequency, r3SchwartzWitnessBlock_apply]

/-- The frequency profile is divergence-free at every frequency: the two surviving terms of
`ξ · F ξ` are `i b ξ ⬝ ξ₀ξ₁` and `-i b ξ ⬝ ξ₁ξ₀`. -/
theorem r3SchwartzWitnessFrequency_divergence (ξ : R3) :
    r3RawDivergencePointwise ξ (r3SchwartzWitnessFrequency ξ) = 0 := by
  unfold r3RawDivergencePointwise
  rw [r3SchwartzWitnessFrequency_apply_zero, r3SchwartzWitnessFrequency_apply_one,
    r3SchwartzWitnessFrequency_apply_two]
  push_cast
  ring

/-- The frequency profile is conjugate-symmetric, `conj (F (-ξ)) = F ξ`: the bump is real and
even, and the vector factor is odd with real entries. -/
theorem r3SchwartzWitnessFrequency_conjSymm :
    r3SchwartzReflectCLM (r3SchwartzConjCLM r3SchwartzWitnessFrequency) =
      r3SchwartzWitnessFrequency := by
  refine SchwartzMap.ext fun ξ => ?_
  rw [r3SchwartzReflectCLM_apply, r3SchwartzConjCLM_apply]
  have hb : (r3ConvectionWitnessBump (-ξ) : ℝ) = r3ConvectionWitnessBump ξ :=
    r3ConvectionWitnessBump.neg ξ
  ext i
  fin_cases i <;>
    simp [r3SchwartzWitnessFrequency_apply_zero, r3SchwartzWitnessFrequency_apply_one,
      r3SchwartzWitnessFrequency_apply_two, hb]

/-- The witness datum: the Schwartz inverse Fourier transform of the frequency profile. -/
def r3SchwartzWitnessDatum : R3SchwartzVelocity := 𝓕⁻ r3SchwartzWitnessFrequency

/-- Exact Fourier inversion on Schwartz space: the datum has the designed frequency profile,
with no almost-everywhere qualification. -/
theorem fourier_r3SchwartzWitnessDatum :
    (𝓕 r3SchwartzWitnessDatum : R3SchwartzVelocity) = r3SchwartzWitnessFrequency :=
  fourier_fourierInv_eq _

/-- The witness datum is physically real, by conjugate symmetry of its frequency profile. -/
theorem r3SchwartzWitnessDatum_real :
    r3SchwartzConjCLM r3SchwartzWitnessDatum = r3SchwartzWitnessDatum := by
  rw [r3SchwartzWitnessDatum, r3SchwartzConjCLM_fourierInv, r3SchwartzWitnessFrequency_conjSymm]

/-- A frequency inside the bump plateau at which the profile is visibly nonzero. -/
def r3SchwartzWitnessPoint : R3 := EuclideanSpace.single (1 : Fin 3) ((1 : ℝ) / 2)

/-- The test frequency lies in the closed plateau ball of radius one, so the bump equals `1`
there. -/
theorem r3ConvectionWitnessBump_r3SchwartzWitnessPoint :
    (r3ConvectionWitnessBump r3SchwartzWitnessPoint : ℝ) = 1 := by
  refine r3ConvectionWitnessBump.one_of_mem_closedBall ?_
  rw [mem_closedBall_zero_iff]
  show ‖(EuclideanSpace.single (1 : Fin 3) ((1 : ℝ) / 2) : R3)‖ ≤ (1 : ℝ)
  rw [PiLp.norm_single]
  norm_num

/-- The frequency profile is not the zero Schwartz map: its first component at the test
frequency is `i / 2`. -/
theorem r3SchwartzWitnessFrequency_ne_zero : r3SchwartzWitnessFrequency ≠ 0 := by
  intro h
  have h0 : r3SchwartzWitnessFrequency r3SchwartzWitnessPoint 0 = 0 := by
    rw [h]; simp
  rw [r3SchwartzWitnessFrequency_apply_zero,
    r3ConvectionWitnessBump_r3SchwartzWitnessPoint] at h0
  have hcoord : (r3SchwartzWitnessPoint 1 : ℝ) = 1 / 2 := by
    show (EuclideanSpace.single (1 : Fin 3) ((1 : ℝ) / 2) : R3) 1 = 1 / 2
    simp
  rw [hcoord] at h0
  simp [Complex.ext_iff] at h0

/-- The witness datum is nonzero: the Fourier transform of the zero Schwartz map is zero,
while the datum's Fourier transform is the nonzero profile. -/
theorem r3SchwartzWitnessDatum_ne_zero : r3SchwartzWitnessDatum ≠ 0 := by
  intro h
  refine r3SchwartzWitnessFrequency_ne_zero ?_
  rw [← fourier_r3SchwartzWitnessDatum, h]
  simp

/-- The witness datum is admissible: physically real with everywhere-vanishing raw frequency
divergence. -/
theorem isR3AdmissibleSchwartzDatum_r3SchwartzWitnessDatum :
    IsR3AdmissibleSchwartzDatum r3SchwartzWitnessDatum :=
  ⟨r3SchwartzWitnessDatum_real, fun ξ => by
    rw [fourier_r3SchwartzWitnessDatum]
    exact r3SchwartzWitnessFrequency_divergence ξ⟩

/-- **Non-vacuity of the Stage-9 entry interface**: there is a nonzero real divergence-free
Schwartz velocity field, so `r3AdmissibleSchwartzDatum_navierStokes` is not an empty
implication and is not applied only to the trivial datum. -/
theorem exists_isR3AdmissibleSchwartzDatum_ne_zero :
    ∃ φ : R3SchwartzVelocity, IsR3AdmissibleSchwartzDatum φ ∧ φ ≠ 0 :=
  ⟨r3SchwartzWitnessDatum, isR3AdmissibleSchwartzDatum_r3SchwartzWitnessDatum,
    r3SchwartzWitnessDatum_ne_zero⟩

end

end MNS2
