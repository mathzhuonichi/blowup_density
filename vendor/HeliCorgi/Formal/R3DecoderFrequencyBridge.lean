import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Formal.R3ClassicalIncompressibility
import Formal.R3StokesH2H3Smoothing

/-!
# Bessel decoder → edge-1b frequency hypotheses (Clay edge 3a)

Edge 1b closed the classical incompressibility of the explicit inverse-Fourier physical
representative under two explicit frequency-side `L¹` hypotheses. This file discharges
those hypotheses **from the Bessel decoder** at the strong-track order `3` — and earns the
word "decoder" by theorem, not by naming:

* `r3InverseBesselWeight 3` is proved equal (as a complex multiplier) to the carrier's own
  decoder symbol `r3SobolevWeightComplex (-3)` (`r3InverseBesselWeight_eq_sobolevWeight`),
  and the `L²`-level decode built here is proved to agree with the repository's
  tempered-distribution decoder `r3HsToTemperedCLM 3`
  (`r3L2ToTempered_r3Decoded3PhysicalVelocity`), by reusing the repository's existing
  order-three decode `r3H3ToL2Operator` and its identification
  `r3L2ToTempered_r3H3ToL2Operator` (`R3StokesH2H3Smoothing`);
* Cauchy–Schwarz against the weighted `L²` data gives both edge-1b hypotheses for the
  decoded frequency data of **any** `L²` Bessel coordinate, decoded at order `3`:
  `Integrable (r3DecodedFrequency 3 f)` and
  `Integrable (fun ξ => ‖ξ‖ * ‖r3DecodedFrequency 3 f ξ‖)`; the two weight facts are the
  three-dimensional integrability of `(1+‖ξ‖²)^(-3)` and `‖ξ‖²(1+‖ξ‖²)^(-3)`
  (mathlib's Japanese-bracket lemma, `finrank = 3 < 6` and `3 < 4` — order `3` is the
  honest threshold for the weighted hypothesis, not slack);
* coordinate solenoidality transfers to the decode (the radial weight commutes with the
  normalized frequency divergence), with non-vacuity witnessed by Leray projections;
* capstone: a solenoidal `L²` Bessel coordinate yields, at order `3`, a `C¹` and
  everywhere classically divergence-free explicit inverse-Fourier integral — edge 1b with
  every hypothesis discharged from the decoder.

The definitional equality `R3HsVelocity 3 = R3L2Velocity` is nowhere used as a physical
Sobolev embedding: the coordinate `f` is never itself treated as the physical velocity;
every physical object passes through the explicit inverse Bessel multiplier. No rapid
decay is claimed anywhere. Not claimed *in this file* (edge 3b): the a.e. identification
of the pointwise inverse-Fourier *integral*
`r3PhysicalRepresentative (r3DecodedFrequency 3 f)` with the `L²` decode
`r3Decoded3PhysicalVelocity f` — closed separately in `Formal/R3InversionConsistency.lean`
(`r3PhysicalRepresentative_ae_r3Decoded3PhysicalVelocity`).
-/

namespace MNS2

open MeasureTheory FourierTransform
open scoped FourierTransform SchwartzMap ENNReal

noncomputable section

/-- The real inverse Bessel weight of order `s`. -/
def r3InverseBesselWeight (s : ℝ) (ξ : R3) : ℝ := (1 + ‖ξ‖ ^ 2) ^ (-s / 2)

theorem r3InverseBesselWeight_pos (s : ℝ) (ξ : R3) : 0 < r3InverseBesselWeight s ξ := by
  unfold r3InverseBesselWeight
  positivity

theorem r3InverseBesselWeight_le_one {s : ℝ} (hs : 0 ≤ s) (ξ : R3) :
    r3InverseBesselWeight s ξ ≤ 1 := by
  unfold r3InverseBesselWeight
  have hbase : (1 : ℝ) ≤ 1 + ‖ξ‖ ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
  have hexp : -s / 2 ≤ 0 := by linarith
  exact Real.rpow_le_one_of_one_le_of_nonpos hbase hexp

theorem continuous_r3InverseBesselWeight (s : ℝ) :
    Continuous (r3InverseBesselWeight s) := by
  have hg : (r3InverseBesselWeight s).HasTemperateGrowth := by
    unfold r3InverseBesselWeight
    fun_prop
  exact hg.1.continuous

/-- The inverse Bessel weight is exactly the carrier's decoder symbol at negative order. -/
theorem r3InverseBesselWeight_eq_sobolevWeight (s : ℝ) (ξ : R3) :
    ((r3InverseBesselWeight s ξ : ℝ) : ℂ) = r3SobolevWeightComplex (-s) ξ := by
  unfold r3InverseBesselWeight r3SobolevWeightComplex
  rw [neg_div]

/-- The decoded frequency data of a Bessel coordinate: the inverse Bessel weight applied
to the Fourier transform of the stored coordinate. -/
def r3DecodedFrequency (s : ℝ) (f : R3L2Velocity) : R3 → R3C :=
  fun ξ => r3InverseBesselWeight s ξ • ((𝓕 f : R3L2Velocity) : R3 → R3C) ξ

/-- In dimension three, the order-three inverse Bessel weight is square integrable. -/
theorem memLp_two_r3InverseBesselWeight_three :
    MemLp (r3InverseBesselWeight 3) 2 (volume : Measure R3) := by
  have hmeas : AEStronglyMeasurable (r3InverseBesselWeight 3) (volume : Measure R3) :=
    (continuous_r3InverseBesselWeight 3).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hmeas]
  have hdim : (Module.finrank ℝ R3 : ℝ) < 6 := by
    norm_num [R3]
  refine (integrable_rpow_neg_one_add_norm_sq
    (μ := (volume : Measure R3)) (r := 6) hdim).congr ?_
  filter_upwards with ξ
  have hbase : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
  unfold r3InverseBesselWeight
  rw [← Real.rpow_natCast ((1 + ‖ξ‖ ^ 2) ^ (-(3 : ℝ) / 2)) 2,
    ← Real.rpow_mul hbase.le]
  norm_num

/-- In dimension three, the first-moment-weighted order-three inverse Bessel weight is
square integrable. -/
theorem memLp_two_weighted_r3InverseBesselWeight_three :
    MemLp (fun ξ : R3 => ‖ξ‖ * r3InverseBesselWeight 3 ξ) 2 (volume : Measure R3) := by
  have hmeas : AEStronglyMeasurable
      (fun ξ : R3 => ‖ξ‖ * r3InverseBesselWeight 3 ξ) (volume : Measure R3) :=
    (continuous_norm.mul (continuous_r3InverseBesselWeight 3)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hmeas]
  have hdim : (Module.finrank ℝ R3 : ℝ) < 4 := by
    norm_num [R3]
  refine (integrable_rpow_neg_one_add_norm_sq
    (μ := (volume : Measure R3)) (r := 4) hdim).mono'
    ((continuous_norm.mul (continuous_r3InverseBesselWeight 3)).pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => ?_)
  have hbase : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
  have hsq : (‖ξ‖ * r3InverseBesselWeight 3 ξ) ^ 2 =
      ‖ξ‖ ^ 2 * (1 + ‖ξ‖ ^ 2) ^ (-(3 : ℝ)) := by
    unfold r3InverseBesselWeight
    rw [mul_pow, ← Real.rpow_natCast ((1 + ‖ξ‖ ^ 2) ^ (-(3 : ℝ) / 2)) 2,
      ← Real.rpow_mul hbase.le]
    norm_num
  have hbound : (‖ξ‖ * r3InverseBesselWeight 3 ξ) ^ 2 ≤ (1 + ‖ξ‖ ^ 2) ^ (-(4 : ℝ) / 2) := by
    rw [hsq]
    have hle : ‖ξ‖ ^ 2 ≤ 1 + ‖ξ‖ ^ 2 := by linarith [sq_nonneg ‖ξ‖]
    calc ‖ξ‖ ^ 2 * (1 + ‖ξ‖ ^ 2) ^ (-(3 : ℝ))
        ≤ (1 + ‖ξ‖ ^ 2) * (1 + ‖ξ‖ ^ 2) ^ (-(3 : ℝ)) := by
          have hp : (0 : ℝ) ≤ (1 + ‖ξ‖ ^ 2) ^ (-(3 : ℝ)) := Real.rpow_nonneg hbase.le _
          exact mul_le_mul_of_nonneg_right hle hp
      _ = (1 + ‖ξ‖ ^ 2) ^ (-(4 : ℝ) / 2) := by
          rw [show (1 + ‖ξ‖ ^ 2) * (1 + ‖ξ‖ ^ 2) ^ (-(3 : ℝ)) =
            (1 + ‖ξ‖ ^ 2) ^ (1 : ℝ) * (1 + ‖ξ‖ ^ 2) ^ (-(3 : ℝ)) by rw [Real.rpow_one],
            ← Real.rpow_add hbase]
          norm_num
  calc ‖(‖ξ‖ * r3InverseBesselWeight 3 ξ) ^ 2‖
      = (‖ξ‖ * r3InverseBesselWeight 3 ξ) ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ ≤ (1 + ‖ξ‖ ^ 2) ^ (-(4 : ℝ) / 2) := hbound

/-- **Edge-1b hypothesis one, discharged from the decoder weight**: the decoded frequency
data of any `L²` Bessel coordinate, decoded at order `3`, is integrable (Cauchy–Schwarz:
inverse weight in `L²` against the `L²` Fourier data). -/
theorem integrable_r3DecodedFrequency (f : R3L2Velocity) :
    Integrable (r3DecodedFrequency 3 f) volume := by
  have hF : MemLp ((𝓕 f : R3L2Velocity) : R3 → R3C) 2 volume := Lp.memLp (𝓕 f)
  have hone : MemLp (r3DecodedFrequency 3 f) 1 volume :=
    hF.smul memLp_two_r3InverseBesselWeight_three
  exact memLp_one_iff_integrable.mp hone

/-- **Edge-1b hypothesis two, discharged from the decoder weight**: the decoded frequency
data of any `L²` Bessel coordinate, decoded at order `3`, has integrable first moment. -/
theorem integrable_weighted_r3DecodedFrequency (f : R3L2Velocity) :
    Integrable (fun ξ : R3 => ‖ξ‖ * ‖r3DecodedFrequency 3 f ξ‖) volume := by
  have hF : MemLp (fun ξ : R3 => ‖((𝓕 f : R3L2Velocity) : R3 → R3C) ξ‖) 2 volume :=
    (Lp.memLp (𝓕 f)).norm
  have hone : MemLp (fun ξ : R3 =>
      (fun ξ : R3 => ‖ξ‖ * r3InverseBesselWeight 3 ξ) ξ *
        (fun ξ : R3 => ‖((𝓕 f : R3L2Velocity) : R3 → R3C) ξ‖) ξ) 1 volume :=
    hF.mul memLp_two_weighted_r3InverseBesselWeight_three
  refine (memLp_one_iff_integrable.mp hone).congr
    (Filter.Eventually.of_forall fun ξ => ?_)
  show ‖ξ‖ * r3InverseBesselWeight 3 ξ * ‖((𝓕 f : R3L2Velocity) : R3 → R3C) ξ‖ =
    ‖ξ‖ * ‖r3DecodedFrequency 3 f ξ‖
  unfold r3DecodedFrequency
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (r3InverseBesselWeight_pos 3 ξ)]
  ring

/-- The decoded frequency data is itself square integrable (the weight is bounded by one),
so it bundles as an `L²` element. -/
theorem memLp_two_r3DecodedFrequency (f : R3L2Velocity) :
    MemLp (r3DecodedFrequency 3 f) 2 volume := by
  have hF : MemLp ((𝓕 f : R3L2Velocity) : R3 → R3C) 2 volume := Lp.memLp (𝓕 f)
  refine MemLp.of_le hF
    (((continuous_r3InverseBesselWeight 3).aestronglyMeasurable).smul
      hF.aestronglyMeasurable) (Filter.Eventually.of_forall fun ξ => ?_)
  unfold r3DecodedFrequency
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (r3InverseBesselWeight_pos 3 ξ)]
  have hle := r3InverseBesselWeight_le_one (s := 3) (by norm_num) ξ
  have hnn : (0 : ℝ) ≤ ‖((𝓕 f : R3L2Velocity) : R3 → R3C) ξ‖ := norm_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hle hnn]

/-- The order-three decoded frequency data as an `L²` element. -/
def r3Decoded3FrequencyL2 (f : R3L2Velocity) : R3L2Velocity :=
  (memLp_two_r3DecodedFrequency f).toLp (r3DecodedFrequency 3 f)

/-- The order-three `L²`-level physical decode of a Bessel coordinate: the inverse Fourier
transform of the decoded frequency data. Proved below
(`r3L2ToTempered_r3Decoded3PhysicalVelocity`) to agree with the repository's
tempered-distribution decoder `r3HsToTemperedCLM 3`. -/
def r3Decoded3PhysicalVelocity (f : R3L2Velocity) : R3L2Velocity :=
  𝓕⁻ (r3Decoded3FrequencyL2 f)

/-- Plancherel round-trip: the decoded frequency data is a.e. the Fourier transform of its
own `L²` inverse transform. This instantiates edge-1b's representative hypothesis at
`u := r3Decoded3PhysicalVelocity f`; it is bookkeeping for the constructed decode, not new
information about the carrier. -/
theorem r3DecodedFrequency_ae_coeFn_fourier (f : R3L2Velocity) :
    r3DecodedFrequency 3 f =ᵐ[volume]
      ((𝓕 (r3Decoded3PhysicalVelocity f) : R3L2Velocity) : R3 → R3C) := by
  have h1 : 𝓕 (r3Decoded3PhysicalVelocity f) = r3Decoded3FrequencyL2 f :=
    fourier_fourierInv_eq (r3Decoded3FrequencyL2 f)
  rw [h1]
  exact (MemLp.coeFn_toLp (memLp_two_r3DecodedFrequency f)).symm

/-- The bridge's `L²` decode is the bounded multiplier decode. -/
theorem r3Decoded3PhysicalVelocity_eq (f : R3L2Velocity) :
    r3Decoded3PhysicalVelocity f = r3H3ToL2Operator f := by
  unfold r3Decoded3PhysicalVelocity
  rw [show r3H3ToL2Operator f =
      𝓕⁻ (r3H3InverseBesselL2FrequencyOperator (𝓕 f)) from rfl]
  congr 1
  apply MeasureTheory.Lp.ext
  filter_upwards [MemLp.coeFn_toLp (memLp_two_r3DecodedFrequency f),
    r3H3InverseBesselL2FrequencyOperator_ae (𝓕 f)] with ξ h1 h2
  rw [show ((r3Decoded3FrequencyL2 f : R3L2Velocity) : R3 → R3C) ξ =
      r3DecodedFrequency 3 f ξ from h1, h2]
  unfold r3DecodedFrequency r3H3InverseBesselWeightComplex
  ext j
  simp only [PiLp.smul_apply, Complex.real_smul, smul_eq_mul, mul_eq_mul_right_iff]
  exact Or.inl (r3InverseBesselWeight_eq_sobolevWeight 3 ξ)

/-- **The bridge decode is the Bessel decoder**: the `L²`-level decode constructed here
represents exactly the tempered distribution decoded by the carrier's own
`r3HsToTemperedCLM 3`. -/
theorem r3L2ToTempered_r3Decoded3PhysicalVelocity (f : R3L2Velocity) :
    r3L2ToTemperedCLM (r3Decoded3PhysicalVelocity f) = r3HsToTemperedCLM 3 f := by
  rw [r3Decoded3PhysicalVelocity_eq]
  exact r3L2ToTempered_r3H3ToL2Operator f

/-- Coordinate solenoidality transfers to the physical decode: the radial inverse Bessel
weight commutes with the normalized frequency divergence. -/
theorem r3Decoded3PhysicalVelocity_mem_solenoidal {f : R3L2Velocity}
    (hf : f ∈ r3L2SolenoidalSubmodule) :
    r3Decoded3PhysicalVelocity f ∈ r3L2SolenoidalSubmodule := by
  have hker : r3NormalizedDivergenceFrequencyAux (𝓕 f) = 0 := by
    have h := LinearMap.mem_ker.mp hf
    simpa [r3NormalizedDivergenceL2OperatorAux] using h
  have hnormzero : ∀ᵐ ξ : R3 ∂(volume : Measure R3),
      r3NormalizedDivergencePointwise ξ (((𝓕 f : R3L2Velocity) : R3 → R3C) ξ) = 0 := by
    have hae := r3NormalizedDivergenceFrequencyAux_ae (𝓕 f)
    have hzero : (r3NormalizedDivergenceFrequencyAux (𝓕 f) : R3 → ℂ) =ᵐ[volume] 0 := by
      rw [hker]
      exact Lp.coeFn_zero ℂ 2 volume
    filter_upwards [hae, hzero] with ξ h1 h2
    rw [← h1]
    simpa using h2
  have hkey : r3NormalizedDivergenceL2OperatorAux (r3Decoded3PhysicalVelocity f) = 0 := by
    have h1 : 𝓕 (r3Decoded3PhysicalVelocity f) = r3Decoded3FrequencyL2 f :=
      fourier_fourierInv_eq (r3Decoded3FrequencyL2 f)
    have h2 : r3NormalizedDivergenceL2OperatorAux (r3Decoded3PhysicalVelocity f) =
        r3NormalizedDivergenceFrequencyAux (r3Decoded3FrequencyL2 f) := by
      simp only [r3NormalizedDivergenceL2OperatorAux, ContinuousLinearMap.comp_apply]
      rw [FourierTransform.fourierCLM_apply, h1]
    rw [h2, MeasureTheory.Lp.eq_zero_iff_ae_eq_zero]
    have hae := r3NormalizedDivergenceFrequencyAux_ae (r3Decoded3FrequencyL2 f)
    have hcoe : (r3Decoded3FrequencyL2 f : R3 → R3C) =ᵐ[volume] r3DecodedFrequency 3 f :=
      MemLp.coeFn_toLp (memLp_two_r3DecodedFrequency f)
    filter_upwards [hae, hcoe, hnormzero] with ξ h1 h2 h3
    rw [h1, h2]
    unfold r3DecodedFrequency r3NormalizedDivergencePointwise at *
    simp only [PiLp.smul_apply, Complex.real_smul] at *
    rw [show ∀ a b c : ℂ, ∀ w : ℝ,
      r3NormalizedFrequencyCoordinate 0 ξ * ((w : ℂ) * a) +
        r3NormalizedFrequencyCoordinate 1 ξ * ((w : ℂ) * b) +
        r3NormalizedFrequencyCoordinate 2 ξ * ((w : ℂ) * c) =
        (w : ℂ) * (r3NormalizedFrequencyCoordinate 0 ξ * a +
          r3NormalizedFrequencyCoordinate 1 ξ * b +
          r3NormalizedFrequencyCoordinate 2 ξ * c) from fun a b c w => by ring]
    rw [h3, mul_zero]
    rfl
  exact LinearMap.mem_ker.mpr hkey

/-- **Edge 3a capstone**: a solenoidal `L²` Bessel coordinate yields, through the explicit
order-three inverse Bessel multiplier and the explicit inverse Fourier integral, a `C¹`
function with vanishing classical divergence at every point — edge 1b with every
hypothesis discharged from the decoder. The `C¹` object is the pointwise inverse-Fourier
*integral* of the decoded data; its a.e. agreement with the `L²` decode
`r3Decoded3PhysicalVelocity f` (and hence with the carrier's physical distribution) is
edge 3b and is not claimed here. -/
theorem r3DecodedFrequency_incompressible {f : R3L2Velocity}
    (hf : f ∈ r3L2SolenoidalSubmodule) :
    ContDiff ℝ 1 (r3PhysicalRepresentative (r3DecodedFrequency 3 f)) ∧
      ∀ x : R3,
        r3ClassicalDivergence (r3PhysicalRepresentative (r3DecodedFrequency 3 f)) x = 0 :=
  r3PhysicalRepresentative_incompressible_of_mem_solenoidal
    (r3Decoded3PhysicalVelocity_mem_solenoidal hf)
    (r3DecodedFrequency_ae_coeFn_fourier f)
    (integrable_r3DecodedFrequency f)
    (integrable_weighted_r3DecodedFrequency f)

/-- Non-vacuity: the solenoidal hypothesis of the capstone is satisfied by every Leray
projection, so the capstone applies to a nonzero class of coordinates. -/
theorem r3DecodedFrequency_incompressible_leray (g : R3L2Velocity) :
    ContDiff ℝ 1
        (r3PhysicalRepresentative (r3DecodedFrequency 3 (r3LerayL2Operator g))) ∧
      ∀ x : R3,
        r3ClassicalDivergence
          (r3PhysicalRepresentative (r3DecodedFrequency 3 (r3LerayL2Operator g))) x = 0 :=
  r3DecodedFrequency_incompressible (r3LerayL2Operator_mem_solenoidal g)

end

end MNS2
