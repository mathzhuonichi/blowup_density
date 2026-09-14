-- REVIEW PROBE (lane 145, mutation B): the induction constant 16^m replaced by 4^m (and 256 by 16).
-- Expected: the raising step of exists_isSobolevDatum_norm_le fails.  Read-only copy; not in the build.
import NSFormalization.Section4.D01.FiniteOrderConstructor

/-!
# Quantitative bounds for the finite-order angular Sobolev datum constructor (unit D01 · D-quant)

`FiniteOrderConstructor.lean` produces, from a field with `L²` weak derivatives up to order `m`
(`HasWeakDerivsL2 z m`), an order-`m` angular real-vector Sobolev datum
(`exists_isSobolevDatum_of_memLp_derivs`), but says nothing about the *size* of that datum.  This
module makes the whole pipeline quantitative, closing the last gap between `exists_local`'s bound and
A01's order-2 cap `Kbnd`.

## What is proved here

* `norm_orderZeroDatum_le` (**order-0 bound, deliverable 1**) — `‖orderZeroDatum hz‖ ≤ ‖hz.toLp‖`,
  i.e. constant `c₀ = 1`.  The order-0 realization pipeline
  `orderZeroDatum hz = cyclesToAngularRealVector 0 ∘ (i ↦ realProjectionTo 0 (𝓕 (componentLp hz i)))`
  is an *isometry chain* at order `0`:
  - the vector angular transport is norm-preserving at `s = 0`
    (`Paper3.cyclesToAngularRealVector_norm_le`, `AngularRealVectorBochner.lean:26`, with
    `frequencyUnit ^ |0| = 1`);
  - `𝓕` is the Plancherel isometry (`MeasureTheory.Lp.norm_fourier_eq`);
  - `realProjectionTo 0` is norm non-increasing (`Paper3.realProjectionTo_norm_le`,
    `RealPositiveDensity.lean:40`) and acts as the identity on the real subspace here;
  - the componentwise `L²` decomposition is the Euclidean-valued Plancherel/Pythagoras identity
    `‖hz.toLp‖² = ∑ᵢ ‖componentLp hz i‖²` (`norm_toLp_component_sq_sum`), the piece
    `OrderZeroDatum.lean:40-53` records as absent; it is proved here from
    `EuclideanSpace.norm_eq` and `lintegral_finsetSum'`.

* `norm_raise_le` (**raising bound, deliverable 2**) — for an order-`s` datum `A` of `z` and, for
  each `j`, an order-`s` datum `C j` of the weak `j`-th derivative, the raised order-`(s+1)` datum
  `A'` satisfies `‖A'‖² ≤ 4·(‖A‖² + ∑ⱼ ‖C j‖²)`.  Two ingredients: the pointwise symbol bound
  `(1+‖ξ‖²)^{1/2} ≤ 1 + ∑ⱼ|ξⱼ|` (`FiniteOrderDatum.norm_raiseIntegrand_le`) controls the raised
  integrand by the datum plus its coordinate multiples; and the a.e. identity
  `(2πi)·(ξⱼ·(A i)) =ᵐ frequencyUnit·(C j i)` (`coord_smul_deriv_ae`, re-derived from
  `db_cycles_full`) shows each coordinate multiple `ξⱼ·(A i)` has the *same* `L²` norm as `(C j i)`
  (`eLpNorm_coord_smul_eq`; `frequencyUnit = 2π = ‖2πi‖`).  A four-term Cauchy–Schwarz gives the
  constant `4`.

No `sorry`, no `axiom`; `#print axioms` is standard
(`research/D01/axioms_finite_order_norm.lean`).
-/

noncomputable section

namespace NSFormalization.Section4.D01

open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source NSFormalization.Source.RealSobolev
open scoped ENNReal ComplexConjugate LineDeriv SchwartzMap

variable {z : Space → Space}

/-! ## 0. The Euclidean-valued Plancherel/Pythagoras `L²` identity -/

/-- For `p = 2` the squared `eLpNorm` is the `∫⁻ ‖·‖ₑ²`. -/
theorem eLpNorm_two_sq {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    (f : α → E) : (eLpNorm f 2 μ) ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, one_div]
  rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

/-- The Euclidean-valued `L²` Pythagoras identity at the `eLpNorm` level:
`(eLpNorm z 2)² = ∑ᵢ (eLpNorm (z·ᵢ) 2)²`.  Recorded as absent from the tree at
`OrderZeroDatum.lean:40-53`; proved here from `EuclideanSpace.norm_eq` (fibrewise Pythagoras) and
`lintegral_finsetSum'`. -/
theorem eLpNorm_component_sq_sum (hz : MemLp z 2 volume) :
    (eLpNorm z 2 volume) ^ 2
      = ∑ i : Fin 3, (eLpNorm (fun x => ((z x i : ℝ) : ℂ)) 2 volume) ^ 2 := by
  rw [eLpNorm_two_sq]
  have hmeas : ∀ i : Fin 3, AEMeasurable
      (fun x => ‖((z x i : ℝ) : ℂ)‖ₑ ^ (2 : ℝ)) volume := by
    intro i
    have h1 : AEStronglyMeasurable (fun x => ((z x i : ℝ) : ℂ)) volume := by
      have := hz.aestronglyMeasurable; fun_prop
    exact h1.enorm.pow_const 2
  have hpt : ∫⁻ x, ‖z x‖ₑ ^ (2 : ℝ) ∂volume
      = ∫⁻ x, ∑ i : Fin 3, ‖((z x i : ℝ) : ℂ)‖ₑ ^ (2 : ℝ) ∂volume := by
    apply lintegral_congr
    intro x
    have hnn : (0 : ℝ) ≤ ‖z x‖ := norm_nonneg _
    have hnorm : ‖z x‖ ^ 2 = ∑ i : Fin 3, ‖(z x) i‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    rw [ENNReal.rpow_two, ← ofReal_norm (z x), ← ENNReal.ofReal_pow hnn, hnorm,
      ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    apply Finset.sum_congr rfl
    intro i _
    rw [ENNReal.rpow_two, ENNReal.ofReal_pow (norm_nonneg _),
      ← ofReal_norm (((z x i : ℝ) : ℂ)), Complex.norm_real]
  rw [hpt, lintegral_finsetSum' _ (fun i _ => hmeas i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [eLpNorm_two_sq]

/-- The real-norm form of the Pythagoras identity on the `L²` classes:
`‖hz.toLp‖² = ∑ᵢ ‖componentLp hz i‖²`. -/
theorem norm_toLp_component_sq_sum (hz : MemLp z 2 volume) :
    ‖hz.toLp‖ ^ 2 = ∑ i : Fin 3, ‖componentLp hz i‖ ^ 2 := by
  have hfin : ∀ i : Fin 3, (eLpNorm (fun x => ((z x i : ℝ) : ℂ)) 2 volume) ^ 2 ≠ ∞ :=
    fun i => ENNReal.pow_ne_top (memLp_component hz i).2.ne
  rw [Lp.norm_toLp z hz, ← ENNReal.toReal_pow, eLpNorm_component_sq_sum hz,
    ENNReal.toReal_sum (fun i _ => hfin i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.toReal_pow]
  congr 1
  rw [componentLp, Lp.norm_toLp]

/-! ## 1. The order-0 bound (deliverable 1, constant `c₀ = 1`) -/

/-- **Deliverable 1 — the order-0 bound.**  `‖orderZeroDatum hz‖ ≤ ‖hz.toLp‖`.  Constant `c₀ = 1`;
the order-0 realization pipeline is an isometry chain (see the module docstring). -/
theorem norm_orderZeroDatum_le (hz : MemLp z 2 volume) :
    ‖orderZeroDatum hz‖ ≤ ‖hz.toLp‖ := by
  set v : RealVectorSobolev 0 :=
    WithLp.toLp 2 (fun i => realProjectionTo 0 (𝓕 (componentLp hz i))) with hv
  have hsq : ‖orderZeroDatum hz‖ ^ 2 ≤ ‖hz.toLp‖ ^ 2 := by
    have h0 : orderZeroDatum hz = cyclesToAngularRealVector 0 v := rfl
    have hcyc : ‖orderZeroDatum hz‖ ≤ ‖v‖ := by
      rw [h0]
      have := cyclesToAngularRealVector_norm_le 0 v
      rwa [abs_zero, Real.rpow_zero, one_mul] at this
    have hvsq : ‖v‖ ^ 2 = ∑ i : Fin 3, ‖realProjectionTo 0 (𝓕 (componentLp hz i))‖ ^ 2 :=
      PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => RealSobolevHilbert (0 : ℝ)) v
    have hle : ‖v‖ ^ 2 ≤ ‖hz.toLp‖ ^ 2 := by
      rw [hvsq, norm_toLp_component_sq_sum hz]
      apply Finset.sum_le_sum
      intro i _
      have h1 : ‖realProjectionTo 0 (𝓕 (componentLp hz i))‖ ≤ ‖componentLp hz i‖ := by
        refine (realProjectionTo_norm_le 0 (𝓕 (componentLp hz i))).trans ?_
        rw [Lp.norm_fourier_eq]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    calc ‖orderZeroDatum hz‖ ^ 2 ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hcyc 2
      _ ≤ ‖hz.toLp‖ ^ 2 := hle
  calc ‖orderZeroDatum hz‖ = Real.sqrt (‖orderZeroDatum hz‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖hz.toLp‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖hz.toLp‖ := Real.sqrt_sq (norm_nonneg _)

/-! ## 2. The raising bound (deliverable 2)

`coord_smul_deriv_ae` re-derives the a.e. Fourier identity `(2πi)·(ξⱼ·(A i)) =ᵐ frequencyUnit·(C j i)`
from `db_cycles_full` (the transport used inside `memLp_coord_smul_datum`, whose a.e. form is not
exported); `eLpNorm_coord_smul_eq` reads off that each coordinate multiple `ξⱼ·(A i)` has the same
`L²` norm as the derivative datum `C j i` (`frequencyUnit = 2π = ‖2πi‖`).  `norm_raiseHilbert_le`
combines this with the symbol bound for the per-component estimate `‖raiseHilbert (A i)‖ ≤
‖A i‖ + ∑ⱼ ‖C j i‖`, and `norm_raise_le` assembles the vector bound with a four-term Cauchy–Schwarz. -/

theorem coord_smul_deriv_ae_local {s : ℝ} {z : Space → Space} {w : Fin 3 → Space → Space}
    {A : RealVectorSobolev s} (hA : IsSobolevDatum s z A)
    {C : Fin 3 → RealVectorSobolev s} (hC : ∀ j, IsSobolevDatum s (w j) (C j))
    (hw : ∀ (j i : Fin 3) (ψ : SchwartzMap Space ℂ),
      ∫ x, ψ x * ((w j x i : ℝ) : ℂ)
        = ∫ x, (-∂_{coordinateVector j} ψ) x * ((z x i : ℝ) : ℂ))
    (i j : Fin 3) :
    (fun ξ => (2 * (Real.pi : ℂ) * Complex.I) *
        ((ξ j : ℂ) • (((A i : RealSobolevHilbert s) : FourierData) : Space → ℂ) ξ)) =ᵐ[volume]
      fun ξ => ((frequencyUnit : ℝ) : ℂ) *
        (((C j i : RealSobolevHilbert s) : FourierData) : Space → ℂ) ξ := by
  have hc0 : (0 : ℝ) < frequencyUnit := frequencyUnit_pos
  set c := frequencyUnit with hc
  have hdb := db_cycles_full j hA (hC j) (hw j) i
  set f : FourierData := (cyclesToAngular s).symm ((A i : RealSobolevHilbert s) : FourierData) with hfdef
  set g : FourierData := (cyclesToAngular s).symm ((C j i : RealSobolevHilbert s) : FourierData) with hgdef
  set κm : ℝ≥0∞ := ENNReal.ofReal (|(c⁻¹ ^ (Module.finrank ℝ Space))⁻¹|) with hκm
  have hMP : MeasurePreserving (fun ξ : Space => c⁻¹ • ξ) volume (κm • volume) :=
    ⟨(continuous_const_smul _).measurable, Measure.map_addHaar_smul volume (inv_ne_zero hc0.ne')⟩
  have hAeq : angularFrequencyDilation (angularWeightEquiv s f)
      = ((A i : RealSobolevHilbert s) : FourierData) := by
    have h : cyclesToAngular s f = angularFrequencyDilation (angularWeightEquiv s f) := rfl
    rw [← h, hfdef]; exact (cyclesToAngular s).apply_symm_apply _
  have hCeq : angularFrequencyDilation (angularWeightEquiv s g)
      = ((C j i : RealSobolevHilbert s) : FourierData) := by
    have h : cyclesToAngular s g = angularFrequencyDilation (angularWeightEquiv s g) := rfl
    rw [← h, hgdef]; exact (cyclesToAngular s).apply_symm_apply _
  have hcoeA := angularFrequencyDilation_coeFn (angularWeightEquiv s f)
  have hcoeC := angularFrequencyDilation_coeFn (angularWeightEquiv s g)
  rw [hAeq] at hcoeA
  rw [hCeq] at hcoeC
  have hwA : ∀ᵐ ξ : Space ∂volume,
      ((angularWeightEquiv s f : FourierData) : Space → ℂ) (c⁻¹ • ξ)
        = angularWeightSymbol s (c⁻¹ • ξ) * (f (c⁻¹ • ξ)) :=
    hMP.quasiMeasurePreserving.ae (Measure.ae_smul_measure (angularWeightEquiv_coeFn s f) κm)
  have hwC : ∀ᵐ ξ : Space ∂volume,
      ((angularWeightEquiv s g : FourierData) : Space → ℂ) (c⁻¹ • ξ)
        = angularWeightSymbol s (c⁻¹ • ξ) * (g (c⁻¹ • ξ)) :=
    hMP.quasiMeasurePreserving.ae (Measure.ae_smul_measure (angularWeightEquiv_coeFn s g) κm)
  have hI : ∀ᵐ ξ : Space ∂volume,
      (2 * (Real.pi : ℂ) * Complex.I) * (((c⁻¹ • ξ) j : ℝ) : ℂ) * (f (c⁻¹ • ξ))
        = g (c⁻¹ • ξ) := hMP.quasiMeasurePreserving.ae (Measure.ae_smul_measure hdb κm)
  filter_upwards [hcoeA, hcoeC, hwA, hwC, hI] with ξ eA eC ewA ewC eI
  rw [eA, ewA, eC, ewC]
  have hcoord : (((c⁻¹ • ξ) j : ℝ) : ℂ) = ((c⁻¹ : ℝ) : ℂ) * ((ξ j : ℝ) : ℂ) := by
    rw [show ((c⁻¹ • ξ) j : ℝ) = c⁻¹ * ξ j from rfl, Complex.ofReal_mul]
  rw [hcoord] at eI
  have hcc : ((c⁻¹ : ℝ) : ℂ) * ((c : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hc0.ne', Complex.ofReal_one]
  simp only [Complex.real_smul, smul_eq_mul]
  linear_combination
      (((c : ℝ) : ℂ) * ((c ^ (-3/2 : ℝ) : ℝ) : ℂ) * angularWeightSymbol s (c⁻¹ • ξ)) * eI
    - ((2 * (Real.pi : ℂ) * Complex.I) * ((ξ j : ℝ) : ℂ) * ((c ^ (-3/2 : ℝ) : ℝ) : ℂ)
        * angularWeightSymbol s (c⁻¹ • ξ) * (f (c⁻¹ • ξ))) * hcc

theorem eLpNorm_coord_smul_eq {s : ℝ} {z : Space → Space} {w : Fin 3 → Space → Space}
    {A : RealVectorSobolev s} (hA : IsSobolevDatum s z A)
    {C : Fin 3 → RealVectorSobolev s} (hC : ∀ j, IsSobolevDatum s (w j) (C j))
    (hw : ∀ (j i : Fin 3) (ψ : SchwartzMap Space ℂ),
      ∫ x, ψ x * ((w j x i : ℝ) : ℂ)
        = ∫ x, (-∂_{coordinateVector j} ψ) x * ((z x i : ℝ) : ℂ))
    (i j : Fin 3) :
    eLpNorm (fun ξ => (ξ j : ℂ) • (((A i : RealSobolevHilbert s) : FourierData) : Space → ℂ) ξ) 2 volume
      = eLpNorm (fun ξ => (((C j i : RealSobolevHilbert s) : FourierData) : Space → ℂ) ξ) 2 volume := by
  have hae := coord_smul_deriv_ae_local hA hC hw i j
  have hcong :
      eLpNorm ((2 * (Real.pi : ℂ) * Complex.I) •
        (fun ξ => (ξ j : ℂ) • (((A i : RealSobolevHilbert s) : FourierData) : Space → ℂ) ξ)) 2 volume
      = eLpNorm (((frequencyUnit : ℝ) : ℂ) •
        (fun ξ => (((C j i : RealSobolevHilbert s) : FourierData) : Space → ℂ) ξ)) 2 volume := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [hae] with ξ h
    simpa only [Pi.smul_apply, smul_eq_mul] using h
  rw [eLpNorm_const_smul, eLpNorm_const_smul] at hcong
  have hk : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ₑ = ‖((frequencyUnit : ℝ) : ℂ)‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm]; congr 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos frequencyUnit_pos, frequencyUnit,
      norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]; norm_num
  rw [hk] at hcong
  have h0 : ‖((frequencyUnit : ℝ) : ℂ)‖ₑ ≠ 0 := by
    rw [← ofReal_norm]; simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos frequencyUnit_pos]; exact frequencyUnit_pos
  have ht : ‖((frequencyUnit : ℝ) : ℂ)‖ₑ ≠ ∞ := by rw [← ofReal_norm]; exact ENNReal.ofReal_ne_top
  exact (ENNReal.mul_right_inj h0 ht).mp hcong

theorem norm_raiseHilbert_le {s : ℝ} {z : Space → Space} {w : Fin 3 → Space → Space}
    {A : RealVectorSobolev s} (hA : IsSobolevDatum s z A)
    {C : Fin 3 → RealVectorSobolev s} (hC : ∀ j, IsSobolevDatum s (w j) (C j))
    (hw : ∀ (j i : Fin 3) (ψ : SchwartzMap Space ℂ),
      ∫ x, ψ x * ((w j x i : ℝ) : ℂ)
        = ∫ x, (-∂_{coordinateVector j} ψ) x * ((z x i : ℝ) : ℂ))
    (i : Fin 3)
    (hgi : RaisableWitness ((A i : RealSobolevHilbert s) : FourierData)) :
    ‖raiseHilbert (A i) hgi‖ ≤ ‖A i‖ + ∑ j : Fin 3, ‖C j i‖ := by
  set Ai : Space → ℂ := (((A i : RealSobolevHilbert s) : FourierData) : Space → ℂ) with hAi
  have hAmeas : AEStronglyMeasurable Ai volume := Lp.aestronglyMeasurable _
  have hcoordmeas : ∀ j : Fin 3, AEStronglyMeasurable (fun ξ => (ξ j : ℂ) • Ai ξ) volume :=
    fun j => (memLp_coord_smul_datum hA hC hw i j).aestronglyMeasurable
  have hpt : ∀ ξ, ‖sobolevBesselWeight 1 ξ • Ai ξ‖ ≤ ‖Ai ξ‖ + ∑ j : Fin 3, ‖(ξ j : ℂ) • Ai ξ‖ := by
    intro ξ
    refine (norm_raiseIntegrand_le (A i) ξ).trans (le_of_eq ?_)
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  have hsummeas : AEStronglyMeasurable (fun ξ => ∑ j : Fin 3, ‖(ξ j : ℂ) • Ai ξ‖) volume := by
    simp only [Fin.sum_univ_three]
    exact (((hcoordmeas 0).norm.add (hcoordmeas 1).norm).add (hcoordmeas 2).norm)
  have hsum_le : eLpNorm (fun ξ => ∑ j : Fin 3, ‖(ξ j : ℂ) • Ai ξ‖) 2 volume
      ≤ ∑ j : Fin 3, eLpNorm (fun ξ => (ξ j : ℂ) • Ai ξ) 2 volume := by
    have h := eLpNorm_sum_le (p := (2 : ℝ≥0∞)) (μ := volume)
      (f := fun j => (fun ξ => ‖(ξ j : ℂ) • Ai ξ‖)) (s := (Finset.univ : Finset (Fin 3)))
      (fun j _ => (hcoordmeas j).norm) (by norm_num)
    refine le_trans (le_of_eq ?_) (le_trans h (le_of_eq ?_))
    · congr 1
    · apply Finset.sum_congr rfl; intro j _; rw [eLpNorm_norm]
  have hEbound : eLpNorm (fun ξ => sobolevBesselWeight 1 ξ • Ai ξ) 2 volume
      ≤ eLpNorm Ai 2 volume + ∑ j : Fin 3, eLpNorm (fun ξ => (ξ j : ℂ) • Ai ξ) 2 volume := by
    calc eLpNorm (fun ξ => sobolevBesselWeight 1 ξ • Ai ξ) 2 volume
        ≤ eLpNorm (fun ξ => ‖Ai ξ‖ + ∑ j : Fin 3, ‖(ξ j : ℂ) • Ai ξ‖) 2 volume :=
          eLpNorm_mono_real hpt
      _ ≤ eLpNorm (fun ξ => ‖Ai ξ‖) 2 volume
          + eLpNorm (fun ξ => ∑ j : Fin 3, ‖(ξ j : ℂ) • Ai ξ‖) 2 volume :=
          eLpNorm_add_le hAmeas.norm hsummeas (by norm_num)
      _ ≤ eLpNorm Ai 2 volume + ∑ j : Fin 3, eLpNorm (fun ξ => (ξ j : ℂ) • Ai ξ) 2 volume := by
          rw [eLpNorm_norm]; exact add_le_add le_rfl hsum_le
  have hraise_norm : ‖raiseHilbert (A i) hgi‖
      = (eLpNorm (fun ξ => sobolevBesselWeight 1 ξ • Ai ξ) 2 volume).toReal := by
    rw [show ‖raiseHilbert (A i) hgi‖
        = ‖((raiseHilbert (A i) hgi : RealSobolevHilbert (s + 1)) : FourierData)‖ from rfl,
      coe_raiseHilbert]
    exact Lp.norm_toLp _ hgi
  have hAtop : eLpNorm Ai 2 volume ≠ ∞ := (Lp.memLp _).2.ne
  have hcoordtop : ∀ j : Fin 3, eLpNorm (fun ξ => (ξ j : ℂ) • Ai ξ) 2 volume ≠ ∞ :=
    fun j => (memLp_coord_smul_datum hA hC hw i j).2.ne
  have hsumtop : (eLpNorm Ai 2 volume
      + ∑ j : Fin 3, eLpNorm (fun ξ => (ξ j : ℂ) • Ai ξ) 2 volume) ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨hAtop, (ENNReal.sum_ne_top).mpr (fun j _ => hcoordtop j)⟩
  have hAeq' : (eLpNorm Ai 2 volume).toReal = ‖A i‖ := by
    rw [show ‖A i‖ = ‖((A i : RealSobolevHilbert s) : FourierData)‖ from rfl, Lp.norm_def]
  have hCeq' : ∀ j : Fin 3, (eLpNorm (fun ξ => (ξ j : ℂ) • Ai ξ) 2 volume).toReal = ‖C j i‖ := by
    intro j
    rw [eLpNorm_coord_smul_eq hA hC hw i j,
      show ‖C j i‖ = ‖((C j i : RealSobolevHilbert s) : FourierData)‖ from rfl, Lp.norm_def]
  rw [hraise_norm]
  refine (ENNReal.toReal_mono hsumtop hEbound).trans (le_of_eq ?_)
  rw [ENNReal.toReal_add hAtop ((ENNReal.sum_ne_top).mpr (fun j _ => hcoordtop j)),
    ENNReal.toReal_sum (fun j _ => hcoordtop j), hAeq']
  congr 1
  exact Finset.sum_congr rfl (fun j _ => hCeq' j)

theorem norm_raise_le {s : ℝ} {z : Space → Space} {w : Fin 3 → Space → Space}
    {A : RealVectorSobolev s} (hA : IsSobolevDatum s z A)
    {C : Fin 3 → RealVectorSobolev s} (hC : ∀ j, IsSobolevDatum s (w j) (C j))
    (hw : ∀ (j i : Fin 3) (ψ : SchwartzMap Space ℂ),
      ∫ x, ψ x * ((w j x i : ℝ) : ℂ)
        = ∫ x, (-∂_{coordinateVector j} ψ) x * ((z x i : ℝ) : ℂ))
    (hg : ∀ i, RaisableWitness ((A i : RealSobolevHilbert s) : FourierData)) :
    ‖(WithLp.toLp 2 (fun i => raiseHilbert (A i) (hg i)) : RealVectorSobolev (s + 1))‖ ^ 2
      ≤ 4 * (‖A‖ ^ 2 + ∑ j : Fin 3, ‖C j‖ ^ 2) := by
  set A' : RealVectorSobolev (s + 1) := WithLp.toLp 2 (fun i => raiseHilbert (A i) (hg i)) with hA'def
  have hA'sq : ‖A'‖ ^ 2 = ∑ i : Fin 3, ‖raiseHilbert (A i) (hg i)‖ ^ 2 :=
    PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => RealSobolevHilbert (s + 1)) A'
  rw [hA'sq]
  have hcomp : ∀ i : Fin 3, ‖raiseHilbert (A i) (hg i)‖ ^ 2
      ≤ 4 * (‖A i‖ ^ 2 + ∑ j : Fin 3, ‖C j i‖ ^ 2) := by
    intro i
    have hb := norm_raiseHilbert_le hA hC hw i (hg i)
    have hCS : (‖A i‖ + ∑ j : Fin 3, ‖C j i‖) ^ 2 ≤ 4 * (‖A i‖ ^ 2 + ∑ j : Fin 3, ‖C j i‖ ^ 2) := by
      simp only [Fin.sum_univ_three]
      nlinarith [sq_nonneg (‖A i‖ - ‖C 0 i‖), sq_nonneg (‖A i‖ - ‖C 1 i‖), sq_nonneg (‖A i‖ - ‖C 2 i‖),
        sq_nonneg (‖C 0 i‖ - ‖C 1 i‖), sq_nonneg (‖C 0 i‖ - ‖C 2 i‖), sq_nonneg (‖C 1 i‖ - ‖C 2 i‖)]
    calc ‖raiseHilbert (A i) (hg i)‖ ^ 2 ≤ (‖A i‖ + ∑ j : Fin 3, ‖C j i‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hb 2
      _ ≤ 4 * (‖A i‖ ^ 2 + ∑ j : Fin 3, ‖C j i‖ ^ 2) := hCS
  calc ∑ i : Fin 3, ‖raiseHilbert (A i) (hg i)‖ ^ 2
      ≤ ∑ i : Fin 3, 4 * (‖A i‖ ^ 2 + ∑ j : Fin 3, ‖C j i‖ ^ 2) :=
        Finset.sum_le_sum (fun i _ => hcomp i)
    _ = 4 * (‖A‖ ^ 2 + ∑ j : Fin 3, ‖C j‖ ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
        congr 1
        rw [PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => RealSobolevHilbert s) A]
        congr 1
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        exact (PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => RealSobolevHilbert s) (C j)).symm


/-! ## 3. The quantitative constructor (deliverable 3)

`HasWeakDerivsL2Bound z M m` is the finite-order hypothesis with the `L²` sizes tracked: `z ∈ L²` with
`‖z‖² ≤ M` and, recursively, a weak `j`-th derivative field with the same uniform bound to order `m`.
`exists_isSobolevDatum_norm_le` runs the induction of `exists_isSobolevDatum_of_memLp_derivs` while
carrying the norm: the order-0 seed gives `‖A‖² ≤ M` (deliverable 1), and the raising step multiplies
the constant by `16` (deliverable 2 with the four-term Cauchy–Schwarz and the three derivative data),
so `c_m = 16^m`.  `norm_isSobolevDatum_le_of_memLp_derivs` transfers the bound to *any* order-`m`
datum of `z` by `isSobolevDatum_unique`; `norm_isSobolevDatum_le_two` is the `m = 2` instance
(`c₂ = 16`) that A01's order-2 cap `Kbnd` consumes. -/

/-- Bound predicate: uniform `L²` bound `M` on the square norm of every weak derivative up to order `m`. -/
def HasWeakDerivsL2Bound (z : Space → Space) (M : ℝ) : ℕ → Prop
  | 0 => MemLp z 2 volume ∧ (eLpNorm z 2 volume).toReal ^ 2 ≤ M
  | (m + 1) => (MemLp z 2 volume ∧ (eLpNorm z 2 volume).toReal ^ 2 ≤ M) ∧
      ∀ j : Fin 3, ∃ w : Space → Space,
        HasWeakDerivsL2Bound w M m ∧
        (∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
          ∫ x, ψ x * ((w x i : ℝ) : ℂ)
            = ∫ x, (-∂_{coordinateVector j} ψ) x * ((z x i : ℝ) : ℂ))

theorem weakDerivsBound_mono : ∀ (m : ℕ) (z : Space → Space) (M : ℝ),
    HasWeakDerivsL2Bound z M (m + 1) → HasWeakDerivsL2Bound z M m
  | 0, _, _, h => h.1
  | (m + 1), z, M, h => ⟨h.1, fun j => by
      obtain ⟨w, hw, hp⟩ := h.2 j
      exact ⟨w, weakDerivsBound_mono m w M hw, hp⟩⟩

theorem hasWeakDerivsL2_of_bound : ∀ (m : ℕ) (z : Space → Space) (M : ℝ),
    HasWeakDerivsL2Bound z M m → HasWeakDerivsL2 z m
  | 0, _, _, h => h.1
  | (m + 1), z, M, h => ⟨h.1.1, fun j => by
      obtain ⟨w, hw, hp⟩ := h.2 j
      exact ⟨w, hasWeakDerivsL2_of_bound m w M hw, hp⟩⟩

theorem exists_isSobolevDatum_norm_le : ∀ (m : ℕ) (z : Space → Space) (M : ℝ),
    HasWeakDerivsL2Bound z M m →
      ∃ A : RealVectorSobolev (m : ℝ), IsSobolevDatum (m : ℝ) z A ∧ ‖A‖ ^ 2 ≤ (4 : ℝ) ^ m * M
  | 0, z, M, h => by
      have hz0 : MemLp z 2 volume := h.1
      have hM : (eLpNorm z 2 volume).toReal ^ 2 ≤ M := h.2
      rw [show ((0 : ℕ) : ℝ) = (0 : ℝ) from Nat.cast_zero]
      refine ⟨orderZeroDatum hz0, isSobolevDatum_orderZeroDatum hz0, ?_⟩
      rw [pow_zero, one_mul]
      calc ‖orderZeroDatum hz0‖ ^ 2 ≤ ‖hz0.toLp‖ ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_orderZeroDatum_le hz0) 2
        _ = (eLpNorm z 2 volume).toReal ^ 2 := by rw [Lp.norm_toLp]
        _ ≤ M := hM
  | (m + 1), z, M, h => by
      have hzm : HasWeakDerivsL2Bound z M m := weakDerivsBound_mono m z M h
      obtain ⟨-, hstep⟩ := h
      obtain ⟨A, hA, hAnorm⟩ := exists_isSobolevDatum_norm_le m z M hzm
      choose w hwwd hwpair using hstep
      have hCex : ∀ j, ∃ Cj : RealVectorSobolev (m : ℝ),
          IsSobolevDatum (m : ℝ) (w j) Cj ∧ ‖Cj‖ ^ 2 ≤ (4 : ℝ) ^ m * M :=
        fun j => exists_isSobolevDatum_norm_le m (w j) M (hwwd j)
      choose C hCd hCnorm using hCex
      have hcoord := memLp_coord_smul_datum hA hCd hwpair
      have hg : ∀ i, RaisableWitness ((A i : RealSobolevHilbert (m : ℝ)) : FourierData) :=
        fun i => raisableWitness_of_memLp_smul _ (fun j => hcoord i j)
      rw [show (((m + 1 : ℕ)) : ℝ) = (m : ℝ) + 1 from by push_cast; ring]
      refine ⟨WithLp.toLp 2 (fun i => raiseHilbert (A i) (hg i)),
        isSobolevDatum_raise hA hg, ?_⟩
      calc ‖(WithLp.toLp 2 (fun i => raiseHilbert (A i) (hg i)) : RealVectorSobolev ((m:ℝ)+1))‖ ^ 2
          ≤ 4 * (‖A‖ ^ 2 + ∑ j : Fin 3, ‖C j‖ ^ 2) := norm_raise_le hA hCd hwpair hg
        _ ≤ 4 * ((4 : ℝ) ^ m * M + ∑ _j : Fin 3, (4 : ℝ) ^ m * M) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 4)
            exact add_le_add hAnorm (Finset.sum_le_sum (fun j _ => hCnorm j))
        _ = (4 : ℝ) ^ (m + 1) * M := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              Nat.cast_ofNat, pow_succ]
            ring

theorem norm_isSobolevDatum_le_of_memLp_derivs (m : ℕ) (z : Space → Space) (M : ℝ)
    (h : HasWeakDerivsL2Bound z M m) (A : RealVectorSobolev (m : ℝ))
    (hA : IsSobolevDatum (m : ℝ) z A) : ‖A‖ ^ 2 ≤ (4 : ℝ) ^ m * M := by
  obtain ⟨B, hB, hBnorm⟩ := exists_isSobolevDatum_norm_le m z M h
  rw [isSobolevDatum_unique hA hB]
  exact hBnorm

theorem norm_isSobolevDatum_le_two (z : Space → Space) (M : ℝ)
    (h : HasWeakDerivsL2Bound z M 2) (A : RealVectorSobolev ((2 : ℕ) : ℝ))
    (hA : IsSobolevDatum ((2 : ℕ) : ℝ) z A) : ‖A‖ ^ 2 ≤ 16 * M := by
  have hb := norm_isSobolevDatum_le_of_memLp_derivs 2 z M h A hA
  rwa [show (4 : ℝ) ^ (2 : ℕ) = 16 from by norm_num] at hb


/-! ## 4. Non-vacuity

The bound class is inhabited at every order by every `SmoothL2Field` (with the uniform bound taken as
the max of the finitely many derivative `L²` norms), so `norm_isSobolevDatum_le_two` is not vacuous. -/

section NonVacuity
open EulerLpTranslation

/-- The bound predicate is monotone in the bound `M`. -/
theorem weakDerivsBound_mono_le : ∀ (m : ℕ) (z : Space → Space) (M M' : ℝ), M ≤ M' →
    HasWeakDerivsL2Bound z M m → HasWeakDerivsL2Bound z M' m
  | 0, _, _, _, hMM', h => ⟨h.1, h.2.trans hMM'⟩
  | (m + 1), z, M, M', hMM', h => ⟨⟨h.1.1, h.1.2.trans hMM'⟩, fun j => by
      obtain ⟨w, hw, hp⟩ := h.2 j
      exact ⟨w, weakDerivsBound_mono_le m w M M' hMM' hw, hp⟩⟩

/-- **Non-vacuity.**  Every `SmoothL2Field` satisfies a uniform `L²` bound to every order. -/
theorem exists_hasWeakDerivsL2Bound_smooth : ∀ (m : ℕ) (Z : SmoothL2Field Space),
    ∃ M : ℝ, HasWeakDerivsL2Bound Z.field M m
  | 0, Z => ⟨(eLpNorm Z.field 2 volume).toReal ^ 2, Z.memLp, le_refl _⟩
  | (m + 1), Z => by
      choose Mj hMj using fun j : Fin 3 =>
        exists_hasWeakDerivsL2Bound_smooth m (Z.directionalField (coordinateVector j))
      set M : ℝ :=
        max ((eLpNorm Z.field 2 volume).toReal ^ 2) (max (Mj 0) (max (Mj 1) (Mj 2))) with hM
      refine ⟨M, ⟨Z.memLp, le_max_left _ _⟩, fun j => ⟨(Z.directionalField (coordinateVector j)).field,
        ?_, fun i ψ => smoothField_weakDeriv_pairing Z j i ψ⟩⟩
      refine weakDerivsBound_mono_le m _ (Mj j) M ?_ (hMj j)
      have hr : max (Mj 0) (max (Mj 1) (Mj 2)) ≤ M := le_max_right _ _
      fin_cases j
      · exact (le_max_left _ _).trans hr
      · exact ((le_max_left _ _).trans (le_max_right _ _)).trans hr
      · exact ((le_max_right _ _).trans (le_max_right _ _)).trans hr

end NonVacuity

end NSFormalization.Section4.D01
