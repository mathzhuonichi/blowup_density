import NSFormalization.Section4.D01.LeraySymbol
import NSFormalization.Paper3.RealVectorPositiveDensity
import Formal.R3LerayPointwiseL2
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The operator-valued `L²` Fourier multiplier for the Leray complement (D01 · P2 · SL3/SL2)

`research/D01/P2_SPLIT.md` sub-lemmas **SL3** (the operator-valued `L²` multiplier) and
**SL2** (reality preservation), following the reviewer-corrected route of
`research/D01/REVIEW_P2.md`.

`Section4/D01/LeraySymbol.lean` (lane 062) proved the *real* fibre symbol
`complementSymbol ξ = (ℝ ∙ ξ).starProjection = ξξᵀ/‖ξ‖²` (`(I−P)`).  The Fourier data are
`ℂ`-valued, so the fibre algebra the multiplier actually consumes is the **complex** one.
This module adds the complex complement symbol `complementSymbolComplex`, mirror of
HeliCorgi's solenoidal `MNS2.r3LeraySymbolComplex`, and bundles it into the
operator-valued `L²` multiplier

  `lerayComplementL2 : R3L2Velocity →L[ℝ] R3L2Velocity`,   `(F̂)(ξ) ↦ (I−P)(ξ)(F̂ ξ)`,

with operator norm `≤ 1` (fibrewise contraction, `MemLp.of_le` / `Lp.norm_le_norm_of_ae_le`),
the a.e. action `lerayComplementL2 F =ᵐ fun ξ => complementSymbolComplex ξ (F ξ)`, idempotence,
the complementary solenoidal projection `lerayL2 = 1 − lerayComplementL2` with
`lerayL2 + lerayComplementL2 = 1`, the fibre facts (kills transverse / fixes longitudinal `L²`
fields) and reality preservation (commutes with the vector conjugate-reflection `realSymmetry`,
hence preserves the *raw* carrier's reality fixed-point set; `coordinates_realSymmetryVec` bridges
it componentwise to the scalar `Source.RealSobolev.realSubspace`).

The heavy lifting versus HeliCorgi's `R3LerayPointwiseL2.lean` (which builds only a bare
*function*) is bundling into a genuine `ContinuousLinearMap` while keeping `opNorm ≤ 1`; the
matrix genuinely mixes coordinates, so the constant `1` survives only in the vector-valued
picture (a nine-scalar-entry assembly reaches only `≤ 3`, `REVIEW_P2.md` finding 1c).

No `sorry`, no `axiom`; `#print axioms` is standard (`research/D01/axioms_sl3.lean`).
-/

noncomputable section

namespace NSFormalization.Section4.D01.Leray

open MeasureTheory
open scoped ComplexConjugate

/-! ## 1. The complex complement fibre symbol -/

/-- **The complex Leray complement fibre symbol** at frequency `ξ`: the orthogonal
projection of the complex Fourier fibre `R3C` onto the longitudinal line
`ℂ ∙ ξ_ℂ` spanned by the embedded real frequency vector.  This is the complexification of
`LeraySymbol.complementSymbol ξ`, and the fibre complement of HeliCorgi's solenoidal
`MNS2.r3LeraySymbolComplex ξ = (ℂ ∙ ξ_ℂ)ᗮ.starProjection`. -/
def complementSymbolComplex (ξ : MNS2.R3) : MNS2.R3C →L[ℂ] MNS2.R3C :=
  (ℂ ∙ MNS2.r3FrequencyVectorComplex ξ).starProjection

/-- Explicit rank-one formula `(I−P)(ξ)v = (⟪ξ_ℂ, v⟫ / ‖ξ_ℂ‖²) • ξ_ℂ`. -/
theorem complementSymbolComplex_apply (ξ : MNS2.R3) (v : MNS2.R3C) :
    complementSymbolComplex ξ v =
      (inner ℂ (MNS2.r3FrequencyVectorComplex ξ) v /
        (((‖MNS2.r3FrequencyVectorComplex ξ‖ ^ 2 : ℝ) : ℂ))) •
        MNS2.r3FrequencyVectorComplex ξ := by
  simpa [complementSymbolComplex] using
    (Submodule.starProjection_singleton (𝕜 := ℂ) (v := MNS2.r3FrequencyVectorComplex ξ) v)

/-- Every output is longitudinal. -/
theorem complementSymbolComplex_apply_mem (ξ : MNS2.R3) (v : MNS2.R3C) :
    complementSymbolComplex ξ v ∈ ℂ ∙ MNS2.r3FrequencyVectorComplex ξ := by
  simp only [complementSymbolComplex]
  exact Submodule.starProjection_apply_mem _ v

/-- Fixes every longitudinal vector. -/
theorem complementSymbolComplex_fixed_of_mem (ξ : MNS2.R3) (v : MNS2.R3C)
    (hv : v ∈ ℂ ∙ MNS2.r3FrequencyVectorComplex ξ) : complementSymbolComplex ξ v = v := by
  simpa [complementSymbolComplex] using
    (Submodule.starProjection_eq_self_iff
      (K := ℂ ∙ MNS2.r3FrequencyVectorComplex ξ) (v := v)).2 hv

/-- **Projection.** Idempotent at every frequency. -/
theorem complementSymbolComplex_idempotent (ξ : MNS2.R3) (v : MNS2.R3C) :
    complementSymbolComplex ξ (complementSymbolComplex ξ v) = complementSymbolComplex ξ v :=
  complementSymbolComplex_fixed_of_mem ξ _ (complementSymbolComplex_apply_mem ξ v)

/-- **Fibrewise contraction.** -/
theorem norm_complementSymbolComplex_le (ξ : MNS2.R3) (v : MNS2.R3C) :
    ‖complementSymbolComplex ξ v‖ ≤ ‖v‖ := by
  simpa [complementSymbolComplex] using
    (ℂ ∙ MNS2.r3FrequencyVectorComplex ξ).norm_starProjection_apply_le v

/-- **Operator norm ≤ 1** at every frequency. -/
theorem complementSymbolComplex_opNorm_le_one (ξ : MNS2.R3) :
    ‖complementSymbolComplex ξ‖ ≤ 1 := by
  simpa [complementSymbolComplex] using
    (ℂ ∙ MNS2.r3FrequencyVectorComplex ξ).starProjection_norm_le

/-- **Complementarity with HeliCorgi's solenoidal symbol** `P(ξ)`: `P + (I−P) = I`. -/
theorem r3LeraySymbolComplex_add_complementSymbolComplex (ξ : MNS2.R3) (v : MNS2.R3C) :
    MNS2.r3LeraySymbolComplex ξ v + complementSymbolComplex ξ v = v := by
  have h : MNS2.r3LeraySymbolComplex ξ v =
      v - complementSymbolComplex ξ v := by
    change (ℂ ∙ MNS2.r3FrequencyVectorComplex ξ)ᗮ.starProjection v = _
    rw [Submodule.starProjection_orthogonal_val]
    rfl
  rw [h]; abel

/-- The complement symbol is `I` minus HeliCorgi's solenoidal symbol. -/
theorem complementSymbolComplex_eq_sub (ξ : MNS2.R3) (v : MNS2.R3C) :
    complementSymbolComplex ξ v = v - MNS2.r3LeraySymbolComplex ξ v := by
  have := r3LeraySymbolComplex_add_complementSymbolComplex ξ v
  linear_combination (norm := module) this

/-- **Kills transverse (solenoidal) directions.** -/
theorem complementSymbolComplex_eq_zero_of_inner_eq_zero (ξ : MNS2.R3) (v : MNS2.R3C)
    (h : inner ℂ (MNS2.r3FrequencyVectorComplex ξ) v = 0) : complementSymbolComplex ξ v = 0 := by
  rw [complementSymbolComplex_apply, h, zero_div, zero_smul]

/-! ## 2. The pointwise action and its `L²` membership -/

/-- The complex complement symbol applied pointwise to a Fourier-side `L²` velocity. -/
def lerayComplementAction (f : MNS2.R3L2Velocity) : MNS2.R3 → MNS2.R3C :=
  fun ξ => complementSymbolComplex ξ (f ξ)

theorem aestronglyMeasurable_lerayComplementAction (f : MNS2.R3L2Velocity) :
    AEStronglyMeasurable (lerayComplementAction f) volume := by
  unfold lerayComplementAction
  rw [show (fun ξ => complementSymbolComplex ξ (f ξ)) =
      fun ξ =>
        (inner ℂ (MNS2.r3FrequencyVectorComplex ξ) (f ξ) /
          (((‖MNS2.r3FrequencyVectorComplex ξ‖ ^ 2 : ℝ) : ℂ))) •
          MNS2.r3FrequencyVectorComplex ξ by
      funext ξ; exact complementSymbolComplex_apply ξ (f ξ)]
  have hfreq : AEStronglyMeasurable MNS2.r3FrequencyVectorComplex volume :=
    MNS2.continuous_r3FrequencyVectorComplex.aestronglyMeasurable
  have hf : AEStronglyMeasurable (fun ξ : MNS2.R3 => f ξ) volume := Lp.aestronglyMeasurable f
  have hinner : AEStronglyMeasurable
      (fun ξ : MNS2.R3 => inner ℂ (MNS2.r3FrequencyVectorComplex ξ) (f ξ)) volume :=
    hfreq.inner hf
  have hden : AEStronglyMeasurable
      (fun ξ : MNS2.R3 => (((‖MNS2.r3FrequencyVectorComplex ξ‖ ^ 2 : ℝ) : ℂ))) volume := by
    fun_prop
  have hquot : AEStronglyMeasurable
      (fun ξ : MNS2.R3 => inner ℂ (MNS2.r3FrequencyVectorComplex ξ) (f ξ) /
        (((‖MNS2.r3FrequencyVectorComplex ξ‖ ^ 2 : ℝ) : ℂ))) volume :=
    (hinner.aemeasurable.div hden.aemeasurable).aestronglyMeasurable
  exact hquot.smul hfreq

theorem memLp_lerayComplementAction (f : MNS2.R3L2Velocity) :
    MemLp (lerayComplementAction f) 2 volume :=
  (Lp.memLp f).of_le (aestronglyMeasurable_lerayComplementAction f)
    (ae_of_all _ fun ξ => norm_complementSymbolComplex_le ξ (f ξ))

/-! ## 3. The bundled complement multiplier as a `ℂ`-CLM -/

/-- The complement multiplier as an `L²` element (the `toLp` of the pointwise action). -/
def lerayComplementFun (f : MNS2.R3L2Velocity) : MNS2.R3L2Velocity :=
  (memLp_lerayComplementAction f).toLp (lerayComplementAction f)

theorem lerayComplementFun_ae (f : MNS2.R3L2Velocity) :
    lerayComplementFun f =ᵐ[volume] fun ξ => complementSymbolComplex ξ (f ξ) :=
  (memLp_lerayComplementAction f).coeFn_toLp

theorem lerayComplementFun_add (f g : MNS2.R3L2Velocity) :
    lerayComplementFun (f + g) = lerayComplementFun f + lerayComplementFun g := by
  apply Lp.ext
  filter_upwards [lerayComplementFun_ae (f + g), lerayComplementFun_ae f,
    lerayComplementFun_ae g, Lp.coeFn_add f g,
    Lp.coeFn_add (lerayComplementFun f) (lerayComplementFun g)] with ξ h₁ h₂ h₃ h₄ h₅
  rw [h₅, h₁, h₄]
  simp only [Pi.add_apply]
  rw [map_add, h₂, h₃]

theorem lerayComplementFun_smul (c : ℂ) (f : MNS2.R3L2Velocity) :
    lerayComplementFun (c • f) = c • lerayComplementFun f := by
  apply Lp.ext
  filter_upwards [lerayComplementFun_ae (c • f), lerayComplementFun_ae f,
    Lp.coeFn_smul c f, Lp.coeFn_smul c (lerayComplementFun f)] with ξ h₁ h₂ h₃ h₄
  rw [h₄, h₁, h₃]
  simp only [Pi.smul_apply]
  rw [map_smul, h₂]

theorem norm_lerayComplementFun_le (f : MNS2.R3L2Velocity) :
    ‖lerayComplementFun f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [lerayComplementFun_ae f] with ξ hξ
  rw [hξ]; exact norm_complementSymbolComplex_le ξ (f ξ)

/-- The complement multiplier as a `ℂ`-linear map. -/
def lerayComplementLinear : MNS2.R3L2Velocity →ₗ[ℂ] MNS2.R3L2Velocity where
  toFun := lerayComplementFun
  map_add' := lerayComplementFun_add
  map_smul' c f := lerayComplementFun_smul c f

/-- **The operator-valued `L²` Leray-complement multiplier** (ℂ-linear form). -/
def lerayComplementL2C : MNS2.R3L2Velocity →L[ℂ] MNS2.R3L2Velocity :=
  lerayComplementLinear.mkContinuous 1 (fun f => by rw [one_mul]; exact norm_lerayComplementFun_le f)

theorem lerayComplementL2C_apply (f : MNS2.R3L2Velocity) :
    lerayComplementL2C f = lerayComplementFun f := rfl

theorem lerayComplementL2C_opNorm_le_one : ‖lerayComplementL2C‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The a.e. action of the multiplier: `(I−P)F =ᵐ fun ξ => (I−P)(ξ)(F ξ)`. -/
theorem lerayComplementL2C_ae (f : MNS2.R3L2Velocity) :
    lerayComplementL2C f =ᵐ[volume] fun ξ => complementSymbolComplex ξ (f ξ) :=
  lerayComplementFun_ae f

/-- **The operator-valued `L²` Leray-complement multiplier** (real-linear form, the datum
convention).  Same underlying map, scalars restricted to `ℝ`. -/
def lerayComplementL2 : MNS2.R3L2Velocity →L[ℝ] MNS2.R3L2Velocity :=
  lerayComplementL2C.restrictScalars ℝ

theorem lerayComplementL2_apply (f : MNS2.R3L2Velocity) :
    lerayComplementL2 f = lerayComplementFun f := rfl

/-- **Operator norm `≤ 1`.** -/
theorem lerayComplementL2_opNorm_le_one : ‖lerayComplementL2‖ ≤ 1 := by
  rw [lerayComplementL2, ContinuousLinearMap.norm_restrictScalars]
  exact lerayComplementL2C_opNorm_le_one

/-- **The a.e. action** `(I−P)F =ᵐ fun ξ => (I−P)(ξ)(F ξ)`. -/
theorem lerayComplementL2_ae (f : MNS2.R3L2Velocity) :
    lerayComplementL2 f =ᵐ[volume] fun ξ => complementSymbolComplex ξ (f ξ) :=
  lerayComplementFun_ae f

/-! ## 4. Idempotence and the complementary solenoidal projection -/

/-- **Idempotence.** `(I−P)²  = (I−P)` on `L²`. -/
theorem lerayComplementL2_idempotent (f : MNS2.R3L2Velocity) :
    lerayComplementL2 (lerayComplementL2 f) = lerayComplementL2 f := by
  apply Lp.ext
  filter_upwards [lerayComplementL2_ae (lerayComplementL2 f), lerayComplementL2_ae f]
    with ξ h₁ h₂
  rw [h₁, h₂, complementSymbolComplex_idempotent]

/-- **The complementary solenoidal Leray projector** `P = I − (I−P)`. -/
def lerayL2 : MNS2.R3L2Velocity →L[ℝ] MNS2.R3L2Velocity := 1 - lerayComplementL2

/-- **Helmholtz decomposition of the identity**: `P + (I−P) = I`. -/
theorem lerayL2_add_lerayComplementL2 : lerayL2 + lerayComplementL2 = 1 := by
  unfold lerayL2; abel

/-- The solenoidal projector realizes HeliCorgi's pointwise complex Leray symbol
`P(ξ) = MNS2.r3LeraySymbolComplex ξ` almost everywhere. -/
theorem lerayL2_ae (f : MNS2.R3L2Velocity) :
    lerayL2 f =ᵐ[volume] fun ξ => MNS2.r3LeraySymbolComplex ξ (f ξ) := by
  have hsub : lerayL2 f = f - lerayComplementL2 f := rfl
  rw [hsub]
  filter_upwards [Lp.coeFn_sub f (lerayComplementL2 f), lerayComplementL2_ae f] with ξ h₁ h₂
  rw [h₁]
  simp only [Pi.sub_apply]
  rw [h₂, complementSymbolComplex_eq_sub]
  abel

/-! ## 5. Fibre facts lifted to `L²` fields -/

/-- **`(I−P)` fixes a longitudinal (gradient) field.**  If the Fourier data are a.e.
longitudinal (`F̂(ξ) ∈ ℂ ∙ ξ_ℂ`), the complement multiplier is the identity. -/
theorem lerayComplementL2_eq_self_of_longitudinal (f : MNS2.R3L2Velocity)
    (h : ∀ᵐ ξ ∂volume, (f ξ) ∈ ℂ ∙ MNS2.r3FrequencyVectorComplex ξ) :
    lerayComplementL2 f = f := by
  apply Lp.ext
  filter_upwards [lerayComplementL2_ae f, h] with ξ h₁ h₂
  rw [h₁]
  exact complementSymbolComplex_fixed_of_mem ξ (f ξ) h₂

/-- **`(I−P)` kills a transverse (solenoidal) field.**  If the Fourier data are a.e.
orthogonal to the frequency (`⟪ξ_ℂ, F̂(ξ)⟫ = 0`), the complement multiplier is zero. -/
theorem lerayComplementL2_eq_zero_of_transverse (f : MNS2.R3L2Velocity)
    (h : ∀ᵐ ξ ∂volume, inner ℂ (MNS2.r3FrequencyVectorComplex ξ) (f ξ) = 0) :
    lerayComplementL2 f = 0 := by
  apply Lp.ext
  filter_upwards [lerayComplementL2_ae f, h,
    Lp.coeFn_zero (E := MNS2.R3C) (p := 2) (μ := (volume : Measure MNS2.R3))] with ξ h₁ h₂ h₃
  rw [h₁, h₃, Pi.zero_apply,
    complementSymbolComplex_eq_zero_of_inner_eq_zero ξ (f ξ) h₂]

/-! ## 6. Reality preservation (SL2)

The multiplier maps the Fourier transforms of *real* velocity fields to Fourier transforms of
real fields.  Reality of `L²` data is the conjugate-reflection symmetry `Â(ξ) = conj Â(−ξ)`; on
`R3L2Velocity` it is the fixed-point set of the real-linear involution
`realSymmetryVec = conjugationVec ∘ reflectionVec` (the vector analogue of the scalar
`Source.RealSobolev.realSymmetry`).  Because the fibre symbol is **real-entried** (commutes with
coordinatewise conjugation, `conjR3C_complementSymbolComplex`) and **even** in `ξ`
(`complementSymbolComplex_neg`), the multiplier commutes with `realSymmetryVec`
(`realSymmetryVec_lerayComplementL2`), so it preserves the reality subspace.  This mirrors
`NSFormalization.Paper3.realSymmetry_angularDirectionalDerivative` (lane 066). -/

/-- Coordinatewise complex conjugation on the Fourier fibre `R3C`. -/
def conjR3C : MNS2.R3C ≃ₗᵢ[ℝ] MNS2.R3C :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin 3 => Complex.conjLIE)

theorem conjR3C_apply (v : MNS2.R3C) : conjR3C v = WithLp.toLp 2 (fun i => conj (v i)) := by
  rw [conjR3C, LinearIsometryEquiv.piLpCongrRight_apply]; rfl

theorem conjR3C_smul (c : ℂ) (w : MNS2.R3C) : conjR3C (c • w) = conj c • conjR3C w := by
  rw [conjR3C_apply, conjR3C_apply]; ext i
  simp only [PiLp.smul_apply, smul_eq_mul, map_mul]

/-- The embedded real frequency vector is fixed by conjugation. -/
theorem conjR3C_r3FrequencyVectorComplex (ξ : MNS2.R3) :
    conjR3C (MNS2.r3FrequencyVectorComplex ξ) = MNS2.r3FrequencyVectorComplex ξ := by
  rw [conjR3C_apply]; ext i; simp [MNS2.r3FrequencyVectorComplex]

theorem r3FrequencyVectorComplex_neg (ξ : MNS2.R3) :
    MNS2.r3FrequencyVectorComplex (-ξ) = - MNS2.r3FrequencyVectorComplex ξ := by
  ext i; simp [MNS2.r3FrequencyVectorComplex]

/-- **Even in `ξ`.** -/
theorem complementSymbolComplex_neg (ξ : MNS2.R3) :
    complementSymbolComplex (-ξ) = complementSymbolComplex ξ := by
  ext v
  rw [complementSymbolComplex_apply, complementSymbolComplex_apply, r3FrequencyVectorComplex_neg]
  simp only [inner_neg_left, norm_neg, neg_div, neg_smul, smul_neg, neg_neg]

/-- Conjugation is `starRingEnd`-semilinear against the (real) frequency inner product. -/
theorem inner_conjR3C (ξ : MNS2.R3) (v : MNS2.R3C) :
    inner ℂ (MNS2.r3FrequencyVectorComplex ξ) (conjR3C v) =
      conj (inner ℂ (MNS2.r3FrequencyVectorComplex ξ) v) := by
  rw [conjR3C_apply, PiLp.inner_apply, PiLp.inner_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hfr : (MNS2.r3FrequencyVectorComplex ξ) i = ((ξ i : ℝ) : ℂ) := rfl
  simp only [RCLike.inner_apply, map_mul, hfr, Complex.conj_ofReal]

/-- **Real matrix entries.** The complement symbol commutes with coordinatewise conjugation. -/
theorem conjR3C_complementSymbolComplex (ξ : MNS2.R3) (v : MNS2.R3C) :
    conjR3C (complementSymbolComplex ξ v) = complementSymbolComplex ξ (conjR3C v) := by
  rw [complementSymbolComplex_apply, complementSymbolComplex_apply, conjR3C_smul,
    conjR3C_r3FrequencyVectorComplex, inner_conjR3C]
  congr 1
  rw [map_div₀]; congr 1; rw [Complex.conj_ofReal]

/-- Reflection `ξ ↦ −ξ` on the vector `L²`. -/
def reflectionVec : MNS2.R3L2Velocity →ₗᵢ[ℝ] MNS2.R3L2Velocity :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun ξ : MNS2.R3 => -ξ) (Measure.measurePreserving_neg volume)

/-- Coordinatewise conjugation on the vector `L²`. -/
def conjugationVec : MNS2.R3L2Velocity →L[ℝ] MNS2.R3L2Velocity :=
  conjR3C.toLinearIsometry.toContinuousLinearMap.compLpL 2 volume

/-- The conjugate-reflection reality involution on the vector `L²`. -/
def realSymmetryVec : MNS2.R3L2Velocity →L[ℝ] MNS2.R3L2Velocity :=
  conjugationVec.comp reflectionVec.toContinuousLinearMap

theorem realSymmetryVec_ae (g : MNS2.R3L2Velocity) :
    (realSymmetryVec g : MNS2.R3 → MNS2.R3C) =ᵐ[volume] fun ξ => conjR3C (g (-ξ)) := by
  have hc := ContinuousLinearMap.coeFn_compLpL
    conjR3C.toLinearIsometry.toContinuousLinearMap (reflectionVec g)
  have hr := Lp.coeFn_compMeasurePreserving g
    (Measure.measurePreserving_neg (volume : Measure MNS2.R3))
  filter_upwards [hc, hr] with ξ hξ hrξ
  exact hξ.trans (congrArg conjR3C hrξ)

/-- **SL2 — the multiplier commutes with the reality involution.**  (Real, even symbol.) -/
theorem realSymmetryVec_lerayComplementL2 (f : MNS2.R3L2Velocity) :
    realSymmetryVec (lerayComplementL2 f) = lerayComplementL2 (realSymmetryVec f) := by
  apply Lp.ext
  have hr := (Measure.measurePreserving_neg (volume : Measure MNS2.R3)).quasiMeasurePreserving.ae
    (lerayComplementL2_ae f)
  filter_upwards [realSymmetryVec_ae (lerayComplementL2 f),
    lerayComplementL2_ae (realSymmetryVec f), realSymmetryVec_ae f, hr] with ξ h₁ h₂ h₃ h₄
  rw [h₁, h₄, h₂, h₃, conjR3C_complementSymbolComplex, complementSymbolComplex_neg]

/-- **SL2 — reality preservation (raw carrier).**  The complement multiplier maps the reality
subspace *of the raw vector `L²`* — the fixed-point set of the module's own `realSymmetryVec`,
i.e. the Fourier transforms of real fields — into itself.  This is not yet the datum-level
`RealVectorSobolev m`; the componentwise link to `Source.RealSobolev.realSubspace` is
`coordinates_realSymmetryVec` below. -/
theorem realSymmetryVec_lerayComplementL2_eq_self (f : MNS2.R3L2Velocity)
    (hf : realSymmetryVec f = f) :
    realSymmetryVec (lerayComplementL2 f) = lerayComplementL2 f := by
  rw [realSymmetryVec_lerayComplementL2, hf]

/-! ## 7. The `q = 2` `assemble`/`coordinates` isometry (datum-carrier bridge)

The manuscript's datum carrier is `RealVectorSobolev m = Product (Fin 3) (RealSobolevHilbert m)`
— a `PiLp 2` *of* scalar `Lp ℂ 2` spaces — whereas the multiplier above acts on
`R3L2Velocity = Lp (EuclideanSpace ℂ (Fin 3)) 2` — the `Lp` *of* a `PiLp 2`.  The bridge is
`Source.FiniteHilbertBochner.coordinates` / `assemble`.  The reviewer (`REVIEW_P2.md`, finding 1)
identified its **`q = 2` isometry** as the one genuine work item for lifting the multiplier to the
datum carrier with operator norm `≤ 1` (the componentwise nine-scalar route reaches only `≤ 3`).

This section proves that work item: both directions of the bridge are `q = 2` isometries — the
`coordinates` half (`coordinates_norm`) via the `L²` inner product (`L2.inner_def`) and
Fubini/Tonelli on the finite fibre sum (`MeasureTheory.integral_finsetSum`, `PiLp.inner_apply`),
and the `assemble` half (`assemble_norm`) as its inverse, using the round trip
`coordinates_assemble` (`coordinates ∘ assemble = id`).  The lemmas are stated generically in the
`FiniteHilbertBochner` parameters (`ι`, `α`, `μ`) since `RealSobolevHilbert` is order-neutral, so a
single operator serves every Sobolev order once the carrier bridge is bundled.

The `coordinates_assemble` / `assemble_norm` / `coordinates_realSymmetryVec` proofs here are
adapted from the reviewer's probes on `research/D01/REVIEW_SL3.md`: the working route keeps the
`assemble` sum whole at the coeFn level (`Lp.coeFn_finsetSum` + `ContinuousLinearMap.coeFn_compLpL`
+ `insert_apply`), pinning `insert`'s scalar to `ℂ` to sidestep the name/instance ambiguity that an
earlier draft mistook for a `whnf` blow-up.  With them the datum-carrier repackaging
`lerayComplement m : RealVectorSobolev m →L[ℝ] RealVectorSobolev m` is a short follow-on
(conjugation `coordinates ∘ lerayComplementL2 ∘ assemble` + `codRestrict`), all inside
`Section4/D01/`. -/

open NSFormalization.Source.FiniteHilbertBochner (assemble coordinates coord Product insert_apply)

/-- Local unambiguous alias for `FiniteHilbertBochner.insert` (clashes with `Insert.insert`),
scalar pinned to `ℂ` at use sites.  Proof helper only. -/
private noncomputable abbrev ins := @NSFormalization.Source.FiniteHilbertBochner.insert

section IsometryBridge
variable {ι : Type*} [Fintype ι] {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- The `i`-th coordinate of a bundled `L²` vector field is a.e. its pointwise `i`-th component. -/
theorem coordinates_ae (b : Lp (Product ι ℂ) 2 μ) (i : ι) :
    (coordinates 2 μ b i : α → ℂ) =ᵐ[μ] fun t => (b t) i := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (coord i) b] with t ht
  exact ht

/-- `coordinates` preserves the `L²` inner product into the `PiLp 2` datum carrier. -/
theorem coordinates_inner_self (b : Lp (Product ι ℂ) 2 μ) :
    (inner ℂ (WithLp.toLp 2 (coordinates 2 μ b) : Product ι (Lp ℂ 2 μ))
      (WithLp.toLp 2 (coordinates 2 μ b)) : ℂ) = inner ℂ b b := by
  rw [PiLp.inner_apply]
  have key : ∀ i, (inner ℂ (coordinates 2 μ b i) (coordinates 2 μ b i) : ℂ)
      = ∫ t, (inner ℂ ((coordinates 2 μ b i) t) ((coordinates 2 μ b i) t) : ℂ) ∂μ :=
    fun i => L2.inner_def _ _
  simp_rw [key]
  rw [← MeasureTheory.integral_finsetSum Finset.univ
      (fun i (_ : i ∈ Finset.univ) =>
        L2.integrable_inner (coordinates 2 μ b i) (coordinates 2 μ b i)),
    L2.inner_def b b]
  refine integral_congr_ae ?_
  filter_upwards [ae_all_iff.2 (fun i => coordinates_ae μ b i)] with t ht
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl (fun i _ => by rw [ht i])

/-- **The `coordinates` half of the `q = 2` isometry** (SL3 datum-carrier bridge).  `coordinates`
maps a bundled `L²` velocity field isometrically onto its `PiLp 2` tuple of scalar `L²`
components.  The `assemble` direction is `assemble_norm` below; together they are the full
`REVIEW_P2.md` work item. -/
theorem coordinates_norm (b : Lp (Product ι ℂ) 2 μ) :
    ‖(WithLp.toLp 2 (coordinates 2 μ b) : Product ι (Lp ℂ 2 μ))‖ = ‖b‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), coordinates_inner_self]

/-- **`coordinates ∘ assemble = id`** (after the reviewer's probes, `REVIEW_SL3.md`).  Assembling
scalar `L²` components into a bundled vector field and reading off the `j`-th coordinate returns
the `j`-th component.  Specialises at `ι = Fin 3`, `μ = volume` to the manuscript datum carrier. -/
theorem coordinates_assemble [DecidableEq ι] (h : ι → Lp ℂ 2 μ) (j : ι) :
    coordinates 2 μ (assemble 2 μ h) j = h j := by
  apply Lp.ext
  have hsum : ∀ᵐ t ∂μ, (assemble 2 μ h) t = ∑ i, ins (H := ℂ) i (h i t) := by
    have hco : ∀ᵐ t ∂μ, ∀ i : ι,
        ((ins (H := ℂ) i).compLpL 2 μ (h i)) t = ins i (h i t) := by
      rw [ae_all_iff]
      intro i
      filter_upwards [ContinuousLinearMap.coeFn_compLpL (ins (H := ℂ) i) (h i)] with t ht
      exact ht
    filter_upwards [Lp.coeFn_finsetSum Finset.univ
      (fun i => (ins (H := ℂ) i).compLpL 2 μ (h i)), hco] with t ht hco
    change (∑ i, (ins (H := ℂ) i).compLpL 2 μ (h i)) t = _
    rw [ht]
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun i _ => hco i)
  filter_upwards [coordinates_ae μ (assemble 2 μ h) j, hsum] with t ht hs
  rw [ht, hs]
  simp [insert_apply]

/-- **The `assemble` half of the `q = 2` isometry** (after the reviewer's probes).  `assemble` is
the isometric inverse of `coordinates`: it maps a `PiLp 2` tuple of scalar `L²` functions
isometrically onto the bundled vector field.  Four lines from `coordinates_assemble` and
`coordinates_norm`; supplies the `opNorm ≤ 1` transport by conjugation-by-isometry the
componentwise nine-scalar route (bounded only by `≤ |ι|`) cannot. -/
theorem assemble_norm [DecidableEq ι] (h : ι → Lp ℂ 2 μ) :
    ‖assemble 2 μ h‖ = ‖(WithLp.toLp 2 h : Product ι (Lp ℂ 2 μ))‖ := by
  have hc : coordinates 2 μ (assemble 2 μ h) = h := funext (coordinates_assemble μ h)
  have hnorm := coordinates_norm μ (assemble 2 μ h)
  rw [hc] at hnorm
  exact hnorm.symm

end IsometryBridge

/-- **Reality intertwiner through the carrier bridge** (after the reviewer's probe G).  The
module's vector conjugate-reflection `realSymmetryVec` restricts, componentwise through
`coordinates`, to the scalar `Source.RealSobolev.realSymmetry`.  This is the missing link from the
raw-carrier reality result `realSymmetryVec_lerayComplementL2_eq_self` to the datum-level
`RealVectorSobolev m = Product (Fin 3) (RealSobolevHilbert m)`: it lets the follow-on lane
`codRestrict` the operator onto the reality subspace componentwise. -/
theorem coordinates_realSymmetryVec (b : MNS2.R3L2Velocity) (i : Fin 3) :
    coordinates 2 volume (realSymmetryVec b) i =
      NSFormalization.Source.RealSobolev.realSymmetry (coordinates 2 volume b i) := by
  apply Lp.ext
  have hrefl := (Measure.measurePreserving_neg (volume : Measure MNS2.R3)).quasiMeasurePreserving.ae
    (coordinates_ae volume b i)
  filter_upwards [coordinates_ae volume (realSymmetryVec b) i, realSymmetryVec_ae b,
    NSFormalization.Source.RealSobolev.realSymmetry_ae (coordinates 2 volume b i), hrefl]
    with t h1 h2 h3 h4
  rw [h1, h2, h3, h4, conjR3C_apply]

end NSFormalization.Section4.D01.Leray
