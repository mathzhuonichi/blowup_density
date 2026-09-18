import NSFormalization.Section3.T22.RestrictBridge
import NSFormalization.Section3.T22.OrderZeroIsometry
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# T22 · unit U-A5 — the `orderZero` field of `BoundedDomainNormAPI`

This module proves the `orderZero` field of the reconciled `BoundedDomainNormAPI`
(`research/T22/Spec.lean:125-128`, restated verbatim in `Section3/T22/Domain.lean`)
as the theorem

`orderZero : ∀ Ω, IsOpen Ω → ∀ z, ContDiffOn ℝ ∞ z Ω →
    domainSobolevENorm Ω 0 (restrictField Ω z) = eLpNorm z 2 (volume.restrict Ω)`.

Both sides may be `⊤`; no compact-support or `L²` hypothesis is assumed.

## Route (`research/T22/T22_SPLIT.md` unit U-A5)

The quotient norm `domainSobolevENorm Ω 0 (restrictField Ω z)` is the infimum over all
whole-space order-0 Sobolev data `A` whose distributional restriction to `Ω` is
`restrictField Ω z`.  Two inequalities:

* `≤`.  When `eLpNorm z 2 (volume.restrict Ω) < ⊤` the zero extension `E₀z = Ω.indicator z`
  lies in `L²(ℝ³)` (`memLp_indicator_iff_restrict`); its explicit order-0 datum
  `orderZeroDatum` restricts to `restrictField Ω z` (`restrictBridge`, lane 383) and has
  norm `eLpNorm (E₀z) 2 volume = eLpNorm z 2 (volume.restrict Ω)`
  (`norm_orderZeroDatum_eq`, lane 387, and `eLpNorm_indicator_eq_eLpNorm_restrict`).  When the
  right-hand side is `⊤` the inequality is trivial.

* `≥`.  Every order-0 datum `A` is the order-0 datum `orderZeroDatum hw` of some `L²` field
  `w` (`orderZeroDatum_surjective`, the surjectivity supplied here from the L² Fourier
  inversion and the real-subspace ⟺ a.e.-real bridge).  If `A` restricts to `restrictField Ω z`
  then `restrictField Ω w = restrictField Ω z`, so `w =ᵐ z` on `Ω` by the du Bois-Reymond
  lemma (`restrictField_eq_ae`), whence
  `eLpNorm z 2 (volume.restrict Ω) = eLpNorm w 2 (volume.restrict Ω) ≤ eLpNorm w 2 volume = ‖A‖ₑ`.

No `sorry`/`axiom`/`native_decide`; every declaration prints `[propext, Classical.choice,
Quot.sound]`.  The order-0 `cyclesToAngularRealVector` unification is heartbeat-heavy (flagged
in lane 387): `orderZeroDatum_surjective` carries a commented `set_option maxHeartbeats 400000`.
-/

noncomputable section

namespace NSFormalization.Section3.T22

open MeasureTheory FourierTransform NavierStokes.ProblemStatement Set
open NSFormalization.Paper3
open NSFormalization.Source.RealSobolev
open NSFormalization.Section4.D01
open NSFormalization.Section4.A02 (SpatialField)
open scoped ContDiff ENNReal ComplexConjugate SchwartzMap

/-! ## 1. Order-0 realization surjectivity -/

/-- The inverse `L²` Fourier transform of a conjugate-symmetric (`realSubspace 0`) datum is
conjugation-fixed. -/
theorem conjugation_fourierInv_of_mem {h : FourierData} (hh : h ∈ realSubspace (0 : ℝ)) :
    conjugation (𝓕⁻ h) = 𝓕⁻ h := by
  have hfix : realSymmetry h = h := (mem_realSubspace_iff 0 h).mp hh
  have key : 𝓕 (conjugation (𝓕⁻ h)) = 𝓕 (𝓕⁻ h) := by
    rw [fourier_conjugation, fourier_fourierInv_eq, hfix]
  have := congrArg (fun x => (𝓕⁻ x : FourierData)) key
  simpa only [fourierInv_fourier_eq] using this

/-- Hence its values are a.e. real: the `ℂ`-cast of the real part agrees with the function. -/
theorem fourierInv_ofReal_re_ae {h : FourierData} (hh : h ∈ realSubspace (0 : ℝ)) :
    (fun x => (((((𝓕⁻ h : FourierData)) : Space → ℂ) x).re : ℂ)) =ᵐ[volume]
      (((𝓕⁻ h : FourierData)) : Space → ℂ) := by
  have hconj : conjugation (𝓕⁻ h) = 𝓕⁻ h := conjugation_fourierInv_of_mem hh
  have hae := conjugation_ae (𝓕⁻ h)
  rw [hconj] at hae
  filter_upwards [hae] with x hx
  exact (Complex.conj_eq_iff_re.mp hx.symm)

/-- Assemble three complex `L²` classes into a real Euclidean three-vector field by real parts. -/
def fieldOf (g : Fin 3 → FourierData) : Space → Space :=
  fun x => WithLp.toLp 2 (fun i => (((g i : Space → ℂ)) x).re)

@[simp] theorem fieldOf_apply (g : Fin 3 → FourierData) (x : Space) (i : Fin 3) :
    fieldOf g x i = (((g i : Space → ℂ)) x).re := rfl

theorem memLp_fieldOf (g : Fin 3 → FourierData) : MemLp (fieldOf g) 2 volume := by
  rw [memLp_piLp_iff]
  intro i
  exact Complex.reCLM.comp_memLp' (Lp.memLp (g i))

set_option maxHeartbeats 400000 in
/-- **Order-0 realization is surjective.**  Every `A : RealVectorSobolev 0` is the explicit
order-0 datum `orderZeroDatum hw` of a square-integrable field `w`.  This is the converse of the
field → datum direction `exists_isSobolevDatum_zero_of_memLp`, and the missing ingredient
(beyond the invertible angular transport and `L²` Fourier equivalence already in the tree) is the
real-subspace ⟺ a.e.-real bridge `conjugation_fourierInv_of_mem`. -/
theorem orderZeroDatum_surjective (A : RealVectorSobolev (0 : ℝ)) :
    ∃ (w : Space → Space) (hw : MemLp w 2 volume), orderZeroDatum hw = A := by
  set v : RealVectorSobolev (0 : ℝ) := (cyclesToAngularRealVector 0).symm A with hv
  set g : Fin 3 → FourierData := fun i => 𝓕⁻ ((v i : FourierData)) with hg
  have hmem : ∀ i, ((v i : FourierData)) ∈ realSubspace (0 : ℝ) := fun i => (v i).2
  refine ⟨fieldOf g, memLp_fieldOf g, ?_⟩
  have hcomp : ∀ i, componentLp (memLp_fieldOf g) i = g i := by
    intro i
    apply Lp.ext
    have h1 := componentLp_ae (memLp_fieldOf g) i
    have h2 := fourierInv_ofReal_re_ae (hmem i)
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hx1]
    simp only [fieldOf_apply]
    exact hx2
  have hfour : ∀ i, 𝓕 (componentLp (memLp_fieldOf g) i) = ((v i : FourierData)) := by
    intro i
    rw [hcomp i, hg, fourier_fourierInv_eq]
  have hproj : ∀ i, realProjectionTo 0 (𝓕 (componentLp (memLp_fieldOf g) i)) = v i := by
    intro i
    rw [hfour i]
    exact realProjectionTo_inclusion 0 (v i)
  have hveq : WithLp.toLp 2 (fun i => realProjectionTo 0 (𝓕 (componentLp (memLp_fieldOf g) i))) = v := by
    rw [show (fun i => realProjectionTo 0 (𝓕 (componentLp (memLp_fieldOf g) i))) = (fun i => v i)
        from funext hproj]
  have hkey : WithLp.toLp 2 (fun i => realProjectionTo 0 (𝓕 (componentLp (memLp_fieldOf g) i)))
      = (cyclesToAngularRealVector 0).symm A := hveq.trans hv
  show cyclesToAngularRealVector 0
      (WithLp.toLp 2 (fun i => realProjectionTo 0 (𝓕 (componentLp (memLp_fieldOf g) i)))) = A
  simp only [hkey, ContinuousLinearEquiv.apply_symm_apply]

/-! ## 2. The du Bois-Reymond bridge -/

/-- Two fields whose restricted physical functionals agree on all compactly supported interior
tests are a.e. equal on the domain.  `w` is `L²` on `ℝ³`, `z` is smooth on `Ω`. -/
theorem restrictField_eq_ae {Ω : Set Space} (hΩ : IsOpen Ω) {w z : SpatialField}
    (hw : MemLp w 2 volume) (hz : ContDiffOn ℝ ∞ z Ω)
    (heq : restrictField Ω w = restrictField Ω z) :
    w =ᵐ[volume.restrict Ω] z := by
  have hmΩ : MeasurableSet Ω := hΩ.measurableSet
  have hcomp : ∀ i : Fin 3, ∀ᵐ x ∂volume, x ∈ Ω → (w x i - z x i) = 0 := by
    intro i
    have hwi : MemLp (fun x => w x i) 2 volume := (memLp_piLp_iff (p := 2) (μ := volume)).mp hw i
    have hzci : ContinuousOn (fun x => z x i) Ω := by
      have hc : Continuous (fun v : Space => v i) := by fun_prop
      exact hc.comp_continuousOn hz.continuousOn
    have hli : LocallyIntegrableOn (fun x => w x i - z x i) Ω volume :=
      ((hwi.locallyIntegrable one_le_two).locallyIntegrableOn Ω).sub (hzci.locallyIntegrableOn hmΩ)
    refine hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hli ?_
    intro g hg hgc hgsub
    have hgC : ContDiff ℝ ∞ (fun x => ((g x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
    have hgcC : HasCompactSupport (fun x => ((g x : ℝ) : ℂ)) := by
      apply hgc.comp_left (g := fun r : ℝ => (r : ℂ)); simp
    have htsupp_eq : tsupport (fun x => ((g x : ℝ) : ℂ)) = tsupport g := by
      unfold tsupport
      congr 1
      ext x; simp [Function.mem_support, Complex.ofReal_eq_zero]
    set ψ : SchwartzMap Space ℂ := hgcC.toSchwartzMap hgC with hψ
    have hψval : ∀ x, (ψ : Space → ℂ) x = ((g x : ℝ) : ℂ) := fun x => rfl
    have hψc : HasCompactSupport (ψ : Space → ℂ) := hgcC
    have hψsub : tsupport (ψ : Space → ℂ) ⊆ Ω := by
      rw [show tsupport (ψ : Space → ℂ) = tsupport g from htsupp_eq]; exact hgsub
    have happ := congrFun (congrFun heq i) ⟨ψ, hψc, hψsub⟩
    simp only [restrictField, hψval] at happ
    have hwΩ : ∫ x in Ω, g x * (w x i) ∂volume = ∫ x in Ω, g x * (z x i) ∂volume := by
      have h := happ
      simp only [← Complex.ofReal_mul] at h
      exact_mod_cast h
    have hg2 : MemLp g 2 volume := hg.continuous.memLp_of_hasCompactSupport hgc
    have hgwi : Integrable (fun x => g x * (w x i)) volume :=
      memLp_one_iff_integrable.mp (hwi.mul' hg2)
    have hgzi : Integrable (fun x => g x * (z x i)) volume := by
      have hcz : ContinuousOn (fun x => g x * z x i) (tsupport g) :=
        (hg.continuous.continuousOn).mul (hzci.mono hgsub)
      have hint : IntegrableOn (fun x => g x * z x i) (tsupport g) volume :=
        hcz.integrableOn_compact hgc
      refine hint.integrable_of_forall_notMem_eq_zero ?_
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
    have hoffw : ∀ x, x ∉ Ω → g x * (w x i) = 0 := fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hgsub h)), zero_mul]
    have hoffz : ∀ x, x ∉ Ω → g x * (z x i) = 0 := fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hgsub h)), zero_mul]
    calc ∫ x, g x • (w x i - z x i) ∂volume
        = ∫ x, (g x * (w x i) - g x * (z x i)) ∂volume := by
          apply integral_congr_ae; filter_upwards [] with x; simp only [smul_eq_mul]; ring
      _ = (∫ x, g x * (w x i) ∂volume) - (∫ x, g x * (z x i) ∂volume) := integral_sub hgwi hgzi
      _ = (∫ x in Ω, g x * (w x i) ∂volume) - (∫ x in Ω, g x * (z x i) ∂volume) := by
          rw [setIntegral_eq_integral_of_forall_compl_eq_zero hoffw,
            setIntegral_eq_integral_of_forall_compl_eq_zero hoffz]
      _ = 0 := by rw [hwΩ]; ring
  have hall : ∀ᵐ x ∂volume, ∀ i : Fin 3, x ∈ Ω → (w x i - z x i) = 0 := (ae_all_iff).mpr hcomp
  have hfield : ∀ᵐ x ∂volume, x ∈ Ω → w x = z x := by
    filter_upwards [hall] with x hx hmem
    have hcoord : ∀ i, w x i = z x i := fun i => sub_eq_zero.mp (hx i hmem)
    exact WithLp.ofLp_injective (p := 2) (funext hcoord)
  exact (ae_restrict_iff' hmΩ).mpr hfield

/-! ## 3. The general datum-restriction bridge and the order-0 field norm identity -/

/-- Any whole-space order-`s` datum of `z` restricts, on compactly supported interior tests, to
the physical domain functional of `z`.  (The zero-extension special case is lane 383's
`restrictDatum_eq_restrictField`.) -/
theorem restrictDatum_eq_restrictField_of_datum {Ω : Set Space} {s : ℝ}
    {z : SpatialField} {A : RealVectorSobolev s} (hA : IsSobolevDatum s z A) :
    restrictDatum Ω s A = restrictField Ω z := by
  funext i ψ
  rw [restrictDatum, hA i ψ.1, restrictField]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)).symm
  rw [image_eq_zero_of_notMem_tsupport (fun h => hx (ψ.2.2 h)), zero_mul]

/-- At order `0` a square-integrable field's quotient Sobolev norm is its `L²` norm. -/
theorem sobolevENorm_zero_eq_eLpNorm {w : SpatialField} (hw : MemLp w 2 volume) :
    sobolevENorm 0 w = eLpNorm w 2 volume := by
  have hle := sobolevENorm_le_of_isSobolevDatum (isSobolevDatum_orderZeroDatum hw)
  have hge : ‖orderZeroDatum hw‖ₑ ≤ sobolevENorm 0 w := by
    refine le_iInf ?_
    rintro ⟨B, hB⟩
    rw [isSobolevDatum_unique (isSobolevDatum_orderZeroDatum hw) hB]
  rw [le_antisymm hle hge, norm_orderZeroDatum_eq hw]

/-! ## 4. The `orderZero` field, verbatim -/

/-- **U-A5 — the `orderZero` field of `BoundedDomainNormAPI`.**  At order zero the bounded-domain
restriction quotient norm is the `L²(Ω)` norm of the restricted field; either side may be `⊤`. -/
theorem orderZero (Ω : Set Space) (hΩ : IsOpen Ω) (z : SpatialField)
    (hz : ContDiffOn ℝ ∞ z Ω) :
    domainSobolevENorm Ω 0 (restrictField Ω z) = eLpNorm z 2 (volume.restrict Ω) := by
  refine le_antisymm ?_ ?_
  · -- `≤`
    rcases eq_or_ne (eLpNorm z 2 (volume.restrict Ω)) ⊤ with htop | hfin
    · rw [htop]; exact le_top
    · have hmΩ : MeasurableSet Ω := hΩ.measurableSet
      have haem : AEStronglyMeasurable z (volume.restrict Ω) :=
        hz.continuousOn.aestronglyMeasurable hmΩ
      have hzL2 : MemLp z 2 (volume.restrict Ω) := ⟨haem, lt_of_le_of_ne le_top hfin⟩
      have hE : MemLp (zeroExtension Ω z) 2 volume :=
        (memLp_indicator_iff_restrict hmΩ).mpr hzL2
      calc domainSobolevENorm Ω 0 (restrictField Ω z)
          ≤ sobolevENorm 0 (zeroExtension Ω z) := domainSobolevENorm_le_sobolevENorm
        _ = eLpNorm (zeroExtension Ω z) 2 volume := sobolevENorm_zero_eq_eLpNorm hE
        _ = eLpNorm z 2 (volume.restrict Ω) := eLpNorm_indicator_eq_eLpNorm_restrict hmΩ
  · -- `≥`
    refine le_iInf ?_
    rintro ⟨A, hA_restr⟩
    obtain ⟨w, hw, hAeq⟩ := orderZeroDatum_surjective A
    have hdatum : IsSobolevDatum 0 w A := hAeq ▸ isSobolevDatum_orderZeroDatum hw
    have hnorm : ‖A‖ₑ = eLpNorm w 2 volume := hAeq ▸ norm_orderZeroDatum_eq hw
    have hbridge : restrictField Ω w = restrictField Ω z :=
      (restrictDatum_eq_restrictField_of_datum hdatum).symm.trans hA_restr
    have haew : w =ᵐ[volume.restrict Ω] z := restrictField_eq_ae hΩ hw hz hbridge
    calc eLpNorm z 2 (volume.restrict Ω)
        = eLpNorm w 2 (volume.restrict Ω) := (eLpNorm_congr_ae haew).symm
      _ ≤ eLpNorm w 2 volume := eLpNorm_mono_measure _ Measure.restrict_le_self
      _ = ‖A‖ₑ := hnorm.symm

end NSFormalization.Section3.T22
