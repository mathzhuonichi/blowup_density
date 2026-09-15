import NSFormalization.Section4.D01.LerayMultiplier
import NSFormalization.Paper3.RealVectorPositiveDensity

/-!
# The Leray-complement multiplier on the manuscript's datum carrier (D01 · P2 · SL3 final step)

`research/D01/P2_SPLIT.md` sub-lemma **SL3** (and **SL2**), final step: repackage lane 073's
raw-carrier operator-valued `L²` Leray-complement multiplier
`Section4/D01/LerayMultiplier.lean`'s `lerayComplementL2 : R3L2Velocity →L[ℝ] R3L2Velocity`
onto the manuscript's datum carrier
`RealVectorSobolev s = Product (Fin 3) (RealSobolevHilbert s)` — a `PiLp 2` *of* the reality
subspace of the scalar Fourier `L²`, as opposed to the `Lp` *of* a `PiLp 2` on which the raw
multiplier acts.

The bridge is `Source.FiniteHilbertBochner.coordinates`/`assemble`, whose `q = 2` isometry
(`coordinates_norm`, `assemble_norm`, `coordinates_assemble` in `LerayMultiplier.lean`) is what
carries the operator norm `≤ 1` across.

Contents:

* `lerayComplementAmbient` (**item 1**): the multiplier on the ambient product
  `Product (Fin 3) (Lp ℂ 2 volume)`, bundled as a `→L[ℝ]` with `‖·‖ ≤ 1`
  (`= coordinates ∘ lerayComplementL2 ∘ assemble`, all three isometric-or-contractive pieces).
* `realSymmetryVec_assemble` (**item 2**, the intertwiner) and
  `image_component_mem_realSubspace` (**item 2**, reality preservation): the multiplier maps
  data whose components lie in `Source.RealSobolev.realSubspace s` to data with the same property.
* `lerayComplement` (**item 3**): the datum-carrier operator
  `RealVectorSobolev s →L[ℝ] RealVectorSobolev s`, defined componentwise via
  `LinearMap.mkContinuous`; `lerayComplement_toAmbient` identifies it with the restriction of
  `lerayComplementAmbient`.
* `lerayComplement_opNorm_le_one`, `lerayComplement_idempotent`, `lerayComplement_ae`,
  `lerayComplement_eq_zero_of_transverse` (**item 4**).

The order `s` is a phantom (`realSubspace` discards it, `LerayMultiplier`/lane 051), so one
operator serves every order; the datum interface is nevertheless indexed by `s`.

No `sorry`, no `axiom`; `#print axioms` is standard (`research/D01/axioms_leray_datum.lean`).
-/

noncomputable section

namespace NSFormalization.Section4.D01.Leray

open MeasureTheory
open scoped ComplexConjugate
open NSFormalization.Source.FiniteHilbertBochner (assemble coordinates coord Product insert_apply)
open NSFormalization.Source.RealSobolev (realSymmetry realSubspace RealSobolevHilbert FourierData
  mem_realSubspace_iff realSymmetry_ae)
open NSFormalization.Paper3 (RealVectorSobolev)

/-- Local unambiguous alias for `FiniteHilbertBochner.insert` (clashes with `Insert.insert`),
scalar pinned to `ℂ` at use sites.  Proof helper only. -/
private noncomputable abbrev ins := @NSFormalization.Source.FiniteHilbertBochner.insert

/-! ## 1. Two `assemble`/conjugation helpers -/

/-- The coeFn of `assemble` is a.e. the finite sum of coordinate insertions. -/
private theorem assemble_ae {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*}
    [MeasurableSpace α] (μ : Measure α) (h : ι → Lp ℂ 2 μ) :
    (assemble 2 μ h : α → PiLp 2 (fun _ : ι => ℂ)) =ᵐ[μ] fun t => ∑ i, ins (H := ℂ) i (h i t) := by
  have hco : ∀ᵐ t ∂μ, ∀ i : ι,
      ((ins (H := ℂ) i).compLpL 2 μ (h i)) t = ins i (h i t) := by
    rw [ae_all_iff]; intro i
    filter_upwards [ContinuousLinearMap.coeFn_compLpL (ins (H := ℂ) i) (h i)] with t ht
    exact ht
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun i => (ins (H := ℂ) i).compLpL 2 μ (h i)), hco] with t ht hco
  change (∑ i, (ins (H := ℂ) i).compLpL 2 μ (h i)) t = _
  rw [ht]; simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => hco i)

/-- Coordinatewise conjugation sends a single coordinate insertion to the insertion of the
conjugate. -/
private theorem conjR3C_single (i : Fin 3) (z : ℂ) :
    conjR3C (ins (H := ℂ) i z) = ins (H := ℂ) i (conj z) := by
  rw [conjR3C_apply, insert_apply, insert_apply]
  ext j; by_cases hj : j = i <;> simp [PiLp.single_apply, hj]

/-! ## 2. The reality intertwiner (SL2) -/

/-- **The reality intertwiner.**  The vector conjugate-reflection involution commutes with
`assemble`, distributing over the componentwise scalar `Source.RealSobolev.realSymmetry`.  This is
the `assemble`-side companion of `coordinates_realSymmetryVec` (`LerayMultiplier.lean`). -/
theorem realSymmetryVec_assemble (h : Fin 3 → Lp ℂ 2 (volume : Measure MNS2.R3)) :
    realSymmetryVec (assemble 2 volume h) = assemble 2 volume (fun i => realSymmetry (h i)) := by
  apply Lp.ext
  have hLraw := (Measure.measurePreserving_neg
      (volume : Measure MNS2.R3)).quasiMeasurePreserving.ae (assemble_ae (volume) h)
  have hcomp : ∀ᵐ t ∂(volume : Measure MNS2.R3), ∀ i : Fin 3,
      (realSymmetry (h i) : MNS2.R3 → ℂ) t = conj (h i (-t)) := by
    rw [ae_all_iff]; intro i; exact realSymmetry_ae (h i)
  filter_upwards [realSymmetryVec_ae (assemble 2 volume h),
    hLraw, assemble_ae (volume) (fun i => realSymmetry (h i)), hcomp] with t hL hLraw hR hcomp
  rw [hL, hLraw, hR, map_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [conjR3C_single, hcomp i])

/-- **Reality preservation (SL2, ambient form).**  If every scalar component `g i` lies in the
reality subspace, so does every component of the multiplier's image.  This is the reality
statement behind the codomain restriction of `lerayComplement`. -/
theorem image_component_mem_realSubspace (s : ℝ) (g : Fin 3 → FourierData)
    (hg : ∀ i, g i ∈ realSubspace s) (i : Fin 3) :
    coordinates 2 volume (lerayComplementL2 (assemble 2 volume g)) i ∈ realSubspace s := by
  set b := assemble 2 volume g with hb
  have hbreal : realSymmetryVec b = b := by
    rw [hb, realSymmetryVec_assemble]
    congr 1
    funext j
    exact (mem_realSubspace_iff s _).mp (hg j)
  have hLb : realSymmetryVec (lerayComplementL2 b) = lerayComplementL2 b :=
    realSymmetryVec_lerayComplementL2_eq_self b hbreal
  have hco := coordinates_realSymmetryVec (lerayComplementL2 b) i
  rw [hLb] at hco
  exact (mem_realSubspace_iff s _).mpr hco.symm

/-! ## 3. The ambient multiplier (item 1) -/

/-- The Leray-complement multiplier on the ambient product carrier, as a real-linear map. -/
private noncomputable def lerayComplementAmbientLM :
    Product (Fin 3) (Lp ℂ 2 (volume : Measure MNS2.R3)) →ₗ[ℝ]
      Product (Fin 3) (Lp ℂ 2 (volume : Measure MNS2.R3)) where
  toFun h := WithLp.toLp 2 (coordinates 2 volume
    (lerayComplementL2 (assemble 2 volume (WithLp.ofLp h))))
  map_add' h h' := by
    have hc : coordinates 2 volume (lerayComplementL2 (assemble 2 volume (WithLp.ofLp (h + h'))))
        = coordinates 2 volume (lerayComplementL2 (assemble 2 volume (WithLp.ofLp h)))
          + coordinates 2 volume (lerayComplementL2 (assemble 2 volume (WithLp.ofLp h'))) := by
      funext i
      rw [WithLp.ofLp_add,
        show assemble 2 volume (WithLp.ofLp h + WithLp.ofLp h')
          = assemble 2 volume (WithLp.ofLp h) + assemble 2 volume (WithLp.ofLp h') by
            simp only [assemble, Pi.add_apply, map_add, Finset.sum_add_distrib], map_add]
      simp only [coordinates, map_add, Pi.add_apply]
    rw [hc, WithLp.toLp_add]
  map_smul' c h := by
    have hc : coordinates 2 volume (lerayComplementL2 (assemble 2 volume (WithLp.ofLp (c • h))))
        = c • coordinates 2 volume (lerayComplementL2 (assemble 2 volume (WithLp.ofLp h))) := by
      funext i
      rw [WithLp.ofLp_smul,
        show assemble 2 volume (c • WithLp.ofLp h) = c • assemble 2 volume (WithLp.ofLp h) by
          simp only [assemble, Pi.smul_apply, map_smul, Finset.smul_sum], map_smul]
      simp only [coordinates, map_smul, Pi.smul_apply]
    rw [hc, WithLp.toLp_smul]; rfl

/-- Contraction of the raw multiplier (`opNorm ≤ 1` unfolded to a pointwise bound). -/
theorem lerayComplementL2_norm_le (b : MNS2.R3L2Velocity) : ‖lerayComplementL2 b‖ ≤ ‖b‖ := by
  rw [lerayComplementL2_apply]; exact norm_lerayComplementFun_le b

/-- **The Leray-complement multiplier on the ambient product carrier** (item 1):
`coordinates ∘ lerayComplementL2 ∘ assemble` on `Product (Fin 3) (Lp ℂ 2 volume)`, bundled as a
continuous real-linear map with operator norm `≤ 1` (the two carrier bridges are `q = 2`
isometries, the middle factor a contraction). -/
noncomputable def lerayComplementAmbient :
    Product (Fin 3) (Lp ℂ 2 (volume : Measure MNS2.R3)) →L[ℝ]
      Product (Fin 3) (Lp ℂ 2 (volume : Measure MNS2.R3)) :=
  lerayComplementAmbientLM.mkContinuous 1 (fun h => by
    rw [one_mul]
    show ‖WithLp.toLp 2 (coordinates 2 volume
      (lerayComplementL2 (assemble 2 volume (WithLp.ofLp h))))‖ ≤ ‖h‖
    rw [coordinates_norm]
    refine (lerayComplementL2_norm_le _).trans ?_
    rw [assemble_norm, WithLp.toLp_ofLp])

theorem lerayComplementAmbient_apply
    (h : Product (Fin 3) (Lp ℂ 2 (volume : Measure MNS2.R3))) :
    lerayComplementAmbient h = WithLp.toLp 2 (coordinates 2 volume
      (lerayComplementL2 (assemble 2 volume (WithLp.ofLp h)))) := rfl

/-- **Operator norm `≤ 1`** (item 1). -/
theorem lerayComplementAmbient_opNorm_le_one : ‖lerayComplementAmbient‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-! ## 4. The datum-carrier multiplier (item 3) -/

/-- The datum-carrier image as a raw function: read off the ambient components and repackage each
into the reality subspace (`image_component_mem_realSubspace`). -/
private noncomputable def lcFunVec (s : ℝ) (h : RealVectorSobolev s) : RealVectorSobolev s :=
  WithLp.toLp 2 (fun i =>
    (⟨coordinates 2 volume (lerayComplementL2 (assemble 2 volume (fun j => ((h j : FourierData))))) i,
      image_component_mem_realSubspace s (fun j => ((h j : FourierData))) (fun j => (h j).2) i⟩
      : RealSobolevHilbert s))

private theorem lcFunVec_coe (s : ℝ) (h : RealVectorSobolev s) (i : Fin 3) :
    (((lcFunVec s h) i) : FourierData) =
      coordinates 2 volume
        (lerayComplementL2 (assemble 2 volume (fun j => ((h j : FourierData))))) i :=
  rfl

private theorem lcFunVec_add (s : ℝ) (h h' : RealVectorSobolev s) :
    lcFunVec s (h + h') = lcFunVec s h + lcFunVec s h' := by
  apply PiLp.ext; intro i; apply Subtype.ext
  rw [lcFunVec_coe]
  have hin : (fun j => (((h + h') j) : FourierData))
      = (fun j => ((h j : FourierData))) + (fun j => ((h' j : FourierData))) := by
    funext j; rfl
  rw [hin,
    show assemble 2 volume ((fun j => ((h j : FourierData))) + (fun j => ((h' j : FourierData))))
      = assemble 2 volume (fun j => ((h j : FourierData)))
        + assemble 2 volume (fun j => ((h' j : FourierData))) by
      simp only [assemble, Pi.add_apply, map_add, Finset.sum_add_distrib], map_add]
  simp only [coordinates, map_add]
  rfl

private theorem lcFunVec_smul (s : ℝ) (c : ℝ) (h : RealVectorSobolev s) :
    lcFunVec s (c • h) = c • lcFunVec s h := by
  apply PiLp.ext; intro i; apply Subtype.ext
  rw [lcFunVec_coe]
  have hin : (fun j => (((c • h) j) : FourierData)) = c • (fun j => ((h j : FourierData))) := by
    funext j; rfl
  rw [hin,
    show assemble 2 volume (c • (fun j => ((h j : FourierData))))
      = c • assemble 2 volume (fun j => ((h j : FourierData))) by
      simp only [assemble, Pi.smul_apply, map_smul, Finset.smul_sum], map_smul]
  simp only [coordinates, map_smul]
  rfl

/-- The datum-carrier norm equals the ambient norm of the coerced component tuple. -/
private theorem datumNorm_eq (s : ℝ) (g : Fin 3 → RealSobolevHilbert s) :
    ‖(WithLp.toLp 2 g : RealVectorSobolev s)‖ =
      ‖(WithLp.toLp 2 (fun i => ((g i : FourierData)))
        : Product (Fin 3) (Lp ℂ 2 (volume : Measure MNS2.R3)))‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  congr 1

private theorem lcFunVec_norm_le (s : ℝ) (h : RealVectorSobolev s) : ‖lcFunVec s h‖ ≤ ‖h‖ := by
  have key : ‖lcFunVec s h‖
      = ‖lerayComplementL2 (assemble 2 volume (fun j => ((h j : FourierData))))‖ := by
    have e1 : ‖lcFunVec s h‖
        = ‖(WithLp.toLp 2 (fun i => (((lcFunVec s h) i) : FourierData))
            : Product (Fin 3) (Lp ℂ 2 (volume : Measure MNS2.R3)))‖ := by
      conv_lhs => rw [show lcFunVec s h = WithLp.toLp 2 (fun i => (lcFunVec s h) i) from rfl]
      rw [datumNorm_eq]
    rw [e1]
    have e2 : (fun i => (((lcFunVec s h) i) : FourierData))
        = coordinates 2 volume
            (lerayComplementL2 (assemble 2 volume (fun j => ((h j : FourierData))))) := by
      funext i; rw [lcFunVec_coe]
    rw [e2, coordinates_norm]
  rw [key]
  refine (lerayComplementL2_norm_le _).trans ?_
  rw [assemble_norm]
  have hnorm := datumNorm_eq s (fun j => h j)
  rw [show (WithLp.toLp 2 (fun j => h j) : RealVectorSobolev s) = h from rfl] at hnorm
  rw [← hnorm]

private noncomputable def lerayComplementLM (s : ℝ) :
    RealVectorSobolev s →ₗ[ℝ] RealVectorSobolev s where
  toFun := lcFunVec s
  map_add' := lcFunVec_add s
  map_smul' c h := lcFunVec_smul s c h

/-- **The Leray-complement multiplier on the manuscript datum carrier** (item 3):
`RealVectorSobolev s →L[ℝ] RealVectorSobolev s`, defined componentwise (route recorded in
`research/D01/ATTEMPTS_LERAY_DATUM.md`).  It is the restriction of `lerayComplementAmbient`
(`lerayComplement_toAmbient`). -/
noncomputable def lerayComplement (s : ℝ) : RealVectorSobolev s →L[ℝ] RealVectorSobolev s :=
  (lerayComplementLM s).mkContinuous 1 (fun h => by rw [one_mul]; exact lcFunVec_norm_le s h)

/-- The `i`-th component of `lerayComplement s h`, coerced back to the ambient scalar `L²`, is the
`i`-th ambient coordinate of the raw multiplier applied to the assembled input. -/
theorem lerayComplement_coe (s : ℝ) (h : RealVectorSobolev s) (i : Fin 3) :
    (((lerayComplement s h) i) : FourierData) =
      coordinates 2 volume
        (lerayComplementL2 (assemble 2 volume (fun j => ((h j : FourierData))))) i :=
  rfl

/-- **`lerayComplement s` is the restriction of `lerayComplementAmbient`.**  Its image, read into
the ambient product, equals `lerayComplementAmbient` of the ambient inclusion of the input. -/
theorem lerayComplement_toAmbient (s : ℝ) (h : RealVectorSobolev s) :
    (WithLp.toLp 2 (fun i => (((lerayComplement s h) i) : FourierData))
      : Product (Fin 3) (Lp ℂ 2 (volume : Measure MNS2.R3)))
      = lerayComplementAmbient
          (WithLp.toLp 2 (fun i => ((h i : FourierData)))) := by
  rw [lerayComplementAmbient_apply]
  congr 1

/-- **Operator norm `≤ 1`** (item 4). -/
theorem lerayComplement_opNorm_le_one (s : ℝ) : ‖lerayComplement s‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- **Idempotence** (item 4): `(I−P)² = (I−P)` on the datum carrier. -/
theorem lerayComplement_idempotent (s : ℝ) (h : RealVectorSobolev s) :
    lerayComplement s (lerayComplement s h) = lerayComplement s h := by
  apply PiLp.ext; intro i; apply Subtype.ext
  rw [lerayComplement_coe, lerayComplement_coe]
  set b0 := assemble 2 volume (fun k => ((h k : FourierData))) with hb0
  have hfun : (fun j => (((lerayComplement s h) j) : FourierData))
      = coordinates 2 volume (lerayComplementL2 b0) := by
    funext j; rw [lerayComplement_coe]
  rw [hfun, NSFormalization.Source.FiniteHilbertBochner.assemble_coordinates,
    lerayComplementL2_idempotent]

/-- **The a.e. action** (item 4): componentwise, `(I−P)` acts a.e. by the complex complement fibre
symbol applied to the assembled Fourier data.  (The shape falls out of `lerayComplementL2_ae` and
`coordinates_ae` through the carrier bridge.) -/
theorem lerayComplement_ae (s : ℝ) (h : RealVectorSobolev s) (i : Fin 3) :
    (((lerayComplement s h) i) : FourierData) =ᵐ[volume]
      fun ξ => (complementSymbolComplex ξ
        ((assemble 2 volume (fun j => ((h j : FourierData)))) ξ)) i := by
  rw [lerayComplement_coe]
  filter_upwards [coordinates_ae volume
      (lerayComplementL2 (assemble 2 volume (fun j => ((h j : FourierData))))) i,
    lerayComplementL2_ae (assemble 2 volume (fun j => ((h j : FourierData))))] with t ht h2
  rw [ht, h2]

/-- The complex inner product against the embedded frequency vector, as the longitudinal
combination `∑ⱼ ξⱼ · vⱼ` (matching lane 079's transverse shape). -/
theorem inner_r3FreqVec (ξ : MNS2.R3) (v : MNS2.R3C) :
    inner ℂ (MNS2.r3FrequencyVectorComplex ξ) v = ∑ j, ((ξ j : ℝ) : ℂ) * v j := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hfr : (MNS2.r3FrequencyVectorComplex ξ) j = ((ξ j : ℝ) : ℂ) := rfl
  rw [RCLike.inner_apply, hfr, Complex.conj_ofReal, mul_comm]

/-- **`(I−P)` kills a transverse (solenoidal) datum** (item 4).  If the components are a.e.
transverse in the lane-079 shape `∑ⱼ ξⱼ · Âⱼ(ξ) = 0`, the datum-carrier multiplier is zero. -/
theorem lerayComplement_eq_zero_of_transverse (s : ℝ) (h : RealVectorSobolev s)
    (htr : ∀ᵐ ξ ∂(volume : Measure MNS2.R3),
      ∑ j : Fin 3, ((ξ j : ℝ) : ℂ) * (((h j : FourierData)) ξ) = 0) :
    lerayComplement s h = 0 := by
  set b := assemble 2 volume (fun j => ((h j : FourierData))) with hb
  have hb0 : lerayComplementL2 b = 0 := by
    apply lerayComplementL2_eq_zero_of_transverse
    have hall : ∀ᵐ ξ ∂(volume : Measure MNS2.R3), ∀ j : Fin 3,
        (((h j : FourierData)) : MNS2.R3 → ℂ) ξ = (b ξ) j := by
      rw [ae_all_iff]; intro j
      rw [hb, ← coordinates_assemble volume (fun j => ((h j : FourierData))) j]
      exact coordinates_ae volume b j
    filter_upwards [htr, hall] with ξ hξ hall
    rw [inner_r3FreqVec]
    calc ∑ j, ((ξ j : ℝ) : ℂ) * (b ξ) j
        = ∑ j : Fin 3, ((ξ j : ℝ) : ℂ) * (((h j : FourierData)) ξ) :=
          Finset.sum_congr rfl (fun j _ => by rw [hall j])
      _ = 0 := hξ
  apply PiLp.ext; intro i; apply Subtype.ext
  rw [lerayComplement_coe, hb0]
  simp only [coordinates, map_zero]
  rfl

end NSFormalization.Section4.D01.Leray
