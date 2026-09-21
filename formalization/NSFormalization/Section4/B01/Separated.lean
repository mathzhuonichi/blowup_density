import NSFormalization.Section4.D01.ForceClass

/-!
# B01 unit 6: assembling a finite separated sum as an element of `F_c`

This module discharges the `B01` obligation `separatedAssembly` of `research/B01/Spec.lean:292`
(unit 6 of `research/B01/COMPARISON.md:150`), the field of `BochnerApproxAPI` that turns a pair
(smooth compact time factors `φ j`, smooth compact spatial profiles `h j` with data `A j`) into a
single member of `F_c` together with its order-`s` Sobolev datum path.  It is the Lean form of
`paper/sections/04-whole-space.tex:260`, "the finite sum `Σ_j φ_j(t) h_j(x)` … is jointly smooth
with compact support strictly inside `R³ × (0,∞)`".

The three conjuncts:

* `MemForceCompact (separatedField φ h)` — joint smoothness (`ContDiff.sum` of the products),
  compact support (finite union of the single-product supports of `PBD:54`
  `separated_physical_hasCompactSupport`, generalized to a vector spatial profile), and
  `tsupport ⊆ Ioi 0 ×ˢ univ` (the `PPD:47-53` single-product `tsupport` pattern summed);
* `IsSobolevPath s (separatedField φ h) (separatedPath φ A)` — additivity of
  `Data.IsSobolevDatum` over the finite sum, obtained directly from `map_sum`/`map_smul` of the
  ℂ-linear `Paper3.angularRealization` and `MeasureTheory.integral_finsetSum` (the integrand of
  each product is integrable because `h j` is continuous with compact support);
* `AEStronglyMeasurable (separatedPath φ A) forceTimeMeasure` — the datum path is continuous.

## Restated `Contracts.V1.Data` predicates

`formalization/` is an upstream Lake package of `verification/` and cannot import `Contracts.*`.
`IsSobolevPath`, `IsSobolevDatum`, `MemForceCompact` and `forceTimeMeasure` are reused from
`Section4/D01/{ForceClass,SmoothDatum}.lean`, which restate them token-for-token from
`Contracts/V1/Data.lean:174,160,559,118`.  `separatedField` and `separatedPath` are restated
verbatim from `research/B01/Spec.lean:140,147`, with the `SpatialField := Space → Space`
(`Data.lean:99`) abbreviation and the `VelocityField` spacetime type
(`= Contracts.V1.Data.SpaceTimeField`, `Data.lean:104`, the spelling `D01/ForceClass.lean`
uses); the conformance file `research/B01/axioms_u68.lean` discharges the spec field through the
resulting definitional equalities.
-/

noncomputable section

namespace NSFormalization.Section4.B01

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source.RealSobolev
open NSFormalization.Source.FiniteHilbertBochner
open NSFormalization.Section4.D01
open scoped ContDiff ENNReal SchwartzMap

/-! ## 0. The separated objects (`research/B01/Spec.lean:140,147`) -/

/-- `Contracts.V1.Data.SpatialField` (`Data.lean:99`), restated. -/
abbrev SpatialField := Space → Space

/-- `research/B01/Spec.lean:140`, restated: the physical spacetime field assembled from smooth
compactly supported time factors `φ` and spatial profiles `h`.  The value type is `VelocityField`
(`= Contracts.V1.Data.SpaceTimeField`, `Data.lean:104`), the spelling `D01/ForceClass.lean`
uses for `IsSobolevPath`/`MemForceCompact`. -/
def separatedField {J : ℕ} (φ : Fin J → ℝ → ℝ) (h : Fin J → SpatialField) :
    VelocityField :=
  fun z => ∑ j, φ j z.1 • h j z.2

/-- `research/B01/Spec.lean:147`, restated: the order-`s` datum path of `separatedField φ h`. -/
def separatedPath {J : ℕ} {s : ℝ} (φ : Fin J → ℝ → ℝ)
    (A : Fin J → RealVectorSobolev s) : ℝ → RealVectorSobolev s :=
  fun t => ∑ j, φ j t • A j

/-! ## 1. Pointwise algebra helpers -/

/-- A Schwartz test paired with a continuous compactly supported field component is integrable:
the product is continuous with compact support.  This is the `SchwartzPairable` side condition of
`Data.IsSobolevDatum`'s totalization caveat (`Data.lean:148-155`), here with no order hypothesis
because the profile is genuinely compactly supported. -/
theorem integrable_schwartz_mul {z : Space → Space} (hz : Continuous z)
    (hc : HasCompactSupport z) (i : Fin 3) (ψ : SchwartzMap Space ℂ) :
    Integrable (fun x : Space => ψ x * ((z x i : ℝ) : ℂ)) volume := by
  have hcont : Continuous (fun x : Space => ψ x * ((z x i : ℝ) : ℂ)) :=
    ψ.continuous.mul (Complex.continuous_ofReal.comp
      ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp hz))
  have hcpt : HasCompactSupport (fun x : Space => ψ x * ((z x i : ℝ) : ℂ)) := by
    apply HasCompactSupport.mul_left
    have h1 : HasCompactSupport (fun x : Space => (z x i : ℝ)) :=
      hc.comp_left (g := fun v : Space => (v i : ℝ)) (by simp)
    exact h1.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  exact hcont.integrable_of_hasCompactSupport hcpt

/-- Coordinate `i` of a finite `ℝ`-linear combination in `RealVectorSobolev s`, coerced into
`FourierData`, is the corresponding combination of the coerced coordinates.  Uses that the
projection `coord i` is a bundled `ℝ`-CLM and that the subspace coercion commutes definitionally
with `+` and `•`. -/
theorem coe_sum_smul_apply (s : ℝ) {J : ℕ} (c : Fin J → ℝ)
    (A : Fin J → RealVectorSobolev s) (i : Fin 3) :
    (((∑ j, c j • A j) i : RealSobolevHilbert s) : FourierData)
      = ∑ j, c j • ((A j i : RealSobolevHilbert s) : FourierData) := by
  have h1 : ((∑ j, c j • A j) i) = coord i (∑ j, c j • A j) := rfl
  rw [h1, map_sum]; push_cast; simp only [map_smul]; rfl

/-- Coordinate `i` of a finite `ℝ`-linear combination in Euclidean `Space`. -/
theorem space_sum_apply {J : ℕ} (c : Fin J → ℝ) (v : Fin J → Space) (i : Fin 3) :
    ((∑ j, c j • v j : Space) i) = ∑ j, c j * (v j i) := by
  have h1 : ((∑ j, c j • v j : Space) i)
      = (EuclideanSpace.proj i : Space →L[ℝ] ℝ) (∑ j, c j • v j) := rfl
  rw [h1, map_sum]; simp only [map_smul, smul_eq_mul]; rfl

/-- `Paper3.angularRealization s` is a bundled ℂ-CLM, hence commutes with finite sums and with
`ℝ`-scalars (by `map_smul_of_tower`); pushed through the evaluation at a test `ψ`. -/
theorem angReal_sum_smul (s : ℝ) {J : ℕ} (c : Fin J → ℝ) (x : Fin J → FourierData)
    (ψ : SchwartzMap Space ℂ) :
    angularRealization s (∑ j, c j • x j) ψ = ∑ j, c j • (angularRealization s (x j) ψ) := by
  rw [map_sum, sum_apply]
  exact Finset.sum_congr rfl (fun j _ => by rw [ContinuousLinearMap.map_smul_of_tower]; rfl)

/-! ## 2. Support of a finite separated sum -/

/-- The single product `z ↦ a z.1 • b z.2` of a compactly supported scalar time factor and a
compactly supported vector spatial profile has compact support.  Vector generalization of
`PBD:54` `separated_physical_hasCompactSupport`. -/
theorem hasCompactSupport_sepTerm {a : ℝ → ℝ} (ha : HasCompactSupport a)
    {b : Space → Space} (hb : HasCompactSupport b) :
    HasCompactSupport (fun z : SpaceTime => a z.1 • b z.2) := by
  apply HasCompactSupport.of_support_subset_isCompact (ha.prod hb)
  intro z hz
  refine ⟨subset_tsupport a ?_, subset_tsupport b ?_⟩
  · intro hz0; exact hz (by simp [hz0])
  · intro hz0; exact hz (by simp [hz0])

/-- The single product's support lies in `Prod.fst ⁻¹' tsupport a`.  The `PPD:47-53` pattern. -/
theorem tsupport_sepTerm_subset {a : ℝ → ℝ} {b : Space → Space} :
    tsupport (fun z : SpaceTime => a z.1 • b z.2) ⊆ Prod.fst ⁻¹' tsupport a := by
  apply closure_minimal ?_ ((isClosed_tsupport a).preimage continuous_fst)
  intro z hz
  apply subset_tsupport a
  intro hz0
  exact hz (by simp [hz0])

/-- The support of a finite sum of spacetime fields lies in the union of the summands' supports. -/
theorem tsupport_finsetSum_subset {ι : Type*} [DecidableEq ι] {M : Type*} [AddCommMonoid M]
    [TopologicalSpace M] (s : Finset ι) (g : ι → SpaceTime → M) :
    tsupport (fun z => ∑ j ∈ s, g j z) ⊆ ⋃ j ∈ s, tsupport (g j) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha IH =>
    have heq : (fun z => ∑ j ∈ insert a s, g j z)
        = (fun z => g a z) + (fun z => ∑ j ∈ s, g j z) := by
      funext z; simp [Finset.sum_insert ha]
    rw [heq, Finset.set_biUnion_insert]
    exact (tsupport_add _ _).trans (union_subset_union_right _ IH)

/-! ## 3. The three conjuncts -/

/-- Joint smoothness of the finite separated sum. -/
theorem contDiff_separatedField {J : ℕ} (φ : Fin J → ℝ → ℝ) (h : Fin J → SpatialField)
    (hφs : ∀ j, ContDiff ℝ ∞ (φ j)) (hhs : ∀ j, ContDiff ℝ ∞ (h j)) :
    ContDiff ℝ ∞ (separatedField φ h) :=
  ContDiff.sum fun j _ => ((hφs j).comp contDiff_fst).smul ((hhs j).comp contDiff_snd)

/-- Compact support of the finite separated sum, contained strictly inside `t > 0`. -/
theorem hasCompactSupport_separatedField {J : ℕ} (φ : Fin J → ℝ → ℝ) (h : Fin J → SpatialField)
    (hφc : ∀ j, HasCompactSupport (φ j)) (hhc : ∀ j, HasCompactSupport (h j)) :
    HasCompactSupport (separatedField φ h) := by
  have hsub := tsupport_finsetSum_subset (Finset.univ : Finset (Fin J))
    (fun j (z : SpaceTime) => φ j z.1 • h j z.2)
  have hcpt : IsCompact (⋃ j ∈ (Finset.univ : Finset (Fin J)),
      tsupport (fun z : SpaceTime => φ j z.1 • h j z.2)) := by
    refine (Set.Finite.isCompact_biUnion (Finset.univ : Finset (Fin J)).finite_toSet
      (fun j _ => ?_))
    exact hasCompactSupport_sepTerm (hφc j) (hhc j)
  exact hcpt.of_isClosed_subset (isClosed_tsupport _) hsub

theorem tsupport_separatedField_pos {J : ℕ} (φ : Fin J → ℝ → ℝ) (h : Fin J → SpatialField)
    (hφpos : ∀ j, tsupport (φ j) ⊆ Ioi (0 : ℝ)) :
    ∀ z ∈ tsupport (separatedField φ h), 0 < z.1 := by
  intro z hz
  have hsub := tsupport_finsetSum_subset (Finset.univ : Finset (Fin J))
    (fun j (z : SpaceTime) => φ j z.1 • h j z.2)
  obtain ⟨j, -, hzj⟩ := Set.mem_iUnion₂.mp (hsub hz)
  exact hφpos j (tsupport_sepTerm_subset hzj)

/-- **Unit 6, the Sobolev-path half.**  The datum path `separatedPath φ A` is the order-`s`
Sobolev datum trajectory of `separatedField φ h` whenever each `A j` is the datum of the
continuous compactly supported profile `h j`.  Additivity of `Data.IsSobolevDatum` over the
finite sum, from `map_sum`/`map_smul` of `Paper3.angularRealization` and `integral_finsetSum`. -/
theorem isSobolevPath_separated (s : ℝ) {J : ℕ} (φ : Fin J → ℝ → ℝ) (h : Fin J → SpatialField)
    (A : Fin J → RealVectorSobolev s)
    (hhcont : ∀ j, Continuous (h j)) (hhc : ∀ j, HasCompactSupport (h j))
    (hA : ∀ j, IsSobolevDatum s (h j) (A j)) :
    IsSobolevPath s (separatedField φ h) (separatedPath φ A) := by
  intro t _ht i ψ
  have hLHS : angularRealization s ((separatedPath φ A t i : RealSobolevHilbert s) : FourierData) ψ
      = ∑ j, φ j t • ∫ x, ψ x * ((h j x i : ℝ) : ℂ) := by
    show angularRealization s (((∑ j, φ j t • A j) i : RealSobolevHilbert s) : FourierData) ψ = _
    rw [coe_sum_smul_apply, angReal_sum_smul]
    exact Finset.sum_congr rfl (fun j _ => by rw [hA j i ψ])
  have hRHS : (∫ x, ψ x * ((separatedField φ h (t, x) i : ℝ) : ℂ))
      = ∑ j, φ j t • ∫ x, ψ x * ((h j x i : ℝ) : ℂ) := by
    have hint : ∀ x : Space, ψ x * ((separatedField φ h (t, x) i : ℝ) : ℂ)
        = ∑ j, (φ j t : ℂ) * (ψ x * ((h j x i : ℝ) : ℂ)) := by
      intro x
      show ψ x * (((∑ j, φ j t • h j x : Space) i : ℝ) : ℂ) = _
      rw [space_sum_apply]; push_cast; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [integral_congr_ae (Filter.Eventually.of_forall hint),
      integral_finsetSum _ (fun j _ => (integrable_schwartz_mul (hhcont j) (hhc j) i ψ).const_mul _)]
    exact Finset.sum_congr rfl (fun j _ => by rw [integral_const_mul, Complex.real_smul])
  rw [hLHS, hRHS]

/-- The datum path is continuous, hence a.e. strongly measurable. -/
theorem aestronglyMeasurable_separatedPath (s : ℝ) {J : ℕ} (φ : Fin J → ℝ → ℝ)
    (A : Fin J → RealVectorSobolev s) (hφs : ∀ j, ContDiff ℝ ∞ (φ j)) :
    AEStronglyMeasurable (separatedPath φ A) forceTimeMeasure := by
  have : SecondCountableTopologyEither ℝ (RealVectorSobolev s) := ⟨Or.inl inferInstance⟩
  exact (continuous_finsetSum Finset.univ
    (fun j _ => (hφs j).continuous.smul continuous_const)).aestronglyMeasurable

/-! ## 4. Unit 6: `separatedAssembly` (`research/B01/Spec.lean:292`) -/

/-- **Unit 6, `separatedAssembly`.**  The finite separated sum `Σ_j φ_j(t) h_j(x)` of smooth
compact time factors (supported in `t > 0`) and smooth compact spatial profiles (with data
`A j`) lies in `F_c`, its Sobolev datum path is `separatedPath φ A`, and that path is a.e.
strongly measurable.  `paper/sections/04-whole-space.tex:260`. -/
theorem separatedAssembly (s : ℝ) {J : ℕ} (φ : Fin J → ℝ → ℝ)
    (h : Fin J → SpatialField) (A : Fin J → RealVectorSobolev s)
    (hφs : ∀ j, ContDiff ℝ ∞ (φ j)) (hφc : ∀ j, HasCompactSupport (φ j))
    (hφpos : ∀ j, tsupport (φ j) ⊆ Ioi (0 : ℝ))
    (hhs : ∀ j, ContDiff ℝ ∞ (h j)) (hhc : ∀ j, HasCompactSupport (h j))
    (hA : ∀ j, IsSobolevDatum s (h j) (A j)) :
    MemForceCompact (separatedField φ h) ∧
      IsSobolevPath s (separatedField φ h) (separatedPath φ A) ∧
      AEStronglyMeasurable (separatedPath φ A) forceTimeMeasure :=
  ⟨memForceCompact_of_smooth_support (contDiff_separatedField φ h hφs hhs)
      (hasCompactSupport_separatedField φ h hφc hhc)
      (tsupport_separatedField_pos φ h hφpos),
    isSobolevPath_separated s φ h A (fun j => (hhs j).continuous) hhc hA,
    aestronglyMeasurable_separatedPath s φ A hφs⟩

end NSFormalization.Section4.B01
