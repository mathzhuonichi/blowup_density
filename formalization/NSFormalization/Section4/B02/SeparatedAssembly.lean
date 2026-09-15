import NSFormalization.Section4.B01.Separated
import NSFormalization.Section4.D01.HomogeneousWitness

/-!
# B02: assembling a finite separated sum as an element of `F_c`, homogeneously

This module discharges the `B02` obligation `separatedAssembly` of
`research/B02/Spec.lean:582-600`, the field of `HomogeneousApproxAPI` that turns a pair
(smooth compact time factors `φ j` supported in `t > 0`, smooth compact spatial profiles `h j`
with order-`s` homogeneous data `A j`) into a single member of `F_c` together with its order-`s`
*homogeneous* datum path.  It is the homogeneous twin of `Section4/B01/Separated.lean`'s
`separatedAssembly` (`research/B01/Spec.lean:292`), the Lean form of
`paper/sections/04-whole-space.tex:260`.

The spec field differs from `B01`'s in **exactly one conjunct and its matching hypothesis**:
`IsHomogeneousPath s` / `IsHomogeneousSliceDatum s` replace `IsSobolevPath s` / `IsSobolevDatum s`.
The two realization-independent conjuncts are reused **verbatim** from `B01`:

* `MemForceCompact (separatedField φ h)` — `B01.memForceCompact_of_smooth_support` composed with
  `B01.{contDiff, hasCompactSupport, tsupport_…}_separatedField`;
* `AEStronglyMeasurable (separatedPath φ A) forceTimeMeasure` —
  `B01.aestronglyMeasurable_separatedPath`.

## The homogeneous conjunct and the range of `s`

The reviewer's route (`research/B02/REVIEW_REMAINING.md` F1): at each `t ≥ 0` the slice
`x ↦ Σ_j φ_j(t) h_j(x)` is smooth compactly supported, so `D01`'s compact-datum constructor
`homogeneousVectorDatum` produces a homogeneous slice datum for it; by **linearity** of that
concrete constructor (proved here, no integrability side conditions because every profile is
Schwartz) that datum equals `Σ_j φ_j(t) • A_j = separatedPath φ A t` once each `A_j` is identified
with the datum of `h_j` via the **unconditional** uniqueness `isHomogeneousSliceDatum_unique`.

This route needs `-3/2 < s`, because `D01`'s constructor `homogeneousVectorDatum`
(`homogeneousDatum` / `memLp_homogeneousProfile`) requires it: only at `s > -3/2` is
`∫_{|ξ|<1} |ξ|^{2s} dξ` finite.  The spec field `research/B02/Spec.lean:582` quantifies over **all**
real `s`.  So the theorem below carries an extra hypothesis `hs : -3 / 2 < s` and is **not** the
verbatim field.  This is harmless for every consumer: `approxCompactHomogeneous`
(`Spec.lean:607`) uses only `SplitRange s = (-3/2 < s ∧ s ≤ 0)`, which already implies `-3/2 < s`.
See `research/B02/ATTEMPTS_SEPARATED.md` for why the verbatim `∀ s : ℝ` field cannot be reached by
this route (it would need finite-sum / scalar-`smul` additivity combinators for
`IsSliceDistribution` and `IsHomogeneousDatum`, which carry the totalization integrability
bookkeeping that `D01` only proved for the two-term `_sub` forms); the contract lane decides the
field shape.

## Restated `Contracts.V1.Data` predicates

`formalization/` cannot import `Contracts.*`.  `separatedField`, `separatedPath`, `MemForceCompact`
and `forceTimeMeasure` are reused from `Section4/{B01/Separated, D01/ForceClass}.lean` (which
restate them token-for-token from `Contracts/V1/Data.lean`); `IsHomogeneousPath` and
`IsHomogeneousSliceDatum` from `Section4/D01/HomogeneousWitness.lean` §5, §15 (each definitionally
the `Data.lean` one).  The conformance file `research/B02/axioms_separated.lean` discharges the
spec field through the resulting definitional equalities.
-/

noncomputable section

namespace NSFormalization.Section4.B02

open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source (angularFourier)
open NSFormalization.Source.RealSobolev
open NSFormalization.Section4.D01.Homogeneous
open scoped ContDiff ENNReal SchwartzMap ComplexConjugate

/-! ## 1. Linearity of the concrete homogeneous constructor

Every profile here is Schwartz, so the datum `|ξ|^s ĥ` is built from the Schwartz-level Fourier
CLM and the linearity is free of integrability side conditions. -/

/-- The manuscript's angular transform, packaged as `D01.Homogeneous.schwartzAngularFourier`, is a
finite `ℝ`-linear combination of a Schwartz family: it is
`schwartzAngularDilation ∘ 𝓕`, a composition of two `ℂ`-continuous-linear maps. -/
theorem schwartzAngularFourier_finsetSum_smul {J : ℕ} (c : Fin J → ℝ)
    (g : Fin J → SchwartzMap Space ℂ) :
    schwartzAngularFourier (∑ j, c j • g j) = ∑ j, c j • schwartzAngularFourier (g j) := by
  have key : ∀ φ : SchwartzMap Space ℂ,
      schwartzAngularFourier φ
        = (schwartzAngularDilation.comp (SchwartzMap.fourierTransformCLM ℂ)) φ :=
    fun _ => rfl
  rw [key, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [key, ContinuousLinearMap.map_smul_of_tower]

/-- Pointwise: the homogeneous profile `|ξ|^s · (angular transform)` of a finite `ℝ`-combination of
Schwartz profiles is the same combination of the individual homogeneous profiles. -/
theorem homogeneousProfile_finsetSum_smul_apply {s : ℝ} {J : ℕ} (c : Fin J → ℝ)
    (g : Fin J → SchwartzMap Space ℂ) (ξ : Space) :
    homogeneousProfile s ((∑ j, c j • g j : SchwartzMap Space ℂ) : Space → ℂ) ξ
      = ∑ j, c j • homogeneousProfile s ((g j : SchwartzMap Space ℂ) : Space → ℂ) ξ := by
  simp only [homogeneousProfile]
  have hL : angularFourier ((∑ j, c j • g j : SchwartzMap Space ℂ) : Space → ℂ) ξ
      = ∑ j, c j • (angularFourier ((g j : SchwartzMap Space ℂ) : Space → ℂ) ξ) := by
    rw [← schwartzAngularFourier_apply, schwartzAngularFourier_finsetSum_smul]
    simp only [sum_apply, smul_apply, schwartzAngularFourier_apply]
  rw [hL, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [mul_smul_comm]

/-- The `L²` homogeneous datum of a finite `ℝ`-combination of Schwartz profiles is that combination
of the individual data (order `-3/2 < s`, no integrability side conditions). -/
theorem homogeneousDatum_finsetSum_smul {s : ℝ} (hs : -3 / 2 < s) {J : ℕ} (c : Fin J → ℝ)
    (g : Fin J → SchwartzMap Space ℂ) :
    homogeneousDatum hs (∑ j, c j • g j) = ∑ j, c j • homogeneousDatum hs (g j) := by
  apply Lp.ext
  have h1 := homogeneousDatum_ae hs (∑ j, c j • g j)
  have h2 := Lp.coeFn_finsetSum (Finset.univ : Finset (Fin J))
    (fun j => c j • homogeneousDatum hs (g j))
  have h4 := MeasureTheory.ae_all_iff.mpr
    (fun j => Lp.coeFn_smul (c j) (homogeneousDatum hs (g j)))
  have h5 := MeasureTheory.ae_all_iff.mpr (fun j => homogeneousDatum_ae hs (g j))
  filter_upwards [h1, h2, h4, h5] with ξ e1 e2 e4 e5
  rw [e1, e2, Finset.sum_apply, homogeneousProfile_finsetSum_smul_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [e4 j, Pi.smul_apply, e5 j]

/-! ## 2. Compact support of a finite `ℝ`-combination of spatial profiles -/

/-- The support of a finite `ℝ`-combination of compactly supported spatial profiles lies in the
finite union of their supports, hence is compact. -/
theorem hasCompactSupport_sum_smul {J : ℕ} (c : Fin J → ℝ) (h : Fin J → Space → Space)
    (hhc : ∀ j, HasCompactSupport (h j)) :
    HasCompactSupport (fun x : Space => ∑ j, c j • h j x) := by
  have hcpt : IsCompact (⋃ j ∈ (Finset.univ : Finset (Fin J)), tsupport (h j)) :=
    (Finset.univ : Finset (Fin J)).finite_toSet.isCompact_biUnion (fun j _ => hhc j)
  apply hcpt.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hcpt.isClosed
  intro x hx
  rw [Function.mem_support] at hx
  rw [Set.mem_iUnion₂]
  by_contra hnot
  apply hx
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have hx0 : x ∉ tsupport (h j) := fun hmem => hnot ⟨j, Finset.mem_univ j, hmem⟩
  rw [image_eq_zero_of_notMem_tsupport hx0, smul_zero]

/-! ## 3. The homogeneous slice datum of a finite separated combination -/

/-- **Core homogeneous linearity.**  A finite `ℝ`-combination `x ↦ Σ_j c_j h_j(x)` of smooth
compact spatial profiles, each with an order-`s` homogeneous slice datum `A_j`, has the combination
`Σ_j c_j • A_j` as *its* order-`s` homogeneous slice datum, at every order `-3/2 < s`.

Route: the concrete datum of `h_j` is `homogeneousVectorDatum` of its Schwartz components; by
uniqueness `A_j` equals it.  The slice is smooth compact, so `homogeneousVectorDatum` of its
components is a datum of it; by the constructor's linearity that datum is `Σ_j c_j • A_j`. -/
theorem isHomogeneousSliceDatum_sum_smul {s : ℝ} (hs : -3 / 2 < s) {J : ℕ}
    (c : Fin J → ℝ) (h : Fin J → Space → Space) (A : Fin J → RealVectorSobolev s)
    (hhs : ∀ j, ContDiff ℝ ∞ (h j)) (hhc : ∀ j, HasCompactSupport (h j))
    (hA : ∀ j, IsHomogeneousSliceDatum s (h j) (A j)) :
    IsHomogeneousSliceDatum s (fun x => ∑ j, c j • h j x) (∑ j, c j • A j) := by
  -- Schwartz components of each profile and the canonical datum they carry.
  have hreⱼ : ∀ j, ∀ (i : Fin 3) (x : Space),
      conj (compactSchwartzComponents (hhs j) (hhc j) i x)
        = compactSchwartzComponents (hhs j) (hhc j) i x :=
    fun j i x => by rw [compactSchwartzComponents_apply, Complex.conj_ofReal]
  have hBdatum : ∀ j, IsHomogeneousSliceDatum s (h j)
      (homogeneousVectorDatum hs (compactSchwartzComponents (hhs j) (hhc j)) (hreⱼ j)) :=
    fun j => isHomogeneousSliceDatum_schwartz hs (h j)
      (compactSchwartzComponents (hhs j) (hhc j)) (fun _ _ => rfl) (hreⱼ j)
  -- Uniqueness pins each given datum to the canonical one.
  have hAB : ∀ j, A j
      = homogeneousVectorDatum hs (compactSchwartzComponents (hhs j) (hhc j)) (hreⱼ j) :=
    fun j => isHomogeneousSliceDatum_unique (hA j) (hBdatum j)
  -- The slice is smooth compact, so it too has the canonical datum.
  have hzs : ContDiff ℝ ∞ (fun x : Space => ∑ j, c j • h j x) :=
    ContDiff.sum (fun j _ => (hhs j).const_smul (c j))
  have hzc : HasCompactSupport (fun x : Space => ∑ j, c j • h j x) :=
    hasCompactSupport_sum_smul c h hhc
  have hreΨ : ∀ (i : Fin 3) (x : Space),
      conj (compactSchwartzComponents hzs hzc i x) = compactSchwartzComponents hzs hzc i x :=
    fun i x => by rw [compactSchwartzComponents_apply, Complex.conj_ofReal]
  have hCdatum : IsHomogeneousSliceDatum s (fun x => ∑ j, c j • h j x)
      (homogeneousVectorDatum hs (compactSchwartzComponents hzs hzc) hreΨ) :=
    isHomogeneousSliceDatum_schwartz hs _ (compactSchwartzComponents hzs hzc) (fun _ _ => rfl) hreΨ
  -- The canonical datum of the slice is `Σ_j c_j • (canonical datum of h_j)`.
  have hkey : homogeneousVectorDatum hs (compactSchwartzComponents hzs hzc) hreΨ
      = ∑ j, c j • homogeneousVectorDatum hs (compactSchwartzComponents (hhs j) (hhc j)) (hreⱼ j) := by
    apply WithLp.ofLp_injective 2
    funext i
    apply Subtype.ext
    rw [B01.coe_sum_smul_apply]
    simp only [homogeneousVectorDatum_coe]
    -- the `i`-th component of the slice equals `Σ_j c_j • (i-th component of h_j)`, as Schwartz maps
    have hcomp : compactSchwartzComponents hzs hzc i
        = ∑ j, c j • compactSchwartzComponents (hhs j) (hhc j) i := by
      apply SchwartzMap.ext
      intro x
      rw [sum_apply]
      simp only [smul_apply, compactSchwartzComponents_apply]
      rw [B01.space_sum_apply]
      push_cast
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Complex.real_smul]
    rw [hcomp, homogeneousDatum_finsetSum_smul]
  rw [show (∑ j, c j • A j)
      = ∑ j, c j • homogeneousVectorDatum hs (compactSchwartzComponents (hhs j) (hhc j)) (hreⱼ j) from
    Finset.sum_congr rfl (fun j _ => by rw [hAB j])]
  rw [← hkey]
  exact hCdatum

/-! ## 4. `separatedAssembly` (`research/B02/Spec.lean:582-600`)

Stated with the extra hypothesis `hs : -3 / 2 < s` (see the module docstring and
`research/B02/ATTEMPTS_SEPARATED.md`); every other token matches the spec field. -/

/-- **`separatedAssembly`, homogeneous, on `-3/2 < s`.**  The finite separated sum
`Σ_j φ_j(t) h_j(x)` of smooth compact time factors (supported in `t > 0`) and smooth compact
spatial profiles (with order-`s` homogeneous data `A j`) lies in `F_c`, its order-`s` homogeneous
datum path is `separatedPath φ A`, and that path is a.e. strongly measurable.
`paper/sections/04-whole-space.tex:260`. -/
theorem separatedAssembly (s : ℝ) (hs : -3 / 2 < s) {J : ℕ} (φ : Fin J → ℝ → ℝ)
    (h : Fin J → Space → Space) (A : Fin J → RealVectorSobolev s)
    (hφs : ∀ j, ContDiff ℝ ∞ (φ j)) (hφc : ∀ j, HasCompactSupport (φ j))
    (hφpos : ∀ j, tsupport (φ j) ⊆ Ioi (0 : ℝ))
    (hhs : ∀ j, ContDiff ℝ ∞ (h j)) (hhc : ∀ j, HasCompactSupport (h j))
    (hA : ∀ j, IsHomogeneousSliceDatum s (h j) (A j)) :
    D01.MemForceCompact (B01.separatedField φ h) ∧
      IsHomogeneousPath s (B01.separatedField φ h) (B01.separatedPath φ A) ∧
      AEStronglyMeasurable (B01.separatedPath φ A) D01.forceTimeMeasure := by
  refine ⟨D01.memForceCompact_of_smooth_support
      (B01.contDiff_separatedField φ h hφs hhs)
      (B01.hasCompactSupport_separatedField φ h hφc hhc)
      (B01.tsupport_separatedField_pos φ h hφpos), ?_, ?_⟩
  · intro t _
    exact isHomogeneousSliceDatum_sum_smul hs (fun j => φ j t) h A hhs hhc hA
  · exact B01.aestronglyMeasurable_separatedPath s φ A hφs

end NSFormalization.Section4.B02
