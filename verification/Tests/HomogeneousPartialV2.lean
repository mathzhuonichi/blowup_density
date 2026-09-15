import Contracts.V2.HomogeneousPartial
import Bindings.HomogeneousPartialV2
import TestSupport.Axioms

/-! The exact public type and its transitive trust boundary are both checked.

The version-one test `Tests.HomogeneousPartial` is untouched and keeps running
against `Bindings.homogeneousPartial`; this is the second, stronger acceptance test,
not a replacement.  `Bindings.homogeneousPartial_of_v2` is the checked link between
the two: it projects
`Contracts.V1.HomogeneousPartial.HomogeneousApproxPartialAPI` out of the version-two
witness, so nothing that version one guarantees is lost by version two.

The two `example`s below print the two new fields in their manuscript shapes:
`approxCompactHomogeneous` at `q = 2`, `s = -1` as the density conclusion of
`04-whole-space.tex:219,228`, and `separatedAssembly` as the membership of the
finite separated sum in `F_c` of `04-whole-space.tex:260`. -/

noncomputable section
namespace BlowupDensity.Tests

open Set MeasureTheory
open NSFormalization.Paper3 (RealVectorSobolev)
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal

/-- An implementation must supply every field of the unchanged version-one
specification **and** the two fields of lanes 103 and 110 (`separatedAssembly`,
`approxCompactHomogeneous`).  `χ` is a data field, so `HomogeneousApproxPartialV2API`
is a `Type` and this is a `def`, as version one's `checkedHomogeneousPartial` is. -/
def checkedHomogeneousPartialV2 :
    Contracts.V2.HomogeneousPartial.HomogeneousApproxPartialV2API :=
  Bindings.homogeneousPartialV2

run_cmd TestSupport.checkAxioms ``checkedHomogeneousPartialV2

/-- **Manuscript shape of `approxCompactHomogeneous`** (`04-whole-space.tex:219`
prop:Renergy homogeneous clause, with `:228` the compact-difference caveat): at
`q = 2`, `s = -1` — the case `R46` consumes — smooth compact forces `F_c` are dense
in `L²(0,∞;Ḣ^{-1}(R³))`, i.e. every Bochner datum `b` is approximated to within any
`r > 0` by a member `f ∈ F_c` whose order-`(-1)` homogeneous datum path `D` is
strongly measurable and within `r` of `b`.  `SplitRange (-1)` holds since
`-3/2 < -1 ≤ 0`. -/
example : ∀ b : ℝ → RealVectorSobolev (-1 : ℝ),
    MemBochnerDatum 2 (-1) b → ∀ r : ℝ≥0∞, 0 < r →
      ∃ f ∈ forceClassCompact, ∃ D : ℝ → RealVectorSobolev (-1 : ℝ),
        IsHomogeneousPath (-1) f D ∧
          AEStronglyMeasurable D forceTimeMeasure ∧
          bochnerDatumENorm 2 (-1) (D - b) < r :=
  checkedHomogeneousPartialV2.approxCompactHomogeneous 2 one_le_two (by simp) (-1)
    ⟨by norm_num, by norm_num⟩

/-- **Manuscript shape of `separatedAssembly`** (`04-whole-space.tex:260`): the
finite separated sum `Σ_j φ_j(t)h_j(x)` of smooth compact time factors (supported in
`t > 0`) and smooth compact spatial profiles with order-`s` homogeneous data `A j`
is a member of `F_c` (`Contracts.V1.BochnerPartial.separatedField φ h ∈ forceClassCompact`),
and its order-`s` homogeneous datum path is `separatedPath φ A`.  On `-3/2 < s`, the
honest hypothesis the tree proves. -/
example (s : ℝ) (hs : -3 / 2 < s) (J : ℕ) (φ : Fin J → ℝ → ℝ)
    (h : Fin J → SpatialField) (A : Fin J → RealVectorSobolev s)
    (hφs : ∀ j, ContDiff ℝ ∞ (φ j)) (hφc : ∀ j, HasCompactSupport (φ j))
    (hφpos : ∀ j, tsupport (φ j) ⊆ Ioi (0 : ℝ))
    (hhs : ∀ j, ContDiff ℝ ∞ (h j)) (hhc : ∀ j, HasCompactSupport (h j))
    (hA : ∀ j, IsHomogeneousSliceDatum s (h j) (A j)) :
    Contracts.V1.BochnerPartial.separatedField φ h ∈ forceClassCompact ∧
      IsHomogeneousPath s (Contracts.V1.BochnerPartial.separatedField φ h)
        (Contracts.V1.BochnerPartial.separatedPath φ A) :=
  have H := checkedHomogeneousPartialV2.separatedAssembly s hs J φ h A
    hφs hφc hφpos hhs hhc hA
  ⟨H.1, H.2.1⟩

end BlowupDensity.Tests
