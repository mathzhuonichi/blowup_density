import NSFormalization.Source.PhysicalIntegerSobolev
import NSFormalization.Paper3.AngularRealVectorBochner

/-!
# Angular Sobolev data of an `H^∞` field (unit D01/L2)

`verification/Contracts/V1/Data.lean` states every Sobolev quantity of Section 4
through the *datum* form

```
IsSobolevDatum (s : ℝ) (z : SpatialField) (A : RealVectorSobolev s) : Prop :=
  ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
    angularRealization s ((A i : FourierData)) ψ = ∫ x : Space, ψ x * ((z x i : ℝ) : ℂ)
```

and `MemHInfty a := ContDiff ℝ ∞ a ∧ ∀ m : ℕ, ∃ A, IsSobolevDatum (m : ℝ) a A`.  This
module supplies **one** of the two implications of `research/D01/RECONCILIATION.md` unit
**L2**, the `⟸` one: a physical field whose spatial jets are all square integrable —
draft B's `EulerLpTranslation.SmoothL2Field` shape, i.e. `ContDiff ℝ ∞ z` together with
`MemLp (iteratedFDeriv ℝ n z) 2 volume` for every `n` — *has* an angular real-vector
datum, at every real order, with no compact-support hypothesis.  Before this module the
only in-tree producer of *real angular vector* data was
`Paper3.realCompactSobolevTimeSlice`, which needs `HasCompactSupport`;
`Source.PhysicalIntegerSobolev.vectorSobolevDatum` (`:42`) already produced non-compact
data, but in the cycles convention and with no reality constraint.

## Scope: jets ⟹ datum only

The converse — `MemHInfty z → ∀ n, MemLp (iteratedFDeriv ℝ n z) 2 volume`, equivalently
`MemHInfty z → ∃ A : SmoothL2Field Space, A.field = z` — is **not** proved here, and unit
L2 asks for both directions.  This matters for the downstream units:

* **A03 unit U2 is not closed by this module.**  `research/A03/Spec.lean:324,330,339`
  state `memHInfty_memHm`, `memHInfty_component` and `memHInfty_partialDeriv` with
  `Contracts.V1.Data.MemHInfty z` as a *hypothesis*, i.e. in the datum form.  Getting
  physical `L²` membership, componentwise admissibility, or `∂_j` out of that hypothesis
  needs datum ⟹ jets first, and that step is absent.  What this module *does* retire is
  the sizing risk `research/A03/COMPARISON.md:210-221` records — "if L2 stalls, U2 is an
  L" — since the non-compact datum producer now exists; the residual `⟹` direction is the
  one `RECONCILIATION.md:153` binds to `Source.FourierPhysicalJets.smoothL2FieldOfFourier`
  and `physicalJetLp_ae`.  U2 is unblocked, not closed.
* **A02 unit U1b** likewise starts from `ClassicalSolutionR.sobolev`'s datum path
  (`Data.lean:643-645`), not from a jet carrier; see the docstring of
  `angularRealization_smoothAngularDatum_directional` below.

## Conventions

The Fourier normalization is the manuscript's angular one,
`ẑ(ξ) = (2π)^{-3/2} ∫ e^{-i x·ξ} z(x) dx` (`paper/sections/01-introduction.tex:91,94`),
carried by `Paper3.angularRealization`; reality is the conjugate reflection
`F(-ξ) = conj (F ξ)` of `02-preliminaries.tex:72`, i.e. membership in
`Source.RealSobolev.realSubspace`; the three components are summed with the Euclidean
`PiLp 2` norm of `01-introduction.tex:103`, i.e. `Paper3.RealVectorSobolev`.

## Route

`Source.PhysicalIntegerSobolev.integerSobolevDatum` already builds, from an
`SmoothL2Field ℂ`, a **cycles-convention** datum of every integer order realizing the
physical tempered distribution, by iterating the physical Bessel operator
`1 - (2π)^{-2} Δ` and lowering the order.  Three things are added here.

1. *Reality.*  The cycles datum of a real-valued field is fixed by
   `Source.RealSobolev.realSymmetry`, so it lives in the closed real subspace.  This is
   proved along the construction: conjugation commutes with the `L²` Fourier transform
   (`fourier_conjugation`, by density from `Source.RealSobolev.fourier_conjugate`), the
   physical Bessel operator preserves real-valuedness (`IsRealField.besselField`), and
   `Paper3.sobolevOrderLowering` — multiplication by the real even symbol
   `(1+‖ξ‖²)^{(r-s)/2}` — commutes with conjugate reflection
   (`realSymmetry_sobolevOrderLowering`).
2. *Arbitrary real order.*  Lowering from any integer `m ≥ s` gives every real order `s`,
   half-integers and negative orders included.
3. *Angular normalization.*  `Paper3.cyclesToAngularRealVector` transports the real
   vector datum to the manuscript's angular convention without changing the physical
   distribution (`Paper3.angularRealization_cyclesToAngularReal`).

`isSobolevDatum` below is *definitionally* `Contracts.V1.Data.IsSobolevDatum`, and
`hInftyENorm` is definitionally `Contracts.V1.Data.sobolevENorm`; they are restated here
because the `NSFormalization` package is a dependency of the `Contracts` library and
cannot import it.
-/

noncomputable section

namespace NSFormalization.Section4.D01

open Set MeasureTheory FourierTransform EulerLpTranslation NavierStokes.ProblemStatement
open EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
open NSFormalization.Paper3
open NSFormalization.Source NSFormalization.Source.RealSobolev
open NSFormalization.Source.PhysicalSobolevDistribution
open NSFormalization.Source.PhysicalBesselSobolev
open NSFormalization.Source.PhysicalIntegerSobolev
open scoped ContDiff ENNReal ComplexConjugate LineDeriv

/-! ## 1. Conjugation, conjugate reflection and the `L²` Fourier transform -/

/-- The a.e. representative of `Source.RealSobolev.conjugation` is pointwise conjugation. -/
theorem conjugation_ae (h : FourierData) :
    (conjugation h : Space → ℂ) =ᵐ[volume] fun x => conj (h x) :=
  ContinuousLinearMap.coeFn_compLpL Complex.conjLIE.toContinuousLinearMap h

/-- Pointwise conjugation of a Schwartz function is the `L²` conjugation of its class. -/
theorem conjugation_toLp (φ : SchwartzMap Space ℂ) :
    conjugation (φ.toLp 2 volume) = (conjugateSchwartz φ).toLp 2 volume := by
  apply Lp.ext
  filter_upwards [conjugation_ae (φ.toLp 2 volume),
    φ.coeFn_toLp 2 volume, (conjugateSchwartz φ).coeFn_toLp 2 volume] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃]
  rfl

/-- Conjugation of the physical function is conjugate reflection of its `L²` Fourier
transform.  `Source.RealSobolev.fourier_conjugate` is the pointwise Schwartz statement;
this is its extension to all of `L²` by density, with no `L¹` hypothesis. -/
theorem fourier_conjugation (u : FourierData) :
    𝓕 (conjugation u) = realSymmetry (𝓕 u) := by
  refine (SchwartzMap.denseRange_toLpCLM (E := Space) (F := ℂ) (p := 2)
    (μ := volume) ENNReal.ofNat_ne_top).induction_on u
    (isClosed_eq
      ((fourierCLM ℂ (Lp ℂ 2 (volume : Measure Space))).continuous.comp conjugation.continuous)
      (realSymmetry.continuous.comp
        (fourierCLM ℂ (Lp ℂ 2 (volume : Measure Space))).continuous)) ?_
  intro φ
  change 𝓕 (conjugation (φ.toLp 2 volume)) = realSymmetry (𝓕 (φ.toLp 2 volume))
  rw [conjugation_toLp, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq,
    ← frequencyRealSchwartz_toLp]
  congr 1
  ext ξ
  rw [SchwartzMap.fourier_coe, frequencyRealSchwartz_apply, SchwartzMap.fourier_coe]
  exact RealSobolev.fourier_conjugate (φ : Space → ℂ) ξ

/-! ## 2. Real-valued smooth `L²` fields -/

/-- A complex smooth `L²` field whose values are real.  This is the hypothesis under
which the cycles Sobolev datum lands in `Source.RealSobolev.realSubspace`. -/
def IsRealField (A : SmoothL2Field ℂ) : Prop := ∀ x : Space, conj (A.field x) = A.field x

theorem IsRealField.add {A B : SmoothL2Field ℂ} (hA : IsRealField A) (hB : IsRealField B) :
    IsRealField (addField A B) := by
  intro x
  rw [addField_field, map_add, hA x, hB x]

theorem IsRealField.sum {ι : Type*} (I : Finset ι) (A : ι → SmoothL2Field ℂ)
    (h : ∀ i ∈ I, IsRealField (A i)) : IsRealField (sumField I A) := by
  intro x
  rw [sumField_field, map_sum]
  exact Finset.sum_congr rfl fun i hi => h i hi x

theorem IsRealField.scale (c : ℝ) {A : SmoothL2Field ℂ} (hA : IsRealField A) :
    IsRealField (scaleField c A) := by
  intro x
  show conj ((c • ContinuousLinearMap.id ℝ ℂ) (A.field x)) =
    (c • ContinuousLinearMap.id ℝ ℂ) (A.field x)
  simp only [smul_apply, ContinuousLinearMap.id_apply,
    Complex.real_smul, map_mul, Complex.conj_ofReal, hA x]

/-- The classical directional derivative of a real-valued field is real valued. -/
theorem IsRealField.directional {A : SmoothL2Field ℂ} (hA : IsRealField A) (v : Space) :
    IsRealField (A.directionalField v) := by
  intro x
  show conj (fderiv ℝ A.field x v) = fderiv ℝ A.field x v
  have hd : HasFDerivAt A.field (fderiv ℝ A.field x) x :=
    (A.smooth.differentiable (by simp) x).hasFDerivAt
  have hc : HasFDerivAt (fun y => conj (A.field y))
      ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.comp (fderiv ℝ A.field x)) x :=
    (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.hasFDerivAt.comp x hd
  rw [funext hA] at hc
  exact congrArg (fun L : Space →L[ℝ] ℂ => L v) hc.fderiv.symm

theorem IsRealField.laplacian {A : SmoothL2Field ℂ} (hA : IsRealField A) :
    IsRealField (laplacianField A) := by
  show IsRealField (EulerOrdinarySobolev.sumField Finset.univ (fun i : Fin 3 =>
    (A.directionalField (EuclideanSpace.basisFun (Fin 3) ℝ i)).directionalField
      (EuclideanSpace.basisFun (Fin 3) ℝ i)))
  exact IsRealField.sum _ _ fun i _ => (hA.directional _).directional _

theorem IsRealField.bessel {A : SmoothL2Field ℂ} (hA : IsRealField A) :
    IsRealField (besselField A) :=
  hA.add (IsRealField.scale _ hA.laplacian)

theorem IsRealField.iteratedBessel {A : SmoothL2Field ℂ} (hA : IsRealField A) :
    ∀ k : ℕ, IsRealField (iteratedBesselField k A)
  | 0 => hA
  | k + 1 => (hA.iteratedBessel k).bessel

/-- The `L²` class of a real-valued field is fixed by conjugation. -/
theorem conjugation_toLp_of_isRealField {A : SmoothL2Field ℂ} (hA : IsRealField A) :
    conjugation A.toLp = A.toLp := by
  apply Lp.ext
  filter_upwards [conjugation_ae A.toLp, A.toLp_ae] with x h₁ h₂
  rw [h₁, h₂]
  exact hA x

/-! ## 3. Reality of the cycles Sobolev datum -/

/-- The order-zero datum of a real-valued field has the conjugate-reflection symmetry
of `02-preliminaries.tex:72`. -/
theorem realSymmetry_physicalH0Datum {A : SmoothL2Field ℂ} (hA : IsRealField A) :
    realSymmetry (physicalH0Datum A) = physicalH0Datum A := by
  show realSymmetry (𝓕 A.toLp) = 𝓕 A.toLp
  rw [← fourier_conjugation A.toLp, conjugation_toLp_of_isRealField hA]

theorem realSymmetry_evenSobolevDatum (k : ℕ) {A : SmoothL2Field ℂ} (hA : IsRealField A) :
    realSymmetry (evenSobolevDatum k A) = evenSobolevDatum k A :=
  realSymmetry_physicalH0Datum (hA.iteratedBessel k)

/-- Order lowering multiplies by the real, even symbol `(1+‖ξ‖²)^{(r-s)/2}`, so it
commutes with conjugate reflection. -/
theorem realSymmetry_sobolevOrderLowering (s r : ℝ) (hrs : r ≤ s) (h : SobolevHilbert s) :
    realSymmetry (sobolevOrderLowering s r hrs h) =
      sobolevOrderLowering s r hrs (realSymmetry h) := by
  apply Lp.ext
  have hr := (Measure.measurePreserving_neg (volume : Measure Space)).quasiMeasurePreserving.ae
    (sobolevOrderLowering_coeFn s r hrs h)
  filter_upwards [realSymmetry_ae (sobolevOrderLowering s r hrs h),
    sobolevOrderLowering_coeFn s r hrs (realSymmetry h), realSymmetry_ae h, hr]
    with ξ h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄, map_mul]
  congr 1
  simp [sobolevBesselWeight]

theorem realSymmetry_integerSobolevDatum (n : ℕ) {A : SmoothL2Field ℂ} (hA : IsRealField A) :
    realSymmetry (integerSobolevDatum n A) = integerSobolevDatum n A := by
  rw [integerSobolevDatum, realSymmetry_sobolevOrderLowering,
    realSymmetry_evenSobolevDatum n hA]

/-- Every component of a real Euclidean three-vector field is a real-valued complex
field. -/
theorem isRealField_componentField (i : Fin 3) (A : SmoothL2Field Space) :
    IsRealField (componentField i A) := fun _ => Complex.conj_ofReal _

/-! ## 4. The angular real-vector datum of a smooth `L²` field -/

/-- `Contracts.V1.Data.IsSobolevDatum`, restated verbatim.  The `NSFormalization`
package is a dependency of the `Contracts` library, so it cannot import it; the two
predicates are definitionally equal and a binding module can discharge one by the
other with `exact`. -/
def IsSobolevDatum (s : ℝ) (z : Space → Space) (A : RealVectorSobolev s) : Prop :=
  ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
    angularRealization s ((A i : FourierData)) ψ = ∫ x : Space, ψ x * ((z x i : ℝ) : ℂ)

/-- **The zero field has the zero datum at every order.**  Lives here, next to `IsSobolevDatum`,
so that a consumer needing only this three-line fact does not inherit the Leray/pressure stack
(previously it sat in `A04/PressureDrop`, dragging in ~20 modules — lane 155,
`research/MAINT/REVIEW_144.md` item 4).  A04 modules keep using the bare name via their existing
`open NSFormalization.Section4.D01`. -/
theorem isSobolevDatum_zero (s : ℝ) : IsSobolevDatum s (fun _ : Space => (0 : Space)) 0 := by
  intro i ψ
  simp

/-- One component of the cycles-convention real Sobolev datum, at any real order `s`
below the integer order `m` at which `Source.PhysicalIntegerSobolev` builds it. -/
def cyclesComponentDatum (m : ℕ) (s : ℝ) (hs : s ≤ (m : ℝ)) (A : SmoothL2Field Space)
    (i : Fin 3) : RealSobolevHilbert s :=
  realProjectionTo s
    (sobolevOrderLowering (m : ℝ) s hs (integerSobolevDatum m (componentField i A)))

/-- The real-part projection is the identity on it: the datum of a real physical
component already has the conjugate-reflection symmetry. -/
theorem coe_cyclesComponentDatum (m : ℕ) (s : ℝ) (hs : s ≤ (m : ℝ)) (A : SmoothL2Field Space)
    (i : Fin 3) :
    ((cyclesComponentDatum m s hs A i : RealSobolevHilbert s) : FourierData) =
      sobolevOrderLowering (m : ℝ) s hs (integerSobolevDatum m (componentField i A)) :=
  realProjection_eq_self (s := s) ((mem_realSubspace_iff _ _).mpr (by
    rw [realSymmetry_sobolevOrderLowering,
      realSymmetry_integerSobolevDatum m (isRealField_componentField i A)]))

/-- The manuscript-normalized angular real-vector datum of a smooth `L²` field, at any
real order `s ≤ m`. -/
def smoothAngularDatum (m : ℕ) (s : ℝ) (hs : s ≤ (m : ℝ)) (A : SmoothL2Field Space) :
    RealVectorSobolev s :=
  cyclesToAngularRealVector s (WithLp.toLp 2 (fun i => cyclesComponentDatum m s hs A i))

/-- Each component of the angular datum realizes the physical tempered distribution of
that component of the field. -/
theorem angularRealization_smoothAngularDatum (m : ℕ) (s : ℝ) (hs : s ≤ (m : ℝ))
    (A : SmoothL2Field Space) (i : Fin 3) :
    angularRealization s ((smoothAngularDatum m s hs A i : FourierData)) =
      physicalDistribution (componentField i A) := by
  show angularRealization s
    ((cyclesToAngularReal s (cyclesComponentDatum m s hs A i) : RealSobolevHilbert s)
      : FourierData) = _
  rw [angularRealization_cyclesToAngularReal, coe_cyclesComponentDatum,
    sobolevRealization_orderLowering, integerSobolevDatum_realization]

/-- **Unit L2, construction.**  The angular datum pairs with every Schwartz test exactly
as the original physical field, which is `Contracts.V1.Data.IsSobolevDatum`. -/
theorem smoothAngularDatum_isSobolevDatum (m : ℕ) (s : ℝ) (hs : s ≤ (m : ℝ))
    (A : SmoothL2Field Space) : IsSobolevDatum s A.field (smoothAngularDatum m s hs A) := by
  intro i ψ
  rw [angularRealization_smoothAngularDatum, physicalDistribution_apply]
  simp only [componentField_field, smul_eq_mul]

/-! ## 5. The statements of unit L2 -/

/-- **Unit L2.**  A smooth real three-vector field all of whose spatial jets are square
integrable — draft B's `EulerLpTranslation.SmoothL2Field` hypothesis — has an angular
real-vector Sobolev datum at **every real order**, with no compact-support or `L¹`
assumption.  Half-integer and negative orders are included. -/
theorem exists_isSobolevDatum_of_contDiff_memLp {z : Space → Space} (hz : ContDiff ℝ ∞ z)
    (hL2 : ∀ n : ℕ, MemLp (iteratedFDeriv ℝ n z) 2 volume) (s : ℝ) :
    ∃ A : RealVectorSobolev s, IsSobolevDatum s z A :=
  ⟨smoothAngularDatum ⌈s⌉₊ s (Nat.le_ceil s) ⟨z, hz, hL2⟩,
    smoothAngularDatum_isSobolevDatum ⌈s⌉₊ s (Nat.le_ceil s) ⟨z, hz, hL2⟩⟩

/-- **Unit L2, the `⟸` direction of `RECONCILIATION.md`.**  The statement is
definitionally `Contracts.V1.Data.MemHInfty z`: the physical jet form of `H^∞` implies
the datum form used throughout `Data.lean`. -/
theorem memHInfty_of_contDiff_memLp {z : Space → Space} (hz : ContDiff ℝ ∞ z)
    (hL2 : ∀ n : ℕ, MemLp (iteratedFDeriv ℝ n z) 2 volume) :
    ContDiff ℝ ∞ z ∧
      ∀ m : ℕ, ∃ A : RealVectorSobolev (m : ℝ), IsSobolevDatum (m : ℝ) z A :=
  ⟨hz, fun m => exists_isSobolevDatum_of_contDiff_memLp hz hL2 (m : ℝ)⟩

/-- `Contracts.V1.Data.sobolevENorm`, restated verbatim. -/
def sobolevENorm (s : ℝ) (z : Space → Space) : ℝ≥0∞ :=
  ⨅ A : {A : RealVectorSobolev s // IsSobolevDatum s z A}, ‖A.1‖ₑ

theorem sobolevENorm_le_of_isSobolevDatum {s : ℝ} {z : Space → Space}
    {A : RealVectorSobolev s} (h : IsSobolevDatum s z A) : sobolevENorm s z ≤ ‖A‖ₑ :=
  iInf_le (fun A : {A : RealVectorSobolev s // IsSobolevDatum s z A} => ‖A.1‖ₑ) ⟨A, h⟩

/-- The manuscript norm of an `H^∞` field is finite at every real order: the datum
infimum of `Data.lean` is not the empty infimum `⊤`. -/
theorem sobolevENorm_ne_top_of_contDiff_memLp {z : Space → Space} (hz : ContDiff ℝ ∞ z)
    (hL2 : ∀ n : ℕ, MemLp (iteratedFDeriv ℝ n z) 2 volume) (s : ℝ) :
    sobolevENorm s z ≠ ⊤ := by
  obtain ⟨A, hA⟩ := exists_isSobolevDatum_of_contDiff_memLp hz hL2 s
  exact ne_top_of_le_ne_top (by simp) (sobolevENorm_le_of_isSobolevDatum hA)

/-! ## 6. Norm control -/

theorem norm_cyclesComponentDatum_le (m : ℕ) (s : ℝ) (hs : s ≤ (m : ℝ))
    (A : SmoothL2Field Space) (i : Fin 3) :
    ‖cyclesComponentDatum m s hs A i‖ ≤ ‖(iteratedBesselField m (componentField i A)).toLp‖ :=
  (realProjectionTo_norm_le s _).trans
    ((sobolevOrderLowering_norm_le _ _ _ _).trans (norm_integerSobolevDatum_le m _))

/-- The datum norm is controlled by the `L²` norms of the physical Bessel iterates
`(1 - (2π)^{-2} Δ)^m z_i`; `frequencyUnit ^ |s|` is the constant of the cycles-to-angular
normalization change (`Paper3.cyclesToAngularRealVector_norm_le`). -/
theorem norm_smoothAngularDatum_le (m : ℕ) (s : ℝ) (hs : s ≤ (m : ℝ)) (A : SmoothL2Field Space) :
    ‖smoothAngularDatum m s hs A‖ ≤ frequencyUnit ^ |s| *
      Real.sqrt (∑ i : Fin 3, ‖(iteratedBesselField m (componentField i A)).toLp‖ ^ 2) := by
  set v : RealVectorSobolev s := WithLp.toLp 2 (fun i => cyclesComponentDatum m s hs A i) with hv
  have h2 : ‖v‖ ≤
      Real.sqrt (∑ i : Fin 3, ‖(iteratedBesselField m (componentField i A)).toLp‖ ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg v)]
    apply Real.sqrt_le_sqrt
    rw [PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_le_sum
    intro i _
    have hi : ‖v.ofLp i‖ ≤ ‖(iteratedBesselField m (componentField i A)).toLp‖ :=
      norm_cyclesComponentDatum_le m s hs A i
    nlinarith [norm_nonneg (v.ofLp i)]
  exact (cyclesToAngularRealVector_norm_le s v).trans
    (mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg frequencyUnit_pos.le _))

theorem sobolevENorm_le_norm_smoothAngularDatum (m : ℕ) (s : ℝ) (hs : s ≤ (m : ℝ))
    (A : SmoothL2Field Space) :
    sobolevENorm s A.field ≤ ‖smoothAngularDatum m s hs A‖ₑ :=
  sobolevENorm_le_of_isSobolevDatum (smoothAngularDatum_isSobolevDatum m s hs A)

/-! ## 7. Physical-versus-datum derivative identification -/

/-- Taking a component and differentiating commute on smooth `L²` fields. -/
theorem componentField_directionalField (i : Fin 3) (A : SmoothL2Field Space) (v : Space) :
    componentField i (A.directionalField v) = (componentField i A).directionalField v := by
  apply field_ext
  funext x
  have hd : HasFDerivAt A.field (fderiv ℝ A.field x) x :=
    (A.smooth.differentiable (by simp) x).hasFDerivAt
  have hc : HasFDerivAt (fun y => (Complex.ofRealCLM.comp (EuclideanSpace.proj i)) (A.field y))
      ((Complex.ofRealCLM.comp (EuclideanSpace.proj i)).comp (fderiv ℝ A.field x)) x :=
    (Complex.ofRealCLM.comp (EuclideanSpace.proj i)).hasFDerivAt.comp x hd
  show (Complex.ofRealCLM.comp (EuclideanSpace.proj i)) (fderiv ℝ A.field x v) =
    fderiv ℝ (fun y => (Complex.ofRealCLM.comp (EuclideanSpace.proj i)) (A.field y)) x v
  rw [hc.fderiv]
  rfl

/-- **The shape of A02 unit U1b(iii), on the jet carrier.**  The angular datum of the
physical directional derivative `∂_v z` realizes exactly the distributional derivative of
the distribution realized by the angular datum of `z`.  This is
`Source.PhysicalSobolevDistribution.physicalDistribution_directionalField` (`:29`)
transported to the manuscript's normalization.

What this is *not* (`research/A02/COMPARISON.md:163-164` splits U1 into U1a and U1b, and
U1b into three parts):

* the derivative is `EulerLpTranslation.SmoothL2Field.directionalField v`, i.e.
  `fun x => fderiv ℝ z x v` on the **jet carrier**, not the upstream
  `spatialDerivative u t x`
  (`vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:59`), and it starts
  from a `SmoothL2Field`, not from `ClassicalSolutionR.sobolev`'s datum path
  (`Data.lean:643-645`) where U1b actually begins;
* U1b(i), the embedding `‖z‖_∞ ≤ C‖z‖_{H²}` on the angular carrier (= A01 unit **A1**),
  is untouched;
* U1b(ii), the order shift `‖∇v‖_{H²} ≤ ‖v‖_{H³}` on the angular datum carrier, is
  untouched: `norm_smoothAngularDatum_le` is a **one-sided** bound in the physical Bessel
  iterates, not a comparison of two datum norms. -/
theorem angularRealization_smoothAngularDatum_directional (m : ℕ) (s : ℝ) (hs : s ≤ (m : ℝ))
    (A : SmoothL2Field Space) (v : Space) (i : Fin 3) :
    angularRealization s ((smoothAngularDatum m s hs (A.directionalField v) i : FourierData)) =
      ∂_{v} (angularRealization s ((smoothAngularDatum m s hs A i : FourierData))) := by
  rw [angularRealization_smoothAngularDatum, angularRealization_smoothAngularDatum,
    componentField_directionalField, physicalDistribution_directionalField]

/-- Consequently `∂_v z` itself has an angular datum at every real order, and it is the
one produced by the same construction from the derivative field. -/
theorem exists_isSobolevDatum_fderiv {z : Space → Space} (hz : ContDiff ℝ ∞ z)
    (hL2 : ∀ n : ℕ, MemLp (iteratedFDeriv ℝ n z) 2 volume) (v : Space) (s : ℝ) :
    ∃ A : RealVectorSobolev s, IsSobolevDatum s (fun x => fderiv ℝ z x v) A :=
  ⟨smoothAngularDatum ⌈s⌉₊ s (Nat.le_ceil s) ((⟨z, hz, hL2⟩ : SmoothL2Field Space).directionalField v),
    smoothAngularDatum_isSobolevDatum ⌈s⌉₊ s (Nat.le_ceil s) _⟩

end NSFormalization.Section4.D01
