import NSFormalization.Section4.A03.RealAngularProduct
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# `eq:Rproduct` and `eq:algebra` for physical real scalar fields on `R³`

Task `A03` (`collaboration/tasks/A03.md`), Lemma A.1 (`lem:calculus`,
`paper/sections/appendix-a-local-theory.tex:7-27`), first clause of
`eq:Rproduct` (`:9-11`)

  `‖vw‖_{H^m} ≤ C_m(‖v‖_{H²}‖w‖_{H^m} + ‖w‖_{H²}‖v‖_{H^m})`,  integer `m ≥ 2`,

and `eq:algebra` (`:16`), on the **datum carrier** of
`verification/Contracts/V1/Data.lean`: `vw` is the literal pointwise product of
two physical real scalar fields, and both sides are the datum norms of
`01-introduction.tex:94` in the manuscript's angular normalization.

## The three steps

1. *Datum uniqueness* (D01 unit **L1**).  `Paper3.angularRealization_injective`
   (`Paper3/AngularFourierDilation.lean:203`) makes the order-`s` datum of a
   physical field unique, so the infimum `scalarSobolevENorm` is attained and
   equals the norm of *the* datum.  Without this the tame bound could not be
   read back as a bound on the infimum: the low factor produced by
   `Paper3.angularOrderLowering` is *a* order-two datum, and only uniqueness
   makes its norm equal to `‖·‖_{H²}`.
2. *The physical identification*.  `Paper3.angularRealization_product`
   (`Paper3/AngularTameProduct.lean:174`) says the completed product realizes
   the pointwise product of the two **bounded continuous representatives**.
   `representative_ae` below turns that into the pointwise product of the two
   *physical fields*, by the fundamental lemma of the calculus of variations
   (`MeasureTheory.ae_eq_of_integral_contDiff_smul_eq`).  This is where the
   `MemLp _ 2` half of the admissibility predicate is used: it makes the field
   locally integrable, which is what the fundamental lemma needs, and it is also
   what rules out the junk-`0` totalization recorded at
   `Contracts/V1/Data.lean:148-155`.
3. *The estimate*, `NSFormalization.Section4.A03.norm_mulDatum_le`, which is
   `Paper3.angularProduct_tame_bound` (`Paper3/AngularTameProduct.lean:76`) with
   the reality of the product added.

## Paper-versus-Lean

The manuscript's `C_m` is any constant depending only on the order and the fixed
domain (`appendix-a-local-theory.tex:10`).  `scalarTameConst` is the in-tree
cycles constant `2^{m-1}·besselConstant` times the angular normalization factor
`(2π)^{2m+2}`, plus one; `algebraConst` multiplies it once more by the price
`(2π)^{k}·(2π)^{2}` of reading an `H²` norm off an `H^k` datum.  See
`research/A03/ATTEMPTS_TAME.md` for the `(2π)` bookkeeping.
-/

noncomputable section

open MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source NSFormalization.Source.RealSobolev
open NSFormalization.Source.FourierTameProduct
open scoped ContDiff SchwartzMap ENNReal ComplexConjugate

namespace NSFormalization.Section4.A03

/-! ## 1. The scalar datum carrier

`Contracts.V1.Data` supplies `IsSobolevDatum` and `sobolevENorm` for real
**three-vector** fields only; `eq:Rproduct`'s `vw` is a product of scalars.  The
two definitions below are the scalar case of the same pairing, i.e. literally one
component of `Data.IsSobolevDatum`
(`NSFormalization.Section4.D01.IsSobolevDatum` is its verbatim restatement). -/

/-- `01-introduction.tex:91,94`: `A` is *the* order-`s` angular real Sobolev
datum of the physical scalar `a`.  One component of `Data.IsSobolevDatum`. -/
def IsScalarSobolevDatum (s : ℝ) (a : Space → ℝ) (A : RealSobolevHilbert s) : Prop :=
  ∀ ψ : SchwartzMap Space ℂ,
    angularRealization s (A : FourierData) ψ = ∫ x : Space, ψ x * ((a x : ℝ) : ℂ)

/-- `01-introduction.tex:94`, `‖a‖_{H^s(R³)}` for a physical scalar: the norm of
the order-`s` datum, and `⊤` (the empty infimum) when `a` has none. -/
def scalarSobolevENorm (s : ℝ) (a : Space → ℝ) : ℝ≥0∞ :=
  ⨅ A : {A : RealSobolevHilbert s // IsScalarSobolevDatum s a A}, ‖A.1‖ₑ

/-- The admissible scalar class at integer order `m`: genuinely square
integrable, with a finite order-`m` norm.  `MemLp` is what excludes the junk
totalization of `Contracts/V1/Data.lean:148-155`. -/
def MemHmScalar (m : ℕ) (a : Space → ℝ) : Prop :=
  MemLp a 2 volume ∧ scalarSobolevENorm (m : ℝ) a ≠ ⊤

/-- **D01 unit L1, scalar case.**  A physical scalar has at most one order-`s`
datum, because `Paper3.angularRealization` is injective. -/
theorem IsScalarSobolevDatum.unique {s : ℝ} {a : Space → ℝ} {A B : RealSobolevHilbert s}
    (hA : IsScalarSobolevDatum s a A) (hB : IsScalarSobolevDatum s a B) : A = B :=
  Subtype.ext (angularRealization_injective s (by ext ψ; rw [hA ψ, hB ψ]))

theorem scalarSobolevENorm_le {s : ℝ} {a : Space → ℝ} {A : RealSobolevHilbert s}
    (hA : IsScalarSobolevDatum s a A) : scalarSobolevENorm s a ≤ ‖A‖ₑ :=
  iInf_le (fun A : {A : RealSobolevHilbert s // IsScalarSobolevDatum s a A} => ‖A.1‖ₑ) ⟨A, hA⟩

/-- The infimum defining `scalarSobolevENorm` is attained at the unique datum. -/
theorem scalarSobolevENorm_eq {s : ℝ} {a : Space → ℝ} {A : RealSobolevHilbert s}
    (hA : IsScalarSobolevDatum s a A) : scalarSobolevENorm s a = ‖A‖ₑ := by
  refine le_antisymm (scalarSobolevENorm_le hA) (le_iInf ?_)
  rintro ⟨B, hB⟩
  rw [hA.unique hB]

/-- A finite order-`s` norm means the datum exists: the empty infimum is `⊤`. -/
theorem exists_scalarSobolevDatum {s : ℝ} {a : Space → ℝ} (h : scalarSobolevENorm s a ≠ ⊤) :
    ∃ A : RealSobolevHilbert s, IsScalarSobolevDatum s a A := by
  by_contra hc
  refine h ?_
  have : IsEmpty {A : RealSobolevHilbert s // IsScalarSobolevDatum s a A} :=
    ⟨fun A => hc ⟨A.1, A.2⟩⟩
  rw [scalarSobolevENorm, iInf_of_isEmpty, sInf_empty]

/-- Order lowering of the datum, at the level of the physical field:
`lowerDatum` realizes the same distribution. -/
theorem IsScalarSobolevDatum.lower {s r : ℝ} (hrs : r ≤ s) {a : Space → ℝ}
    {A : RealSobolevHilbert s} (hA : IsScalarSobolevDatum s a A) :
    IsScalarSobolevDatum r a (lowerDatum s r hrs A) := by
  intro ψ
  show angularRealization r (angularOrderLowering s r hrs (A : FourierData)) ψ = _
  rw [angularRealization_orderLowering]
  exact hA ψ

/-! ## 2. The physical identification

`appendix-a-local-theory.tex:49-50`, "Absolute Fourier convergence also proves
the `L^∞` estimate": every `H^s` datum with `s ≥ 2` has a bounded continuous
representative.  The lemmas here say that this representative *is* the physical
field, almost everywhere — which is what turns the abstract completed product
into pointwise multiplication of fields. -/

/-- Fundamental lemma of the calculus of variations, in the Schwartz-pairing
form used by `Contracts.V1.Data.IsSobolevDatum`: two locally integrable
functions pairing equally with every Schwartz test agree almost everywhere.
Mathlib's `ae_eq_of_integral_contDiff_smul_eq` quantifies over smooth compactly
supported *real* test functions; `HasCompactSupport.toSchwartzMap` converts
those into Schwartz maps. -/
theorem ae_eq_of_schwartz_pairing {f g : Space → ℂ}
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume)
    (h : ∀ ψ : SchwartzMap Space ℂ, ∫ x : Space, ψ x * f x = ∫ x : Space, ψ x * g x) :
    ∀ᵐ x ∂(volume : Measure Space), f x = g x := by
  refine ae_eq_of_integral_contDiff_smul_eq hf hg ?_
  intro φ hφ hcs
  have hs : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hcs.comp_left rfl
  have hd : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ) := Complex.ofRealCLM.contDiff.comp hφ
  simpa [Complex.real_smul] using h (hs.toSchwartzMap hd)

theorem locallyIntegrable_ofReal {a : Space → ℝ} (ha : MemLp a 2 volume) :
    LocallyIntegrable (fun x => ((a x : ℝ) : ℂ)) volume :=
  (Complex.ofRealCLM.comp_memLp' ha).locallyIntegrable (by norm_num)

/-- The bounded continuous representative of the order-`s` datum of a locally
integrable physical scalar agrees with that scalar almost everywhere.  Local
integrability is the exact hypothesis the fundamental lemma needs, and it is what
rules out the junk-`0` totalization of `Contracts/V1/Data.lean:148-155`; on the
admissible class `MemHmScalar` it comes from `MemLp _ 2` through
`locallyIntegrable_ofReal`. -/
theorem representative_ae {s : ℝ} (hs : 2 ≤ s) {a : Space → ℝ}
    (ha : LocallyIntegrable (fun x => ((a x : ℝ) : ℂ)) volume)
    {A : RealSobolevHilbert s} (hA : IsScalarSobolevDatum s a A) :
    (fun x => angularBoundedRepresentative s hs (A : FourierData) x) =ᵐ[volume]
      fun x => ((a x : ℝ) : ℂ) := by
  refine ae_eq_of_schwartz_pairing ?_ ha ?_
  · exact (map_continuous (angularBoundedRepresentative s hs (A : FourierData))).locallyIntegrable
  · intro ψ
    rw [← angularRealization_boundedRepresentative s hs, hA ψ]

/-- **The completed product is the physical product.**  `mulDatum` is the
order-`m` datum of the literal pointwise product `a·b`. -/
theorem isScalarSobolevDatum_mul (m : ℕ) (hm : 2 ≤ m) {a b : Space → ℝ}
    (ha : LocallyIntegrable (fun x => ((a x : ℝ) : ℂ)) volume)
    (hb : LocallyIntegrable (fun x => ((b x : ℝ) : ℂ)) volume)
    {A B : RealSobolevHilbert (m : ℝ)} (hA : IsScalarSobolevDatum (m : ℝ) a A)
    (hB : IsScalarSobolevDatum (m : ℝ) b B) :
    IsScalarSobolevDatum (m : ℝ) (fun x => a x * b x) (mulDatum m hm A B) := by
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  intro ψ
  show angularRealization (m : ℝ)
    (angularProduct m hm (A : FourierData) (B : FourierData)) ψ = _
  rw [angularRealization_product m hm (A : FourierData) (B : FourierData) ψ]
  refine integral_congr_ae ?_
  filter_upwards [representative_ae hm2 ha hA, representative_ae hm2 hb hB] with x h1 h2
  rw [h1, h2]
  push_cast
  ring

/-- Sums: the datum of `a + b` is the sum of the data.  Proved through the
bounded representatives, which are linear in the datum, so no integrability of
`ψ·a` has to be established separately. -/
theorem isScalarSobolevDatum_add {s : ℝ} (hs : 2 ≤ s) {a b : Space → ℝ}
    (ha : LocallyIntegrable (fun x => ((a x : ℝ) : ℂ)) volume)
    (hb : LocallyIntegrable (fun x => ((b x : ℝ) : ℂ)) volume)
    {A B : RealSobolevHilbert s} (hA : IsScalarSobolevDatum s a A)
    (hB : IsScalarSobolevDatum s b B) :
    IsScalarSobolevDatum s (fun x => a x + b x) (A + B) := by
  intro ψ
  show angularRealization s ((A : FourierData) + (B : FourierData)) ψ = _
  rw [angularRealization_boundedRepresentative s hs, map_add]
  refine integral_congr_ae ?_
  filter_upwards [representative_ae hs ha hA, representative_ae hs hb hB] with x h1 h2
  show ψ x * (angularBoundedRepresentative s hs (A : FourierData) x +
    angularBoundedRepresentative s hs (B : FourierData) x) = _
  rw [h1, h2]
  push_cast
  ring

theorem isScalarSobolevDatum_sub {s : ℝ} (hs : 2 ≤ s) {a b : Space → ℝ}
    (ha : LocallyIntegrable (fun x => ((a x : ℝ) : ℂ)) volume)
    (hb : LocallyIntegrable (fun x => ((b x : ℝ) : ℂ)) volume)
    {A B : RealSobolevHilbert s} (hA : IsScalarSobolevDatum s a A)
    (hB : IsScalarSobolevDatum s b B) :
    IsScalarSobolevDatum s (fun x => a x - b x) (A - B) := by
  intro ψ
  show angularRealization s ((A : FourierData) - (B : FourierData)) ψ = _
  rw [angularRealization_boundedRepresentative s hs, map_sub]
  refine integral_congr_ae ?_
  filter_upwards [representative_ae hs ha hA, representative_ae hs hb hB] with x h1 h2
  show ψ x * (angularBoundedRepresentative s hs (A : FourierData) x -
    angularBoundedRepresentative s hs (B : FourierData) x) = _
  rw [h1, h2]
  push_cast
  ring

/-! ## 2b. Scalar multiplication of Sobolev data (promoted from A04/MomentumDatum in lane 109) -/

/-- **The datum of a real scalar multiple, scalar case.**  `c • A` is the order-`s`
datum of `c · a`. -/
theorem isScalarSobolevDatum_smul {s : ℝ} (c : ℝ) {a : Space → ℝ} {A : RealSobolevHilbert s}
    (hA : IsScalarSobolevDatum s a A) :
    IsScalarSobolevDatum s (fun x => c * a x) (c • A) := by
  intro ψ
  show angularRealization s ((c • A : RealSobolevHilbert s) : FourierData) ψ = _
  have hco : ((c • A : RealSobolevHilbert s) : FourierData)
      = c • ((A : RealSobolevHilbert s) : FourierData) := rfl
  rw [hco, LinearMapClass.map_smul_of_tower, smul_apply, hA ψ, ← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Complex.real_smul]
  push_cast
  ring

/-- **The datum of a negation, scalar case.**  `-A` is the order-`s` datum of `-a`
(`c = -1`). -/
theorem isScalarSobolevDatum_neg {s : ℝ} {a : Space → ℝ} {A : RealSobolevHilbert s}
    (hA : IsScalarSobolevDatum s a A) : IsScalarSobolevDatum s (fun x => - a x) (- A) := by
  simpa using isScalarSobolevDatum_smul (-1 : ℝ) hA

/-! ## 3. The estimates -/

-- Needs more than the default: the `ENNReal.ofReal_add` step re-elaborates the datum norms
-- through `SobolevHilbert s`, an `abbrev` for `Lp ℂ 2 volume`, and times out in `isDefEq`.
set_option maxHeartbeats 1200000 in
/-- **`appendix-a-local-theory.tex:9-11` eq:Rproduct, first clause**, for
physical real scalar fields on `R³`:
`‖ab‖_{H^m} ≤ C_m(‖a‖_{H²}‖b‖_{H^m} + ‖b‖_{H²}‖a‖_{H^m})` for every integer
`m ≥ 2`, with `C_m` independent of the fields and of their supports. -/
theorem tameProductScalar (m : ℕ) (hm : 2 ≤ m) {a b : Space → ℝ}
    (ha : MemHmScalar m a) (hb : MemHmScalar m b) :
    scalarSobolevENorm (m : ℝ) (fun x => a x * b x) ≤
      ENNReal.ofReal (scalarTameConst m) *
        (scalarSobolevENorm 2 a * scalarSobolevENorm (m : ℝ) b +
          scalarSobolevENorm 2 b * scalarSobolevENorm (m : ℝ) a) := by
  have hm2 : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  obtain ⟨A, hA⟩ := exists_scalarSobolevDatum ha.2
  obtain ⟨B, hB⟩ := exists_scalarSobolevDatum hb.2
  rw [scalarSobolevENorm_eq hA, scalarSobolevENorm_eq hB, scalarSobolevENorm_eq (hA.lower hm2),
    scalarSobolevENorm_eq (hB.lower hm2)]
  refine (scalarSobolevENorm_le (isScalarSobolevDatum_mul m hm
    (locallyIntegrable_ofReal ha.1) (locallyIntegrable_ofReal hb.1) hA hB)).trans ?_
  have hreal := norm_mulDatum_le m hm hm2 A B
  calc ‖mulDatum m hm A B‖ₑ
      = ENNReal.ofReal ‖mulDatum m hm A B‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (scalarTameConst m *
          (‖lowerDatum (m : ℝ) 2 hm2 B‖ * ‖A‖ + ‖lowerDatum (m : ℝ) 2 hm2 A‖ * ‖B‖)) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (scalarTameConst m) *
          (‖lowerDatum (m : ℝ) 2 hm2 A‖ₑ * ‖B‖ₑ + ‖lowerDatum (m : ℝ) 2 hm2 B‖ₑ * ‖A‖ₑ) := by
        rw [ENNReal.ofReal_mul (scalarTameConst_pos m).le,
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_mul (norm_nonneg _),
          ofReal_norm, ofReal_norm, ofReal_norm, ofReal_norm, add_comm]

/-- `appendix-a-local-theory.tex:14-15`, "`‖·‖_{H²} ≤ ‖·‖_{H^k}` for `k ≥ 2`",
in the manuscript's angular normalization, where reading an `H²` norm off an
`H^k` datum costs the fixed factor `lowerConst`. -/
theorem scalarSobolevENorm_two_le (m : ℕ) (hm2 : (2:ℝ) ≤ (m:ℝ)) (a : Space → ℝ) :
    scalarSobolevENorm 2 a ≤
      ENNReal.ofReal (lowerConst (m : ℝ) 2) * scalarSobolevENorm (m : ℝ) a := by
  by_cases h : scalarSobolevENorm (m : ℝ) a = ⊤
  · rw [h, ENNReal.mul_top (by simpa using lowerConst_pos (m : ℝ) 2)]
    exact le_top
  obtain ⟨A, hA⟩ := exists_scalarSobolevDatum h
  rw [scalarSobolevENorm_eq hA, scalarSobolevENorm_eq (hA.lower hm2)]
  calc ‖lowerDatum (m : ℝ) 2 hm2 A‖ₑ
      = ENNReal.ofReal ‖lowerDatum (m : ℝ) 2 hm2 A‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (lowerConst (m : ℝ) 2 * ‖A‖) :=
        ENNReal.ofReal_le_ofReal (norm_lowerDatum_le (m : ℝ) 2 hm2 A)
    _ = ENNReal.ofReal (lowerConst (m : ℝ) 2) * ‖A‖ₑ := by
        rw [ENNReal.ofReal_mul (lowerConst_pos _ _).le, ofReal_norm]

/-- `appendix-a-local-theory.tex:16` eq:algebra's constant. -/
def algebraConst (m : ℕ) : ℝ := 2 * scalarTameConst m * lowerConst (m : ℝ) 2

theorem algebraConst_pos (m : ℕ) : 0 < algebraConst m :=
  mul_pos (by linarith [scalarTameConst_pos m]) (lowerConst_pos _ _)

/-- **`appendix-a-local-theory.tex:14-16` eq:algebra** for physical real scalar
fields: `‖ab‖_{H^k} ≤ C_k‖a‖_{H^k}‖b‖_{H^k}` for every integer `k ≥ 2`.  The
manuscript states it for `k ≥ 3`; the proof — `eq:Rproduct` plus
`‖·‖_{H²} ≤ ‖·‖_{H^k}` — needs only `k ≥ 2`, so that is what is proved. -/
theorem algebraProductScalar (m : ℕ) (hm : 2 ≤ m) {a b : Space → ℝ}
    (ha : MemHmScalar m a) (hb : MemHmScalar m b) :
    scalarSobolevENorm (m : ℝ) (fun x => a x * b x) ≤
      ENNReal.ofReal (algebraConst m) *
        (scalarSobolevENorm (m : ℝ) a * scalarSobolevENorm (m : ℝ) b) := by
  have hm2 : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  refine (tameProductScalar m hm ha hb).trans ?_
  have h1 := scalarSobolevENorm_two_le m hm2 a
  have h2 := scalarSobolevENorm_two_le m hm2 b
  calc ENNReal.ofReal (scalarTameConst m) *
        (scalarSobolevENorm 2 a * scalarSobolevENorm (m : ℝ) b +
          scalarSobolevENorm 2 b * scalarSobolevENorm (m : ℝ) a)
      ≤ ENNReal.ofReal (scalarTameConst m) *
        ((ENNReal.ofReal (lowerConst (m : ℝ) 2) * scalarSobolevENorm (m : ℝ) a) *
            scalarSobolevENorm (m : ℝ) b +
          (ENNReal.ofReal (lowerConst (m : ℝ) 2) * scalarSobolevENorm (m : ℝ) b) *
            scalarSobolevENorm (m : ℝ) a) := by gcongr
    _ = ENNReal.ofReal (algebraConst m) *
        (scalarSobolevENorm (m : ℝ) a * scalarSobolevENorm (m : ℝ) b) := by
        rw [algebraConst, ENNReal.ofReal_mul (by linarith [scalarTameConst_pos m]),
          ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
        ring

end NSFormalization.Section4.A03
