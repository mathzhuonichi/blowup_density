import NSFormalization.Paper3.AngularTameProduct
import NSFormalization.Section4.D01.SmoothDatum

/-!
# Reality of the completed angular Sobolev product and of angular order lowering

Support layer for task `A03` (`collaboration/tasks/A03.md`), the *product*
clauses of Lemma A.1 (`lem:calculus`,
`paper/sections/appendix-a-local-theory.tex:7-27`): `eq:Rproduct` (`:9-13`),
`eq:algebra` (`:16`) and `eq:tame` (`:17-18`).

## What is here, and why it is needed

`NSFormalization.Paper3.angularProduct`
(`formalization/NSFormalization/Paper3/AngularTameProduct.lean:61`) is the
completed bilinear multiplication of Sobolev data in the manuscript's angular
normalization, and `angularProduct_tame_bound` (`:76`) is `eq:Rproduct` for it.
Both live on the *ambient complex* datum space
`Source.RealSobolev.FourierData = Lp ℂ 2 volume`.

Section 4's data are **real**: `Contracts.V1.Data.IsSobolevDatum` takes its
values in `Paper3.RealVectorSobolev s`, whose components lie in the
conjugate-reflection-symmetric subspace `Source.RealSobolev.realSubspace`
(`02-preliminaries.tex:72`, `Source/RealSobolev.lean:118`).  Nothing in tree says
that this subspace is stable under `angularProduct`, and
`research/A03/COMPARISON.md:164-169` flags exactly this as "the one genuinely new
(easy) lemma".  `realSymmetry_angularProduct` below is that lemma, and
`mulDatum` is the resulting product of two *real* data.

The same question for `Paper3.angularOrderLowering` (`AngularTameProduct.lean:40`)
— the operator that supplies the `H²` low factor of `eq:Rproduct` — is answered by
`realSymmetry_angularOrderLowering`, and `lowerDatum` is the corresponding
operation on real data.

## Route

Reality is `realSymmetry h = h`.  `Paper3.cyclesToAngular_realSymmetry`
(`Paper3/AngularRealSobolev.lean:54`) already commutes the cycles-to-angular
transport with `realSymmetry`, and
`NSFormalization.Section4.D01.realSymmetry_sobolevOrderLowering`
(`Section4/D01/SmoothDatum.lean:208`) does the same for the cycles order
lowering, so both angular statements reduce to the cycles model.  For the
product the cycles statement `realSymmetry_sobolevProduct` is proved by density
from `Paper3.sobolevProduct_weightedFourierLp`: on the Schwartz core the
completed product *is* pointwise multiplication, and
`Source.RealSobolev.weightedFourierLp_conjugate` (`Source/RealSobolev.lean:72`)
turns conjugate reflection of a datum into pointwise conjugation of its Schwartz
function, under which pointwise multiplication is a ring homomorphism.

No new Fourier analysis is introduced: every statement below is an algebraic
consequence of the completed product and of conjugation.
-/

noncomputable section

open MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source NSFormalization.Source.RealSobolev
open NSFormalization.Source.FourierTameProduct
open NSFormalization.Section4.D01 (realSymmetry_sobolevOrderLowering)
open scoped ContDiff SchwartzMap ENNReal ComplexConjugate

namespace NSFormalization.Section4.A03

/-! ## 1. Conjugate reflection through the cycles-to-angular transport -/

/-- The inverse cycles-to-angular transport commutes with conjugate reflection.
Companion of `Paper3.cyclesToAngular_realSymmetry`. -/
theorem cyclesToAngular_symm_realSymmetry (s : ℝ) (h : FourierData) :
    (cyclesToAngular s).symm (realSymmetry h) = realSymmetry ((cyclesToAngular s).symm h) := by
  apply (cyclesToAngular s).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, ← cyclesToAngular_realSymmetry,
    ContinuousLinearEquiv.apply_symm_apply]

/-- `Paper3.angularOrderLowering` is multiplication by the real even symbol
`(1+‖ξ‖²)^{(r-s)/2}` read in the angular normalization, so it commutes with the
conjugate reflection of `02-preliminaries.tex:72`. -/
theorem realSymmetry_angularOrderLowering (s r : ℝ) (hrs : r ≤ s) (h : FourierData) :
    realSymmetry (angularOrderLowering s r hrs h) =
      angularOrderLowering s r hrs (realSymmetry h) := by
  change realSymmetry (cyclesToAngular r
      (sobolevOrderLowering s r hrs ((cyclesToAngular s).symm h))) =
    cyclesToAngular r (sobolevOrderLowering s r hrs ((cyclesToAngular s).symm (realSymmetry h)))
  rw [cyclesToAngular_realSymmetry, realSymmetry_sobolevOrderLowering,
    cyclesToAngular_symm_realSymmetry]

/-! ## 2. Reality of the completed product -/

/-- The completed **cycles** Sobolev product commutes with conjugate reflection.
Proved by density from `Paper3.sobolevProduct_weightedFourierLp`, on whose
Schwartz core the product is literal pointwise multiplication, together with
`Source.RealSobolev.weightedFourierLp_conjugate`. -/
theorem realSymmetry_sobolevProduct (m : ℕ) (hm : 2 ≤ m) (h k : SobolevHilbert m) :
    realSymmetry (sobolevProduct m hm h k) =
      sobolevProduct m hm (realSymmetry h) (realSymmetry k) := by
  refine (denseRange_weightedFourierLp m).induction_on h
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro φ
  refine (denseRange_weightedFourierLp m).induction_on k
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro ψ
  rw [sobolevProduct_weightedFourierLp, ← weightedFourierLp_conjugate,
    ← weightedFourierLp_conjugate, ← weightedFourierLp_conjugate,
    sobolevProduct_weightedFourierLp]
  congr 1
  ext x
  simp [schwartzProduct_apply, conjugateSchwartz_apply]

-- Needs more than the default: the `realSymmetry_sobolevProduct` rewrite unifies through
-- `SobolevHilbert s`, an `abbrev` for `Lp ℂ 2 volume`, and times out in `isDefEq` at 200 000.
set_option maxHeartbeats 400000 in
/-- The completed **angular** Sobolev product commutes with conjugate reflection. -/
theorem realSymmetry_angularProduct (m : ℕ) (hm : 2 ≤ m) (h k : FourierData) :
    realSymmetry (angularProduct m hm h k) =
      angularProduct m hm (realSymmetry h) (realSymmetry k) := by
  rw [angularProduct_apply, angularProduct_apply, cyclesToAngular_realSymmetry,
    realSymmetry_sobolevProduct, cyclesToAngular_symm_realSymmetry,
    cyclesToAngular_symm_realSymmetry]

/-- **Stability of the reality subspace under the completed product.**  This is
`research/A03/COMPARISON.md:164-169`'s "one genuinely new lemma". -/
theorem angularProduct_mem_realSubspace (m : ℕ) (hm : 2 ≤ m) (s : ℝ) {h k : FourierData}
    (hh : h ∈ realSubspace s) (hk : k ∈ realSubspace s) :
    angularProduct m hm h k ∈ realSubspace s :=
  (mem_realSubspace_iff s _).mpr <| by
    rw [realSymmetry_angularProduct, (mem_realSubspace_iff s h).mp hh,
      (mem_realSubspace_iff s k).mp hk]

theorem angularOrderLowering_mem_realSubspace (s r : ℝ) (hrs : r ≤ s) {h : FourierData}
    (hh : h ∈ realSubspace s) : angularOrderLowering s r hrs h ∈ realSubspace r :=
  (mem_realSubspace_iff r _).mpr <| by
    rw [realSymmetry_angularOrderLowering, (mem_realSubspace_iff s h).mp hh]

/-! ## 3. The two operations on real data -/

/-- `appendix-a-local-theory.tex:10`'s low factor `‖·‖_{H²}`: the order-`r`
datum obtained from an order-`s` real datum, `r ≤ s`.  It realizes the same
tempered distribution (`Paper3.angularRealization_orderLowering`), so it is the
order-`r` datum of the same physical field. -/
def lowerDatum (s r : ℝ) (hrs : r ≤ s) (A : RealSobolevHilbert s) : RealSobolevHilbert r :=
  ⟨angularOrderLowering s r hrs (A : FourierData),
    angularOrderLowering_mem_realSubspace s r hrs A.property⟩

@[simp] theorem coe_lowerDatum (s r : ℝ) (hrs : r ≤ s) (A : RealSobolevHilbert s) :
    ((lowerDatum s r hrs A : RealSobolevHilbert r) : FourierData) =
      angularOrderLowering s r hrs (A : FourierData) := rfl

/-- `appendix-a-local-theory.tex:9-11` eq:Rproduct: the completed product of two
real order-`m` data, `m ≥ 2`. -/
def mulDatum (m : ℕ) (hm : 2 ≤ m) (A B : RealSobolevHilbert (m : ℝ)) :
    RealSobolevHilbert (m : ℝ) :=
  ⟨angularProduct m hm (A : FourierData) (B : FourierData),
    angularProduct_mem_realSubspace m hm _ A.property B.property⟩

@[simp] theorem coe_mulDatum (m : ℕ) (hm : 2 ≤ m) (A B : RealSobolevHilbert (m : ℝ)) :
    ((mulDatum m hm A B : RealSobolevHilbert (m : ℝ)) : FourierData) =
      angularProduct m hm (A : FourierData) (B : FourierData) := rfl

/-! ## 4. Constants and norm bounds

Both constants below are `+ 1` versions of the products of in-tree constants.
The manuscript's `C_m` is fixed only up to the order and the fixed domain
(`appendix-a-local-theory.tex:10`), so a larger constant is still *a* constant of
`eq:Rproduct`; the `+ 1` buys strict positivity without needing positivity of
`Source.BesselH2Fourier.besselConstant`, of which only nonnegativity is proved in
tree (`Source/BesselH2Fourier.lean`). -/

/-- `appendix-a-local-theory.tex:10-11`, the constant `C_m` of `eq:Rproduct` in
the manuscript's angular normalization.  It is
`Paper3.sobolevTameConstant m = 2^{m-1}·besselConstant`
(`Paper3/CompleteTameProduct.lean:12`, the cycles constant) multiplied by the
normalization factor `(2π)^{2m+2}` of `angularProduct_tame_bound`
(`Paper3/AngularTameProduct.lean:76`), plus one.  `Source.frequencyUnit` is `2π`. -/
def scalarTameConst (m : ℕ) : ℝ :=
  frequencyUnit ^ (2 * (m : ℝ) + 2) * sobolevTameConstant m + 1

theorem scalarTameConst_pos (m : ℕ) : 0 < scalarTameConst m := by
  have h1 : (0:ℝ) ≤ frequencyUnit ^ (2 * (m : ℝ) + 2) :=
    Real.rpow_nonneg frequencyUnit_pos.le _
  have h3 : (0:ℝ) ≤ frequencyUnit ^ (2 * (m : ℝ) + 2) * sobolevTameConstant m :=
    mul_nonneg h1 (sobolevTameConstant_nonneg m)
  simp only [scalarTameConst]
  linarith

/-- The price of lowering the order from `s` to `r` in the angular
normalization: `(2π)^{|r|}` for the transport in and `(2π)^{|s|}` for the
transport out, the cycles order lowering itself being a contraction
(`Paper3.sobolevOrderLowering_norm_le`). -/
def lowerConst (s r : ℝ) : ℝ := frequencyUnit ^ |r| * frequencyUnit ^ |s| + 1

theorem lowerConst_pos (s r : ℝ) : 0 < lowerConst s r := by
  have h1 : (0:ℝ) ≤ frequencyUnit ^ |r| * frequencyUnit ^ |s| :=
    mul_nonneg (Real.rpow_nonneg frequencyUnit_pos.le _)
      (Real.rpow_nonneg frequencyUnit_pos.le _)
  simp only [lowerConst]
  linarith

theorem norm_lowerDatum_le (s r : ℝ) (hrs : r ≤ s) (A : RealSobolevHilbert s) :
    ‖lowerDatum s r hrs A‖ ≤ lowerConst s r * ‖A‖ := by
  have h1 : ‖angularOrderLowering s r hrs (A : FourierData)‖ ≤
      frequencyUnit ^ |r| * ‖sobolevOrderLowering s r hrs ((cyclesToAngular s).symm A)‖ :=
    cyclesToAngular_norm_le r _
  have h2 : ‖sobolevOrderLowering s r hrs ((cyclesToAngular s).symm (A : FourierData))‖ ≤
      frequencyUnit ^ |s| * ‖(A : FourierData)‖ :=
    (sobolevOrderLowering_norm_le s r hrs _).trans (cyclesToAngular_symm_norm_le s _)
  have hr : (0:ℝ) ≤ frequencyUnit ^ |r| := Real.rpow_nonneg frequencyUnit_pos.le _
  have hs : (0:ℝ) ≤ frequencyUnit ^ |s| := Real.rpow_nonneg frequencyUnit_pos.le _
  have hA : (0:ℝ) ≤ ‖(A : FourierData)‖ := norm_nonneg _
  show ‖angularOrderLowering s r hrs (A : FourierData)‖ ≤ lowerConst s r * ‖(A : FourierData)‖
  simp only [lowerConst]
  nlinarith [mul_le_mul_of_nonneg_left h2 hr]

/-- `appendix-a-local-theory.tex:9-11` eq:Rproduct on real data, with the
constant of the manuscript and the low factors at order two. -/
theorem norm_mulDatum_le (m : ℕ) (hm : 2 ≤ m) (hm2 : (2:ℝ) ≤ (m:ℝ))
    (A B : RealSobolevHilbert (m : ℝ)) :
    ‖mulDatum m hm A B‖ ≤ scalarTameConst m *
      (‖lowerDatum (m : ℝ) 2 hm2 B‖ * ‖A‖ + ‖lowerDatum (m : ℝ) 2 hm2 A‖ * ‖B‖) := by
  have hb : (0:ℝ) ≤ ‖lowerDatum (m : ℝ) 2 hm2 B‖ * ‖A‖ +
      ‖lowerDatum (m : ℝ) 2 hm2 A‖ * ‖B‖ := by positivity
  refine (angularProduct_tame_bound m hm (A : FourierData) (B : FourierData)).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ hb
  simp only [scalarTameConst]
  linarith

end NSFormalization.Section4.A03
