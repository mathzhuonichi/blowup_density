import NSFormalization.Section4.A03.ScalarTameProduct
import NSFormalization.Section4.A03.SmoothJets

/-!
# `eq:Rproduct` componentwise: real three-vector fields on `R³`

Task `A03`, Lemma A.1 (`lem:calculus`,
`paper/sections/appendix-a-local-theory.tex:7-27`) at `:50`, "The argument
applies componentwise to vectors and tensors".

`Contracts.V1.Data.sobolevENorm` measures a real three-vector field by the
Euclidean (`PiLp 2`) norm of its datum, i.e. by "summing the squared component
norms" (`01-introduction.tex:103`).  This module connects that quantity to the
scalar quantity of `ScalarTameProduct.lean` in the only two ways the estimates
need — a component is dominated by the whole field, and the whole field is
dominated by the sum of its components — and then transports `eq:Rproduct` to
the product `a·w` of a physical scalar with a physical three-vector, the shape
every Section 4 nonlinearity has.

`NSFormalization.Section4.D01.IsSobolevDatum` and `...sobolevENorm`
(`Section4/D01/SmoothDatum.lean:237,306`) are the verbatim restatements of the
contract's vector notions; they are used here because the `NSFormalization`
package cannot import `Contracts`.

## The dimensional factor

Passing between the Euclidean assembly and the sum of the three components costs
a factor of at most `3`, which is absorbed into the constants.
`appendix-a-local-theory.tex:10` allows this: `C_m` depends only on the order and
on the fixed domain `R³`, never on the field or its support.
-/

noncomputable section

open MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source NSFormalization.Source.RealSobolev
open NSFormalization.Section4.D01 (IsSobolevDatum sobolevENorm sobolevENorm_le_of_isSobolevDatum)
open scoped ContDiff SchwartzMap ENNReal

namespace NSFormalization.Section4.A03

/-! ## 1. The vector datum carrier -/

/-- The admissible three-vector class at integer order `m`
(`02-preliminaries.tex:29-30`): genuinely square integrable, with a finite
order-`m` norm. -/
def MemHmVector (m : ℕ) (z : Space → Space) : Prop :=
  MemLp z 2 volume ∧ sobolevENorm (m : ℝ) z ≠ ⊤

/-- A vector datum is exactly the triple of the scalar data of the components:
`Data.IsSobolevDatum` quantifies over `i` and then over the Schwartz test, which
is componentwise `IsScalarSobolevDatum`.  Definitional. -/
theorem isSobolevDatum_iff (s : ℝ) (z : Space → Space) (A : RealVectorSobolev s) :
    IsSobolevDatum s z A ↔ ∀ i : Fin 3, IsScalarSobolevDatum s (fun x => z x i) (A i) :=
  Iff.rfl

/-- Component extraction, the left-to-right half of `isSobolevDatum_iff`. -/
theorem IsSobolevDatum.component {s : ℝ} {z : Space → Space} {A : RealVectorSobolev s}
    (hA : IsSobolevDatum s z A) (i : Fin 3) :
    IsScalarSobolevDatum s (fun x => z x i) (A i) := hA i

/-- **D01 unit L1, vector case.**  Componentwise from the scalar uniqueness. -/
theorem IsSobolevDatum.unique {s : ℝ} {z : Space → Space} {A B : RealVectorSobolev s}
    (hA : IsSobolevDatum s z A) (hB : IsSobolevDatum s z B) : A = B := by
  have hb : WithLp.ofLp A = WithLp.ofLp B :=
    funext fun i => IsScalarSobolevDatum.unique (IsSobolevDatum.component hA i)
      (IsSobolevDatum.component hB i)
  simpa using congrArg (WithLp.toLp 2) hb

theorem sobolevENorm_eq {s : ℝ} {z : Space → Space} {A : RealVectorSobolev s}
    (hA : IsSobolevDatum s z A) : sobolevENorm s z = ‖A‖ₑ := by
  refine le_antisymm (sobolevENorm_le_of_isSobolevDatum hA) (le_iInf ?_)
  rintro ⟨B, hB⟩
  rw [IsSobolevDatum.unique hA hB]

theorem exists_sobolevDatum {s : ℝ} {z : Space → Space} (h : sobolevENorm s z ≠ ⊤) :
    ∃ A : RealVectorSobolev s, IsSobolevDatum s z A := by
  by_contra hc
  refine h ?_
  have : IsEmpty {A : RealVectorSobolev s // IsSobolevDatum s z A} := ⟨fun A => hc ⟨A.1, A.2⟩⟩
  rw [sobolevENorm, iInf_of_isEmpty, sInf_empty]

/-! ## 2. Components versus the Euclidean assembly -/

theorem norm_le_sum_components {s : ℝ} (A : RealVectorSobolev s) : ‖A‖ ≤ ∑ i : Fin 3, ‖A i‖ := by
  rw [PiLp.norm_eq_of_L2]
  have h : ∑ i : Fin 3, ‖A i‖ ^ 2 ≤ (∑ i : Fin 3, ‖A i‖) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => norm_nonneg (A i))
  calc Real.sqrt (∑ i : Fin 3, ‖A i‖ ^ 2) ≤ Real.sqrt ((∑ i : Fin 3, ‖A i‖) ^ 2) :=
        Real.sqrt_le_sqrt h
    _ = ∑ i : Fin 3, ‖A i‖ := Real.sqrt_sq (Finset.sum_nonneg fun i _ => norm_nonneg _)

/-- `01-introduction.tex:103`: each component of a three-vector field is
dominated by the field.  Holds with no hypothesis, because the right-hand side is
`⊤` when `z` has no order-`s` datum. -/
theorem scalarSobolevENorm_component_le (s : ℝ) (z : Space → Space) (i : Fin 3) :
    scalarSobolevENorm s (fun x => z x i) ≤ sobolevENorm s z := by
  refine le_iInf ?_
  rintro ⟨A, hA⟩
  exact (scalarSobolevENorm_le (IsSobolevDatum.component hA i)).trans (by
    simpa using ENNReal.ofReal_le_ofReal (PiLp.norm_apply_le A i))

/-- `01-introduction.tex:103` in the other direction, with the dimensional factor
implicit in the sum. -/
theorem sobolevENorm_le_sum_components (s : ℝ) (z : Space → Space) :
    sobolevENorm s z ≤ ∑ i : Fin 3, scalarSobolevENorm s (fun x => z x i) := by
  by_cases h : ∃ i : Fin 3, scalarSobolevENorm s (fun x => z x i) = ⊤
  · obtain ⟨i, hi⟩ := h
    have htop : ∑ i : Fin 3, scalarSobolevENorm s (fun x => z x i) = ⊤ :=
      eq_top_iff.mpr (le_trans (le_of_eq hi.symm)
        (Finset.single_le_sum (f := fun i : Fin 3 => scalarSobolevENorm s (fun x => z x i))
          (fun _ _ => by simp) (Finset.mem_univ i)))
    rw [htop]
    exact le_top
  simp only [not_exists] at h
  choose A hA using fun i : Fin 3 => exists_scalarSobolevDatum (h i)
  have hdat : IsSobolevDatum s z (WithLp.toLp 2 A) := fun i => hA i
  refine (sobolevENorm_le_of_isSobolevDatum hdat).trans ?_
  have hr : ‖(WithLp.toLp 2 A : RealVectorSobolev s)‖ ≤ ∑ i : Fin 3, ‖A i‖ :=
    norm_le_sum_components _
  calc ‖(WithLp.toLp 2 A : RealVectorSobolev s)‖ₑ
      = ENNReal.ofReal ‖(WithLp.toLp 2 A : RealVectorSobolev s)‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (∑ i : Fin 3, ‖A i‖) := ENNReal.ofReal_le_ofReal hr
    _ = ∑ i : Fin 3, ‖A i‖ₑ := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg (A i))]
        exact Finset.sum_congr rfl fun i _ => ofReal_norm _
    _ = ∑ i : Fin 3, scalarSobolevENorm s (fun x => z x i) :=
        Finset.sum_congr rfl fun i _ => (scalarSobolevENorm_eq (hA i)).symm

theorem MemHmVector.component {m : ℕ} {z : Space → Space} (h : MemHmVector m z) (i : Fin 3) :
    MemHmScalar m (fun x => z x i) :=
  ⟨(EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' h.1,
    ne_top_of_le_ne_top h.2 (scalarSobolevENorm_component_le _ _ i)⟩

/-! ## 3. Vector sums and order lowering

The hypothesis of the two datum-algebra lemmas is **componentwise local
integrability**, not `MemLp _ 2`.  That is the exact hypothesis the fundamental
lemma of the calculus of variations needs, and it is what the columns of
`u ⊗ u` have: a product of two `L²` factors is `L¹` (`MemLp.integrable_mul`),
hence locally integrable, while it need not itself be `L²`. -/

/-- Componentwise local integrability of a physical three-vector field: the
hypothesis under which an order-`s` datum determines the field. -/
def LocIntField (F : Space → Space) : Prop :=
  ∀ i : Fin 3, LocallyIntegrable (fun x => ((F x i : ℝ) : ℂ)) volume

theorem locIntField_of_memLp {F : Space → Space} (h : MemLp F 2 volume) : LocIntField F :=
  fun i => locallyIntegrable_ofReal ((EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' h)

/-- The product of an `L²` scalar with an `L²` three-vector field is `L¹`, hence
locally integrable, in every component. -/
theorem locIntField_smul {a : Space → ℝ} {w : Space → Space}
    (ha : MemLp a 2 volume) (hw : MemLp w 2 volume) : LocIntField (fun x => a x • w x) := by
  intro i
  have hai : MemLp (fun x => ((a x : ℝ) : ℂ)) 2 volume := Complex.ofRealCLM.comp_memLp' ha
  have hwi : MemLp (fun x => ((w x i : ℝ) : ℂ)) 2 volume :=
    Complex.ofRealCLM.comp_memLp' ((EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hw)
  have hint : Integrable (fun x => ((a x : ℝ) : ℂ) * ((w x i : ℝ) : ℂ)) volume :=
    hai.integrable_mul hwi
  refine hint.locallyIntegrable.congr (Filter.Eventually.of_forall fun x => ?_)
  have hpt : (a x • w x) i = a x * w x i := rfl
  show ((a x : ℝ) : ℂ) * ((w x i : ℝ) : ℂ) = (((a x • w x) i : ℝ) : ℂ)
  rw [hpt]
  push_cast
  ring

theorem LocIntField.sub {F G : Space → Space} (hF : LocIntField F) (hG : LocIntField G) :
    LocIntField (fun x => F x - G x) := by
  intro i
  refine ((hF i).sub (hG i)).congr (Filter.Eventually.of_forall fun x => ?_)
  have hpt : (F x - G x) i = F x i - G x i := rfl
  show ((F x i : ℝ) : ℂ) - ((G x i : ℝ) : ℂ) = (((F x - G x) i : ℝ) : ℂ)
  rw [hpt]
  push_cast
  ring

/-- Sums of vector fields: the datum of `F + G` is the sum of the data. -/
theorem isSobolevDatum_add {s : ℝ} (hs : 2 ≤ s) {F G : Space → Space}
    (hF : LocIntField F) (hG : LocIntField G)
    {A B : RealVectorSobolev s} (hA : IsSobolevDatum s F A) (hB : IsSobolevDatum s G B) :
    IsSobolevDatum s (fun x => F x + G x) (A + B) := fun i =>
  isScalarSobolevDatum_add hs (hF i) (hG i) (hA i) (hB i)

theorem isSobolevDatum_sub {s : ℝ} (hs : 2 ≤ s) {F G : Space → Space}
    (hF : LocIntField F) (hG : LocIntField G)
    {A B : RealVectorSobolev s} (hA : IsSobolevDatum s F A) (hB : IsSobolevDatum s G B) :
    IsSobolevDatum s (fun x => F x - G x) (A - B) := fun i =>
  isScalarSobolevDatum_sub hs (hF i) (hG i) (hA i) (hB i)

/-- Subadditivity of the manuscript norm on physical three-vector fields, with
constant one. -/
theorem sobolevENorm_add_le {s : ℝ} (hs : 2 ≤ s) {F G : Space → Space}
    (hF : LocIntField F) (hG : LocIntField G) :
    sobolevENorm s (fun x => F x + G x) ≤ sobolevENorm s F + sobolevENorm s G := by
  by_cases hFt : sobolevENorm s F = ⊤
  · simp [hFt]
  by_cases hGt : sobolevENorm s G = ⊤
  · simp [hGt]
  obtain ⟨A, hA⟩ := exists_sobolevDatum hFt
  obtain ⟨B, hB⟩ := exists_sobolevDatum hGt
  rw [sobolevENorm_eq hA, sobolevENorm_eq hB]
  refine (sobolevENorm_le_of_isSobolevDatum (isSobolevDatum_add hs hF hG hA hB)).trans ?_
  calc ‖A + B‖ₑ = ENNReal.ofReal ‖A + B‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (‖A‖ + ‖B‖) := ENNReal.ofReal_le_ofReal (norm_add_le A B)
    _ = ‖A‖ₑ + ‖B‖ₑ := by
        rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _), ofReal_norm, ofReal_norm]

theorem sobolevENorm_sub_le {s : ℝ} (hs : 2 ≤ s) {F G : Space → Space}
    (hF : LocIntField F) (hG : LocIntField G) :
    sobolevENorm s (fun x => F x - G x) ≤ sobolevENorm s F + sobolevENorm s G := by
  by_cases hFt : sobolevENorm s F = ⊤
  · simp [hFt]
  by_cases hGt : sobolevENorm s G = ⊤
  · simp [hGt]
  obtain ⟨A, hA⟩ := exists_sobolevDatum hFt
  obtain ⟨B, hB⟩ := exists_sobolevDatum hGt
  rw [sobolevENorm_eq hA, sobolevENorm_eq hB]
  refine (sobolevENorm_le_of_isSobolevDatum (isSobolevDatum_sub hs hF hG hA hB)).trans ?_
  calc ‖A - B‖ₑ = ENNReal.ofReal ‖A - B‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (‖A‖ + ‖B‖) := ENNReal.ofReal_le_ofReal (norm_sub_le A B)
    _ = ‖A‖ₑ + ‖B‖ₑ := by
        rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _), ofReal_norm, ofReal_norm]

/-- `appendix-a-local-theory.tex:14-15`, `‖·‖_{H²} ≤ ‖·‖_{H^m}`, for three-vector
fields, with the normalization constant and the dimensional factor. -/
theorem sobolevENorm_two_le (m : ℕ) (hm2 : (2:ℝ) ≤ (m:ℝ)) (z : Space → Space) :
    sobolevENorm 2 z ≤ ENNReal.ofReal (3 * lowerConst (m : ℝ) 2) * sobolevENorm (m : ℝ) z := by
  refine (sobolevENorm_le_sum_components 2 z).trans ?_
  have hstep : ∀ i : Fin 3, scalarSobolevENorm 2 (fun x => z x i) ≤
      ENNReal.ofReal (lowerConst (m : ℝ) 2) * sobolevENorm (m : ℝ) z := fun i =>
    (scalarSobolevENorm_two_le m hm2 _).trans
      (by gcongr; exact scalarSobolevENorm_component_le _ _ i)
  calc ∑ i : Fin 3, scalarSobolevENorm 2 (fun x => z x i)
      ≤ ∑ _i : Fin 3, ENNReal.ofReal (lowerConst (m : ℝ) 2) * sobolevENorm (m : ℝ) z :=
        Finset.sum_le_sum fun i _ => hstep i
    _ = ENNReal.ofReal (3 * lowerConst (m : ℝ) 2) * sobolevENorm (m : ℝ) z := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3), ENNReal.ofReal_ofNat]
        simp [mul_assoc, nsmul_eq_mul]

/-! ## 4. The tame product of a scalar with a three-vector -/

/-- The constant of `eq:Rproduct` for the product of a physical scalar with a
physical three-vector: `scalarTameConst` times the dimensional factor `3`. -/
def vectorTameConst (m : ℕ) : ℝ := 3 * scalarTameConst m

theorem vectorTameConst_pos (m : ℕ) : 0 < vectorTameConst m := by
  have := scalarTameConst_pos m
  simp only [vectorTameConst]; linarith

/-- **`appendix-a-local-theory.tex:9-11` eq:Rproduct with `:50`**, for the
product `x ↦ a(x)·w(x)` of a physical real scalar with a physical real
three-vector field. -/
theorem tameProductVector (m : ℕ) (hm : 2 ≤ m) {a : Space → ℝ} {w : Space → Space}
    (ha : MemHmScalar m a) (hw : MemHmVector m w) :
    sobolevENorm (m : ℝ) (fun x => a x • w x) ≤
      ENNReal.ofReal (vectorTameConst m) *
        (scalarSobolevENorm 2 a * sobolevENorm (m : ℝ) w +
          sobolevENorm 2 w * scalarSobolevENorm (m : ℝ) a) := by
  refine (sobolevENorm_le_sum_components (m : ℝ) _).trans ?_
  have hstep : ∀ i : Fin 3, scalarSobolevENorm (m : ℝ) (fun x => (a x • w x) i) ≤
      ENNReal.ofReal (scalarTameConst m) *
        (scalarSobolevENorm 2 a * sobolevENorm (m : ℝ) w +
          sobolevENorm 2 w * scalarSobolevENorm (m : ℝ) a) := by
    intro i
    have := tameProductScalar m hm ha (hw.component i)
    refine this.trans ?_
    gcongr <;> exact scalarSobolevENorm_component_le _ _ i
  calc ∑ i : Fin 3, scalarSobolevENorm (m : ℝ) (fun x => (a x • w x) i)
      ≤ ∑ _i : Fin 3, ENNReal.ofReal (scalarTameConst m) *
          (scalarSobolevENorm 2 a * sobolevENorm (m : ℝ) w +
            sobolevENorm 2 w * scalarSobolevENorm (m : ℝ) a) :=
        Finset.sum_le_sum fun i _ => hstep i
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, vectorTameConst,
          ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3), ENNReal.ofReal_ofNat]
        simp [mul_assoc, nsmul_eq_mul]

/-- `eq:Rproduct` for two scalars, restated with the (larger) scalar-times-vector
constant, so that one constant serves both clauses of the contract. -/
theorem tameProductScalar_vectorConst (m : ℕ) (hm : 2 ≤ m) {a b : Space → ℝ}
    (ha : MemHmScalar m a) (hb : MemHmScalar m b) :
    scalarSobolevENorm (m : ℝ) (fun x => a x * b x) ≤
      ENNReal.ofReal (vectorTameConst m) *
        (scalarSobolevENorm 2 a * scalarSobolevENorm (m : ℝ) b +
          scalarSobolevENorm 2 b * scalarSobolevENorm (m : ℝ) a) := by
  refine (tameProductScalar m hm ha hb).trans ?_
  have hc : ENNReal.ofReal (scalarTameConst m) ≤ ENNReal.ofReal (vectorTameConst m) :=
    ENNReal.ofReal_le_ofReal (by simp only [vectorTameConst]; nlinarith [scalarTameConst_pos m])
  exact mul_le_mul_left hc _

/-- `appendix-a-local-theory.tex:16` eq:algebra's constant in the scalar-times-
vector form. -/
def vectorAlgebraConst (m : ℕ) : ℝ := 2 * vectorTameConst m * (3 * lowerConst (m : ℝ) 2)

theorem vectorAlgebraConst_pos (m : ℕ) : 0 < vectorAlgebraConst m := by
  have h1 := vectorTameConst_pos m
  have h2 := lowerConst_pos (m : ℝ) 2
  simp only [vectorAlgebraConst]
  nlinarith

/-- **`appendix-a-local-theory.tex:14-16` eq:algebra**, scalar times vector. -/
theorem algebraProductVector (m : ℕ) (hm : 2 ≤ m) {a : Space → ℝ} {w : Space → Space}
    (ha : MemHmScalar m a) (hw : MemHmVector m w) :
    sobolevENorm (m : ℝ) (fun x => a x • w x) ≤
      ENNReal.ofReal (vectorAlgebraConst m) *
        (scalarSobolevENorm (m : ℝ) a * sobolevENorm (m : ℝ) w) := by
  have hm2 : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  refine (tameProductVector m hm ha hw).trans ?_
  have h1 := scalarSobolevENorm_two_le m hm2 a
  have h2 := sobolevENorm_two_le m hm2 w
  have hL : ENNReal.ofReal (lowerConst (m : ℝ) 2) ≤ ENNReal.ofReal (3 * lowerConst (m : ℝ) 2) :=
    ENNReal.ofReal_le_ofReal (by nlinarith [lowerConst_pos (m : ℝ) 2])
  calc ENNReal.ofReal (vectorTameConst m) *
        (scalarSobolevENorm 2 a * sobolevENorm (m : ℝ) w +
          sobolevENorm 2 w * scalarSobolevENorm (m : ℝ) a)
      ≤ ENNReal.ofReal (vectorTameConst m) *
        ((ENNReal.ofReal (3 * lowerConst (m : ℝ) 2) * scalarSobolevENorm (m : ℝ) a) *
            sobolevENorm (m : ℝ) w +
          (ENNReal.ofReal (3 * lowerConst (m : ℝ) 2) * sobolevENorm (m : ℝ) w) *
            scalarSobolevENorm (m : ℝ) a) := by
        gcongr
        exact h1.trans (by gcongr)
    _ = ENNReal.ofReal (vectorAlgebraConst m) *
          (scalarSobolevENorm (m : ℝ) a * sobolevENorm (m : ℝ) w) := by
        rw [vectorAlgebraConst,
          ENNReal.ofReal_mul (by nlinarith [vectorTameConst_pos m] : (0:ℝ) ≤ 2 * vectorTameConst m),
          ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
        ring

/-! ## 5. The smooth instances

`Section4/D01/SmoothDatum.lean` produces an angular real-vector datum at every
real order from the **jet** form of `H^∞` — smooth with all Fréchet jets square
integrable, `SmoothL2` — with no compact-support hypothesis.  These are the
instances by which Section 4's smooth fields enter the clauses above. -/

theorem SmoothL2.memLp {w : Space → Space} (h : SmoothL2 w) : MemLp w 2 volume :=
  (h.2 0).congr_norm h.1.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ => norm_iteratedFDeriv_zero)

/-- A smooth field with square-integrable jets is admissible at every integer
order.  This is `Section4.D01.sobolevENorm_ne_top_of_contDiff_memLp`. -/
theorem SmoothL2.memHmVector {w : Space → Space} (h : SmoothL2 w) (m : ℕ) : MemHmVector m w :=
  ⟨h.memLp, NSFormalization.Section4.D01.sobolevENorm_ne_top_of_contDiff_memLp h.1 h.2 _⟩

theorem SmoothL2.memHmScalar {w : Space → Space} (h : SmoothL2 w) (m : ℕ) (i : Fin 3) :
    MemHmScalar m (fun x => w x i) :=
  (h.memHmVector m).component i

end NSFormalization.Section4.A03
