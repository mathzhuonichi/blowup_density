import NSFormalization.Source.PhysicalBesselSobolev
import NSFormalization.Paper3.SobolevOrderLowering
import NSFormalization.Source.InsertionSobolev

/-! Explicit integer-order Fourier Sobolev data for physical smooth L² fields,
with Euclidean vector assembly and persistence for the actual insertion. -/
noncomputable section
namespace NSFormalization.Source.PhysicalIntegerSobolev
open Set MeasureTheory EulerLpTranslation NavierStokes.ProblemStatement
open SmoothL2Field NSFormalization.Paper3 PhysicalSobolevDistribution PhysicalBesselSobolev
open scoped SchwartzMap ContDiff ENNReal

/-- Lower the explicit order-2n datum to order n. -/
def integerSobolevDatum (n : ℕ) (A : SmoothL2Field ℂ) : SobolevHilbert (n : ℝ) :=
  sobolevOrderLowering (2 * (n : ℝ)) (n : ℝ) (by nlinarith [Nat.cast_nonneg (α := ℝ) n]) (evenSobolevDatum n A)

 theorem integerSobolevDatum_realization (n : ℕ) (A : SmoothL2Field ℂ) :
    sobolevRealization (n : ℝ) (integerSobolevDatum n A) = physicalDistribution A := by
  rw [integerSobolevDatum, sobolevRealization_orderLowering, evenSobolevDatum_realization]

 theorem norm_integerSobolevDatum_le (n : ℕ) (A : SmoothL2Field ℂ) :
    ‖integerSobolevDatum n A‖ ≤ ‖(iteratedBesselField n A).toLp‖ := by
  exact (sobolevOrderLowering_norm_le _ _ _ _).trans_eq (norm_evenSobolevDatum n A)

 theorem continuous_integerSobolevDatum {K : Type*} [TopologicalSpace K]
    (A : K → SmoothL2Field ℂ) (hA : ∀ j, Continuous (fun t => (A t).jetLp j)) (n : ℕ) :
    Continuous (fun t => integerSobolevDatum n (A t)) :=
  (sobolevOrderLowering (2 * (n : ℝ)) (n : ℝ) (by nlinarith [Nat.cast_nonneg (α := ℝ) n])).continuous.comp
    (continuous_evenSobolevDatum A hA n)

/-- Real-linear complexification of one actual velocity component. -/
def componentField (i : Fin 3) (A : SmoothL2Field Space) : SmoothL2Field ℂ :=
  mapField (Complex.ofRealCLM.comp (EuclideanSpace.proj i)) A

@[simp] theorem componentField_field (i : Fin 3) (A : SmoothL2Field Space) (x : Space) :
    (componentField i A).field x = ((A.field x i : ℝ) : ℂ) := rfl

/-- The Euclidean L² product of three scalar Sobolev Hilbert data spaces. -/
abbrev VectorSobolevHilbert (s : ℝ) := PiLp 2 (fun _ : Fin 3 => SobolevHilbert s)

/-- Explicit componentwise datum, assembled with the Euclidean product norm. -/
def vectorSobolevDatum (n : ℕ) (A : SmoothL2Field Space) : VectorSobolevHilbert (n : ℝ) :=
  WithLp.toLp 2 (fun i => integerSobolevDatum n (componentField i A))

 theorem norm_vectorSobolevDatum_sq (n : ℕ) (A : SmoothL2Field Space) :
    ‖vectorSobolevDatum n A‖ ^ 2 =
      ∑ i : Fin 3, ‖integerSobolevDatum n (componentField i A)‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ _

 theorem vectorSobolevDatum_realization (n : ℕ) (A : SmoothL2Field Space) (i : Fin 3) :
    sobolevRealization (n : ℝ) (vectorSobolevDatum n A i) =
      physicalDistribution (componentField i A) := integerSobolevDatum_realization _ _

 theorem vectorSobolevDatum_pairing (n : ℕ) (A : SmoothL2Field Space) (i : Fin 3)
    (φ : 𝓢(Space, ℂ)) :
    sobolevRealization (n : ℝ) (vectorSobolevDatum n A i) φ =
      ∫ x, φ x • ((A.field x i : ℝ) : ℂ) := by
  rw [vectorSobolevDatum_realization, physicalDistribution_apply]
  rfl

 theorem continuous_vectorSobolevDatum {K : Type*} [TopologicalSpace K]
    (A : K → SmoothL2Field Space) (hA : ∀ j, Continuous (fun t => (A t).jetLp j)) (n : ℕ) :
    Continuous (fun t => vectorSobolevDatum n (A t)) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => SobolevHilbert (n : ℝ))).comp
  apply continuous_pi
  intro i
  exact continuous_integerSobolevDatum _ (continuous_jetLp_mapField _ A hA) n

/-- The same inserted velocity has continuous integer Sobolev data on the
whole closed presingular slab, with the original reference-path premises. -/
theorem exists_inserted_sobolev_data {ν r T τ b : ℝ} {x₀ : Space}
    {v g V G : VelocityField} {q Q : PressureField}
    (hb : b < T)
    (hvs : ContDiffOn ℝ ∞ v (Ico (0 : ℝ) T ×ˢ univ))
    (h : InsertionFamily.InsertionProperties ν v q g x₀ r T τ V Q G)
    (A : Icc (0 : ℝ) b → SmoothL2Field Space)
    (hA : ∀ j, Continuous (fun t => (A t).jetLp j))
    (hAv : ∀ t : Icc (0 : ℝ) b, ∀ x, (A t).field x = v (t, x)) :
    ∃ B : Icc (0 : ℝ) b → SmoothL2Field Space,
      (∀ t : Icc (0 : ℝ) b, ∀ x, (B t).field x = V (t, x)) ∧
      (∀ j, Continuous (fun t => (B t).jetLp j)) ∧
      (∀ n, Continuous (fun t => vectorSobolevDatum n (B t))) ∧
      ∀ (n : ℕ) (t : Icc (0 : ℝ) b) (i : Fin 3) (φ : 𝓢(Space, ℂ)),
        sobolevRealization (n : ℝ) (vectorSobolevDatum n (B t) i) φ =
          ∫ x, φ x • ((V (t, x) i : ℝ) : ℂ) := by
  obtain ⟨B, hBV, hB⟩ := InsertionSobolev.exists_inserted_path hb hvs h A hA hAv
  refine ⟨B, hBV, hB, continuous_vectorSobolevDatum B hB, ?_⟩
  intro n t i φ
  rw [vectorSobolevDatum_pairing]
  simp_rw [hBV]

end NSFormalization.Source.PhysicalIntegerSobolev
