import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! Finite Euclidean products and their Bochner reconstruction. -/
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace NSFormalization.Source.FiniteHilbertBochner
variable {ι H α : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasurableSpace α]
abbrev Product (ι H : Type*) [Fintype ι] [NormedAddCommGroup H] :=
  PiLp 2 (fun _ : ι => H)

def insert (i : ι) : H →L[ℝ] Product ι H :=
  LinearMap.mkContinuous
    { toFun := fun x => PiLp.single 2 i x
      map_add' := by
        intro x y
        simp [PiLp.single_add]
      map_smul' := by
        intro c x
        ext j
        by_cases h : j = i <;> simp [PiLp.single_apply, h] }
    1 (by intro x; simpa using (PiLp.norm_single 2 (fun _ : ι => H) i x))

@[simp] theorem insert_apply (i : ι) (x : H) : insert i x = PiLp.single 2 i x := by simp [insert]
@[simp] theorem norm_insert (i : ι) (x : H) : ‖insert i x‖ = ‖x‖ :=
  PiLp.norm_single 2 (fun _ : ι => H) i x

theorem insert_opNorm (i : ι) : ‖(insert i : H →L[ℝ] Product ι H)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp

def coord (i : ι) : Product ι H →L[ℝ] H := PiLp.proj 2 (fun _ : ι => H) i

 theorem reconstruction (v : Product ι H) : ∑ i, insert i (coord i v) = v := by
  ext j
  simp [insert, coord, PiLp.single_apply]

variable (q : ℝ≥0∞) [Fact (1 ≤ q)] (μ : Measure α)
def assemble (h : ι → Lp H q μ) : Lp (Product ι H) q μ :=
  ∑ i, (insert i).compLpL q μ (h i)
def coordinates (b : Lp (Product ι H) q μ) (i : ι) : Lp H q μ :=
  (coord i).compLpL q μ b

 theorem assemble_coordinates (b : Lp (Product ι H) q μ) :
    assemble q μ (coordinates q μ b) = b := by
  apply Lp.ext
  have hi : ∀ᵐ t ∂μ, ∀ i : ι,
      ((insert i).compLpL q μ (coordinates q μ b i)) t = insert i (coord i (b t)) := by
    rw [ae_all_iff]
    intro i
    filter_upwards [ContinuousLinearMap.coeFn_compLpL (insert i) (coordinates q μ b i),
      ContinuousLinearMap.coeFn_compLpL (coord i) b] with t ht ht'
    exact ht.trans (congrArg (insert i) ht')
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun i => (insert i).compLpL q μ (coordinates q μ b i)), hi] with t ht hi
  change (∑ i, (insert i).compLpL q μ (coordinates q μ b i)) t = b t
  rw [ht]
  simp only [Finset.sum_apply]
  exact (Finset.sum_congr rfl (fun i _ => hi i)).trans (reconstruction (b t))

 theorem approximation_bound (b : Lp (Product ι H) q μ) (h : ι → Lp H q μ) :
    ‖b - assemble q μ h‖ ≤ ∑ i, ‖coordinates q μ b i - h i‖ := by
  have he : b - assemble q μ h =
      ∑ i, (insert i).compLpL q μ (coordinates q μ b i - h i) := by
    simp only [map_sub, Finset.sum_sub_distrib]
    rw [← assemble, assemble_coordinates]
    rfl
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  refine (((insert i : H →L[ℝ] Product ι H).compLpL q μ).le_opNorm _).trans ?_
  have hn := (ContinuousLinearMap.norm_compLpL_le (p := q) (μ := μ)
    (insert i : H →L[ℝ] Product ι H)).trans (insert_opNorm i)
  exact (mul_le_mul_of_nonneg_right hn (norm_nonneg _)).trans_eq (one_mul _)
end NSFormalization.Source.FiniteHilbertBochner
