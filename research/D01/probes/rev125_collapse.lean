-- Reviewer probe from lane-125 review (research/D01/REVIEW_FINITE_ORDER.md), preserved verbatim.
-- Original reviewer path: /tmp/rev125/p4_neg.lean . Compiles under `lake env lean` from verification/.
-- Exploratory probe (not a registered module): shows row D-b and the Schwartz-duality removal
-- of the smoothness hypothesis are reachable from in-tree lemmas.
import NSFormalization.Section4.D01.FiniteOrderDatum
import NSFormalization.Section4.D01.OrderZeroDatum
import NSFormalization.Section4.D01.DatumToJets

open MeasureTheory NavierStokes.ProblemStatement EulerLpTranslation
open NSFormalization.Paper3 NSFormalization.Source.RealSobolev
open NSFormalization.Section4.D01
open scoped ContDiff ENNReal RealInnerProductSpace

noncomputable section

/-! ### (c) the symbol bound, evaluated at ξ = (1,1,1) -/

def v3 : Space := (WithLp.toLp 2 ![1, 1, 1] : EuclideanSpace ℝ (Fin 3))

theorem v3_normSq : ‖v3‖ ^ 2 = 3 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [v3, Fin.sum_univ_three]
  norm_num

theorem v3_lhs : Real.sqrt (1 + ‖v3‖ ^ 2) = 2 := by
  rw [v3_normSq, show (1 : ℝ) + 3 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem v3_rhs : 1 + ∑ j : Fin 3, |v3 j| = 4 := by
  simp [v3, Fin.sum_univ_three]
  norm_num

/-- The general lemma at ξ = (1,1,1) really says `2 ≤ 4`. -/
example : (2 : ℝ) ≤ 4 := by
  have h := NSFormalization.Section4.D01.sqrt_one_add_normSq_le v3
  rwa [v3_lhs, v3_rhs] at h

/-! ### (d) the negative check: free raising collapses -/

/-- **Collapse.**  If the order-raising step held *without* the `L²` witness — i.e. if every
order-`s` datum could be raised to an order-`(s+1)` datum — then every smooth square-integrable
field would have a square-integrable first derivative, i.e. `L² ∩ C^∞ ⊆ H¹`, which is false
(smooth `L²` fields with non-`L²` gradient exist). -/
theorem free_raise_collapse
    (freeRaise : ∀ {s : ℝ} {z : Space → Space} {A : RealVectorSobolev s},
      IsSobolevDatum s z A → ∃ B : RealVectorSobolev (s + 1), IsSobolevDatum (s + 1) z B)
    {z : Space → Space} (hz : ContDiff ℝ ∞ z) (hL2 : MemLp z 2 volume) :
    MemLp (iteratedFDeriv ℝ 1 z) 2 volume := by
  obtain ⟨B, hB⟩ := freeRaise (isSobolevDatum_orderZeroDatum hL2)
  have key : ∀ r : ℝ, r = ((1 : ℕ) : ℝ) → ∀ C : RealVectorSobolev r, IsSobolevDatum r z C →
      MemLp (iteratedFDeriv ℝ 1 z) 2 volume := by
    rintro r rfl C hC
    exact memLp_iteratedFDeriv_of_isSobolevDatum (m := 1) (j := 1) le_rfl hz hC
  exact key ((0 : ℝ) + 1) (by norm_num) B hB

/-! ### (3) how far is row D-b?  The cycles-level raw multiplier is already in tree,
     smoothness-free, for arbitrary `L²` data. -/

/-- The raw-frequency a.e. Fourier identity for the (weak, distributional) directional derivative,
in the **cycles** variable: one line from `Paper3.sobolevDirectionalDerivative_coeFn`. -/
theorem db_cycles_level (s : ℝ) (a : Space) (h : Lp ℂ 2 (volume : Measure Space)) :
    ((cyclesToAngular (s - 1)).symm (angularDirectionalDerivative s a h) : Space → ℂ)
      =ᵐ[volume] fun ξ => sobolevDirectionalSymbol a ξ *
        (((cyclesToAngular s).symm h : Lp ℂ 2 volume) : Space → ℂ) ξ := by
  have hst : (cyclesToAngular (s - 1)).symm (angularDirectionalDerivative s a h)
      = sobolevDirectionalDerivative s a ((cyclesToAngular s).symm h) :=
    (cyclesToAngular (s - 1)).symm_apply_apply _
  rw [hst]
  exact sobolevDirectionalDerivative_coeFn s a _

/-- and the symbol really is `2πi · ξⱼ · (1+‖ξ‖²)^{-1/2}` in the coordinate directions. -/
theorem db_symbol (j : Fin 3) (ξ : Space) :
    sobolevDirectionalSymbol (NavierStokes.ProblemStatement.coordinateVector j) ξ
      = (2 * (Real.pi : ℂ) * Complex.I) * (((ξ j : ℝ) : ℂ) * sobolevBesselWeight (-1) ξ) := by
  rw [sobolevDirectionalSymbol]
  congr 3
  rw [NavierStokes.ProblemStatement.coordinateVector, EuclideanSpace.inner_single_right]
  simp
