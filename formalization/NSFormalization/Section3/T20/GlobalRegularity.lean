import NSFormalization.Section3.T20.Continuation
import NSFormalization.Section3.T11.Assembly

/-!
# T20 unit U12 — global regularity from the continuation criterion

For zero initial datum and `criticalRho g < criticalSmallnessH1 * ν`, U11 bounds
the squared `H²` integral on every classical horizon.  A maximal periodic pair
only supplies classical solutions on horizons strictly below its lifespan, so
the terminal `≤` case required by T11 is obtained by exhausting `(0, S)` with
the intervals `(0, S - S/(n+2))`.  The U11 bound is uniform along this
exhaustion.  T11's proved, ball-free `H³` continuation criterion then forces
the maximal lifespan to be infinite.

No `PeriodicRestartH1` input is used.
-/

noncomputable section

namespace NSFormalization.Section3.T20

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open scoped ENNReal

/-! ## The endpoint-local finiteness bridge -/

/-- U11's classical-solution estimate extends to the common velocity of a
maximal periodic pair at every finite horizon at or below the maximal
lifespan.  The non-strict endpoint is the only content: all estimates are
applied on strictly shorter classical horizons and passed to the union. -/
theorem maximal_squaredHTwoIntegralT_ne_top
    {ν S : ℝ} {g u : SpaceTimeField} {p : SpaceTimeScalar}
    (hν : 0 < ν) (hg : g ∈ forceClassT)
    (hsmall : criticalRho g < ENNReal.ofReal (criticalSmallnessH1 * ν))
    (hmax : IsMaximalPeriodicSolution ν (fun _ : Space ↦ 0) g u p)
    (hS : 0 < S)
    (hSL : ENNReal.ofReal S ≤ maximalLifespanT ν (fun _ : Space ↦ 0) g) :
    squaredHTwoIntegralT S u ≠ ⊤ := by
  set bb : ℕ → ℝ := fun n ↦ S - S / ((n : ℝ) + 2) with hbbdef
  have hbbpos : ∀ n : ℕ, 0 < bb n := by
    intro n
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hfrac : S / ((n : ℝ) + 2) < S := by
      rw [div_lt_iff₀ h2]
      nlinarith
    simp only [hbbdef]
    linarith
  have hbblt : ∀ n : ℕ, bb n < S := by
    intro n
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hfrac : 0 < S / ((n : ℝ) + 2) := div_pos hS h2
    simp only [hbbdef]
    linarith
  have hbbmono : Monotone bb := by
    intro i j hij
    have hle : ((i : ℝ) + 2) ≤ ((j : ℝ) + 2) := by
      have hijR : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.2 hij
      linarith
    have hdiv : S / ((j : ℝ) + 2) ≤ S / ((i : ℝ) + 2) := by
      gcongr
    simp only [hbbdef]
    linarith
  have hunion : Ioo (0 : ℝ) S = ⋃ n : ℕ, Ioo (0 : ℝ) (bb n) := by
    refine Subset.antisymm (fun t ht ↦ ?_)
      (iUnion_subset fun n ↦ Ioo_subset_Ioo le_rfl (hbblt n).le)
    obtain ⟨n, hn⟩ := exists_nat_gt (S / (S - t))
    refine mem_iUnion.2 ⟨n, ht.1, ?_⟩
    have hSt : (0 : ℝ) < S - t := sub_pos.2 ht.2
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hn2 : S / (S - t) < (n : ℝ) + 2 := by linarith
    rw [div_lt_iff₀ hSt] at hn2
    have hfrac : S / ((n : ℝ) + 2) < S - t := by
      rw [div_lt_iff₀ h2]
      nlinarith
    simp only [hbbdef]
    linarith
  have hdir : Directed (· ⊆ ·) (fun n : ℕ ↦ Ioo (0 : ℝ) (bb n)) := by
    intro i j
    exact ⟨max i j, Ioo_subset_Ioo le_rfl (hbbmono (le_max_left i j)),
      Ioo_subset_Ioo le_rfl (hbbmono (le_max_right i j))⟩
  have hρ : criticalRho g ≠ ⊤ := ne_top_of_lt hsmall
  have hbound_ne :
      ENNReal.ofReal S * criticalRho g ^ (2 : ℝ) +
        ENNReal.ofReal (Ccriterion * (ν⁻¹) ^ 2) *
          meanFreeForceLTwoSqIntegral (meanFreeForce g) ≠ ⊤ := by
    refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (meanFreeForceLTwoSqIntegral_ne_top hg)⟩
    rw [enorm_rpow_two]
    exact ENNReal.pow_ne_top hρ
  apply ne_top_of_le_ne_top hbound_ne
  rw [squaredHTwoIntegralT, hunion, setLIntegral_iUnion_of_directed _ hdir]
  refine iSup_le fun n ↦ ?_
  have hbnlife : ENNReal.ofReal (bb n) <
      maximalLifespanT ν (fun _ : Space ↦ 0) g :=
    ((ENNReal.ofReal_lt_ofReal_iff hS).2 (hbblt n)).trans_le hSL
  obtain ⟨w, hwv, -⟩ := hmax.2 (bb n) (hbbpos n) hbnlife
  have hc := continuationBound ν hν g hg hsmall (bb n) w
    (bb n) (hbbpos n) le_rfl
  have hb := hc.1.le.trans hc.2.1
  rw [hwv] at hb
  refine hb.trans (add_le_add ?_ le_rfl)
  exact mul_le_mul (ENNReal.ofReal_le_ofReal (hbblt n).le) le_rfl bot_le bot_le

/-! ## The canonical field -/

/-- **T20 U12, `prop:critical`.**  Under the fixed critical smallness radius,
the from-rest periodic solution has infinite maximal lifespan.  This is the
`globalRegularity` field of `CriticalRegularityTAPI` verbatim at
`c = criticalSmallnessH1`. -/
theorem globalRegularity : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      criticalRho g < ENNReal.ofReal (criticalSmallnessH1 * ν) →
        maximalLifespanT ν (fun _ : Space ↦ 0) g = ⊤ := by
  intro ν hν g hg hsmall
  obtain ⟨u, p, hmax⟩ := exists_maximal_unconditional ν hν
    (fun _ : Space ↦ 0) zero_mem_initialClassT g hg
  exact periodicContinuationH3API.lifespanInfiniteOfLocallyFinite ν hν
    (fun _ : Space ↦ 0) zero_mem_initialClassT g hg u p hmax
    (fun S hS hSL ↦
      maximal_squaredHTwoIntegralT_ne_top hν hg hsmall hmax hS hSL)

end NSFormalization.Section3.T20
