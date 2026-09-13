import NSFormalization.Paper1.PeriodicDuhamelNormBound

noncomputable section
namespace NSFormalization.Paper1

/-- Explicit conditional contract for a Picard map on a normed carrier.
The ball and Lipschitz estimate are hypotheses: this structure does not assert
that they follow from a PDE estimate. -/
structure PicardContractionContract (E : Type*) [NormedAddCommGroup E] where
  map : E → E
  ball : Set E
  q : ℝ
  q_nonneg : 0 ≤ q
  q_lt_one : q < 1
  self_map : ∀ x, x ∈ ball → map x ∈ ball
  lipschitz_on : ∀ ⦃x y : E⦄, x ∈ ball → y ∈ ball → ‖map x - map y‖ ≤ q * ‖x - y‖

/-- Two fixed points of an explicitly contractive Picard map in its ball agree. -/
theorem PicardContractionContract.fixed_eq
    {E : Type*} [NormedAddCommGroup E]
    (C : PicardContractionContract E)
    {x y : E} (hx : x ∈ C.ball) (hy : y ∈ C.ball)
    (hxfix : C.map x = x) (hyfix : C.map y = y) : x = y := by
  have hle0 := C.lipschitz_on hx hy
  have hle : ‖x - y‖ ≤ C.q * ‖x - y‖ := by
    simpa [hxfix, hyfix] using hle0
  have hzero : ‖x - y‖ = 0 := by
    nlinarith [norm_nonneg (x - y), C.q_nonneg, C.q_lt_one]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

end NSFormalization.Paper1
