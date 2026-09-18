import NSFormalization.Section3.T24.AffineWitness

/-!
# T24a Ua7: `infinite_dimensional` — a linearly independent admissible sequence

`paper/sections/03-torus.tex:688-691`:

> To verify infinite dimensionality explicitly, choose countably many disjoint
> small balls inside `B₀`.  In each ball choose a smooth compactly supported
> vector potential with nonzero curl, and multiply that curl by a fixed nonzero
> time bump in `(τ₀,τ₁)`.  These divergence-free fields are linearly independent
> because their spatial supports are disjoint.

This module realises that sentence.  The balls are `closedBall (c + (r 2⁻ⁿ⁺¹/2)·e₁)
(r 2⁻ⁿ/16)`, `n : ℕ`: they shrink geometrically towards `c` along the `e₁`-axis,
all sit inside `ball c r`, and are pairwise disjoint.  On the `n`-th ball we put
the canonical witness of `Section3/T24/AffineWitness.lean`,
`b n = ∇ × (θ(t) φₙ(x) e₁)` with `θ` a single time bump supported in
`(τ₀, τ₁)` and `φₙ` a `ContDiffBump` on the `n`-th ball.

The only hypotheses are the two geometric facts the cylinder needs to be
nondegenerate: `0 < r` and `τ₀ < τ₁`.  (`AffineBasics.window` shows the
canonical parameter package also carries `0 < τ₀` and `τ₁ < 1`; neither is used
here, and `AffineBasics.radius_pos` is the `0 < r` clause.)

Linear independence is the disjoint-support argument: `b n ≠ 0`
(`AffineWitness.curlBump_ne_zero`) produces a spacetime point `z` at which
`b n z ≠ 0`; that point lies in the carrier of `b n`, hence its spatial
coordinate lies in the `n`-th ball, hence outside every other ball, so every
other `b i` vanishes at `z`.  Evaluating a vanishing finite combination at `z`
kills all but the `n`-th coefficient.
-/

noncomputable section

namespace NSFormalization.Section3.T24

open Set
open NavierStokes.ProblemStatement
open scoped ContDiff BigOperators

namespace AffineFamily

/-! ## 1. The geometric data: a shrinking sequence of disjoint balls -/

/-- The geometric scale `2⁻ⁿ`. -/
def scale (n : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ n

theorem scale_pos (n : ℕ) : 0 < scale n := pow_pos (by norm_num) n

theorem scale_le_one (n : ℕ) : scale n ≤ 1 := by
  induction n with
  | zero => simp [scale]
  | succ k ih =>
      have hk := scale_pos k
      have : scale (k + 1) = scale k / 2 := by
        simp only [scale, pow_succ]; ring
      rw [this]; linarith

theorem scale_succ (n : ℕ) : scale (n + 1) = scale n / 2 := by
  simp only [scale, pow_succ]; ring

theorem scale_antitone : Antitone scale :=
  antitone_nat_of_succ_le fun n => by rw [scale_succ]; linarith [scale_pos n]

/-- Distance of the `n`-th ball centre from `c`, along `e₁`. -/
def centerOffset (r : ℝ) (n : ℕ) : ℝ := r * scale n / 2

/-- Radius of the `n`-th ball. -/
def ballRadius (r : ℝ) (n : ℕ) : ℝ := r * scale n / 16

theorem ballRadius_pos {r : ℝ} (hr : 0 < r) (n : ℕ) : 0 < ballRadius r n := by
  have h := mul_pos hr (scale_pos n)
  simp only [ballRadius]
  linarith

/-- The `n`-th ball centre. -/
def center (c : Space) (r : ℝ) (n : ℕ) : Space :=
  c + centerOffset r n • coordinateVector 0

theorem norm_e0 : ‖(coordinateVector 0 : Space)‖ = 1 := by simp [coordinateVector]

theorem dist_center_self (c : Space) (r : ℝ) (n : ℕ) :
    dist (center c r n) c = |centerOffset r n| := by
  rw [center, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_e0, mul_one,
    Real.norm_eq_abs]

theorem dist_center_center (c : Space) (r : ℝ) (n m : ℕ) :
    dist (center c r n) (center c r m) = |centerOffset r n - centerOffset r m| := by
  have hsub : center c r n - center c r m =
      (centerOffset r n - centerOffset r m) • coordinateVector 0 := by
    simp only [center, sub_smul]
    abel
  rw [dist_eq_norm, hsub, norm_smul, norm_e0, mul_one, Real.norm_eq_abs]

/-- Each closed ball sits strictly inside `ball c r`. -/
theorem closedBall_subset_ball {c : Space} {r : ℝ} (hr : 0 < r) (n : ℕ) :
    Metric.closedBall (center c r n) (ballRadius r n) ⊆ Metric.ball c r := by
  intro y hy
  have hle : r * scale n ≤ r := by
    have := scale_le_one n
    nlinarith
  have hpos : 0 < r * scale n := mul_pos hr (scale_pos n)
  have hoff : |centerOffset r n| = centerOffset r n :=
    abs_of_nonneg (by simp only [centerOffset]; linarith)
  have htri : dist y c ≤ dist y (center c r n) + dist (center c r n) c :=
    dist_triangle _ _ _
  rw [dist_center_self, hoff] at htri
  have hy' : dist y (center c r n) ≤ ballRadius r n := Metric.mem_closedBall.mp hy
  have : dist y c ≤ ballRadius r n + centerOffset r n := by linarith
  refine Metric.mem_ball.mpr (lt_of_le_of_lt this ?_)
  simp only [ballRadius, centerOffset]
  linarith

/-- Separation of two different balls: the sum of radii is strictly smaller than
the distance between the centres.  Proved first for `n < m`. -/
theorem radius_add_lt_of_lt {r : ℝ} (hr : 0 < r) {n m : ℕ} (hnm : n < m) :
    ballRadius r n + ballRadius r m < centerOffset r n - centerOffset r m := by
  have hsm : scale m ≤ scale n / 2 := by
    have h1 : scale m ≤ scale (n + 1) := scale_antitone hnm
    rwa [scale_succ] at h1
  have hmul : r * scale m ≤ r * scale n / 2 := by
    have := mul_le_mul_of_nonneg_left hsm hr.le
    linarith
  have hpos : 0 < r * scale n := mul_pos hr (scale_pos n)
  simp only [ballRadius, centerOffset]
  linarith

theorem radius_add_lt {r : ℝ} (hr : 0 < r) {n m : ℕ} (hnm : n ≠ m) :
    ballRadius r n + ballRadius r m <
      |centerOffset r n - centerOffset r m| := by
  rcases lt_or_gt_of_ne hnm with h | h
  · have hlt := radius_add_lt_of_lt hr h
    have hnn : 0 ≤ centerOffset r n - centerOffset r m := by
      have := ballRadius_pos hr n
      have := ballRadius_pos hr m
      linarith
    rwa [abs_of_nonneg hnn]
  · have hlt := radius_add_lt_of_lt hr h
    have hnn : 0 ≤ centerOffset r m - centerOffset r n := by
      have := ballRadius_pos hr n
      have := ballRadius_pos hr m
      linarith
    rw [abs_sub_comm, abs_of_nonneg hnn]
    linarith

/-- Different balls are disjoint: no point lies in two of them. -/
theorem notMem_closedBall_of_ne {c : Space} {r : ℝ} (hr : 0 < r) {n m : ℕ}
    (hnm : n ≠ m) {y : Space} (hy : y ∈ Metric.closedBall (center c r n) (ballRadius r n)) :
    y ∉ Metric.closedBall (center c r m) (ballRadius r m) := by
  intro hy'
  have h1 : dist (center c r n) y ≤ ballRadius r n := by
    rw [dist_comm]; exact Metric.mem_closedBall.mp hy
  have h2 : dist y (center c r m) ≤ ballRadius r m := Metric.mem_closedBall.mp hy'
  have htri : dist (center c r n) (center c r m) ≤
      dist (center c r n) y + dist y (center c r m) := dist_triangle _ _ _
  rw [dist_center_center] at htri
  have := radius_add_lt hr hnm
  linarith

/-! ## 2. The bumps -/

/-- A single time bump, plateau `(τ₁-τ₀)/8`, support radius `(τ₁-τ₀)/4`,
centred at the midpoint of `(τ₀, τ₁)`. -/
def timeBump (τ₀ τ₁ : ℝ) (hτ : τ₀ < τ₁) : ContDiffBump ((τ₀ + τ₁) / 2) :=
  ⟨(τ₁ - τ₀) / 8, (τ₁ - τ₀) / 4, by linarith, by linarith⟩

theorem timeBump_support (τ₀ τ₁ : ℝ) (hτ : τ₀ < τ₁) :
    Metric.closedBall ((τ₀ + τ₁) / 2) (timeBump τ₀ τ₁ hτ).rOut ⊆ Ioo τ₀ τ₁ := by
  have h : (timeBump τ₀ τ₁ hτ).rOut = (τ₁ - τ₀) / 4 := rfl
  rw [h, Real.closedBall_eq_Icc]
  exact Icc_subset_Ioo (by linarith) (by linarith)

/-- The `n`-th spatial bump, plateau half the ball radius. -/
def spaceBump (c : Space) (r : ℝ) (hr : 0 < r) (n : ℕ) :
    ContDiffBump (center c r n) :=
  ⟨ballRadius r n / 2, ballRadius r n, by linarith [ballRadius_pos hr n],
    by linarith [ballRadius_pos hr n]⟩

theorem spaceBump_rOut (c : Space) (r : ℝ) (hr : 0 < r) (n : ℕ) :
    (spaceBump c r hr n).rOut = ballRadius r n := rfl

/-! ## 3. The family -/

/-- The countable admissible family `b n = ∇ × (θ(t) φₙ(x) e₁)`. -/
def bFam (c : Space) (r τ₀ τ₁ : ℝ) (hr : 0 < r) (hτ : τ₀ < τ₁) (n : ℕ) :
    VelocityField :=
  AffineWitness.curlBump (timeBump τ₀ τ₁ hτ) (spaceBump c r hr n)

theorem bFam_admissible (c : Space) (r τ₀ τ₁ : ℝ) (hr : 0 < r) (hτ : τ₀ < τ₁)
    (n : ℕ) : AffineAdmissible c r τ₀ τ₁ (bFam c r τ₀ τ₁ hr hτ n) :=
  AffineWitness.curlBump_admissible _ _ (timeBump_support τ₀ τ₁ hτ)
    (by rw [spaceBump_rOut]; exact closedBall_subset_ball hr n)

theorem bFam_ne_zero (c : Space) (r τ₀ τ₁ : ℝ) (hr : 0 < r) (hτ : τ₀ < τ₁)
    (n : ℕ) : bFam c r τ₀ τ₁ hr hτ n ≠ 0 :=
  AffineWitness.curlBump_ne_zero _ _

theorem bFam_mem_ball_of_ne_zero (c : Space) (r τ₀ τ₁ : ℝ) (hr : 0 < r)
    (hτ : τ₀ < τ₁) (n : ℕ) {z : SpaceTime} (hz : bFam c r τ₀ τ₁ hr hτ n z ≠ 0) :
    z.2 ∈ Metric.closedBall (center c r n) (ballRadius r n) := by
  have hmem : z ∈ AffineWitness.carrier (timeBump τ₀ τ₁ hτ) (spaceBump c r hr n) :=
    AffineWitness.tsupport_curlBump_subset _ _
      (subset_tsupport _ (Function.mem_support.mpr hz))
  exact hmem.2

theorem bFam_eq_zero_of_notMem_ball (c : Space) (r τ₀ τ₁ : ℝ) (hr : 0 < r)
    (hτ : τ₀ < τ₁) (n : ℕ) {z : SpaceTime}
    (hz : z.2 ∉ Metric.closedBall (center c r n) (ballRadius r n)) :
    bFam c r τ₀ τ₁ hr hτ n z = 0 :=
  AffineWitness.curlBump_eq_zero_of_notMem _ _ (fun h => hz h.2)

theorem bFam_linearIndependent (c : Space) (r τ₀ τ₁ : ℝ) (hr : 0 < r)
    (hτ : τ₀ < τ₁) : LinearIndependent ℝ (bFam c r τ₀ τ₁ hr hτ) := by
  rw [linearIndependent_iff']
  intro s g hsum n hn
  obtain ⟨z, hz⟩ : ∃ z : SpaceTime, bFam c r τ₀ τ₁ hr hτ n z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact bFam_ne_zero c r τ₀ τ₁ hr hτ n (funext hcon)
  have hball := bFam_mem_ball_of_ne_zero c r τ₀ τ₁ hr hτ n hz
  have hpt : ∑ i ∈ s, g i • bFam c r τ₀ τ₁ hr hτ i z = 0 := by
    have := congrFun hsum z
    simpa using this
  have hsingle : ∑ i ∈ s, g i • bFam c r τ₀ τ₁ hr hτ i z =
      g n • bFam c r τ₀ τ₁ hr hτ n z := by
    refine Finset.sum_eq_single_of_mem n hn ?_
    intro i _ hin
    have hout : z.2 ∉ Metric.closedBall (center c r i) (ballRadius r i) :=
      notMem_closedBall_of_ne hr (Ne.symm hin) hball
    rw [bFam_eq_zero_of_notMem_ball c r τ₀ τ₁ hr hτ i hout, smul_zero]
  rw [hsingle] at hpt
  rcases smul_eq_zero.mp hpt with h | h
  · exact h
  · exact absurd h hz

end AffineFamily

/-- **Ua7 / `Spec.lean:1085-1087`** (`03-torus.tex:688-691`): the admissible
class of affine variations contains an `ℝ`-linearly independent sequence, so the
affine family `b ↦ U + b` is genuinely infinite dimensional.

The only hypotheses are the nondegeneracy of the cylinder `Ioo τ₀ τ₁ ×ˢ ball c r`
(`0 < r`, `τ₀ < τ₁`).  The witness is
`AffineFamily.bFam c r τ₀ τ₁ hr hτ n = ∇ × (θ(t) φₙ(x) e₁)` with `φₙ` a bump on
the `n`-th of a sequence of pairwise disjoint balls inside `ball c r`. -/
theorem infinite_dimensional (c : Space) (r τ₀ τ₁ : ℝ) (hr : 0 < r)
    (hτ : τ₀ < τ₁) :
    ∃ b : ℕ → VelocityField,
      (∀ n : ℕ, AffineAdmissible c r τ₀ τ₁ (b n)) ∧ LinearIndependent ℝ b :=
  ⟨AffineFamily.bFam c r τ₀ τ₁ hr hτ,
    AffineFamily.bFam_admissible c r τ₀ τ₁ hr hτ,
    AffineFamily.bFam_linearIndependent c r τ₀ τ₁ hr hτ⟩

end NSFormalization.Section3.T24
