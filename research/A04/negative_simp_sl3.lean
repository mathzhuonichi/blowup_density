import NSFormalization.Section4.A04.LaplacianAssembly
import NSFormalization.Section4.D01.SmoothDatum

/-!
# Lane 115 (SIMP-A04, SL3 cluster) — load-bearing evidence + non-vacuity

**This file must compile SILENTLY** (exit 0, no errors, no warnings).  It holds the *genuine*
load-bearing evidence for the SL3-cluster exports, in the form the lane-115 reviewer required
(`research/A04/REVIEW_SIMP_SL3.md`, Findings 3–5): **refutation-by-collapse** — state the
weakened claim as a closed `Prop`, then *prove* it entails something manifestly false.  The
companion `research/A04/negative_simp_sl3_fail.lean` holds the weaker signature/drift checks
(which must FAIL) and the reviewer's controls.

The collapse theorems, fidelity examples and the non-degenerate non-vacuity witnesses below are
transcribed from the reviewer's probes `/tmp/rev115/{p2_collapse,p4_nonvacuity}.lean` (verbatim,
credit: opus lane-115 reviewer); the N1 collapse is the reviewer's `p5_n1_collapse.lean` **repaired**
(the reviewer left it open on an order-cast wrinkle — `RealSobolevHilbert (↑m+1-1)` vs `↑m`, defeq
only at `default` transparency so `WithLp.toLp_zero` will not fire — routed here through the
in-module `derivDatumStep` / `norm_sq_derivDatumStep`, which passes through
`angularDirectionalDerivative` on `Lp` where no cast appears).

Note (reviewer + `LESSONS.md`): `exact?` is **not** usable on this cluster — it hits
`(deterministic) timeout at whnf, 1000000 heartbeats` on `WeakenedNoHL` — so refutation-by-collapse,
not `exact?`, is the right technique here.

Contents:
* §1 `WeakenedNoHL` + `datum_zero_of_weakenedNoHL` / `physical_pairing_zero_of_weakenedNoHL` —
  dropping `hL` from `inner_datum_laplacian_le'` forces every smooth `L²` field to vanish
  distributionally (take `L := G`, so `‖G‖² ≤ -‖∇u‖² ≤ 0`).  **`hL` is load-bearing.**
* §2 `WeakenedPairing` + `deriv_eq_zero_of_weakenedPairing` /
  `distributional_deriv_zero_of_weakenedPairing` — dropping the minus from
  `real_inner_angularDirectionalDerivative` forces `angularDirectionalDerivative s a = 0` at every
  order and direction.  **The sign is load-bearing** (same argument applies to the ℂ version
  `inner_angularDirectionalDerivative_right`).
* §3 `WeakenedN1` + `gradient_zero_of_weakenedN1` — dropping `hA` from
  `gradientSobolevENorm_toReal_sq_eq_datum_sum` (take `A := 0`) forces `‖∇Z‖_{H^m} = 0` for every
  smooth `L²` field.  **`hA` is load-bearing.**
* §4 fidelity: each `Weakened*` premise is EXACTLY the named export minus one hypothesis (or minus
  the sign), derived here from the real export with the hypothesis restored.
* §5 non-vacuity: the datum hypotheses are inhabited by genuine data of an arbitrary field
  (`smoothAngularDatum`), and both pairing exports run on a **nonzero** carrier element
  (`unitBall`) at **strict, pairwise-distinct** orders and a **nonzero** direction.
-/

noncomputable section

open MeasureTheory Metric NavierStokes.ProblemStatement
open NSFormalization.Section4.A04
open NSFormalization.Paper3
open NSFormalization.Section4.D01 (IsSobolevDatum smoothAngularDatum smoothAngularDatum_isSobolevDatum)
open NSFormalization.Section4.A03 (gradientSobolevENorm)
open NSFormalization.Section4.A05 (SmoothL2)
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Source.RealSobolev (RealSobolevHilbert FourierData)
open EulerLpTranslation (SmoothL2Field)
open scoped LineDeriv SchwartzMap ENNReal

/-! ## §1 — `hL` is load-bearing (refutation-by-collapse; reviewer `p2_collapse.lean`) -/

/-- `inner_datum_laplacian_le'` with the hypothesis `hL : IsSobolevDatum m (Δu) L` dropped and
`L` left universally quantified. -/
def WeakenedNoHL : Prop :=
  ∀ (m : ℕ) (u : SpaceTimeField) (t : ℝ), SmoothL2 (fun x => u (t, x)) →
    ∀ (G : RealVectorSobolev (m : ℝ)) (A' : RealVectorSobolev ((m : ℝ) + 1))
      (A : RealVectorSobolev ((m : ℝ) + 2)) (L : RealVectorSobolev (m : ℝ)),
      IsSobolevDatum (m : ℝ) (fun x => u (t, x)) G →
      IsSobolevDatum ((m : ℝ) + 1) (fun x => u (t, x)) A' →
      IsSobolevDatum ((m : ℝ) + 2) (fun x => u (t, x)) A →
      (inner ℝ G L : ℝ) ≤ - gradientSobolevNormAt (m : ℝ) u t ^ 2

set_option autoImplicit false in
/-- **Collapse 1.** `WeakenedNoHL` forces the order-`m` datum of *every* smooth `L²` field to be
zero (take `L := G`, so `‖G‖² ≤ -‖∇u‖² ≤ 0`). -/
theorem datum_zero_of_weakenedNoHL (H : WeakenedNoHL) (Z : SmoothL2Field Space) (m : ℕ) :
    smoothAngularDatum (m + 2) (m : ℝ) (by push_cast; linarith) Z = 0 := by
  set G := smoothAngularDatum (m + 2) (m : ℝ) (by push_cast; linarith) Z with hGdef
  have key := H m (fun p => Z.field p.2) 0 ⟨Z.smooth, Z.integrable⟩ G
    (smoothAngularDatum (m + 2) ((m : ℝ) + 1) (by push_cast; linarith) Z)
    (smoothAngularDatum (m + 2) ((m : ℝ) + 2) (by push_cast; linarith) Z)
    G
    (smoothAngularDatum_isSobolevDatum _ _ _ Z)
    (smoothAngularDatum_isSobolevDatum _ _ _ Z)
    (smoothAngularDatum_isSobolevDatum _ _ _ Z)
  rw [real_inner_self_eq_norm_sq] at key
  have hneg : - gradientSobolevNormAt (m : ℝ) (fun p => Z.field p.2) 0 ^ 2 ≤ 0 := by
    simpa using sq_nonneg (gradientSobolevNormAt (m : ℝ) (fun p => Z.field p.2) 0)
  have : ‖G‖ ^ 2 ≤ 0 := le_trans key hneg
  have hG0 : ‖G‖ = 0 := by nlinarith [norm_nonneg G]
  exact norm_eq_zero.mp hG0

set_option autoImplicit false in
/-- **Collapse 1'.**  Hence every smooth `L²` field pairs to zero against every Schwartz function
— i.e. `WeakenedNoHL` says every smooth `L²` field vanishes distributionally.  Manifestly false
(take a Gaussian), so `hL` is load-bearing. -/
theorem physical_pairing_zero_of_weakenedNoHL (H : WeakenedNoHL) (Z : SmoothL2Field Space)
    (m : ℕ) (i : Fin 3) (ψ : SchwartzMap Space ℂ) :
    ∫ x : Space, ψ x * ((Z.field x i : ℝ) : ℂ) = 0 := by
  have hdat := smoothAngularDatum_isSobolevDatum (m + 2) (m : ℝ) (by push_cast; linarith) Z i ψ
  rw [datum_zero_of_weakenedNoHL H Z m] at hdat
  simpa using hdat.symm

/-! ## §2 — the pairing minus sign is load-bearing (reviewer `p2_collapse.lean`) -/

/-- `real_inner_angularDirectionalDerivative` with the leading minus dropped. -/
def WeakenedPairing : Prop :=
  ∀ (s : ℝ) (a : Space) (f g : Lp ℂ 2 (volume : Measure Space)),
    (inner ℝ f (angularDirectionalDerivative s a g) : ℝ) =
      (inner ℝ (angularDirectionalDerivative s a f) g : ℝ)

set_option autoImplicit false in
/-- **Collapse 2.**  `WeakenedPairing` forces `D_a` to be the zero operator at every order and
direction — so the sign is load-bearing, not cosmetic. -/
theorem deriv_eq_zero_of_weakenedPairing (H : WeakenedPairing) (s : ℝ) (a : Space)
    (f : Lp ℂ 2 (volume : Measure Space)) :
    angularDirectionalDerivative s a f = 0 := by
  have hz : ∀ g : Lp ℂ 2 (volume : Measure Space),
      (inner ℝ (angularDirectionalDerivative s a f) g : ℝ) = 0 := by
    intro g
    have h1 := H s a f g
    have h2 := real_inner_angularDirectionalDerivative s a f g
    linarith [h1, h2]
  have := hz (angularDirectionalDerivative s a f)
  rw [real_inner_self_eq_norm_sq] at this
  have : ‖angularDirectionalDerivative s a f‖ = 0 := by
    nlinarith [norm_nonneg (angularDirectionalDerivative s a f)]
  exact norm_eq_zero.mp this

set_option autoImplicit false in
/-- **Collapse 2'.**  Hence every distributional directional derivative in the range of
`angularRealization s` vanishes — manifestly false.  So the minus sign is load-bearing.  The same
argument applies verbatim to the ℂ export `inner_angularDirectionalDerivative_right` (of which the
real version is the real part). -/
theorem distributional_deriv_zero_of_weakenedPairing (H : WeakenedPairing) (s : ℝ) (a : Space)
    (h : Lp ℂ 2 (volume : Measure Space)) :
    ∂_{a} (angularRealization s h) = 0 := by
  rw [← angularRealization_directionalDerivative s a h,
    deriv_eq_zero_of_weakenedPairing H s a h, map_zero]

/-! ## §3 — `hA` is load-bearing (reviewer `p5_n1_collapse.lean`, repaired) -/

/-- `gradientSobolevENorm_toReal_sq_eq_datum_sum` with `hA` dropped (`A` free). -/
def WeakenedN1 : Prop :=
  ∀ (Z : SmoothL2Field Space) (m : ℕ) (A : RealVectorSobolev ((m : ℝ) + 1)),
    (gradientSobolevENorm (m : ℝ) Z.field).toReal ^ 2 =
      ∑ j : Fin 3, ‖((WithLp.toLp 2 fun i =>
          angularDirectionalDerivativeReal ((m : ℝ) + 1) (coordinateVector j) (A i)) :
          RealVectorSobolev (m : ℝ))‖ ^ 2

set_option autoImplicit false in
/-- **Collapse 3.**  `WeakenedN1` (take `A = 0`) says every smooth `L²` field has zero `H^m`
gradient norm — manifestly false.  So `hA` is load-bearing.  (Repair of the reviewer's `p5`: the
`A = 0` datum-sum term is definitionally `derivDatumStep m j 0`, so `norm_sq_derivDatumStep` routes
the norm through `angularDirectionalDerivative` on `Lp`, sidestepping the `↑m+1-1` vs `↑m`
order-cast that blocked `WithLp.toLp_zero`.) -/
theorem gradient_zero_of_weakenedN1 (H : WeakenedN1) (Z : SmoothL2Field Space) (m : ℕ) :
    (gradientSobolevENorm (m : ℝ) Z.field).toReal = 0 := by
  have h := H Z m 0
  have hrhs : (∑ j : Fin 3, ‖((WithLp.toLp 2 fun i =>
      angularDirectionalDerivativeReal ((m : ℝ) + 1) (coordinateVector j)
        ((0 : RealVectorSobolev ((m : ℝ) + 1)) i)) : RealVectorSobolev (m : ℝ))‖ ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    show ‖derivDatumStep m j (0 : RealVectorSobolev ((m : ℝ) + 1))‖ ^ 2 = 0
    rw [norm_sq_derivDatumStep]
    apply Finset.sum_eq_zero
    intro i _
    rw [show (((0 : RealVectorSobolev ((m : ℝ) + 1)) i : RealSobolevHilbert ((m : ℝ) + 1)) :
          FourierData) = 0 from by
        rw [show ((0 : RealVectorSobolev ((m : ℝ) + 1)) i) = 0 from rfl]; rfl,
      map_zero, norm_zero]; ring
  rw [hrhs] at h
  nlinarith [h, ENNReal.toReal_nonneg (a := gradientSobolevENorm (m : ℝ) Z.field)]

#print axioms datum_zero_of_weakenedNoHL
#print axioms physical_pairing_zero_of_weakenedNoHL
#print axioms deriv_eq_zero_of_weakenedPairing
#print axioms distributional_deriv_zero_of_weakenedPairing
#print axioms gradient_zero_of_weakenedN1

/-! ## §4 — fidelity: each `Weakened*` premise is the named export minus one hypothesis -/

-- `WeakenedNoHL` is `inner_datum_laplacian_le'` with `hL` restored — i.e. the real theorem.
example : ∀ (m : ℕ) (u : SpaceTimeField) (t : ℝ), SmoothL2 (fun x => u (t, x)) →
    ∀ (G : RealVectorSobolev (m : ℝ)) (A' : RealVectorSobolev ((m : ℝ) + 1))
      (A : RealVectorSobolev ((m : ℝ) + 2)) (L : RealVectorSobolev (m : ℝ)),
      IsSobolevDatum (m : ℝ) (fun x => u (t, x)) G →
      IsSobolevDatum ((m : ℝ) + 1) (fun x => u (t, x)) A' →
      IsSobolevDatum ((m : ℝ) + 2) (fun x => u (t, x)) A →
      IsSobolevDatum (m : ℝ) (fun x => spatialLaplacian u t x) L →
      (inner ℝ G L : ℝ) ≤ - gradientSobolevNormAt (m : ℝ) u t ^ 2 :=
  fun m _u _t hsl _G _A' _A _L hG hA' hA hL => inner_datum_laplacian_le' m hsl hG hA' hA hL

-- `WeakenedPairing` is `real_inner_angularDirectionalDerivative` with the minus restored.
example : ∀ (s : ℝ) (a : Space) (f g : Lp ℂ 2 (volume : Measure Space)),
    (inner ℝ f (angularDirectionalDerivative s a g) : ℝ) =
      -(inner ℝ (angularDirectionalDerivative s a f) g : ℝ) :=
  real_inner_angularDirectionalDerivative

-- `WeakenedN1` is `gradientSobolevENorm_toReal_sq_eq_datum_sum` with `hA` restored.
example : ∀ (Z : SmoothL2Field Space) (m : ℕ) (A : RealVectorSobolev ((m : ℝ) + 1)),
    IsSobolevDatum ((m : ℝ) + 1) Z.field A →
    (gradientSobolevENorm (m : ℝ) Z.field).toReal ^ 2 =
      ∑ j : Fin 3, ‖((WithLp.toLp 2 fun i =>
          angularDirectionalDerivativeReal ((m : ℝ) + 1) (coordinateVector j) (A i)) :
          RealVectorSobolev (m : ℝ))‖ ^ 2 :=
  fun _Z m _A hA => gradientSobolevENorm_toReal_sq_eq_datum_sum m hA

/-! ## §5 — non-vacuity (non-degenerate witnesses; reviewer `p4_nonvacuity.lean`) -/

-- V0: the `SmoothL2Field Space` carrier is inhabited (so V1's `∀ Z` is not over an empty class).
example : Nonempty (SmoothL2Field Space) :=
  ⟨⟨fun _ => 0, contDiff_const, fun n => by simp⟩⟩

-- V1 (the strong witness): for ANY genuine smooth L² field and any m, the three datum hypotheses
-- of the datum-based exports hold simultaneously at orders m, m+1, m+2.
example (Z : SmoothL2Field Space) (m : ℕ) :
    IsSobolevDatum (m : ℝ) Z.field (smoothAngularDatum (m + 2) (m : ℝ) (by push_cast; linarith) Z)
    ∧ IsSobolevDatum ((m : ℝ) + 1) Z.field
        (smoothAngularDatum (m + 2) ((m : ℝ) + 1) (by push_cast; linarith) Z)
    ∧ IsSobolevDatum ((m : ℝ) + 2) Z.field
        (smoothAngularDatum (m + 2) ((m : ℝ) + 2) (by push_cast; linarith) Z) :=
  ⟨smoothAngularDatum_isSobolevDatum _ _ _ Z,
   smoothAngularDatum_isSobolevDatum _ _ _ Z,
   smoothAngularDatum_isSobolevDatum _ _ _ Z⟩

/-- A genuinely NONZERO element of the `L²` carrier (unlike the trivial `0` witness). -/
def unitBall : Lp ℂ 2 (volume : Measure Space) :=
  indicatorConstLp 2 (measurableSet_ball (x := (0 : Space)) (ε := 1))
    (measure_ball_lt_top (x := (0 : Space)) (r := 1)).ne (1 : ℂ)

theorem unitBall_ne_zero : unitBall ≠ 0 := by
  have h1 : (0 : ℝ) < (volume : Measure Space).real (ball (0 : Space) 1) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  have hpos : 0 < ‖unitBall‖ := by
    rw [unitBall, norm_indicatorConstLp (by norm_num) (by norm_num)]
    simp only [norm_one, one_mul]
    exact Real.rpow_pos_of_pos h1 _
  exact norm_pos_iff.mp hpos

-- V3 strengthened: strict, pairwise-distinct orders satisfying the lowering-pairing hypotheses.
example : ∃ s r t : ℝ, r < s ∧ t < s ∧ (r + t) / 2 < s ∧ r ≠ t :=
  ⟨1, 0, -1, by norm_num, by norm_num, by norm_num, by norm_num⟩

-- The lowering-pairing identity on a NONZERO element at strict, unequal orders.
example : (inner ℝ (angularOrderLowering 1 0 (by norm_num) unitBall)
      (angularOrderLowering 1 (-1) (by norm_num) unitBall) : ℝ) =
      ‖angularOrderLowering 1 ((0 + (-1)) / 2) (by norm_num) unitBall‖ ^ 2 :=
  real_inner_lowering_pairing 1 0 (-1) (by norm_num) (by norm_num) (by norm_num) unitBall

-- Skew-adjointness on a NONZERO element and a NONZERO direction.
example : (inner ℝ unitBall (angularDirectionalDerivative 1 (coordinateVector 0) unitBall) : ℝ) =
      -(inner ℝ (angularDirectionalDerivative 1 (coordinateVector 0) unitBall) unitBall : ℝ) :=
  real_inner_angularDirectionalDerivative 1 (coordinateVector 0) unitBall unitBall

#print axioms unitBall_ne_zero

end
