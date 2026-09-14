import NSFormalization.Section4.A01.Continuation

/-!
# A01 unit A2b / A3 row A2b-b — invariance-carrying forced global mild continuation

This module removes the angle-invariance hypothesis `hinv` that lane 126 left exposed in
`NSFormalization.Section4.A01.Continuation.forced_global_of_bound'`.  It does so by *forking*
the vendor window induction that builds the continued solution so it carries the
angle-invariance clause window by window, following the lane-126 reviewer's three-step recipe
(`research/A01/REVIEW_A2B.md` §3), and never edits the frozen `Continuation.lean`.

No *global* mild uniqueness is used.  `EulerBoundedMildContinuation.exists_global_mild_of_bound`
is built by iterating windows of length `δ` obtained from `exists_positive_time_budget`, and
that `δ` *guarantees* `kernelMass δ · L < 1` (`Euler/UniformHeatLocal.lean:42-54`): **the
continuation's own windows are the uniqueness regime of `mild_solution_unique`.**  On each such
window the covariance/uniqueness argument of
`Source/ForcedCylinderInvariant.lean:71-112` pins the angle-translated solution to the solution.

## What is proved

* `restart_window_invariance` — **(step 1a)** every `R`-bounded forced mild solution on a
  restart window `[b, b+T]` of length `T ≤ δ` with angle-invariant datum is angle-invariant.
  The reviewer's Probe 2 (`research/A01/probes/probe_restart_window_invariance.lean`),
  promoted verbatim and credited; the contraction `kernelMass T · L < 1` is discharged from
  `exists_positive_time_budget`, not assumed.  Needs `maxHeartbeats 600000`.
* `exists_uniform_restart_time_invariant` — **(step 1b)** the vendor uniform restart together
  with the per-window invariance: invariant data `‖u₀‖ ≤ R` on windows of one fixed length `δ`
  have a forced mild solution with `‖u‖ ≤ R+1`, the window Duhamel equation and angle
  invariance.  Existence is `EulerUniformHeatLocal.exists_uniform_restart_time`; the two window
  lengths are combined with `min`.
* `gluePath_invariant` — **(step 2)** the clamped adjacent-window pasting `gluePath` of two
  angle-invariant paths is angle-invariant.
* `forced_global_mild_of_bound_invariant` — **(step 3)** the fork of
  `EulerBoundedMildContinuation.exists_global_mild_of_bound`'s window induction that carries
  invariance: the a-priori bound `hbound` yields the forced mild solution on all of `[0,S]`
  with `‖u‖ ≤ R`, the right initial value, the forced Duhamel equation and angle invariance of
  `u` on all of `[0,S]`.
* `forced_global_of_bound_unconditional` — **(step 4)** the full `exists_local`-shaped
  conclusion on the prescribed `[0,S]` from the a-priori bound `hbound` **alone**: this is
  `Continuation.forced_global_of_bound'` with `hinv` removed, discharged by step 3.  This closes
  A01 unit A2b except for supplying `hbound` (A3's job).
-/

noncomputable section

namespace NSFormalization.Section4.A01

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
open EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerSmoothFieldSobolevTime EulerQuadraticSource EulerSobolevHeat EulerVolterraConvolution
open NSFormalization.Source.ForcedCylinderLocal NSFormalization.Source.OrdinaryCylinderDescent
open EulerBoundedMildContinuation EulerDivergenceFreeHeat EulerUniformHeatLocal
open EulerTimePathGluing EulerQuadraticMildPasting
open scoped Topology ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-! ## Step 1a — per-window invariance (reviewer probe, promoted and credited) -/

set_option maxHeartbeats 600000 in
/-- **Per-window angle invariance** (reviewer probe, lane 126 review
`research/A01/REVIEW_A2B.md` §F6b, Probe 2 = `research/A01/probes/probe_restart_window_invariance.lean`,
promoted verbatim and credited).  Every `R`-bounded forced mild solution on a restart window
`[b, b+T]` of length `T ≤ δ` with angle-invariant datum is itself angle-invariant.  The
contraction `hsmall : kernelMass T · L < 1` is **discharged** (not assumed): the window length
`δ` from `exists_positive_time_budget` guarantees `kernelMass δ · L < 1`
(`Euler/UniformHeatLocal.lean:42-54`), so the continuation's own windows are the uniqueness
regime.  Needs `maxHeartbeats 600000` (the reviewer bisected `400000` as failing). -/
theorem restart_window_invariance {q : ℕ} (hq : 6 ≤ q) {ν S R : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (hR : 0 ≤ R)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ S ∧
      ∀ (b T : ℝ) (hb : 0 ≤ b) (hT : 0 ≤ T) (hbT : b + T ≤ S), T ≤ δ →
        ∀ u₀ : SobolevSpace 1 (q + 1),
          (∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u₀ = u₀) →
          ∀ u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)), ‖u‖ ≤ R →
            (∀ t : Icc (0 : ℝ) T, u t = heatOperator 1 (q + 1) (2 * ν * t.val).toNNReal u₀ +
              ∫ r in (0 : ℝ)..t.val, heatKernel 1 q ν hν r
                ((coefficients 1 hq (sobolevPath F hF q)).apply
                  (timeWindow b T hb hbT (projIcc 0 T hT (t.val - r)))
                  (u (projIcc 0 T hT (t.val - r))))) →
            ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t := by
  set f := sobolevPath F hF q with hfdef
  set C := coefficients 1 hq f with hCdef
  obtain ⟨δ, hδ, hδS, _, hl⟩ :=
    exists_positive_time_budget ν (C.ballBound R) (C.ballLipschitz R) 1 S (by norm_num) hS
  refine ⟨δ, hδ, hδS, ?_⟩
  intro b T hb hT hbT hTδ u₀ hi u hu hsol θ t
  have hsmall : kernelMass T (parabolicKernelBound ν) * C.ballLipschitz R < 1 := by
    have hmass := EulerUniformHeatLocal.parabolic_mass_mono ν T δ hTδ
    have hL := C.ballLipschitz_nonneg R hR
    have := mul_le_mul_of_nonneg_right hmass hL
    simpa only [kernelMass, parabolicKernelBound_integral ν T hT] using this.trans_lt hl
  set G := (C.comp (timeWindow b T hb hbT)).apply with hGdef
  have hG : Continuous (fun p : Icc (0 : ℝ) T × SobolevSpace 1 (q + 1) => G p.1 p.2) :=
    (C.comp (timeWindow b T hb hbT)).continuous
  have hf : ∀ (θ : AddCircle (1 : ℝ)) s, sobolevTranslation 1 q (0, θ) (f s) = f s :=
    fun θ s => ordinarySobolev_angle q (F s).toLp (F s).translation_contDiff θ
  have hFL : ∀ (s : Icc (0 : ℝ) T) (x y : SobolevSpace 1 (q + 1)),
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖G s x - G s y‖ ≤ C.ballLipschitz R * ‖x - y‖ :=
    fun s x y hx hy => C.apply_sub_bound R hR (timeWindow b T hb hbT s) x y hx hy
  have hsolF : ∀ s : Icc (0 : ℝ) T,
      u s = freeHeatPath 1 (q + 1) ν T u₀ s +
        ∫ r in (0 : ℝ)..s.val, heatKernel 1 q ν hν r
          (G (projIcc 0 T hT (s.val - r)) (u (projIcc 0 T hT (s.val - r)))) := hsol
  let A := sobolevTranslation 1 (q + 1) (0, θ)
  let v : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)) :=
    ⟨fun s => A (u s), A.continuous.comp u.continuous⟩
  have hv : ‖v‖ ≤ R := by
    apply (ContinuousMap.norm_le _ hR).mpr
    intro s
    change ‖sobolevTranslation 1 (q + 1) (0, θ) (u s)‖ ≤ R
    rw [sobolevTranslation_norm]
    exact (ContinuousMap.norm_coe_le_norm u s).trans hu
  have hcov : ∀ (s : Icc (0 : ℝ) T) (w : SobolevSpace 1 (q + 1)),
      G s (A w) = sobolevTranslation 1 q (0, θ) (G s w) :=
    fun s w => source_translation 1 hq f (0, θ) (hf θ) (timeWindow b T hb hbT s) w
  have hsolv : ∀ s : Icc (0 : ℝ) T,
      v s = freeHeatPath 1 (q + 1) ν T u₀ s +
        ∫ r in (0 : ℝ)..s.val, heatKernel 1 q ν hν r
          (G (projIcc 0 T hT (s.val - r)) (v (projIcc 0 T hT (s.val - r)))) := by
    intro s
    change A (u s) = _
    rw [hsolF s, map_add]
    have hfree : A (freeHeatPath 1 (q + 1) ν T u₀ s) = freeHeatPath 1 (q + 1) ν T u₀ s := by
      change sobolevTranslation 1 (q + 1) (0, θ)
        (heatOperator 1 (q + 1) (2 * ν * s.val).toNNReal u₀) = _
      rw [← heatOperator_translation, hi θ]
      rfl
    rw [hfree]
    congr 1
    change (translationIsometry 1 (q + 1) (0, θ))
      (∫ r in (0 : ℝ)..s.val, heatKernel 1 q ν hν r
        (G (projIcc 0 T hT (s.val - r)) (u (projIcc 0 T hT (s.val - r))))) = _
    rw [← (translationIsometry 1 (q + 1) (0, θ)).intervalIntegral_comp_comm]
    apply intervalIntegral.integral_congr
    intro r _
    change A (heatKernel 1 q ν hν r (G _ (u _))) = heatKernel 1 q ν hν r (G _ (A (u _)))
    rw [hcov, heatKernel_translation]
  have huv := mild_solution_unique T hT (heatKernel 1 q ν hν) (parabolicKernelBound ν)
    (heatKernel_joint_continuous 1 q ν hν) (parabolicKernelBound_integrable ν T hT)
    (fun r hr => parabolicKernelBound_nonneg ν r hr.1)
    (fun r hr y => heatKernel_bound 1 q ν hν r hr.1 y)
    (freeHeatPath 1 (q + 1) ν T u₀) G hG R (C.ballLipschitz R)
    (C.ballLipschitz_nonneg R hR) hFL hsmall v u hv hu hsolv hsolF
  exact congrArg (fun w : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)) => w t) huv

/-! ## Step 1b — invariance-carrying uniform restart -/

/-- **Invariance-carrying uniform restart** (step 1b).  On restart windows `[a, a+T]` of one
fixed positive length `δ`, invariant data `u₀` with `‖u₀‖ ≤ R` have a forced mild solution with
`‖u‖ ≤ R+1`, the right initial value, the window Duhamel equation **and** angle invariance.
Existence is the vendor `EulerUniformHeatLocal.exists_uniform_restart_time`; invariance is
`restart_window_invariance` at solution bound `R+1`; the two window lengths are combined with
`min`. -/
theorem exists_uniform_restart_time_invariant {q : ℕ} (hq : 6 ≤ q) {ν S R : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (hR : 0 ≤ R)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ S ∧
      ∀ (a T : ℝ) (ha : 0 ≤ a) (hT : 0 ≤ T) (haT : a + T ≤ S), T ≤ δ →
        ∀ u₀ : SobolevSpace 1 (q + 1), ‖u₀‖ ≤ R →
          (∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u₀ = u₀) →
          ∃ u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)),
            ‖u‖ ≤ R + 1 ∧ u ⟨0, le_rfl, hT⟩ = u₀ ∧
            (∀ t : Icc (0 : ℝ) T, u t = heatOperator 1 (q + 1) (2 * ν * t.val).toNNReal u₀ +
              ∫ r in (0 : ℝ)..t.val, heatKernel 1 q ν hν r
                ((coefficients 1 hq (sobolevPath F hF q)).apply
                  (timeWindow a T ha haT (projIcc 0 T hT (t.val - r)))
                  (u (projIcc 0 T hT (t.val - r))))) ∧
            ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t := by
  obtain ⟨δ₁, hδ₁, hδ₁S, hloc⟩ :=
    exists_uniform_restart_time 1 q ν hν S hS R hR (coefficients 1 hq (sobolevPath F hF q))
  obtain ⟨δ₂, hδ₂, hδ₂S, hinv⟩ :=
    restart_window_invariance (R := R + 1) hq hν hS (by linarith) F hF
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, (min_le_left _ _).trans hδ₁S, ?_⟩
  intro a T ha hT haT hTδ u₀ hu₀ hu₀inv
  obtain ⟨u, hu, hu0, hsol⟩ :=
    hloc a T ha hT haT (le_trans hTδ (min_le_left _ _)) u₀ hu₀
  exact ⟨u, hu, hu0, hsol,
    hinv a T ha hT haT (le_trans hTδ (min_le_right _ _)) u₀ hu₀inv u hu hsol⟩

/-! ## Step 2 — invariance of the glued path -/

/-- **Step 2.**  The clamped adjacent-window pasting of two angle-invariant paths is
angle-invariant, over the vendor gluing `EulerTimePathGluing.gluePath`. -/
theorem gluePath_invariant {q : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (u : C(Icc (0 : ℝ) a, SobolevSpace 1 (q + 1)))
    (v : C(Icc (0 : ℝ) b, SobolevSpace 1 (q + 1)))
    (hmatch : u ⟨a, ha, le_rfl⟩ = v ⟨0, le_rfl, hb⟩)
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hv : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (v t) = v t) :
    ∀ (θ : AddCircle (1 : ℝ)) t,
      sobolevTranslation 1 (q + 1) (0, θ) (gluePath a b ha hb u v hmatch t) =
        gluePath a b ha hb u v hmatch t := by
  intro θ t
  change sobolevTranslation 1 (q + 1) (0, θ) (glueFunction a b ha hb u v t.val) =
    glueFunction a b ha hb u v t.val
  by_cases ht : t.val ≤ a
  · rw [glueFunction_left a b ha hb u v t.val ht]
    exact hu θ (projIcc 0 a ha t.val)
  · rw [glueFunction_right a b ha hb u v hmatch t.val (not_le.mp ht).le]
    exact hv θ (projIcc 0 b hb (t.val - a))

/-! ## Step 3 — the forked continuation induction carrying invariance -/

/-- **Step 3.**  Fork of `EulerBoundedMildContinuation.exists_global_mild_of_bound`'s window
induction, carrying angle invariance clause by clause.  From the a-priori bound `hbound`, the
forced mild solution on all of `[0,S]` exists with `‖u‖ ≤ R`, the right initial value, the
forced Duhamel equation **and** angle invariance of `u` on all of `[0,S]`.  Base datum
invariance is `ordinarySobolev_angle`; restart datum invariance is the inductive hypothesis;
per-window invariance is step 1b; glue invariance is step 2. -/
theorem forced_global_mild_of_bound_invariant {q : ℕ} (hq : 6 ≤ q) {ν S R : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (hR : 0 ≤ R)
    (a : SmoothL2Field Space)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (hu₀ : ‖ordinarySobolev (q + 1) a.toLp a.translation_contDiff‖ ≤ R)
    (hbound : ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
        (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1))),
        (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
            (coefficients 1 hq (sobolevPath F hF q))
            (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) → ‖u‖ ≤ R) :
    ∃ u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)),
      ‖u‖ ≤ R ∧
      u ⟨0, le_rfl, hS.le⟩ = ordinarySobolev (q + 1) a.toLp a.translation_contDiff ∧
      (∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
        (coefficients 1 hq (sobolevPath F hF q))
        (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) ∧
      ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t := by
  set u₀ := ordinarySobolev (q + 1) a.toLp a.translation_contDiff with hu₀def
  set C := coefficients 1 hq (sobolevPath F hF q) with hCdef
  have hu₀inv : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u₀ = u₀ :=
    fun θ => ordinarySobolev_angle (q + 1) a.toLp a.translation_contDiff θ
  obtain ⟨δ, hδ, _hδS, hlocal⟩ := exists_uniform_restart_time_invariant hq hν hS hR F hF
  have hind : ∀ n : ℕ, ∃ (a' : ℝ) (ha' : 0 ≤ a') (ha'S : a' ≤ S),
      min ((n : ℝ) * δ) S ≤ a' ∧
      ∃ u : C(Icc (0 : ℝ) a', SobolevSpace 1 (q + 1)),
        (∀ t, u t = quadraticDuhamel 1 ν hν ha' ha'S C u₀ u t) ∧
        ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t := by
    intro n
    induction n with
    | zero =>
      obtain ⟨u, _, _, hsol, hinvu⟩ := hlocal 0 0 le_rfl le_rfl (by linarith) hδ.le u₀ hu₀ hu₀inv
      refine ⟨0, le_rfl, hS.le, ?_, u, ?_, hinvu⟩
      · simpa only [Nat.cast_zero, zero_mul] using min_le_left (0 : ℝ) S
      · exact (quadratic_mild_window_iff 1 ν hν le_rfl hS.le C u₀ u).mpr hsol
    | succ n ih =>
      obtain ⟨a', ha', ha'S, hgrid, u, hsolu, hinvu⟩ := ih
      let b := min δ (S - a')
      have hb : 0 ≤ b := le_min hδ.le (sub_nonneg.mpr ha'S)
      have hbδ : b ≤ δ := min_le_left _ _
      have habS : a' + b ≤ S := by have h := min_le_right δ (S - a'); dsimp [b]; linarith
      have hu : ‖u ⟨a', ha', le_rfl⟩‖ ≤ R :=
        (u.norm_coe_le_norm _).trans (hbound a' ha' ha'S u hsolu)
      have hdatinv : ∀ θ : AddCircle (1 : ℝ),
          sobolevTranslation 1 (q + 1) (0, θ) (u ⟨a', ha', le_rfl⟩) = u ⟨a', ha', le_rfl⟩ :=
        fun θ => hinvu θ _
      obtain ⟨v, _, hv0, hsolv, hinvv⟩ :=
        hlocal a' b ha' hb habS hbδ (u ⟨a', ha', le_rfl⟩) hu hdatinv
      refine ⟨a' + b, add_nonneg ha' hb, habS, advance_grid S δ a' hδ.le n hgrid,
        gluePath a' b ha' hb u v hv0.symm, ?_, ?_⟩
      · exact glue_quadratic_mild 1 ν hν C a' b ha' hb ha'S habS u v hv0.symm u₀ hsolu hsolv
      · exact gluePath_invariant ha' hb u v hv0.symm hinvu hinvv
  obtain ⟨n, hn⟩ := exists_nat_ge (S / δ)
  have hN : S ≤ (n : ℝ) * δ := (div_le_iff₀ hδ).mp hn
  obtain ⟨a', ha', ha'S, hgrid, u, hsol, hinvu⟩ := hind n
  have hSa : S ≤ a' := by simpa only [min_eq_right hN] using hgrid
  have he : a' = S := le_antisymm ha'S hSa
  subst a'
  refine ⟨u, hbound S ha' ha'S u hsol, ?_, hsol, hinvu⟩
  have hz := hsol ⟨0, le_rfl, hS.le⟩
  simpa only [quadraticDuhamel, mul_zero, Real.toNNReal_zero, heatOperator_zero,
    intervalIntegral.integral_same, add_zero] using hz

/-! ## Step 4 — the unconditional final theorem -/

/-- **Step 4 — final theorem, `hinv` discharged.**  The full `exists_local`-shaped conclusion
on the prescribed `[0,S]` from the a-priori bound `hbound` **alone**: this is
`Continuation.forced_global_of_bound'` with the invariance obligation `hinv` removed,
discharged by step 3.  Closes A01 unit A2b except for supplying `hbound` (A3's job). -/
theorem forced_global_of_bound_unconditional {q : ℕ} (hq : 6 ≤ q) {ν S R : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (hR : 0 ≤ R)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (hu₀ : ‖ordinarySobolev (q + 1) a.toLp a.translation_contDiff‖ ≤ R)
    (hbound : ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
        (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1))),
        (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
            (coefficients 1 hq (sobolevPath F hF q))
            (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) → ‖u‖ ≤ R) :
    ∃ (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
      (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2)),
        ‖u‖ ≤ R ∧
        u ⟨0, le_rfl, hS.le⟩ = ordinarySobolev (q + 1) a.toLp a.translation_contDiff ∧
        U ⟨0, le_rfl, hS.le⟩ = a.toLp ∧
        (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
        (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
        (∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
          (coefficients 1 hq (sobolevPath F hF q))
          (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) ∧
        ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t := by
  obtain ⟨u, hu, hi, hm, hinvu⟩ :=
    forced_global_mild_of_bound_invariant hq hν hS hR a F hF hu₀ hbound
  have hd := forced_mild_divergenceFree hq hν hS a ha F hF u hm
  obtain ⟨U, hU0, hUl⟩ := forced_ordinary_descent hq hS a u hi hinvu
  exact ⟨u, U, hu, hi, hU0, hUl, hd, hm, hinvu⟩

end NSFormalization.Section4.A01
