/-
  Lane 129 (SIMP-D01-orderzero) — POSITIVE tester file (must COMPILE).

  Non-vacuity witnesses for the six main exports of the five P2-chain modules
  `Section4/D01/{OrderZeroSymbol,OrderZeroCurl,OrderZeroAlgebra,MomentumSlice,PressureJets}`,
  plus the "conclusion has content" check (`const_not_jets`).  The companion file
  `negative_simp_p2_fail.lean` holds the load-bearing (drop-one-hypothesis) checks that MUST fail.

  Check:  cd verification && lake env lean ../research/D01/negative_simp_p2.lean
  Expect: exit 0, every `#print axioms` = [propext, Classical.choice, Quot.sound].

  `zeroSol` / `memForceR_zero` / `const_not_jets` reconstruct lane-117 reviewer appendix A
  (`research/D01/REVIEW_SL8_ASSEMBLY.md`); the `∇bump` nonzero curl-free witness reconstructs
  lane-108 reviewer `nonvac.lean` (`research/D01/REVIEW_ORDER_ZERO_CURL.md` §2(e)).
-/
import NSFormalization.Section4.D01.PressureJets

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.D01
open NSFormalization.Section4.A02 (ClassicalSolutionR)
open NSFormalization.Section4.A03 (partialDeriv)
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Source.RealSobolev (FourierData)
open scoped ContDiff

namespace Lane129Neg

/-! ## 0. Order-0 data helpers (the zero field is an order-0 datum at every order). -/

theorem datum_zero (s : ℝ) : IsSobolevDatum s (fun _ : Space => (0 : Space)) 0 := by
  intro i ψ; simp

theorem jets_zero : SmoothSquareIntegrableJets (fun _ : Space => (0 : Space)) := by
  refine ⟨contDiff_const, fun n => ?_⟩
  have hz : iteratedFDeriv ℝ n (fun _ : Space => (0 : Space)) = 0 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · ext x m; simp
    · exact iteratedFDeriv_const_of_ne (by omega) _
  rw [hz]; exact MemLp.zero

/-! ## 1. Non-vacuity of the `ClassicalSolutionR` exports — the zero solution.
    (A nonzero classical solution is out of reach; per the brief, `zeroSol` is the witness.) -/

/-- The zero solution with zero force on `[0,1)` (lane-117 reviewer appendix A, verbatim). -/
def zeroSol (ν : ℝ) : ClassicalSolutionR ν 0 0 1 where
  velocity := 0
  pressure := 0
  horizon_pos := zero_lt_one
  velocity_smooth := contDiffOn_const
  pressure_smooth := contDiffOn_const
  initial := fun _ => rfl
  divergence := by intro t _ x; simp [spatialDivergence, spatialDerivative]
  momentum := by
    intro t _ x
    simp [NavierStokesR3.ProblemStatement.navierStokesResidual, temporalDerivative, advection,
      spatialDerivative, spatialLaplacian, pressureGradient]
  sobolev := fun m => ⟨fun _ => 0, continuousOn_const, fun t _ => datum_zero _⟩
  pressure_gradient := by intro t _; simp [pressureGradient]

theorem memForceR_zero : MemForceR (0 : VelocityField) := by
  refine ⟨contDiffOn_const, fun m => ⟨fun _ => 0, fun t _ => datum_zero _, contDiffOn_const, ?_, ?_⟩⟩
  · exact MemLp.zero
  · exact MemLp.zero

/-- `orderZeroDatum_pressureGradient_eq` (PressureJets, SL8 row i.7) is inhabited. -/
theorem nonvac_orderZeroDatum_pressureGradient_eq (ν : ℝ) :
    orderZeroDatum (memLp_pressureGradient_slice (zeroSol ν) (t := 1/2) (by constructor <;> norm_num))
      = Leray.lerayComplement 0
          (orderZeroDatum (smoothL2_momentumResidual_slice (zeroSol ν) memForceR_zero
            (t := 1/2) (by constructor <;> norm_num)).memLp) :=
  orderZeroDatum_pressureGradient_eq (zeroSol ν) memForceR_zero (by constructor <;> norm_num)

/-- P2 itself is inhabited on the zero solution. -/
theorem nonvac_pressureGradient_jets (ν : ℝ) :
    SmoothSquareIntegrableJets (fun x : Space => pressureGradient (zeroSol ν).pressure (1/2) x) :=
  pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR (zeroSol ν) memForceR_zero
    (by constructor <;> norm_num)

/-- The `∂ₜu ∈ H^∞` corollary is inhabited. -/
theorem nonvac_temporalDerivative_jets (ν : ℝ) :
    SmoothSquareIntegrableJets (fun x : Space => temporalDerivative (zeroSol ν).velocity (1/2) x) :=
  temporalDerivative_slice_smoothSquareIntegrableJets_of_memForceR (zeroSol ν) memForceR_zero
    (by constructor <;> norm_num)

/-- The datum-existence (`hP`) export is inhabited at every order. -/
theorem nonvac_exists_datum (ν : ℝ) (m : ℕ) :
    ∃ P : RealVectorSobolev (m : ℝ),
      IsSobolevDatum (m : ℝ) (fun x : Space => pressureGradient (zeroSol ν).pressure (1/2) x) P :=
  exists_isSobolevDatum_pressureGradient_slice (zeroSol ν) memForceR_zero
    (by constructor <;> norm_num) m

/-! ## 2. The conclusion class is NOT trivially true of every smooth field
    (`const_not_jets`, lane-117 reviewer appendix A): a nonzero constant field is `C^∞` but not
    in the jet class.  So the P2 conclusion `SmoothSquareIntegrableJets` has real content. -/

theorem const_not_jets {c : Space} (hc : c ≠ 0) :
    ContDiff ℝ ∞ (fun _ : Space => c) ∧ ¬ SmoothSquareIntegrableJets (fun _ : Space => c) := by
  refine ⟨contDiff_const, ?_⟩
  rintro ⟨-, h⟩
  have h0 := h 0
  have hconst : MemLp (fun _ : Space => c) 2 volume := by
    refine ⟨aestronglyMeasurable_const, ?_⟩
    have h2 := h0.2
    rwa [eLpNorm_congr_norm_ae (f := iteratedFDeriv ℝ 0 (fun _ : Space => c))
      (g := fun _ : Space => c)
      (Filter.Eventually.of_forall (fun x => by simp [norm_iteratedFDeriv_zero]))] at h2
  rcases (memLp_const_iff (p := 2) two_ne_zero (by simp)).mp hconst with hz | hv
  · exact hc hz
  · simp at hv

/-! ## 3. Non-vacuity of the order-0 / algebra exports — the zero field satisfies every hypothesis.
    So the transverse / longitudinal / additive / Leray-fixed classes are all inhabited. -/

theorem zero_memLp : MemLp (fun _ : Space => (0 : Space)) 2 volume := MemLp.zero
theorem zero_smooth : ContDiff ℝ ∞ (fun _ : Space => (0 : Space)) := contDiff_const

/-- `orderZeroDatum_transverse_of_divergence_free` is inhabited (zero field is divergence-free). -/
theorem nonvac_transverse :
    ∀ᵐ ξ : Space ∂volume,
      ∑ j : Fin 3, ((ξ j : ℝ) : ℂ) * ((orderZeroDatum zero_memLp j : FourierData) ξ) = 0 :=
  orderZeroDatum_transverse_of_divergence_free zero_memLp zero_smooth
    (fun x => by simp [NSFormalization.Section4.A03.partialDeriv, NSFormalization.Section4.A03.lift,
      spatialDerivative])

/-- `orderZeroDatum_longitudinal_of_curl_free` is inhabited (zero field is curl-free). -/
theorem nonvac_longitudinal :
    ∀ᵐ ξ : Space ∂volume, ∀ i j : Fin 3,
      ((ξ i : ℝ) : ℂ) * ((orderZeroDatum zero_memLp j : FourierData) ξ)
        = ((ξ j : ℝ) : ℂ) * ((orderZeroDatum zero_memLp i : FourierData) ξ) :=
  orderZeroDatum_longitudinal_of_curl_free zero_memLp zero_smooth
    (fun i j x => by simp [NSFormalization.Section4.A03.partialDeriv, NSFormalization.Section4.A03.lift,
      spatialDerivative])

/-- `lerayComplement_zero_orderZeroDatum_eq_self` is inhabited. -/
theorem nonvac_leray :
    Leray.lerayComplement 0 (orderZeroDatum zero_memLp) = orderZeroDatum zero_memLp :=
  Leray.lerayComplement_zero_orderZeroDatum_eq_self zero_memLp zero_smooth
    (fun i j x => by simp [NSFormalization.Section4.A03.partialDeriv, NSFormalization.Section4.A03.lift,
      spatialDerivative])

/-- `orderZeroDatum_add` is inhabited. -/
theorem nonvac_add :
    orderZeroDatum (zero_memLp.add zero_memLp)
      = orderZeroDatum zero_memLp + orderZeroDatum zero_memLp :=
  orderZeroDatum_add zero_memLp zero_memLp

/-! ## 4. A NONZERO curl-free witness `∇(bump)` for the order-0 longitudinal / Leray-fixed class.
    `∇(bump)` is smooth, `L²` (compact support), curl-free (Clairaut, via the module's own
    `partialDeriv_gradient_eq_sndFDeriv`), and nonzero — so the curl-free hypothesis class of
    `orderZeroDatum_longitudinal_of_curl_free` / `lerayComplement_zero_orderZeroDatum_eq_self` is
    NOT forced to `z = 0`.  Reconstructs lane-108 reviewer `nonvac.lean`. -/

/-- Time-independent bump as a scalar pressure field. -/
noncomputable def pbump : PressureField := fun q => (Cut.bump : Space → ℝ) q.2
/-- The gradient field `∇(bump)`. -/
noncomputable def gradBump : Space → Space := fun y => pressureGradient pbump 0 y

theorem gradBump_apply (x : Space) (j : Fin 3) :
    (gradBump x).ofLp j = fderiv ℝ (fun z : Space => (Cut.bump : Space → ℝ) z) x (coordinateVector j) :=
  pressureGradient_apply pbump 0 x j

theorem gradBump_smooth : ContDiff ℝ ∞ gradBump := by
  have hd : ContDiff ℝ ∞ (fun y : Space => fderiv ℝ (fun z : Space => pbump (0, z)) y) :=
    Cut.bump_smooth.fderiv_right (m := ∞) (by simp)
  show ContDiff ℝ ∞ (fun y : Space => pressureGradient pbump 0 y)
  refine ContDiff.sum (fun k _ => ?_)
  exact ContDiff.smul
    ((ContinuousLinearMap.apply ℝ ℝ (coordinateVector k)).contDiff.comp hd) contDiff_const

theorem gradBump_zero_far {x : Space} (hx : (2 : ℝ) < ‖x‖) : gradBump x = 0 := by
  have hfd : fderiv ℝ (fun z : Space => (Cut.bump : Space → ℝ) z) x = 0 := by
    have hev : (fun z : Space => (Cut.bump : Space → ℝ) z) =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
      have hopen : IsOpen {y : Space | (2 : ℝ) < ‖y‖} := isOpen_lt continuous_const continuous_norm
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact Cut.bump.zero_of_le_dist (by rw [dist_zero_right]; exact le_of_lt hy)
    rw [hev.fderiv_eq]; simp
  apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
  ext j
  show (gradBump x).ofLp j = (0 : Space).ofLp j
  rw [gradBump_apply, hfd]; simp

theorem gradBump_cs : HasCompactSupport gradBump := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Space) 2)
  intro x hx
  rw [mem_closedBall_zero_iff, not_le] at hx
  exact gradBump_zero_far hx

theorem gradBump_mem : MemLp gradBump 2 volume :=
  gradBump_smooth.continuous.memLp_of_hasCompactSupport gradBump_cs

theorem gradBump_curl (i j : Fin 3) (x : Space) :
    (partialDeriv i gradBump x).ofLp j = (partialDeriv j gradBump x).ofLp i := by
  have hφ : ContDiff ℝ ∞ (fun z : Space => pbump (0, z)) := Cut.bump_smooth
  have hφ2 : ContDiffAt ℝ 2 (fun z : Space => pbump (0, z)) x := hφ.contDiffAt.of_le (by norm_num)
  show partialDeriv i (fun y : Space => pressureGradient pbump 0 y) x j
      = partialDeriv j (fun y : Space => pressureGradient pbump 0 y) x i
  rw [partialDeriv_gradient_eq_sndFDeriv pbump 0 hφ i j x,
      partialDeriv_gradient_eq_sndFDeriv pbump 0 hφ j i x]
  exact (hφ2.isSymmSndFDerivAt (by norm_num)).eq (coordinateVector i) (coordinateVector j)

/-- Reconstruction of a Euclidean vector from its coordinates. -/
theorem euclid_recon (v : Space) : v = ∑ j : Fin 3, (v.ofLp j) • coordinateVector j := by
  ext k; simp [coordinateVector, Pi.single_apply]

/-- `∇(bump) ≠ 0`: were it zero, every directional derivative of `bump` would vanish, forcing
`bump` constant, contradicting `bump 0 = 1` and `bump (3·e₀) = 0`. -/
theorem gradBump_ne_zero : gradBump ≠ 0 := by
  intro hcontra
  have hcomp : ∀ (x : Space) (j : Fin 3),
      fderiv ℝ (fun z : Space => (Cut.bump : Space → ℝ) z) x (coordinateVector j) = 0 := by
    intro x j
    have hz : (gradBump x).ofLp j = (0 : Space).ofLp j := by rw [hcontra]; rfl
    rw [gradBump_apply] at hz; simpa using hz
  have hfd0 : ∀ x : Space, fderiv ℝ (fun z : Space => (Cut.bump : Space → ℝ) z) x = 0 := by
    intro x
    ext v
    rw [euclid_recon v, map_sum]
    simp [hcomp x]
  have hconst := is_const_of_fderiv_eq_zero
    (Cut.bump_smooth.differentiable (by simp)) hfd0
    (0 : Space) (EuclideanSpace.single (0 : Fin 3) (3 : ℝ))
  have h0 : (Cut.bump : Space → ℝ) 0 = 1 := Cut.bump_one (by simp)
  have hfar : (Cut.bump : Space → ℝ) (EuclideanSpace.single (0 : Fin 3) (3 : ℝ)) = 0 := by
    apply Cut.bump.zero_of_le_dist
    rw [dist_zero_right, PiLp.norm_single]
    show (2 : ℝ) ≤ ‖(3 : ℝ)‖
    rw [Real.norm_eq_abs]; norm_num
  rw [h0, hfar] at hconst
  exact one_ne_zero hconst

/-- `∇(bump)` is a NONZERO longitudinal (curl-free) order-0 witness. -/
theorem nonvac_longitudinal_nonzero :
    gradBump ≠ 0 ∧
    (∀ᵐ ξ : Space ∂volume, ∀ i j : Fin 3,
      ((ξ i : ℝ) : ℂ) * ((orderZeroDatum gradBump_mem j : FourierData) ξ)
        = ((ξ j : ℝ) : ℂ) * ((orderZeroDatum gradBump_mem i : FourierData) ξ)) :=
  ⟨gradBump_ne_zero,
   orderZeroDatum_longitudinal_of_curl_free gradBump_mem gradBump_smooth gradBump_curl⟩

/-- `∇(bump)` is a NONZERO field fixed by the order-0 Leray complement. -/
theorem nonvac_leray_nonzero :
    gradBump ≠ 0 ∧
    Leray.lerayComplement 0 (orderZeroDatum gradBump_mem) = orderZeroDatum gradBump_mem :=
  ⟨gradBump_ne_zero,
   Leray.lerayComplement_zero_orderZeroDatum_eq_self gradBump_mem gradBump_smooth gradBump_curl⟩

/-! ## 5. GENUINE COUNTEREXAMPLE — the `hdiv`-free transverse statement is provably FALSE.

    Lifted verbatim from the lane-129 reviewer's `research/D01/REVIEW_SIMP_P2.md` §6 (credit: opus
    reviewer, 2026-09-13), correcting this lane's earlier (wrong) claim that a counterexample was
    "not feasible in a SIMP lane".  No Fourier computation is needed: the `hdiv`-free transverse
    statement, applied to the nonzero curl-free `∇bump`, collapses `orderZeroDatum gradBump = 0`
    (`lerayComplement_eq_zero_of_transverse` + lane-108's `lerayComplement_zero_orderZeroDatum_eq_self`),
    which by `isSobolevDatum_orderZeroDatum` tested against `∇bump`'s own components gives
    `∫ (∂ᵢbump)² = 0`, i.e. `∇bump ≡ 0`, contradicting `gradBump_ne_zero`. -/

/-- The `hdiv`-free transverse statement, quantified exactly as `transverse_drop_hdiv`. -/
def TransverseNoDiv : Prop :=
  ∀ {z : Space → Space} (hz : MemLp z 2 volume), ContDiff ℝ ∞ z →
    ∀ᵐ ξ : Space ∂volume,
      ∑ j : Fin 3, ((ξ j : ℝ) : ℂ) * ((orderZeroDatum hz j : FourierData) ξ) = 0

/-- Step 1: the hypothetical statement collapses the datum of `∇bump` to zero. -/
theorem datum_gradBump_zero (H : TransverseNoDiv) :
    orderZeroDatum gradBump_mem = 0 := by
  have h1 : Leray.lerayComplement 0 (orderZeroDatum gradBump_mem) = 0 :=
    Leray.lerayComplement_eq_zero_of_transverse 0 (orderZeroDatum gradBump_mem)
      (H gradBump_mem gradBump_smooth)
  have h2 : Leray.lerayComplement 0 (orderZeroDatum gradBump_mem) = orderZeroDatum gradBump_mem :=
    Leray.lerayComplement_zero_orderZeroDatum_eq_self gradBump_mem gradBump_smooth gradBump_curl
  rw [h2] at h1; exact h1

noncomputable def gi (i : Fin 3) : Space → ℝ := fun x => (gradBump x).ofLp i

theorem gi_smooth (i : Fin 3) : ContDiff ℝ ∞ (gi i) :=
  ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff).comp gradBump_smooth

theorem gi_cs (i : Fin 3) : HasCompactSupport (gi i) :=
  gradBump_cs.comp_left (g := fun v : Space => v.ofLp i) (by simp)

noncomputable def psi (i : Fin 3) : SchwartzMap Space ℂ :=
  (gi_cs i |>.comp_left (g := fun r : ℝ => ((r : ℝ) : ℂ)) (by simp)).toSchwartzMap
    (by exact (Complex.ofRealCLM.contDiff).comp (gi_smooth i))

theorem psi_apply (i : Fin 3) (x : Space) : psi i x = ((gi i x : ℝ) : ℂ) := rfl

/-- Step 2: a zero order-0 datum forces the field to vanish, contradicting `gradBump ≠ 0`. -/
theorem gradBump_eq_zero_of_datum_zero (h0 : orderZeroDatum gradBump_mem = 0) : False := by
  have hds := isSobolevDatum_orderZeroDatum gradBump_mem
  rw [h0] at hds
  have hzero : ∀ i : Fin 3, ∫ x : Space, (psi i) x * ((gradBump x).ofLp i : ℝ) = 0 := by
    intro i
    have := hds i (psi i)
    simpa using this.symm
  have hsq : ∀ i : Fin 3, (fun x : Space => gi i x * gi i x) =ᵐ[volume] 0 := by
    intro i
    have hint : Integrable (fun x : Space => gi i x * gi i x) volume :=
      ((gi_smooth i).continuous.mul (gi_smooth i).continuous).integrable_of_hasCompactSupport
        ((gi_cs i).mul_right)
    have hre : ∫ x : Space, gi i x * gi i x = 0 := by
      have h1 := hzero i
      simp only [psi_apply] at h1
      have h2 : ∫ x : Space, (((gi i x * gi i x : ℝ)) : ℂ) = 0 := by
        rw [← h1]
        refine integral_congr_ae ?_
        filter_upwards with x
        simp only [gi]; push_cast; ring
      rw [integral_complex_ofReal] at h2
      exact_mod_cast h2
    exact (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg _) hint).mp hre
  have hgi : ∀ (i : Fin 3) (x : Space), gi i x = 0 := by
    intro i
    have hfun : gi i = (fun _ : Space => (0 : ℝ)) := by
      refine ((gi_smooth i).continuous.ae_eq_iff_eq volume
        (continuous_const : Continuous fun _ : Space => (0 : ℝ))).mp ?_
      filter_upwards [hsq i] with x hx
      have hx' : gi i x * gi i x = 0 := by simpa using hx
      exact mul_self_eq_zero.mp hx'
    intro x; exact congrFun hfun x
  apply gradBump_ne_zero
  funext x
  apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
  ext i
  show (gradBump x).ofLp i = (0 : Space).ofLp i
  have h := hgi i x
  simp only [gi] at h
  simpa using h

/-- **The `hdiv`-free transverse statement is FALSE** — so `hdiv` is load-bearing in the strong
(falsification) sense, not merely "the established proof route needs it". -/
theorem transverse_without_hdiv_is_false : ¬ TransverseNoDiv := fun H =>
  gradBump_eq_zero_of_datum_zero (datum_gradBump_zero H)

#print axioms nonvac_orderZeroDatum_pressureGradient_eq
#print axioms nonvac_pressureGradient_jets
#print axioms nonvac_temporalDerivative_jets
#print axioms nonvac_exists_datum
#print axioms const_not_jets
#print axioms nonvac_transverse
#print axioms nonvac_longitudinal
#print axioms nonvac_leray
#print axioms nonvac_add
#print axioms gradBump_ne_zero
#print axioms nonvac_longitudinal_nonzero
#print axioms nonvac_leray_nonzero
#print axioms transverse_without_hdiv_is_false

end Lane129Neg
