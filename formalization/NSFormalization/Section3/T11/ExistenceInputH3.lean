import NSFormalization.Section3.T11.MildClassical
import NSFormalization.Section3.T11.ExtendsBeyond

/-!
# T11 / U9e — the `H³`-ball quantitative local-existence input, proved outright

`research/T11/LEAD_AMENDMENTS.md` amendment 2.  Lane 313's Picard horizon is
governed by the `H³` norm of the datum and by the force size, so the horizon it
produces is uniform over an **`H³`** ball, not over the `H¹` ball of the
manuscript's named predicate.  This module

* states `PeriodicQuantitativeLocalInputH3`, which is
  `PeriodicQuantitativeLocalInput'` (`Section3/T11/LocalExistence.lean:24`,
  amendment 1) with `periodicSobolevENorm 3 a ≤ K` in place of
  `periodicSobolevENorm 1 a ≤ K` and nothing else changed, and **proves it**
  (`periodicQuantitativeLocalInputH3`); and
* re-instantiates the continuation chain of lanes 321/332/337/323 at the `H³`
  ball, so that `restartH3`, `restartBeyondH3`, `extendsBeyondH3`,
  `lifespanInfiniteOfLocallyFiniteH3` and `exists_maximal_unconditional` carry
  no `PeriodicQuantitativeLocalInput'` hypothesis at all.

## The horizon and its dependence

`picardHorizon ν K M` is the explicit Picard horizon
`torusKernelTime ν (torusPicardThreshold ‖bilinear‖ (K.toReal + (M 3).toReal))`.
It depends only on `ν` (through the canonical two-space contract
`torusContractOf ν hν` of lane 317 and through the heat kernel mass), on the
datum-norm bound `K`, and on the single force bound `M 3`; in particular it is
chosen **before** the datum `a` and the force `g`, which is exactly the
uniformity the predicate asks for.

## Which force orders are used

Exactly one: `forceSobolevENormT 1 (3 : ℝ) g ≤ M 3`.  The Picard iteration runs
in `H³ × H²`, so the only force quantity entering the affine part of the Picard
map is the order-three Leray-projected datum path.  That bound is an
`L¹_t H³_x` bound, not a supremum bound, so the classical
`torus_forcedLinear_bound` (which consumes a supremum) is replaced here by
`torus_forcedLinear_bound_L1`: the Duhamel force term is dominated by
`∫₀^T ‖F s‖ ds` because the heat evolution is a contraction at every order.  The
passage from the extended norm to the interval integral is
`intervalIntegral_norm_le_of_forceENorm`, which uses that the order-`s` datum
path of a field is unique on `[0, ∞)` (`datum_unique`), so the infimum defining
`forceSobolevENormT` is attained at the smooth path of lane 334's
`exists_smooth_forceDatumPath`.  No other order of `M` is consumed: all higher
orders enter only through lane 330's `persistence_unconditional`, which is
unconditional.

## What is *not* proved

The `H¹`-ball statements — `PeriodicQuantitativeLocalInput'` itself and the V1
`restart`/`restartBeyond` fields with `periodicSobolevENorm 1` balls — remain
open; see `research/T11/H1_GAP.md`.  They are the subcritical Fujita–Kato local
theory, which is not in the tree.
-/

noncomputable section

namespace NSFormalization.Section3.T11

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar forceTimeMeasure)
open NSFormalization.Section3.T10
open scoped ContDiff ENNReal NNReal

-- Named (never anonymous) short-circuits for the `lp`-based carrier; the global
-- searches on `↥(PeriodicSobolev s)` time out at the default heartbeat budget.
local instance existenceInputH3NormedGroup (s : ℝ) :
    NormedAddCommGroup (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedAddCommGroup
local instance existenceInputH3NormedSpace (s : ℝ) :
    NormedSpace ℝ (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedSpace
local instance existenceInputH3SecondCountableEither (s : ℝ) :
    SecondCountableTopologyEither ℝ (PeriodicSobolev s) :=
  ⟨Or.inl inferInstance⟩

/-! ## 0. The statement -/

/-- **Amendment 2's existence input.**  Verbatim
`PeriodicQuantitativeLocalInput'` with the datum ball taken at order three:
`periodicSobolevENorm 3 a ≤ K` replaces `periodicSobolevENorm 1 a ≤ K`, and
every other quantifier and hypothesis — including the order-wise force bounds
`M` — is unchanged. -/
def PeriodicQuantitativeLocalInputH3 : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ → ∀ M : ℕ → ℝ≥0∞, (∀ m, M m ≠ ⊤) → ∃ δ : ℝ, 0 < δ ∧
    ∀ a : SpatialField, a ∈ initialClassT → periodicSobolevENorm 3 a ≤ K →
      ∀ g : SpaceTimeField, ContDiff ℝ ∞ g → IsPeriodicOn univ g →
        (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ M m) →
          ∃ w : ClassicalSolutionT ν a g δ, PeriodicLocalRegularity ν a g δ w

/-! ## 1. The force side: from `L¹_t H^s` extended norms to interval integrals -/

/-- The order-`s` datum path of a field is unique on `[0, ∞)`, so the infimum
defining `forceSobolevENormT` is attained at **every** admissible path.  This is
the only place where the `L¹`-in-time force bound is unpacked. -/
theorem forceSobolevENormT_eq_of_path (s : ℝ) {g : SpaceTimeField}
    {G : ℝ → PeriodicSobolev s} (hG : IsPeriodicSobolevPath s g G)
    (hm : AEStronglyMeasurable G forceTimeMeasure) :
    forceSobolevENormT 1 s g = eLpNorm G 1 forceTimeMeasure := by
  refine le_antisymm (iInf_le_of_le ⟨G, hG, hm⟩ le_rfl) (le_iInf ?_)
  rintro ⟨G', hG', -⟩
  have hae : G' =ᵐ[forceTimeMeasure] G := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact datum_unique s (fun x ↦ g (t, x)) (G' t) (G t)
      (hG' t (le_of_lt ht)) (hG t (le_of_lt ht))
  exact le_of_eq (eLpNorm_congr_ae hae).symm

/-- An `L¹_t H^s` bound on a force controls the `[0,1]` interval integral of the
`H^s` norm of its datum path.  This is the form the affine part of the Picard
map consumes. -/
theorem intervalIntegral_norm_le_of_forceENorm (s : ℝ) {g : SpaceTimeField}
    {G : ℝ → PeriodicSobolev s} (hG : IsPeriodicSobolevPath s g G)
    (hc : Continuous G) {N : ℝ≥0∞} (hN : N ≠ ⊤)
    (hb : forceSobolevENormT 1 s g ≤ N) :
    ∫ t in (0 : ℝ)..1, ‖G t‖ ≤ N.toReal := by
  have heq := forceSobolevENormT_eq_of_path s hG hc.aestronglyMeasurable
  have hint : IntegrableOn (fun t ↦ ‖G t‖) (Ioc (0 : ℝ) 1) volume :=
    (hc.norm.intervalIntegrable 0 1).1
  rw [intervalIntegral.integral_of_le zero_le_one]
  have hX0 : 0 ≤ ∫ t in Ioc (0 : ℝ) 1, ‖G t‖ :=
    integral_nonneg (fun _ ↦ norm_nonneg _)
  have hkey : ENNReal.ofReal (∫ t in Ioc (0 : ℝ) 1, ‖G t‖) ≤ N := by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall (fun _ ↦ norm_nonneg _))]
    calc ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal ‖G t‖
        ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal ‖G t‖ :=
          lintegral_mono_set Ioc_subset_Ioi_self
      _ = eLpNorm G 1 forceTimeMeasure := by
          rw [eLpNorm_one_eq_lintegral_enorm]
          simp only [ofReal_norm]
      _ = forceSobolevENormT 1 s g := heq.symm
      _ ≤ N := hb
  have hmono := ENNReal.toReal_mono hN hkey
  rwa [ENNReal.toReal_ofReal hX0] at hmono

/-! ## 2. The affine part of the Picard map under an `L¹` force bound -/

/-- The heat evolution of the contract is a contraction at order three. -/
theorem torus_linearEvolution_norm_le {ν : ℝ} (hν : 0 ≤ ν)
    (C : TorusTwoSpaceContract ν) (s : ℝ≥0) (D : PeriodicSobolev 3) :
    ‖C.analytic.linearEvolution s D‖ ≤ ‖D‖ := by
  have he : C.analytic.linearEvolution s D = torusHeat 3 hν s.2 D := by
    apply Subtype.ext
    apply WithLp.ofLp_injective 2
    funext i
    ext k
    exact C.linear_symbol s D i k
  rw [he]
  exact torusHeat_norm_le 3 hν s.2 D

/-- **`L¹`-in-time version of `torus_forcedLinear_bound`.**  The affine part of
the forced Picard map is bounded by `‖A‖` plus the *time integral* of the force
norm over the whole window — no supremum bound on the force is needed, which is
what makes the order-wise `L¹_t H^m` hypotheses of amendment 1 usable. -/
theorem torus_forcedLinear_bound_L1 {ν T : ℝ} (hν : 0 ≤ ν)
    (C : TorusTwoSpaceContract ν) (A : PeriodicSobolev 3)
    (F : ℝ → PeriodicSobolev 3) (hT : 0 ≤ T)
    (hFc : ContinuousOn F (Icc 0 T)) {B : ℝ}
    (hB : ∫ s in (0 : ℝ)..T, ‖F s‖ ≤ B) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    ‖C.analytic.linearEvolution ⟨t, ht.1⟩ A +
      ∫ s in (0 : ℝ)..t,
        C.analytic.linearEvolution (Real.toNNReal (t - s)) (F s)‖ ≤ ‖A‖ + B := by
  have hnorm : IntervalIntegrable (fun s ↦ ‖F s‖) volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hT]
    exact hFc.norm
  have hnormt : IntervalIntegrable (fun s ↦ ‖F s‖) volume 0 t := by
    refine hnorm.mono_set ?_
    rw [uIcc_of_le ht.1, uIcc_of_le hT]
    exact Icc_subset_Icc_right ht.2
  have hFi : IntervalIntegrable
      (fun s ↦ C.analytic.linearEvolution (Real.toNNReal (t - s)) (F s)) volume 0 t :=
    torus_forceIntegrable C F hFc ht
  have h1 : ‖∫ s in (0 : ℝ)..t,
      C.analytic.linearEvolution (Real.toNNReal (t - s)) (F s)‖ ≤
      ∫ s in (0 : ℝ)..t, ‖C.analytic.linearEvolution (Real.toNNReal (t - s)) (F s)‖ :=
    intervalIntegral.norm_integral_le_integral_norm ht.1
  have h2 : ∫ s in (0 : ℝ)..t,
      ‖C.analytic.linearEvolution (Real.toNNReal (t - s)) (F s)‖ ≤
      ∫ s in (0 : ℝ)..t, ‖F s‖ := by
    refine intervalIntegral.integral_mono_on ht.1 hFi.norm hnormt ?_
    intro s _
    exact torus_linearEvolution_norm_le hν C _ _
  have h3 : ∫ s in (0 : ℝ)..t, ‖F s‖ ≤ ∫ s in (0 : ℝ)..T, ‖F s‖ :=
    intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (Filter.Eventually.of_forall (fun _ ↦ norm_nonneg _)) hnorm
  exact (norm_add_le _ _).trans
    (add_le_add (torus_linearEvolution_norm_le hν C _ _)
      (h1.trans (h2.trans (h3.trans hB))))

/-! ## 3. The explicit uniform horizon -/

/-- The canonical two-space contract of lane 317 at viscosity `ν`.  Its only
argument is `ν`, so every constant derived from it — in particular the bilinear
norm entering the Picard threshold — depends on `ν` alone. -/
def torusContractOf (ν : ℝ) (hν : 0 < ν) : TorusTwoSpaceContract ν :=
  (torusTwoSpaceContract_nonempty' ν hν).some

/-- Positivity of the Picard kernel threshold at nonnegative data. -/
theorem torusPicardThreshold_pos {q b : ℝ} (hq : 0 ≤ q) (hb : 0 ≤ b) :
    0 < torusPicardThreshold q b := by
  unfold torusPicardThreshold
  have h1 : 0 < q * (b + 1) ^ 2 + 1 := by
    have := mul_nonneg hq (sq_nonneg (b + 1))
    linarith
  have h2 : 0 < 2 * (q * (2 * (b + 1)) + 1) := by
    have := mul_nonneg hq (by linarith : (0 : ℝ) ≤ 2 * (b + 1))
    linarith
  exact lt_min (div_pos one_pos h1) (div_pos one_pos h2)

/-- **The uniform Picard horizon.**  It depends only on the viscosity `ν`, the
datum-norm bound `K` and the force bounds `M` (through `M 3` alone); it does not
see the datum `a` or the force `g`. -/
def picardHorizon (ν : ℝ) (K : ℝ≥0∞) (M : ℕ → ℝ≥0∞) : ℝ := by
  classical
  exact if hν : 0 < ν then
      torusKernelTime ν (torusPicardThreshold
        ‖(torusContractOf ν hν).analytic.bilinear‖ (K.toReal + (M 3).toReal))
    else 1

/-- The value of the horizon at an admissible viscosity. -/
theorem picardHorizon_eq {ν : ℝ} (hν : 0 < ν) (K : ℝ≥0∞) (M : ℕ → ℝ≥0∞) :
    picardHorizon ν K M =
      torusKernelTime ν (torusPicardThreshold
        ‖(torusContractOf ν hν).analytic.bilinear‖ (K.toReal + (M 3).toReal)) := by
  classical
  unfold picardHorizon
  split
  · rfl
  · rename_i h
    exact False.elim (h hν)

theorem picardHorizon_pos (ν : ℝ) (K : ℝ≥0∞) (M : ℕ → ℝ≥0∞) :
    0 < picardHorizon ν K M := by
  classical
  unfold picardHorizon
  split
  · exact torusKernelTime_pos (torusPicardThreshold_pos (norm_nonneg _)
      (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg))
  · exact one_pos

theorem picardHorizon_le_one (ν : ℝ) (K : ℝ≥0∞) (M : ℕ → ℝ≥0∞) :
    picardHorizon ν K M ≤ 1 := by
  classical
  unfold picardHorizon
  split
  · exact torusKernelTime_le_one _ _
  · exact le_rfl

/-! ## 4. U9e — the `H³`-ball input, proved -/

/-- **The `H³`-ball quantitative local-existence input, proved outright.**

No named input, no placeholder.  Route: the canonical contract `C = torusContractOf
ν hν` (317); the order-three datum `A` of `a` with `‖A‖ ≤ K.toReal` from
`periodicSobolevENorm 3 a ≤ K` (`periodicSobolevENorm_eq_datum`, 309); the
smooth order-three force datum path `F₃` of `g` (334) and its Leray projection
`P = torusLerayCLM 3 ∘ F₃` (330), whose interval integral is bounded by
`(M 3).toReal` through `intervalIntegral_norm_le_of_forceENorm`; the horizon
`picardHorizon ν K M`, at which `torusPicardConstants_explicit` (313) supplies a
self-map/contraction certificate for the radius `K.toReal + (M 3).toReal + 1`;
the fixed point `u` from `torusForcedPicard_exists` (313), whose affine bound is
`torus_forcedLinear_bound_L1`; and finally `mild_to_classical` (334). -/
theorem exists_classical_on_picardHorizon (ν : ℝ) (hν : 0 < ν) (K : ℝ≥0∞) (hK : K ≠ ⊤)
    (M : ℕ → ℝ≥0∞) (hM : ∀ m, M m ≠ ⊤) :
    ∀ a : SpatialField, a ∈ initialClassT → periodicSobolevENorm 3 a ≤ K →
      ∀ g : SpaceTimeField, ContDiff ℝ ∞ g → IsPeriodicOn univ g →
        (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ M m) →
          ∃ w : ClassicalSolutionT ν a g (picardHorizon ν K M),
            PeriodicLocalRegularity ν a g (picardHorizon ν K M) w := by
  intro a ha hKa g hg hgp hMg
  set C : TorusTwoSpaceContract ν := torusContractOf ν hν with hC
  set T : ℝ := picardHorizon ν K M with hTdef
  have hTpos : 0 < T := picardHorizon_pos ν K M
  have hT1 : T ≤ 1 := picardHorizon_le_one ν K M
  -- the datum, with its norm inside the `H³` ball
  obtain ⟨A, hA⟩ := exists_periodicDatum_smooth (3 : ℝ) ha.1 ha.2.1
  have hAK : ‖A‖ ≤ K.toReal := by
    have hnorm : (‖A‖ₑ : ℝ≥0∞) ≤ K := by
      rw [← periodicSobolevENorm_eq_datum hA]
      exact hKa
    have hmono := ENNReal.toReal_mono hK hnorm
    rwa [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)] at hmono
  -- the smooth order-three force datum path and its Leray projection
  obtain ⟨F3, hF3smooth, hF3⟩ := exists_smooth_forceDatumPath hg hgp 3
  have hFpath : IsPeriodicSobolevPath 3 g F3 := by
    intro t _
    refine ⟨(hF3 t).1, (hF3 t).2.1, fun i k ↦ ?_⟩
    simpa using (hF3 t).2.2 i k
  set P : ℝ → PeriodicSobolev 3 := fun t ↦ torusLerayCLM (3 : ℝ) (F3 t) with hPdef
  have hPL : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F3 t) (P t) :=
    fun t _ i k ↦ torusLerayCLM_coeff (3 : ℝ) (F3 t) i k
  have hPcont : Continuous P :=
    (torusLerayCLM (3 : ℝ)).continuous.comp hF3smooth.continuous
  -- the single force order that is consumed: `M 3`
  have hF3L1 : ∫ t in (0 : ℝ)..1, ‖F3 t‖ ≤ (M 3).toReal :=
    intervalIntegral_norm_le_of_forceENorm ((3 : ℕ) : ℝ) (fun t _ ↦ hF3 t)
      hF3smooth.continuous (hM 3) (hMg 3)
  have hPL1 : ∫ t in (0 : ℝ)..T, ‖P t‖ ≤ (M 3).toReal := by
    have hstep : ∫ t in (0 : ℝ)..1, ‖P t‖ ≤ ∫ t in (0 : ℝ)..1, ‖F3 t‖ := by
      refine intervalIntegral.integral_mono_on zero_le_one
        (hPcont.norm.intervalIntegrable 0 1) (hF3smooth.continuous.norm.intervalIntegrable 0 1) ?_
      intro s _
      exact torusLerayDatum_norm_le (3 : ℝ) (F3 s)
    refine le_trans ?_ (hstep.trans hF3L1)
    exact intervalIntegral.integral_mono_interval le_rfl hTpos.le hT1
      (Filter.Eventually.of_forall (fun _ ↦ norm_nonneg _))
      (hPcont.norm.intervalIntegrable 0 1)
  -- the Picard certificate at the ball radius, and the fixed point
  set b : ℝ := K.toReal + (M 3).toReal with hbdef
  have hb0 : 0 ≤ b := add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hTeq : T = torusKernelTime ν
      (torusPicardThreshold ‖C.analytic.bilinear‖ b) := by
    rw [hTdef, picardHorizon_eq hν K M]
  have hPC : TorusPicardConstants C T (b + 1) b := by
    rw [hTeq]
    exact torusPicardConstants_explicit hν C hb0
  have hl : ∀ t, ∀ ht : t ∈ Icc (0 : ℝ) T,
      ‖C.analytic.linearEvolution ⟨t, ht.1⟩ A +
        ∫ s in (0 : ℝ)..t,
          C.analytic.linearEvolution (Real.toNNReal (t - s)) (P s)‖ ≤ b := by
    intro t ht
    refine (torus_forcedLinear_bound_L1 hν.le C A P hTpos.le hPcont.continuousOn
      hPL1 t ht).trans ?_
    rw [hbdef]
    linarith
  obtain ⟨u, hu, -⟩ :=
    torusForcedPicard_exists C A P T (b + 1) b hPC hPcont.continuousOn hl
  obtain ⟨w, hreg, -⟩ :=
    mild_to_classical ν hν C a g T ha hg hgp hTpos A F3 P u hA hFpath hPL hu
  exact ⟨w, hreg⟩

/-- **U9e — the `H³`-ball quantitative local-existence input, proved.**  The
horizon supplied is literally `picardHorizon ν K M`, i.e. it depends only on
`ν`, on the datum-norm bound `K` and on the force bound `M 3`. -/
theorem periodicQuantitativeLocalInputH3 : PeriodicQuantitativeLocalInputH3 :=
  fun ν hν K hK M hM ↦
    ⟨picardHorizon ν K M, picardHorizon_pos ν K M,
      exists_classical_on_picardHorizon ν hν K hK M hM⟩

/-! ## 5. Re-instantiation of lanes 321/332/337/323 at the `H³` ball -/

/-- **Lane 321's `restart` at the `H³` ball, unconditional.**  Identical to
`Section3/T11/Restart.lean:restart` except that the uniform ball is
`periodicSobolevENorm 3 a' ≤ K`; the proof is the same (positive time shifts
only shrink the half-line force integral), with the named input replaced by
`periodicQuantitativeLocalInputH3`. -/
theorem restartH3 :
    ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 ≤ S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t₀ ∈ Icc (0 : ℝ) S,
            ∀ (a' : SpatialField), a' ∈ initialClassT →
              periodicSobolevENorm 3 a' ≤ K →
                ∃ w : ClassicalSolutionT ν a' (timeShiftT t₀ f) δ,
                  PeriodicLocalRegularity ν a' (timeShiftT t₀ f) δ w := by
  intro ν hν f hf S _hS K hK
  let M : ℕ → ℝ≥0∞ := fun m ↦ forceSobolevENormT 1 (m : ℝ) f
  have hM : ∀ m, M m ≠ ⊤ := fun m ↦ forceSobolevENormT_ne_top hf m 1
  obtain ⟨δ, hδ, hlocal⟩ := periodicQuantitativeLocalInputH3 ν hν K hK M hM
  refine ⟨δ, hδ, ?_⟩
  intro t₀ ht₀ a' ha' hKa'
  apply hlocal a' ha' hKa' (timeShiftT t₀ f)
  · exact timeShiftT_contDiff hf.1 t₀
  · exact timeShiftT_periodic hf.2.1 t₀
  · intro m
    exact forceSobolevENormT_timeShift_le (m : ℝ) f t₀ ht₀.1

/-- A positive-horizon classical solution for every admissible datum and force,
with no hypothesis.  This is `exists_periodicLocalSolution_of_input` with the
name discharged; it is also `exists_classical_of_picard` of lane 334, restated
in the shape lane 323 consumes. -/
theorem exists_periodicLocalSolution_unconditional :
    ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∃ δ : ℝ, 0 < δ ∧ ∃ w : ClassicalSolutionT ν a f δ,
          PeriodicLocalRegularity ν a f δ w := by
  intro ν hν a ha f hf
  exact exists_classical_of_picard ν hν a ha f hf.1 hf.2.1

/-- Lane 323's residual input `PeriodicMaximalExistenceInput`, discharged. -/
theorem periodicMaximalExistenceInput_unconditional : PeriodicMaximalExistenceInput := by
  intro ν hν a ha f hf
  obtain ⟨δ, hδ, w, -⟩ := exists_periodicLocalSolution_unconditional ν hν a ha f hf
  exact ⟨δ, hδ, ⟨w⟩⟩

/-- **The `PeriodicLocalTheoryAPI.exists_maximal` field, verbatim and
unconditional.** -/
theorem exists_maximal_unconditional :
    ∀ (ν : ℝ), 0 < ν →
      ∀ (a : SpatialField), a ∈ initialClassT →
        ∀ (f : SpaceTimeField), f ∈ forceClassT →
          ∃ (u : SpaceTimeField) (p : SpaceTimeScalar),
            IsMaximalPeriodicSolution ν a f u p :=
  exists_maximal periodicMaximalExistenceInput_unconditional

/-- **Lane 332's `restartBeyond` at the `H³` ball, unconditional.**  Identical to
`Section3/T11/RestartBeyond.lean:restartBeyond` except that the trajectory
hypothesis is `periodicSobolevENorm 3 (u (t, ·)) ≤ K`; the proof is the same
(the horizon `δ` is chosen by `restartH3` before the datum, so it is uniform
over the ball). -/
theorem restartBeyondH3 :
    ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 < S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ (a : SpatialField), a ∈ initialClassT →
            ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
              SolvesBelowT ν a f S u p →
                (∀ t ∈ Ico (0 : ℝ) S,
                  periodicSobolevENorm 3 (fun x ↦ u (t, x)) ≤ K) →
                    ∃ v : ClassicalSolutionT ν a f (S + δ),
                      (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
                        v.velocity (t, x) = u (t, x)) ∧
                      (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
                        v.pressure (t, x) = p (t, x)) := by
  intro ν hν f hf S hS K hK
  obtain ⟨d, hd, hloc⟩ := restartH3 ν hν f hf S hS.le K hK
  obtain ⟨t₀, ht₀0, ht₀S, ht₀d⟩ : ∃ t₀ : ℝ, 0 ≤ t₀ ∧ t₀ < S ∧ S < t₀ + d :=
    ⟨max 0 (S - d / 2), le_max_left _ _, max_lt hS (by linarith),
      by have := le_max_right 0 (S - d / 2); linarith⟩
  refine ⟨t₀ + d - S, by linarith, ?_⟩
  intro a ha u p hsolve hbound
  obtain ⟨w, hwv, hwp⟩ := hsolve ((t₀ + S) / 2) (by linarith) (by linarith)
  have hbmem : t₀ ∈ Ico (0 : ℝ) ((t₀ + S) / 2) := ⟨ht₀0, by linarith⟩
  have hKa : periodicSobolevENorm 3 (fun x => w.velocity (t₀, x)) ≤ K := by
    rw [hwv]
    exact hbound t₀ ⟨ht₀0, ht₀S⟩
  obtain ⟨w₂, -⟩ := hloc t₀ ⟨ht₀0, ht₀S.le⟩ (fun x => w.velocity (t₀, x))
    (velocitySlice_mem_initialClassT w hbmem) hKa
  obtain ⟨v, -, -⟩ := glueClassicalSolutionT hν w hbmem w₂ (by linarith : (t₀ + S) / 2 < t₀ + d)
  have hrew : S + (t₀ + d - S) = t₀ + d := by ring
  rw [hrew]
  refine ⟨v, ?_, ?_⟩
  · intro t ht x
    obtain ⟨wc, hwcv, -⟩ := hsolve ((t + S) / 2) (by linarith [ht.1]) (by linarith [ht.2])
    have hag := velocity_unique ν hν a ha f hf (t₀ + d) ((t + S) / 2) v wc t
      ⟨ht.1, lt_min (by linarith [ht.2]) (by linarith [ht.2])⟩ x
    rw [hag, hwcv]
  · intro t ht x
    obtain ⟨wc, -, hwcp⟩ := hsolve ((t + S) / 2) (by linarith [ht.1]) (by linarith [ht.2])
    have hag := pressure_unique ν hν a ha f hf (t₀ + d) ((t + S) / 2) v wc t
      ⟨ht.1, lt_min (by linarith [ht.2]) (by linarith [ht.2])⟩ x
    rw [hag, hwcp]

/-- **Lane 337's `extendsBeyond` at the `H³` ball.**  The only remaining binder
is `hHigh`, the `higherOrderBound` field of `PeriodicContinuationAPI` (U12,
lanes 335/336), copied token for token from
`research/T11/probes/api_on_canonical.lean`; the `PeriodicQuantitativeLocalInput'`
hypothesis of `extendsBeyond_of_input` is gone.  Where lane 337 used `hHigh` at
`m = 1` to feed the `H¹` ball, this uses it at `m = 3`. -/
theorem extendsBeyondH3
    (hHigh : ∀ (ν : ℝ), 0 < ν →
      ∀ (a : SpatialField), a ∈ initialClassT →
        ∀ (f : SpaceTimeField), f ∈ forceClassT →
          ∀ (S : ℝ), 0 < S →
            ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
              SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
                ∀ m : ℕ, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
                  ∀ t ∈ Ico (0 : ℝ) S,
                    periodicSobolevENorm (m : ℝ) (fun x ↦ u (t, x)) ≤ M) :
    ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (S : ℝ), 0 < S →
          ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
            SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
              ExtendsBeyondT ν a f S u p := by
  intro ν hν a ha f hf S hS u p hsolve hfin
  obtain ⟨K, hK, hKbound⟩ := hHigh ν hν a ha f hf S hS u p hsolve hfin 3
  obtain ⟨δ, hδ, hrb⟩ := restartBeyondH3 ν hν f hf S hS K hK
  obtain ⟨v, hvu, hvp⟩ := hrb a ha u p hsolve (by
    intro t ht
    simpa only [Nat.cast_ofNat] using hKbound t ht)
  exact ⟨δ, hδ, v, hvu, hvp⟩

/-- **Lane 337's `lifespanInfiniteOfLocallyFinite` at the `H³` ball.**  Same
contraposition, same single use of the criterion at
`S = (maximalLifespanT ν a f).toReal`; the only binder left is `hHigh`. -/
theorem lifespanInfiniteOfLocallyFiniteH3
    (hHigh : ∀ (ν : ℝ), 0 < ν →
      ∀ (a : SpatialField), a ∈ initialClassT →
        ∀ (f : SpaceTimeField), f ∈ forceClassT →
          ∀ (S : ℝ), 0 < S →
            ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
              SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
                ∀ m : ℕ, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
                  ∀ t ∈ Ico (0 : ℝ) S,
                    periodicSobolevENorm (m : ℝ) (fun x ↦ u (t, x)) ≤ M) :
    ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
          IsMaximalPeriodicSolution ν a f u p →
            (∀ S : ℝ, 0 < S →
              ENNReal.ofReal S ≤ maximalLifespanT ν a f →
                squaredHTwoIntegralT S u ≠ ⊤) →
              maximalLifespanT ν a f = ⊤ := by
  intro ν hν a ha f hf u p hmax hcrit
  by_contra hL
  set S : ℝ := (maximalLifespanT ν a f).toReal with hSdef
  have hpos : 0 < maximalLifespanT ν a f := hmax.1
  have hS : 0 < S := ENNReal.toReal_pos hpos.ne' hL
  have hofS : ENNReal.ofReal S = maximalLifespanT ν a f := ENNReal.ofReal_toReal hL
  have hfin : squaredHTwoIntegralT S u ≠ ⊤ := hcrit S hS hofS.le
  have hsolve : SolvesBelowT ν a f S u p := by
    intro b hb0 hbS
    refine hmax.2 b hb0 ?_
    rw [← hofS]
    exact (ENNReal.ofReal_lt_ofReal_iff hS).mpr hbS
  obtain ⟨δ, hδ, hle⟩ := lifespan_ge_of_extends
    (extendsBeyondH3 hHigh ν hν a ha f hf S hS u p hsolve hfin)
  have hle' : ENNReal.ofReal (S + δ) ≤ ENNReal.ofReal S := by
    rw [hofS]; exact hle
  have hcontra : S + δ ≤ S := (ENNReal.ofReal_le_ofReal_iff hS.le).mp hle'
  linarith

/-! ## 6. Non-vacuity -/

/-- The proved input is not vacuous: a nonzero datum, a nonzero smooth periodic
force and a nonzero classical solution inhabit all of its hypotheses at once,
with the `H³` ball. -/
theorem nonzero_forced_witness_H3 :
    ∃ (K : ℝ≥0∞) (M : ℕ → ℝ≥0∞) (a : SpatialField) (g : SpaceTimeField),
      K ≠ ⊤ ∧ (∀ m, M m ≠ ⊤) ∧ a ∈ initialClassT ∧
      periodicSobolevENorm 3 a ≤ K ∧ ContDiff ℝ ∞ g ∧ IsPeriodicOn univ g ∧
      (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ M m) ∧
      ∃ w : ClassicalSolutionT 1 a g 1,
        PeriodicLocalRegularity 1 a g 1 w ∧
        w.velocity (0, 0) ≠ 0 ∧ g (0, 0) ≠ 0 := by
  obtain ⟨-, M, a, g, -, hM, ha, -, hg, hgp, hMg, hw⟩ := nonzero_forced_witness'
  exact ⟨periodicSobolevENorm 3 a, M, a, g,
    periodicSobolevENorm_ne_top_smooth 3 ha.1 ha.2.1, hM, ha, le_rfl, hg, hgp, hMg, hw⟩

/-- The horizon really is chosen before the datum: one `δ` serves every datum in
the `H³` ball and every force obeying the bounds. -/
example (ν : ℝ) (hν : 0 < ν) (K : ℝ≥0∞) (hK : K ≠ ⊤) (M : ℕ → ℝ≥0∞)
    (hM : ∀ m, M m ≠ ⊤) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ a : SpatialField, a ∈ initialClassT → periodicSobolevENorm 3 a ≤ K →
        ∀ g : SpaceTimeField, ContDiff ℝ ∞ g → IsPeriodicOn univ g →
          (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ M m) →
            ∃ w : ClassicalSolutionT ν a g δ, PeriodicLocalRegularity ν a g δ w :=
  periodicQuantitativeLocalInputH3 ν hν K hK M hM

end NSFormalization.Section3.T11
