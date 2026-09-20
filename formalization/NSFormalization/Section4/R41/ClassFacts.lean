import NSFormalization.Section4.R41.NonDensityL1
import NSFormalization.Section4.B01.Spatial
import NSFormalization.Section4.D01.FiniteOrderNorm
import NSFormalization.Section4.C01.PressureJetPath
import NSFormalization.Section4.A01.DatumPathDeriv
import NavierStokes.CompactSpatialForceDecay
import NavierStokes.SpacetimeGluing
import Euler.LpDominatedConvergence
import Euler.InjectivePathDerivativeWithin
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# The small class and norm facts used by the R41 density branch

This module supplies the four elementary interfaces isolated as gaps G2--G5 in
`research/R41D/COMPARISON.md`: rapid forces belong to the ambient force class,
rapid decay is stable under compactly supported corrections, Schwartz initial
data belong to `X_R`, and the force Sobolev enorm of zero vanishes.

The local definitions of `MemForceRapid`, `forceClassRapid`, and
`initialClassSchwartz` below are verbatim restatements of
`Contracts/V1/Data.lean:513,572,578`.  The ambient predicates and norm reuse the
existing definitionally-equal D01/A02 restatements.  Contract-level `rfl`
bridges are audited in `research/R41D/axioms_class_facts.lean`.
-/

noncomputable section

namespace NSFormalization.Section4.R41

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3 NSFormalization.Source.RealSobolev
open EulerLpTranslation
open scoped ContDiff ENNReal SchwartzMap

/-! ## 1. Local restatements -/

/-- `Contracts.V1.Data.MemForceRapid` (`Data.lean:572`), verbatim. -/
def MemForceRapid (f : A02.SpaceTimeField) : Prop :=
  ContDiffOn ℝ ∞ f futureDomain ∧
    ∀ N k : ℕ, ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
      (1 + ‖x‖ + t) ^ N * ‖iteratedFDerivWithin ℝ k f futureDomain (t, x)‖ ≤ C

/-- `Contracts.V1.Data.forceClassRapid` (`Data.lean:578`), verbatim. -/
def forceClassRapid : Set A02.SpaceTimeField := {f | MemForceRapid f}

/-- `Contracts.V1.Data.initialClassSchwartz` (`Data.lean:513`), verbatim. -/
def initialClassSchwartz : Set A02.SpatialField :=
  {a | (∃ φ : SchwartzMap Space Space, ⇑φ = a) ∧ A02.IsSolenoidal a}

/-! ## 2. Rapid normal jets and spatial slices -/

/-- Taking any number of future-time normal derivatives does not enlarge the norm beyond
the corresponding higher joint derivative. -/
theorem norm_iteratedFDerivWithin_normalIter_le {f : A02.SpaceTimeField}
    (hf : ContDiffOn ℝ ∞ f futureDomain) (j k : ℕ) {z : SpaceTime} (hz : z ∈ futureDomain) :
    ‖iteratedFDerivWithin ℝ k (NavierStokes.SpacetimeGluing.normalIter futureDomain f j)
        futureDomain z‖ ≤
      ‖iteratedFDerivWithin ℝ (k + j) f futureDomain z‖ := by
  induction j generalizing k with
  | zero => simp [NavierStokes.SpacetimeGluing.normalIter]
  | succ j ih =>
      have hs := NavierStokes.SpacetimeGluing.normalIter_contDiffOn hf
        ((uniqueDiffOn_Ici (0 : ℝ)).prod uniqueDiffOn_univ) j
      have hD := hs.fderivWithin
        (m := ((⊤ : ℕ∞) : WithTop ℕ∞))
        ((uniqueDiffOn_Ici (0 : ℝ)).prod uniqueDiffOn_univ) (by
          simp only [ENat.coe_top_add_one, le_refl])
      change ‖iteratedFDerivWithin ℝ k
        (fun y => (fderivWithin ℝ
          (NavierStokes.SpacetimeGluing.normalIter futureDomain f j) futureDomain y)
            NavierStokes.SpacetimeGluing.timeVector)
          futureDomain z‖ ≤ _
      calc
        _ ≤ ‖NavierStokes.SpacetimeGluing.timeVector‖ *
            ‖iteratedFDerivWithin ℝ k
              (fderivWithin ℝ
                (NavierStokes.SpacetimeGluing.normalIter futureDomain f j) futureDomain)
              futureDomain z‖ :=
          norm_iteratedFDerivWithin_clm_apply_const (hD z hz)
            ((uniqueDiffOn_Ici (0 : ℝ)).prod uniqueDiffOn_univ) hz (by simp)
        _ = ‖iteratedFDerivWithin ℝ (k + 1)
              (NavierStokes.SpacetimeGluing.normalIter futureDomain f j) futureDomain z‖ := by
          rw [norm_iteratedFDerivWithin_fderivWithin
            ((uniqueDiffOn_Ici (0 : ℝ)).prod uniqueDiffOn_univ) hz]
          simp [NavierStokes.SpacetimeGluing.timeVector]
        _ ≤ ‖iteratedFDerivWithin ℝ (k + 1 + j) f futureDomain z‖ := ih (k + 1)
        _ = ‖iteratedFDerivWithin ℝ (k + (j + 1)) f futureDomain z‖ := by
          rw [Nat.add_assoc k 1 j, Nat.add_comm 1 j]

/-- Every normal time jet of a rapid force satisfies the same family of rapid estimates,
with only the derivative index shifted. -/
theorem normalIter_rapid_bound {f : A02.SpaceTimeField} (hf : MemForceRapid f)
    (j N k : ℕ) : ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
      (1 + ‖x‖ + t) ^ N *
        ‖iteratedFDerivWithin ℝ k
          (NavierStokes.SpacetimeGluing.normalIter futureDomain f j)
          futureDomain (t, x)‖ ≤ C := by
  obtain ⟨C, hC⟩ := hf.2 N (k + j)
  refine ⟨C, fun t ht x => ?_⟩
  have htx : (t, x) ∈ futureDomain :=
    ⟨(show t ∈ Ici (0 : ℝ) from ht), mem_univ x⟩
  exact (mul_le_mul_of_nonneg_left
    (norm_iteratedFDerivWithin_normalIter_le hf.1 j k htx)
    (pow_nonneg (by positivity) N)).trans (hC t ht x)

/-- The affine inclusion of one spatial slice has all positive-order derivative norms at most one. -/
theorem norm_iteratedFDeriv_spatialInclusion_le (t : ℝ) (n : ℕ) (hn : 1 ≤ n) (x : Space) :
    ‖iteratedFDeriv ℝ n (fun y : Space => (t, y)) x‖ ≤ 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 1 + k = k + 1 by omega, ← norm_iteratedFDeriv_fderiv]
  have hd : fderiv ℝ (fun y : Space => (t, y)) =
      fun _ => ContinuousLinearMap.inr ℝ ℝ Space := by
    funext y
    exact (hasFDerivAt_const (x := y) (c := t)).prodMk
      (hasFDerivAt_id (x := y)) |>.fderiv
  rw [hd]
  by_cases hk : k = 0
  · subst k
    simp only [norm_iteratedFDeriv_zero, ContinuousLinearMap.norm_inr, le_refl]
  · rw [iteratedFDeriv_const_of_ne hk]
    simp

/-- A future spatial slice of every normal time jet is a Schwartz map. -/
def rapidNormalSlice {f : A02.SpaceTimeField} (hf : MemForceRapid f)
    (j : ℕ) (t : ℝ) (ht : 0 ≤ t) : SchwartzMap Space Space where
  toFun x := NavierStokes.SpacetimeGluing.normalIter futureDomain f j (t, x)
  smooth' :=
    (NavierStokes.SpacetimeGluing.normalIter_contDiffOn hf.1
      ((uniqueDiffOn_Ici (0 : ℝ)).prod uniqueDiffOn_univ) j).comp_contDiff
        (contDiff_const.prodMk contDiff_id) (fun x => ⟨ht, mem_univ x⟩)
  decay' N k := by
    choose C hC using fun i : ℕ => normalIter_rapid_bound hf j N i
    refine ⟨(k.factorial : ℝ) * ∑ i ∈ Finset.range (k + 1), C i, fun x => ?_⟩
    have hcomp :
        ‖iteratedFDeriv ℝ k
          (fun y : Space =>
            NavierStokes.SpacetimeGluing.normalIter futureDomain f j (t, y)) x‖ ≤
          (k.factorial : ℝ) * ∑ i ∈ Finset.range (k + 1),
            ‖iteratedFDerivWithin ℝ i
              (NavierStokes.SpacetimeGluing.normalIter futureDomain f j)
              futureDomain (t, x)‖ := by
      have hb := norm_iteratedFDeriv_comp_le'
        (g := NavierStokes.SpacetimeGluing.normalIter futureDomain f j)
        (f := fun y : Space => (t, y))
        (n := k) (N := (∞ : WithTop ℕ∞))
        (by rintro z ⟨y, rfl⟩; exact ⟨ht, mem_univ y⟩)
        ((uniqueDiffOn_Ici (0 : ℝ)).prod uniqueDiffOn_univ)
        (NavierStokes.SpacetimeGluing.normalIter_contDiffOn hf.1
          ((uniqueDiffOn_Ici (0 : ℝ)).prod uniqueDiffOn_univ) j)
        (contDiff_const.prodMk contDiff_id) (by simp) x
        (C := ∑ i ∈ Finset.range (k + 1),
          ‖iteratedFDerivWithin ℝ i
            (NavierStokes.SpacetimeGluing.normalIter futureDomain f j)
            futureDomain (t, x)‖)
        (D := 1) (fun i hi => by
          exact Finset.single_le_sum
            (fun n _ => norm_nonneg
              (iteratedFDerivWithin ℝ n
                (NavierStokes.SpacetimeGluing.normalIter futureDomain f j)
                futureDomain (t, x)))
            (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))
        (fun i hi _ => by
          simpa only [one_pow] using norm_iteratedFDeriv_spatialInclusion_le t i hi x)
      change ‖iteratedFDeriv ℝ k
        (fun y : Space =>
          NavierStokes.SpacetimeGluing.normalIter futureDomain f j (t, y)) x‖ ≤ _ at hb
      simpa only [one_pow, mul_one] using hb
    have hxbase : ‖x‖ ^ N ≤ (1 + ‖x‖ + t) ^ N := by
      exact pow_le_pow_left₀ (norm_nonneg x) (by linarith [norm_nonneg x]) N
    calc
      ‖x‖ ^ N *
          ‖iteratedFDeriv ℝ k
            (fun y : Space =>
              NavierStokes.SpacetimeGluing.normalIter futureDomain f j (t, y)) x‖
          ≤ ‖x‖ ^ N * ((k.factorial : ℝ) * ∑ i ∈ Finset.range (k + 1),
              ‖iteratedFDerivWithin ℝ i
                (NavierStokes.SpacetimeGluing.normalIter futureDomain f j)
                futureDomain (t, x)‖) :=
        mul_le_mul_of_nonneg_left hcomp (pow_nonneg (norm_nonneg x) N)
      _ = (k.factorial : ℝ) * (‖x‖ ^ N * ∑ i ∈ Finset.range (k + 1),
            ‖iteratedFDerivWithin ℝ i
              (NavierStokes.SpacetimeGluing.normalIter futureDomain f j)
              futureDomain (t, x)‖) := by ring
      _ = (k.factorial : ℝ) * ∑ i ∈ Finset.range (k + 1),
            (‖x‖ ^ N * ‖iteratedFDerivWithin ℝ i
              (NavierStokes.SpacetimeGluing.normalIter futureDomain f j)
              futureDomain (t, x)‖) := by
        rw [Finset.mul_sum]
      _ ≤ (k.factorial : ℝ) * ∑ i ∈ Finset.range (k + 1), C i := by
        gcongr with i hi
        exact (mul_le_mul_of_nonneg_right hxbase (norm_nonneg _)).trans (hC i t ht x)

/-- Iterated derivatives of a Schwartz map, retained as a Schwartz map. -/
private def schwartzJetAux (n : ℕ) :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V],
      SchwartzMap Space V → SchwartzMap Space (Space [×n]→L[ℝ] V) :=
  Nat.rec (motive := fun n =>
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V],
        SchwartzMap Space V → SchwartzMap Space (Space [×n]→L[ℝ] V))
    (fun V _ _ φ => SchwartzMap.postcompCLM
      (continuousMultilinearCurryFin0 ℝ Space V).symm.toContinuousLinearEquiv.toContinuousLinearMap φ)
    (fun n ih V _ _ φ => SchwartzMap.postcompCLM
      (continuousMultilinearCurryRightEquiv' ℝ n Space V).symm.toContinuousLinearEquiv.toContinuousLinearMap
      (ih (Space →L[ℝ] V) (SchwartzMap.fderivCLM ℝ Space V φ))) n

/-- The Schwartz map whose value is the `n`-th Fréchet derivative. -/
def schwartzJet (n : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (φ : SchwartzMap Space V) : SchwartzMap Space (Space [×n]→L[ℝ] V) :=
  schwartzJetAux n V φ

@[simp] theorem schwartzJet_apply (n : ℕ) {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (φ : SchwartzMap Space V) (x : Space) :
    schwartzJet n φ x = iteratedFDeriv ℝ n φ x := by
  induction n generalizing V with
  | zero =>
      change (continuousMultilinearCurryFin0 ℝ Space V).symm (φ x) = _
      rw [iteratedFDeriv_zero_eq_comp]
      rfl
  | succ n ih =>
      change (continuousMultilinearCurryRightEquiv' ℝ n Space V).symm
        (schwartzJet n (SchwartzMap.fderivCLM ℝ Space V φ) x) = _
      rw [ih, iteratedFDeriv_succ_eq_comp_right]
      rfl

/-- A rapid normal slice as the standard smooth all-jets `L²` carrier. -/
def rapidSmoothSlice {f : A02.SpaceTimeField} (hf : MemForceRapid f)
    (j : ℕ) (t : ℝ) (ht : 0 ≤ t) : SmoothL2Field Space where
  field := rapidNormalSlice hf j t ht
  smooth := (rapidNormalSlice hf j t ht).smooth (⊤ : ℕ∞)
  integrable n := by
    have h := (schwartzJet n (rapidNormalSlice hf j t ht)).memLp 2 volume
    exact h.congr_norm
      (((rapidNormalSlice hf j t ht).smooth (⊤ : ℕ∞)).continuous_iteratedFDeriv
        (by simp)).aestronglyMeasurable
      (ae_of_all volume fun x => congrArg norm (schwartzJet_apply n
        (rapidNormalSlice hf j t ht) x))

@[simp] theorem rapidSmoothSlice_field {f : A02.SpaceTimeField} (hf : MemForceRapid f)
    (j : ℕ) (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    (rapidSmoothSlice hf j t ht).field x =
      NavierStokes.SpacetimeGluing.normalIter futureDomain f j (t, x) := rfl

/-- Spatial derivatives of a future slice are the joint within derivatives with every
input restricted to the spatial summand. -/
theorem iteratedFDeriv_rapidNormalSlice {f : A02.SpaceTimeField} (hf : MemForceRapid f)
    (j k : ℕ) (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    iteratedFDeriv ℝ k (rapidNormalSlice hf j t ht) x =
      (iteratedFDerivWithin ℝ k
        (NavierStokes.SpacetimeGluing.normalIter futureDomain f j)
        futureDomain (t, x)).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.inr ℝ ℝ Space) := by
  let g : Space →ᴬ[ℝ] SpaceTime :=
    (ContinuousLinearMap.inr ℝ ℝ Space).toContinuousAffineMap +
      ContinuousAffineMap.const ℝ Space (t, 0)
  have hg : (⇑g) ⁻¹' futureDomain = (univ : Set Space) := by
    ext y
    simp [g, futureDomain, ht]
  have hs := NavierStokes.SpacetimeGluing.normalIter_contDiffOn hf.1
    ((uniqueDiffOn_Ici (0 : ℝ)).prod uniqueDiffOn_univ) j
  have hTaylor :=
    ((hs.of_le (by simp : (k : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))).ftaylorSeriesWithin
      ((uniqueDiffOn_Ici (0 : ℝ)).prod uniqueDiffOn_univ)).comp_continuousAffineMap g
  have he := hTaylor.eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl
    (by simpa only [hg] using (uniqueDiffOn_univ : UniqueDiffOn ℝ (univ : Set Space)))
    (show x ∈ ⇑g ⁻¹' futureDomain by rw [hg]; exact mem_univ x)
  rw [hg, iteratedFDerivWithin_univ] at he
  change (iteratedFDerivWithin ℝ k
      (NavierStokes.SpacetimeGluing.normalIter futureDomain f j) futureDomain (g x)
        ).compContinuousLinearMap (fun _ => g.contLinear) =
    iteratedFDeriv ℝ k
      (NavierStokes.SpacetimeGluing.normalIter futureDomain f j ∘ ⇑g) x at he
  have hfun :
      (NavierStokes.SpacetimeGluing.normalIter futureDomain f j ∘ ⇑g) =
        fun y : Space =>
          NavierStokes.SpacetimeGluing.normalIter futureDomain f j (t, y) := by
    funext y
    simp [g]
  rw [hfun] at he
  change iteratedFDeriv ℝ k
    (fun y : Space => NavierStokes.SpacetimeGluing.normalIter futureDomain f j (t, y)) x = _
  simpa only [g, ContinuousAffineMap.add_apply, ContinuousLinearMap.coe_toContinuousAffineMap,
    ContinuousAffineMap.coe_const, Pi.add_apply, Function.const_apply,
    ContinuousLinearMap.inr_apply, add_zero, zero_add, Function.comp_apply,
    ContinuousAffineMap.add_contLinear, ContinuousLinearMap.toContinuousAffineMap_contLinear,
    ContinuousAffineMap.const_contLinear, Prod.mk_add_mk] using he.symm

/-- The ordinary `L²` class of a rapid normal-jet slice, totalized by zero before time zero. -/
def rapidNormalLp {f : A02.SpaceTimeField} (hf : MemForceRapid f) (j : ℕ) :
    ℝ → Lp Space 2 (volume : Measure Space) := fun t =>
  if ht : 0 ≤ t then (rapidNormalSlice hf j t ht).toLp 2 volume else 0

/-- A literal representative of `rapidNormalLp`, likewise totalized before zero. -/
def rapidNormalField (f : A02.SpaceTimeField) (j : ℕ) (t : ℝ) (x : Space) : Space :=
  if 0 ≤ t then NavierStokes.SpacetimeGluing.normalIter futureDomain f j (t, x) else 0

/-- The actual spatial `k`-jet of a normal slice in `L²`, totalized before time zero. -/
def rapidJetLp {f : A02.SpaceTimeField} (hf : MemForceRapid f) (j k : ℕ) :
    ℝ → Lp (Space [×k]→L[ℝ] Space) 2 (volume : Measure Space) := fun t =>
  if ht : 0 ≤ t then (rapidSmoothSlice hf j t ht).jetLp k else 0

/-- A literal representative of `rapidJetLp`. -/
def rapidJetField (f : A02.SpaceTimeField) (j k : ℕ) (t : ℝ) (x : Space) :
    Space [×k]→L[ℝ] Space :=
  if _ht : 0 ≤ t then
    iteratedFDeriv ℝ k
      (fun y : Space => NavierStokes.SpacetimeGluing.normalIter futureDomain f j (t, y)) x
  else 0

theorem rapidJetLp_ae {f : A02.SpaceTimeField} (hf : MemForceRapid f) (j k : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    rapidJetLp hf j k t =ᵐ[volume]
      fun x => iteratedFDeriv ℝ k
        (fun y : Space => NavierStokes.SpacetimeGluing.normalIter futureDomain f j (t, y)) x := by
  rw [rapidJetLp, dite_eq_left ht]
  exact (rapidSmoothSlice hf j t ht).jetLp_ae k

theorem rapidJetLp_ae_total {f : A02.SpaceTimeField} (hf : MemForceRapid f)
    (j k : ℕ) (t : ℝ) : rapidJetLp hf j k t =ᵐ[volume] rapidJetField f j k t := by
  by_cases ht : 0 ≤ t
  · filter_upwards [rapidJetLp_ae hf j k ht] with x hx
    simpa only [rapidJetField, dite_eq_left ht] using hx
  · have hz : (0 : Lp (Space [×k]→L[ℝ] Space) 2 (volume : Measure Space)) =ᵐ[volume]
        fun _ : Space => (0 : Space [×k]→L[ℝ] Space) :=
      Lp.coeFn_zero (Space [×k]→L[ℝ] Space) 2 volume
    filter_upwards [hz] with x hx
    rw [rapidJetLp, dite_eq_right ht, hx]
    simp [rapidJetField, ht]

/-- Joint within derivative with every multilinear input restricted to the spatial summand. -/
def jointSpatialJet (f : A02.SpaceTimeField) (j k : ℕ) (t : ℝ) (x : Space) :
    Space [×k]→L[ℝ] Space :=
  (iteratedFDerivWithin ℝ k
    (NavierStokes.SpacetimeGluing.normalIter futureDomain f j)
    futureDomain (t, x)).compContinuousLinearMap
      (fun _ => ContinuousLinearMap.inr ℝ ℝ Space)

/-- At future times the totalized literal jet is the joint spatially restricted jet. -/
theorem rapidJetField_eq_jointSpatialJet {f : A02.SpaceTimeField} (hf : MemForceRapid f)
    (j k : ℕ) {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    rapidJetField f j k t x = jointSpatialJet f j k t x := by
  rw [rapidJetField, dite_eq_left ht, jointSpatialJet]
  exact iteratedFDeriv_rapidNormalSlice hf j k t ht x

/-- Every pointwise spatial jet varies continuously along future time. -/
theorem jointSpatialJet_continuousOn {f : A02.SpaceTimeField} (hf : MemForceRapid f)
    (j k : ℕ) (x : Space) : ContinuousOn (fun t => jointSpatialJet f j k t x) (Ici 0) := by
  have hUD : UniqueDiffOn ℝ futureDomain :=
    (uniqueDiffOn_Ici (0 : ℝ)).prod uniqueDiffOn_univ
  have hs := NavierStokes.SpacetimeGluing.normalIter_contDiffOn hf.1 hUD j
  have hjoint := hs.continuousOn_iteratedFDerivWithin
    (by simp : (k : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞)) hUD
  have hcurve : ContinuousOn (fun t : ℝ =>
      iteratedFDerivWithin ℝ k
        (NavierStokes.SpacetimeGluing.normalIter futureDomain f j)
        futureDomain (t, x)) (Ici 0) :=
    hjoint.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨ht, mem_univ x⟩)
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
    (F := Space) (fun _ : Fin k => ContinuousLinearMap.inr ℝ ℝ Space)).continuous.comp_continuousOn
      hcurve

/-- A single square-integrable spatial majorant controls a fixed spatial jet at every
future time. -/
theorem exists_rapidJet_memLp_majorant {f : A02.SpaceTimeField}
    (hf : MemForceRapid f) (j k : ℕ) :
    ∃ M : Space → ℝ, MemLp M 2 volume ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
      ‖iteratedFDeriv ℝ k
        (fun y : Space => NavierStokes.SpacetimeGluing.normalIter futureDomain f j (t, y)) x‖ ≤ M x := by
  obtain ⟨N, hN⟩ :=
    (inferInstance : (volume : Measure Space).HasTemperateGrowth).exists_eLpNorm_lt_top 2
  obtain ⟨C, hC⟩ := normalIter_rapid_bound hf j N k
  let D : ℝ := max C 0
  let M : Space → ℝ := fun x => D * (1 + ‖x‖) ^ (-(N : ℝ))
  have hbase_cont : Continuous (fun x : Space => (1 + ‖x‖) ^ (-(N : ℝ))) :=
    Continuous.rpow_const (by fun_prop)
      (fun x => Or.inl (show 1 + ‖x‖ ≠ 0 by positivity))
  have hbase_mem : MemLp (fun x : Space => (1 + ‖x‖) ^ (-(N : ℝ))) 2 volume :=
    ⟨hbase_cont.aestronglyMeasurable, hN⟩
  refine ⟨M, hbase_mem.const_mul D, fun t ht x => ?_⟩
  have hspatial :
      ‖iteratedFDeriv ℝ k
        (fun y : Space => NavierStokes.SpacetimeGluing.normalIter futureDomain f j (t, y)) x‖ ≤
      ‖iteratedFDerivWithin ℝ k
        (NavierStokes.SpacetimeGluing.normalIter futureDomain f j)
        futureDomain (t, x)‖ := by
    rw [show (fun y : Space =>
      NavierStokes.SpacetimeGluing.normalIter futureDomain f j (t, y)) =
        ⇑(rapidNormalSlice hf j t ht) by rfl,
      iteratedFDeriv_rapidNormalSlice hf j k t ht x]
    calc
      ‖(iteratedFDerivWithin ℝ k
          (NavierStokes.SpacetimeGluing.normalIter futureDomain f j)
          futureDomain (t, x)).compContinuousLinearMap
            (fun _ => ContinuousLinearMap.inr ℝ ℝ Space)‖
          ≤ ‖iteratedFDerivWithin ℝ k
              (NavierStokes.SpacetimeGluing.normalIter futureDomain f j)
              futureDomain (t, x)‖ *
            ∏ _i : Fin k, ‖ContinuousLinearMap.inr ℝ ℝ Space‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ = _ := by simp only [ContinuousLinearMap.norm_inr, Finset.prod_const_one, mul_one]
  have hxpow : (1 + ‖x‖) ^ N ≤ (1 + ‖x‖ + t) ^ N :=
    pow_le_pow_left₀ (by positivity) (by linarith) N
  have hweighted : (1 + ‖x‖) ^ N *
      ‖iteratedFDeriv ℝ k
        (fun y : Space => NavierStokes.SpacetimeGluing.normalIter futureDomain f j (t, y)) x‖ ≤ D :=
    calc
      _ ≤ (1 + ‖x‖) ^ N *
          ‖iteratedFDerivWithin ℝ k
            (NavierStokes.SpacetimeGluing.normalIter futureDomain f j)
            futureDomain (t, x)‖ :=
        mul_le_mul_of_nonneg_left hspatial (pow_nonneg (by positivity) N)
      _ ≤ (1 + ‖x‖ + t) ^ N *
          ‖iteratedFDerivWithin ℝ k
            (NavierStokes.SpacetimeGluing.normalIter futureDomain f j)
            futureDomain (t, x)‖ :=
        mul_le_mul_of_nonneg_right hxpow (norm_nonneg _)
      _ ≤ C := hC t ht x
      _ ≤ D := le_max_left C 0
  calc
    ‖iteratedFDeriv ℝ k
        (fun y : Space => NavierStokes.SpacetimeGluing.normalIter futureDomain f j (t, y)) x‖
        ≤ D / (1 + ‖x‖) ^ N := (le_div_iff₀' (by positivity)).2 hweighted
    _ = M x := by
      simp only [M]
      rw [div_eq_mul_inv, ← Real.rpow_natCast, Real.rpow_neg (by positivity)]

/-- Every spatial-jet `L²` path is continuous on future time. -/
theorem rapidJetLp_continuousOn {f : A02.SpaceTimeField} (hf : MemForceRapid f)
    (j k : ℕ) : ContinuousOn (rapidJetLp hf j k) (Ici 0) := by
  intro t ht
  obtain ⟨M, hMmem, hM⟩ := exists_rapidJet_memLp_majorant hf j k
  have hv : rapidJetLp hf j k t =ᵐ[volume] jointSpatialJet f j k t := by
    filter_upwards [rapidJetLp_ae hf j k ht] with x hx
    exact hx.trans (iteratedFDeriv_rapidNormalSlice hf j k t ht x)
  apply EulerLpConvergence.tendsto_of_dominated volume
    (rapidJetLp hf j k) (rapidJetLp hf j k t)
    (rapidJetField f j k) (jointSpatialJet f j k t)
    (rapidJetLp_ae_total hf j k) hv (fun x => 2 * M x) (hMmem.const_mul 2)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    filter_upwards [] with x
    rw [rapidJetField_eq_jointSpatialJet hf j k hs x]
    calc
      ‖jointSpatialJet f j k s x - jointSpatialJet f j k t x‖
          ≤ ‖jointSpatialJet f j k s x‖ + ‖jointSpatialJet f j k t x‖ := norm_sub_le _ _
      _ ≤ M x + M x := add_le_add
        (by rw [← rapidJetField_eq_jointSpatialJet hf j k hs x,
            rapidJetField, dite_eq_left (show 0 ≤ s from hs)]; exact hM s hs x)
        (by rw [← rapidJetField_eq_jointSpatialJet hf j k ht x,
            rapidJetField, dite_eq_left (show 0 ≤ t from ht)]; exact hM t ht x)
      _ = 2 * M x := by ring
  · filter_upwards [] with x
    apply (jointSpatialJet_continuousOn hf j k x t ht).congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (rapidJetField_eq_jointSpatialJet hf j k hs x).symm

theorem rapidNormalLp_ae {f : A02.SpaceTimeField} (hf : MemForceRapid f) (j : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    rapidNormalLp hf j t =ᵐ[volume]
      fun x => NavierStokes.SpacetimeGluing.normalIter futureDomain f j (t, x) := by
  rw [rapidNormalLp, dite_eq_left ht]
  exact (rapidNormalSlice hf j t ht).coeFn_toLp 2 volume

theorem rapidNormalLp_ae_total {f : A02.SpaceTimeField} (hf : MemForceRapid f)
    (j : ℕ) (t : ℝ) : rapidNormalLp hf j t =ᵐ[volume] rapidNormalField f j t := by
  by_cases ht : 0 ≤ t
  · filter_upwards [rapidNormalLp_ae hf j ht] with x hx
    simpa only [rapidNormalField, ite_eq_left ht] using hx
  · have hz : (0 : Lp Space 2 (volume : Measure Space)) =ᵐ[volume]
        fun _ : Space => (0 : Space) := Lp.coeFn_zero Space 2 volume
    filter_upwards [hz] with x hx
    rw [rapidNormalLp, dite_eq_right ht, hx]
    simp [rapidNormalField, ht]

theorem slope_rapidNormalLp_ae {f : A02.SpaceTimeField} (hf : MemForceRapid f)
    (j : ℕ) (t s : ℝ) :
    slope (rapidNormalLp hf j) t s =ᵐ[volume]
      fun x => slope (fun r => rapidNormalField f j r x) t s := by
  rw [slope_def_module]
  filter_upwards [Lp.coeFn_smul ((s - t)⁻¹) (rapidNormalLp hf j s - rapidNormalLp hf j t),
    Lp.coeFn_sub (rapidNormalLp hf j s) (rapidNormalLp hf j t),
    rapidNormalLp_ae_total hf j s, rapidNormalLp_ae_total hf j t]
    with x hsm hsub hs ht
  simp only [Pi.smul_apply, Pi.sub_apply] at hsm hsub
  rw [hsm, hsub, hs, ht]
  rfl

/-- Pointwise differentiation of a normal-jet slice, including the right derivative at zero. -/
theorem normalIter_time_hasDerivWithinAt {f : A02.SpaceTimeField}
    (hf : ContDiffOn ℝ ∞ f futureDomain) (j : ℕ) {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    HasDerivWithinAt
      (fun s => NavierStokes.SpacetimeGluing.normalIter futureDomain f j (s, x))
      (NavierStokes.SpacetimeGluing.normalIter futureDomain f (j + 1) (t, x))
      (Ici 0) t := by
  have hsmooth := NavierStokes.SpacetimeGluing.normalIter_contDiffOn hf
    ((uniqueDiffOn_Ici (0 : ℝ)).prod uniqueDiffOn_univ) j
  have hdiff := hsmooth.differentiableOn (by simp) (t, x) ⟨ht, mem_univ x⟩
  have hcurve := hdiff.hasFDerivWithinAt.comp t
    (hasFDerivAt_prodMk_left t x).hasFDerivWithinAt
    (fun y hy => show (y, x) ∈ futureDomain from ⟨hy, mem_univ x⟩)
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, NavierStokes.SpacetimeGluing.normalIter,
    NavierStokes.SpacetimeGluing.directional, NavierStokes.SpacetimeGluing.timeVector] using
    hcurve.hasDerivWithinAt

/-- Every fixed normal jet has a single square-integrable spatial majorant, uniform in
all future times. -/
theorem exists_rapidNormal_memLp_majorant {f : A02.SpaceTimeField}
    (hf : MemForceRapid f) (j : ℕ) :
    ∃ M : Space → ℝ, MemLp M 2 volume ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
      ‖NavierStokes.SpacetimeGluing.normalIter futureDomain f j (t, x)‖ ≤ M x := by
  obtain ⟨N, hN⟩ :=
    (inferInstance : (volume : Measure Space).HasTemperateGrowth).exists_eLpNorm_lt_top 2
  obtain ⟨C, hC⟩ := normalIter_rapid_bound hf j N 0
  let D : ℝ := max C 0
  let M : Space → ℝ := fun x => D * (1 + ‖x‖) ^ (-(N : ℝ))
  have hbase_cont : Continuous (fun x : Space => (1 + ‖x‖) ^ (-(N : ℝ))) :=
    Continuous.rpow_const (by fun_prop)
      (fun x => Or.inl (show 1 + ‖x‖ ≠ 0 by positivity))
  have hbase_mem : MemLp (fun x : Space => (1 + ‖x‖) ^ (-(N : ℝ))) 2 volume :=
    ⟨hbase_cont.aestronglyMeasurable, hN⟩
  refine ⟨M, hbase_mem.const_mul D, fun t ht x => ?_⟩
  have hxpow : (1 + ‖x‖) ^ N ≤ (1 + ‖x‖ + t) ^ N :=
    pow_le_pow_left₀ (by positivity) (by linarith) N
  have hweighted : (1 + ‖x‖) ^ N *
      ‖NavierStokes.SpacetimeGluing.normalIter futureDomain f j (t, x)‖ ≤ D := by
    have hc0 := hC t ht x
    simp only [norm_iteratedFDerivWithin_zero] at hc0
    exact (mul_le_mul_of_nonneg_right hxpow (norm_nonneg _)).trans
      (hc0.trans (le_max_left C 0))
  calc
    ‖NavierStokes.SpacetimeGluing.normalIter futureDomain f j (t, x)‖
        ≤ D / (1 + ‖x‖) ^ N := (le_div_iff₀' (by positivity)).2 hweighted
    _ = M x := by
      simp only [M]
      rw [div_eq_mul_inv, ← Real.rpow_natCast, Real.rpow_neg (by positivity)]

/-- The slope of a pointwise normal jet is bounded by any common bound for the next jet. -/
theorem norm_slope_normalIter_le {f : A02.SpaceTimeField} (hf : MemForceRapid f)
    (j : ℕ) {M : Space → ℝ}
    (hM : ∀ r : ℝ, 0 ≤ r → ∀ x : Space,
      ‖NavierStokes.SpacetimeGluing.normalIter futureDomain f (j + 1) (r, x)‖ ≤ M x)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hst : s ≠ t) (x : Space) :
    ‖slope (fun r => NavierStokes.SpacetimeGluing.normalIter futureDomain f j (r, x)) t s‖
      ≤ M x := by
  have hsub := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r hr => normalIter_time_hasDerivWithinAt hf.1 j hr x)
    (fun r hr => hM r hr x) (convex_Ici (0 : ℝ)) ht hs
  rw [slope_def_module, norm_smul, norm_inv]
  have hn : ‖s - t‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hst)
  calc
    ‖s - t‖⁻¹ *
        ‖NavierStokes.SpacetimeGluing.normalIter futureDomain f j (s, x) -
          NavierStokes.SpacetimeGluing.normalIter futureDomain f j (t, x)‖
        ≤ ‖s - t‖⁻¹ * (M x * ‖s - t‖) :=
      mul_le_mul_of_nonneg_left hsub (inv_nonneg.mpr (norm_nonneg _))
    _ = M x := by field_simp

/-- In actual `L²`, the `j`-th normal slice has within derivative the next normal slice. -/
theorem rapidNormalLp_hasDerivWithinAt {f : A02.SpaceTimeField} (hf : MemForceRapid f)
    (j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (rapidNormalLp hf j) (rapidNormalLp hf (j + 1) t) (Ici 0) t := by
  obtain ⟨M, hMmem, hM⟩ := exists_rapidNormal_memLp_majorant hf (j + 1)
  apply hasDerivWithinAt_iff_tendsto_slope.mpr
  apply EulerLpConvergence.tendsto_of_dominated volume
    (fun s => slope (rapidNormalLp hf j) t s) (rapidNormalLp hf (j + 1) t)
    (fun s x => slope (fun r => rapidNormalField f j r x) t s)
    (fun x => NavierStokes.SpacetimeGluing.normalIter futureDomain f (j + 1) (t, x))
    (slope_rapidNormalLp_ae hf j t) (rapidNormalLp_ae hf (j + 1) ht)
    (fun x => 2 * M x) (hMmem.const_mul 2)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : 0 ≤ s := hs.1
    have hst : s ≠ t := by simpa only [mem_singleton_iff, not_false_eq_true] using hs.2
    filter_upwards [] with x
    have heq : slope (fun r => rapidNormalField f j r x) t s =
        slope (fun r =>
          NavierStokes.SpacetimeGluing.normalIter futureDomain f j (r, x)) t s := by
      rw [slope_def_module, slope_def_module]
      simp only [rapidNormalField, ite_eq_left hs0, ite_eq_left ht]
    rw [heq]
    calc
      ‖slope (fun r =>
            NavierStokes.SpacetimeGluing.normalIter futureDomain f j (r, x)) t s -
          NavierStokes.SpacetimeGluing.normalIter futureDomain f (j + 1) (t, x)‖
          ≤ ‖slope (fun r =>
              NavierStokes.SpacetimeGluing.normalIter futureDomain f j (r, x)) t s‖ +
            ‖NavierStokes.SpacetimeGluing.normalIter futureDomain f (j + 1) (t, x)‖ :=
        norm_sub_le _ _
      _ ≤ M x + M x := add_le_add
        (norm_slope_normalIter_le hf j hM ht hs0 hst x) (hM t ht x)
      _ = 2 * M x := by ring
  · filter_upwards [] with x
    have hlim := hasDerivWithinAt_iff_tendsto_slope.mp
      (normalIter_time_hasDerivWithinAt hf.1 j ht x)
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : 0 ≤ s := hs.1
    rw [slope_def_module, slope_def_module]
    simp only [rapidNormalField, ite_eq_left hs0, ite_eq_left ht]

/-- Every rapid normal-jet path is `C^n` in ordinary spatial `L²`. -/
theorem rapidNormalLp_contDiffOn_nat {f : A02.SpaceTimeField} (hf : MemForceRapid f)
    (j n : ℕ) : ContDiffOn ℝ n (rapidNormalLp hf j) (Ici 0) := by
  induction n generalizing j with
  | zero =>
      apply contDiffOn_zero.mpr
      intro t ht
      exact (rapidNormalLp_hasDerivWithinAt hf j ht).continuousWithinAt
  | succ n ih =>
      rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp]
      apply (contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ici 0)).mpr
      refine ⟨fun t ht => (rapidNormalLp_hasDerivWithinAt hf j ht).differentiableWithinAt,
        by simp, ?_⟩
      exact (ih (j + 1)).congr fun t ht =>
        (rapidNormalLp_hasDerivWithinAt hf j ht).derivWithin
          ((uniqueDiffOn_Ici 0).uniqueDiffWithinAt ht)

/-- Every rapid normal-jet path is smooth in ordinary spatial `L²`. -/
theorem rapidNormalLp_contDiffOn {f : A02.SpaceTimeField} (hf : MemForceRapid f) (j : ℕ) :
    ContDiffOn ℝ ∞ (rapidNormalLp hf j) (Ici 0) :=
  contDiffOn_infty.mpr fun n => rapidNormalLp_contDiffOn_nat hf j n

/-! ## 3. Rapid Sobolev datum paths -/

/-- The canonical order-`m` angular datum of the `j`-th normal slice, totalized by zero. -/
def rapidDatum {f : A02.SpaceTimeField} (hf : MemForceRapid f) (m j : ℕ) :
    ℝ → RealVectorSobolev (m : ℝ) := fun t =>
  if ht : 0 ≤ t then
    D01.smoothAngularDatum m (m : ℝ) le_rfl (rapidSmoothSlice hf j t ht)
  else 0

/-- On every closed future interval, all spatial jets of a rapid normal slice vary
continuously in `L²`. -/
theorem rapidSmoothSlice_jetLp_continuous_Icc {f : A02.SpaceTimeField}
    (hf : MemForceRapid f) (j k : ℕ) {T : ℝ} (_hT : 0 ≤ T) :
    Continuous (fun t : Icc (0 : ℝ) T =>
      (rapidSmoothSlice hf j t.1 t.2.1).jetLp k) := by
  have hcont : Continuous
      ((Icc (0 : ℝ) T).domRestrict (rapidJetLp hf j k)) :=
    continuousOn_iff_continuous_domRestrict.mp
      ((rapidJetLp_continuousOn hf j k).mono Icc_subset_Ici_self)
  apply hcont.congr
  intro t
  simp only [Set.domRestrict_apply, rapidJetLp, dite_eq_left t.2.1]

/-- The order-`m` rapid datum path is continuous on every closed future interval. -/
theorem rapidDatum_continuousOn_Icc {f : A02.SpaceTimeField}
    (hf : MemForceRapid f) (m j : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (rapidDatum hf m j) (Icc (0 : ℝ) T) := by
  let P : Icc (0 : ℝ) T → SmoothL2Field Space :=
    fun t => rapidSmoothSlice hf j t.1 t.2.1
  have hP : ∀ k, Continuous (fun t : Icc (0 : ℝ) T => (P t).jetLp k) := by
    intro k
    exact rapidSmoothSlice_jetLp_continuous_Icc hf j k hT
  have hG := C01.smoothAngularDatum_path_continuous P hP m
  rw [continuousOn_iff_continuous_domRestrict]
  apply hG.congr
  intro t
  simp only [Set.domRestrict_apply, rapidDatum, dite_eq_left t.2.1, P]

/-- The order-`m` rapid datum path is continuous on the whole future half-line. -/
theorem rapidDatum_continuousOn {f : A02.SpaceTimeField} (hf : MemForceRapid f)
    (m j : ℕ) : ContinuousOn (rapidDatum hf m j) (Ici 0) := by
  intro t ht
  let T : ℝ := t + 1
  have hT : 0 ≤ T := by
    dsimp [T]
    exact add_nonneg (show 0 ≤ t from ht) (by norm_num)
  have htT : t < T := by simp [T]
  have htIcc : t ∈ Icc (0 : ℝ) T := ⟨ht, htT.le⟩
  have hc := rapidDatum_continuousOn_Icc hf m j hT t htIcc
  have hIic : Iic T ∈ nhds t :=
    Filter.mem_of_superset (Iio_mem_nhds htT) Iio_subset_Iic_self
  have hIcc : Icc (0 : ℝ) T ∈ nhdsWithin t (Ici (0 : ℝ)) := by
    apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
    refine ⟨Iic T, hIic, ?_⟩
    rintro s ⟨hsT, hs0⟩
    exact ⟨hs0, hsT⟩
  exact hc.mono_of_mem_nhdsWithin hIcc

/-- Lowering a rapid order-`m` datum to order zero gives the fixed order-zero Fourier
map of the physical `L²` slice. -/
theorem lower_rapidDatum_eq_orderZero {f : A02.SpaceTimeField} (hf : MemForceRapid f)
    (m j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    D01.lowerVectorL (m : ℝ) 0 (by positivity) (rapidDatum hf m j t) =
      A01.orderZeroDatumCLM (rapidNormalLp hf j t) := by
  apply D01.isSobolevDatum_unique
  · rw [rapidDatum, dite_eq_left ht]
    exact D01.Leray.isSobolevDatum_lower (by positivity)
      (D01.smoothAngularDatum_isSobolevDatum m (m : ℝ) le_rfl
        (rapidSmoothSlice hf j t ht))
  · rw [← A01.orderZeroDatum_memLp_eq]
    exact A01.IsSobolevDatum.congr_field
      (A01.isSobolevDatum_zero_ordinaryL2 (rapidNormalLp hf j t))
      (rapidNormalLp_ae hf j ht)

/-- On a compact future interval, the normal datum path differentiates to the next
normal datum path, including at both endpoints. -/
theorem rapidDatum_hasDerivWithinAt_Icc {f : A02.SpaceTimeField}
    (hf : MemForceRapid f) (m j : ℕ) {T : ℝ} (hT : 0 < T)
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (rapidDatum hf m j) (rapidDatum hf m (j + 1) t.1)
      (Icc (0 : ℝ) T) t.1 := by
  let Ac : C(Icc (0 : ℝ) T, RealVectorSobolev (m : ℝ)) :=
    ⟨fun u => rapidDatum hf m j u.1,
      continuousOn_iff_continuous_domRestrict.mp
        (rapidDatum_continuousOn_Icc hf m j hT.le)⟩
  let Rc : C(Icc (0 : ℝ) T, RealVectorSobolev (m : ℝ)) :=
    ⟨fun u => rapidDatum hf m (j + 1) u.1,
      continuousOn_iff_continuous_domRestrict.mp
        (rapidDatum_continuousOn_Icc hf m (j + 1) hT.le)⟩
  let L := D01.lowerVectorL (m : ℝ) 0 (by positivity)
  have hdweak : ∀ r ∈ Ioo (0 : ℝ) T,
      HasDerivAt (fun s => L (EulerVolterraConvolution.extendPath T hT.le Ac s))
        (L (EulerVolterraConvolution.extendPath T hT.le Rc r)) r := by
    intro r hr
    have hdLp : HasDerivAt (rapidNormalLp hf j) (rapidNormalLp hf (j + 1) r) r :=
      (rapidNormalLp_hasDerivWithinAt hf j hr.1.le).hasDerivAt (Ici_mem_nhds hr.1)
    have hd0 := A01.orderZeroDatumCLM.hasFDerivAt.comp_hasDerivAt r hdLp
    have hfun :
        (fun s => L (EulerVolterraConvolution.extendPath T hT.le Ac s)) =ᶠ[nhds r]
          fun s => A01.orderZeroDatumCLM (rapidNormalLp hf j s) := by
      filter_upwards [Icc_mem_nhds hr.1 hr.2] with s hs
      simp only [EulerVolterraConvolution.extendPath,
        projIcc_of_mem hT.le hs, Ac, L]
      exact lower_rapidDatum_eq_orderZero hf m j hs.1
    have hval :
        L (EulerVolterraConvolution.extendPath T hT.le Rc r) =
          A01.orderZeroDatumCLM (rapidNormalLp hf (j + 1) r) := by
      simp only [EulerVolterraConvolution.extendPath,
        projIcc_of_mem hT.le ⟨hr.1.le, hr.2.le⟩,
        Rc, L]
      exact lower_rapidDatum_eq_orderZero hf m (j + 1) hr.1.le
    rw [hval]
    exact hd0.congr_of_eventuallyEq hfun
  have hd := EulerInjectivePathDerivative.hasDerivWithinAt_of_injective_map L
    (A01.lowerVectorL_injective (m : ℝ) 0 (by positivity)) T hT.le Ac Rc hdweak t
  apply hd.congr_of_mem _ t.2
  intro r hr
  simp only [EulerVolterraConvolution.extendPath,
    projIcc_of_mem hT.le hr]
  rfl

/-- The normal datum path differentiates to the next one on the whole future half-line. -/
theorem rapidDatum_hasDerivWithinAt {f : A02.SpaceTimeField}
    (hf : MemForceRapid f) (m j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (rapidDatum hf m j) (rapidDatum hf m (j + 1) t) (Ici 0) t := by
  let T : ℝ := t + 1
  have hT : 0 < T := by dsimp [T]; linarith
  have htT : t < T := by simp [T]
  have hd := rapidDatum_hasDerivWithinAt_Icc hf m j hT ⟨t, ht, htT.le⟩
  have hset : Icc (0 : ℝ) T =ᶠ[nhds t] Ici 0 := by
    filter_upwards [Iio_mem_nhds htT] with s hs
    change (0 ≤ s ∧ s ≤ T) = (0 ≤ s)
    apply propext
    exact ⟨fun h => h.1, fun h => ⟨h, hs.le⟩⟩
  exact hd.congr_set hset

/-- Every finite time-differentiability order of a rapid datum path. -/
theorem rapidDatum_contDiffOn_nat {f : A02.SpaceTimeField} (hf : MemForceRapid f)
    (m j n : ℕ) : ContDiffOn ℝ n (rapidDatum hf m j) (Ici 0) := by
  induction n generalizing j with
  | zero => exact contDiffOn_zero.mpr (rapidDatum_continuousOn hf m j)
  | succ n ih =>
      rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp]
      apply (contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ici 0)).mpr
      refine ⟨fun t ht => (rapidDatum_hasDerivWithinAt hf m j ht).differentiableWithinAt,
        by simp, ?_⟩
      exact (ih (j + 1)).congr fun t ht =>
        (rapidDatum_hasDerivWithinAt hf m j ht).derivWithin
          ((uniqueDiffOn_Ici 0).uniqueDiffWithinAt ht)

/-- The canonical order-`m` datum path of a rapid force is smooth in time. -/
theorem rapidDatum_contDiffOn {f : A02.SpaceTimeField} (hf : MemForceRapid f) (m j : ℕ) :
    ContDiffOn ℝ ∞ (rapidDatum hf m j) (Ici 0) :=
  contDiffOn_infty.mpr fun n => rapidDatum_contDiffOn_nat hf m j n

/-! ## 4. Rapid time decay and the ambient force class -/

/-- A decay power selected from temperate growth for a given time exponent. -/
def rapidDecayPower (p : ℝ≥0∞) : ℕ :=
  Classical.choose
    ((inferInstance : (volume : Measure ℝ).HasTemperateGrowth).exists_eLpNorm_lt_top p)

theorem rapidDecayPower_spec (p : ℝ≥0∞) :
    eLpNorm (fun t : ℝ => (1 + ‖t‖) ^ (-(rapidDecayPower p : ℝ))) p volume < ⊤ :=
  Classical.choose_spec
    ((inferInstance : (volume : Measure ℝ).HasTemperateGrowth).exists_eLpNorm_lt_top p)

/-- A fixed scalar majorant that belongs to both `L¹(ℝ)` and `L²(ℝ)`. -/
def rapidTimeDecay (t : ℝ) : ℝ :=
  (1 + ‖t‖) ^ (-(rapidDecayPower 1 : ℝ)) *
    (1 + ‖t‖) ^ (-(rapidDecayPower 2 : ℝ))

theorem rapidTimeDecay_nonneg (t : ℝ) : 0 ≤ rapidTimeDecay t := by
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)

theorem rapidTimeDecay_eq_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    rapidTimeDecay t =
      (1 + t) ^ (-(rapidDecayPower 1 : ℝ)) *
        (1 + t) ^ (-(rapidDecayPower 2 : ℝ)) := by
  rw [rapidTimeDecay, Real.norm_of_nonneg ht]

theorem rapidPowerDecay_memLp (p : ℝ≥0∞) :
    MemLp (fun t : ℝ => (1 + ‖t‖) ^ (-(rapidDecayPower p : ℝ))) p volume := by
  refine ⟨(Continuous.rpow_const (by fun_prop)
    (fun t : ℝ => Or.inl (show 1 + ‖t‖ ≠ 0 by positivity))).aestronglyMeasurable, ?_⟩
  exact rapidDecayPower_spec p

theorem rapidTimeDecay_memLp_one : MemLp rapidTimeDecay 1 D01.forceTimeMeasure := by
  apply ((rapidPowerDecay_memLp 1).mono
    ((Continuous.rpow_const (by fun_prop)
      (fun t : ℝ => Or.inl (show 1 + ‖t‖ ≠ 0 by positivity))).mul
      (Continuous.rpow_const (by fun_prop)
        (fun t : ℝ => Or.inl (show 1 + ‖t‖ ≠ 0 by positivity)))).aestronglyMeasurable ?_).mono_measure
    Measure.restrict_le_self
  filter_upwards [] with t
  simp only [Pi.mul_apply]
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg (by positivity) _)),
    Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact mul_le_of_le_one_right (Real.rpow_nonneg (by positivity) _)
    (Real.rpow_le_one_of_one_le_of_nonpos (by simp) (neg_nonpos.mpr (Nat.cast_nonneg _)))

theorem rapidTimeDecay_memLp_two : MemLp rapidTimeDecay 2 D01.forceTimeMeasure := by
  apply ((rapidPowerDecay_memLp 2).mono
    ((Continuous.rpow_const (by fun_prop)
      (fun t : ℝ => Or.inl (show 1 + ‖t‖ ≠ 0 by positivity))).mul
      (Continuous.rpow_const (by fun_prop)
        (fun t : ℝ => Or.inl (show 1 + ‖t‖ ≠ 0 by positivity)))).aestronglyMeasurable ?_).mono_measure
    Measure.restrict_le_self
  filter_upwards [] with t
  simp only [Pi.mul_apply]
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg (by positivity) _)),
    Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (by positivity) _)
    (Real.rpow_le_one_of_one_le_of_nonpos (by simp) (neg_nonpos.mpr (Nat.cast_nonneg _)))

/-- Restricting a joint derivative to spatial inputs can only decrease its operator norm. -/
theorem norm_spatialJet_le_joint {f : A02.SpaceTimeField} (hf : MemForceRapid f)
    (j k : ℕ) {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    ‖iteratedFDeriv ℝ k
      (fun y : Space => NavierStokes.SpacetimeGluing.normalIter futureDomain f j (t, y)) x‖ ≤
      ‖iteratedFDerivWithin ℝ k
        (NavierStokes.SpacetimeGluing.normalIter futureDomain f j)
        futureDomain (t, x)‖ := by
  rw [show (fun y : Space =>
    NavierStokes.SpacetimeGluing.normalIter futureDomain f j (t, y)) =
      ⇑(rapidNormalSlice hf j t ht) by rfl,
    iteratedFDeriv_rapidNormalSlice hf j k t ht x]
  calc
    ‖(iteratedFDerivWithin ℝ k
        (NavierStokes.SpacetimeGluing.normalIter futureDomain f j)
        futureDomain (t, x)).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.inr ℝ ℝ Space)‖
        ≤ ‖iteratedFDerivWithin ℝ k
            (NavierStokes.SpacetimeGluing.normalIter futureDomain f j)
            futureDomain (t, x)‖ *
          ∏ _i : Fin k, ‖ContinuousLinearMap.inr ℝ ℝ Space‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = _ := by simp only [ContinuousLinearMap.norm_inr, Finset.prod_const_one, mul_one]

/-- Every fixed spatial jet has a separable `L²_x` bound with rapid time decay. -/
theorem exists_rapidJet_time_bound {f : A02.SpaceTimeField}
    (hf : MemForceRapid f) (j k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 ≤ t →
      ‖rapidJetLp hf j k t‖ ≤ K * rapidTimeDecay t := by
  let P : ℕ := rapidDecayPower 1 + rapidDecayPower 2
  obtain ⟨N, hN⟩ :=
    (inferInstance : (volume : Measure Space).HasTemperateGrowth).exists_eLpNorm_lt_top 2
  obtain ⟨C, hC⟩ := normalIter_rapid_bound hf j (N + P) k
  let D : ℝ := max C 0
  let B : Space → ℝ := fun x => (1 + ‖x‖) ^ (-(N : ℝ))
  have hBcont : Continuous B :=
    Continuous.rpow_const (by fun_prop)
      (fun x : Space => Or.inl (show 1 + ‖x‖ ≠ 0 by positivity))
  have hBmem : MemLp B 2 volume := ⟨hBcont.aestronglyMeasurable, hN⟩
  let Bp : Lp ℝ 2 (volume : Measure Space) := hBmem.toLp B
  let K : ℝ := D * ‖Bp‖
  refine ⟨K, mul_nonneg (le_max_right C 0) (norm_nonneg Bp), fun t ht => ?_⟩
  have hpoint (x : Space) :
      ‖iteratedFDeriv ℝ k
        (fun y : Space =>
          NavierStokes.SpacetimeGluing.normalIter futureDomain f j (t, y)) x‖ ≤
        D * B x * rapidTimeDecay t := by
    have hspace : 0 < 1 + ‖x‖ := by positivity
    have htime : 0 < 1 + t := by linarith
    have hbase : 0 < 1 + ‖x‖ + t := by positivity
    have hxpow : (1 + ‖x‖) ^ N ≤ (1 + ‖x‖ + t) ^ N :=
      pow_le_pow_left₀ hspace.le (by linarith) N
    have htpow : (1 + t) ^ P ≤ (1 + ‖x‖ + t) ^ P :=
      pow_le_pow_left₀ htime.le (by linarith [norm_nonneg x]) P
    have hfactor :
        (1 + ‖x‖) ^ N * (1 + t) ^ P ≤ (1 + ‖x‖ + t) ^ (N + P) := by
      calc
        _ ≤ (1 + ‖x‖ + t) ^ N * (1 + ‖x‖ + t) ^ P :=
          mul_le_mul hxpow htpow (pow_nonneg htime.le P)
            (pow_nonneg hbase.le N)
        _ = _ := (pow_add (1 + ‖x‖ + t) N P).symm
    have hspatial := norm_spatialJet_le_joint hf j k ht x
    have hweighted :
        ((1 + ‖x‖) ^ N * (1 + t) ^ P) *
          ‖iteratedFDeriv ℝ k
            (fun y : Space =>
              NavierStokes.SpacetimeGluing.normalIter futureDomain f j (t, y)) x‖ ≤ D := by
      calc
        _ ≤ ((1 + ‖x‖) ^ N * (1 + t) ^ P) *
            ‖iteratedFDerivWithin ℝ k
              (NavierStokes.SpacetimeGluing.normalIter futureDomain f j)
              futureDomain (t, x)‖ :=
          mul_le_mul_of_nonneg_left hspatial
            (mul_nonneg (pow_nonneg hspace.le N) (pow_nonneg htime.le P))
        _ ≤ (1 + ‖x‖ + t) ^ (N + P) *
            ‖iteratedFDerivWithin ℝ k
              (NavierStokes.SpacetimeGluing.normalIter futureDomain f j)
              futureDomain (t, x)‖ :=
          mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)
        _ ≤ C := hC t ht x
        _ ≤ D := le_max_left C 0
    have hdecay : (1 + t) ^ (-(P : ℝ)) = rapidTimeDecay t := by
      simp only [rapidTimeDecay_eq_of_nonneg ht, P, Nat.cast_add, neg_add,
        Real.rpow_add htime]
    calc
      ‖iteratedFDeriv ℝ k
          (fun y : Space =>
            NavierStokes.SpacetimeGluing.normalIter futureDomain f j (t, y)) x‖
          ≤ D / ((1 + ‖x‖) ^ N * (1 + t) ^ P) :=
        (le_div_iff₀' (mul_pos (pow_pos hspace N) (pow_pos htime P))).2 hweighted
      _ = D * B x * rapidTimeDecay t := by
        simp only [B]
        rw [← hdecay, Real.rpow_neg hspace.le, Real.rpow_neg htime.le,
          Real.rpow_natCast, Real.rpow_natCast]
        field_simp
  let c : ℝ := D * rapidTimeDecay t
  have hBp : Bp =ᵐ[volume] B := by
    exact hBmem.coeFn_toLp
  calc
    ‖rapidJetLp hf j k t‖ ≤ ‖c • Bp‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [rapidJetLp_ae hf j k ht, Lp.coeFn_smul c Bp,
        hBp] with x hx hc hBx
      rw [hx, hc, Pi.smul_apply, hBx, norm_smul, Real.norm_of_nonneg
        (mul_nonneg (le_max_right C 0) (rapidTimeDecay_nonneg t)),
        Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      simpa only [c, B, mul_assoc, mul_comm, mul_left_comm] using hpoint x
    _ = c * ‖Bp‖ := by
      rw [norm_smul, Real.norm_of_nonneg
        (mul_nonneg (le_max_right C 0) (rapidTimeDecay_nonneg t))]
    _ = K * rapidTimeDecay t := by
      simp only [c, K]
      ring

/-- Every jet of the zero smooth field is zero. -/
theorem zeroField_jetLp (n : ℕ) :
    (EulerLpTranslation.SmoothL2Field.zeroField : SmoothL2Field Space).jetLp n = 0 := by
  apply Lp.ext
  filter_upwards [
    (EulerLpTranslation.SmoothL2Field.zeroField : SmoothL2Field Space).jetLp_ae n,
    Lp.coeFn_zero (Space [×n]→L[ℝ] Space) 2 volume] with x hx hz
  rw [hx, hz]
  simp [EulerLpTranslation.SmoothL2Field.zeroField]

/-- The canonical smooth angular datum of the zero field is the zero datum. -/
theorem smoothAngularDatum_zero (m : ℕ) :
    D01.smoothAngularDatum m (m : ℝ) le_rfl
      (EulerLpTranslation.SmoothL2Field.zeroField : SmoothL2Field Space) = 0 := by
  apply D01.isSobolevDatum_unique
  · exact D01.smoothAngularDatum_isSobolevDatum m (m : ℝ) le_rfl
      EulerLpTranslation.SmoothL2Field.zeroField
  · apply A01.IsSobolevDatum.congr_field (D01.isSobolevDatum_zero (m : ℝ))
    filter_upwards [] with x
    rfl

/-- The norm of a canonical rapid datum is controlled by the finite sum of its spatial jets. -/
theorem norm_rapidDatum_le_jet_sum {f : A02.SpaceTimeField}
    (hf : MemForceRapid f) (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖rapidDatum hf m 0 t‖ ≤
      (4 : ℝ) ^ m * ∑ k ∈ Finset.range (m + 1), ‖rapidJetLp hf 0 k t‖ := by
  let A := rapidSmoothSlice hf 0 t ht
  have hs := C01.norm_smoothAngularDatum_sub_sq_le m A
    (EulerLpTranslation.SmoothL2Field.zeroField : SmoothL2Field Space)
  rw [smoothAngularDatum_zero, sub_zero] at hs
  simp only [zeroField_jetLp, sub_zero] at hs
  let S : ℝ := ∑ k ∈ Finset.range (m + 1), ‖A.jetLp k‖
  have hS : 0 ≤ S := Finset.sum_nonneg fun k _ => norm_nonneg (A.jetLp k)
  have hsumSq :
      ∑ k ∈ Finset.range (m + 1), ‖A.jetLp k‖ ^ 2 ≤ S ^ 2 := by
    exact Finset.sum_sq_le_sq_sum_of_nonneg fun k _ => norm_nonneg (A.jetLp k)
  have hp : ((4 : ℝ) ^ m) ^ 2 = (16 : ℝ) ^ m := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hs' :
      ‖D01.smoothAngularDatum m (m : ℝ) le_rfl A‖ ^ 2 ≤
        ((4 : ℝ) ^ m * S) ^ 2 := by
    calc
      _ ≤ (16 : ℝ) ^ m * ∑ k ∈ Finset.range (m + 1), ‖A.jetLp k‖ ^ 2 := hs
      _ ≤ (16 : ℝ) ^ m * S ^ 2 :=
        mul_le_mul_of_nonneg_left hsumSq (pow_nonneg (by norm_num) m)
      _ = ((4 : ℝ) ^ m * S) ^ 2 := by rw [mul_pow, hp]
  have hraw :
      ‖D01.smoothAngularDatum m (m : ℝ) le_rfl A‖ ≤ (4 : ℝ) ^ m * S :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (pow_nonneg (by norm_num) m) hS)).mp hs'
  simpa only [rapidDatum, dite_eq_left ht, rapidJetLp, A, S] using hraw

/-- Every canonical rapid datum path has a common `L¹_t`/`L²_t` scalar majorant. -/
theorem exists_rapidDatum_time_bound {f : A02.SpaceTimeField}
    (hf : MemForceRapid f) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 ≤ t →
      ‖rapidDatum hf m 0 t‖ ≤ K * rapidTimeDecay t := by
  choose K hK hbound using fun k : ℕ => exists_rapidJet_time_bound hf 0 k
  let S : ℝ := ∑ k ∈ Finset.range (m + 1), K k
  let Ktotal : ℝ := (4 : ℝ) ^ m * S
  have hS : 0 ≤ S := Finset.sum_nonneg fun k _ => hK k
  refine ⟨Ktotal, mul_nonneg (pow_nonneg (by norm_num) m) hS, fun t ht => ?_⟩
  calc
    ‖rapidDatum hf m 0 t‖
        ≤ (4 : ℝ) ^ m * ∑ k ∈ Finset.range (m + 1), ‖rapidJetLp hf 0 k t‖ :=
      norm_rapidDatum_le_jet_sum hf m ht
    _ ≤ (4 : ℝ) ^ m * ∑ k ∈ Finset.range (m + 1), K k * rapidTimeDecay t := by
      gcongr with k hk
      exact hbound k t ht
    _ = Ktotal * rapidTimeDecay t := by
      rw [← Finset.sum_mul]
      simp only [Ktotal, S]
      ring

/-- The canonical rapid datum path realizes the physical force at every future time. -/
theorem rapidDatum_isSobolevPath {f : A02.SpaceTimeField}
    (hf : MemForceRapid f) (m : ℕ) :
    D01.IsSobolevPath (m : ℝ) f (rapidDatum hf m 0) := by
  intro t ht
  rw [rapidDatum, dite_eq_left ht]
  apply A01.IsSobolevDatum.congr_field
    (D01.smoothAngularDatum_isSobolevDatum m (m : ℝ) le_rfl
      (rapidSmoothSlice hf 0 t ht))
  filter_upwards [] with x
  rw [rapidSmoothSlice_field]
  rfl

theorem rapidDatum_memLp_one {f : A02.SpaceTimeField}
    (hf : MemForceRapid f) (m : ℕ) :
    MemLp (rapidDatum hf m 0) 1 D01.forceTimeMeasure := by
  obtain ⟨K, _hK, hbound⟩ := exists_rapidDatum_time_bound hf m
  let _ : SecondCountableTopologyEither ℝ (RealVectorSobolev (m : ℝ)) :=
    ⟨Or.inl inferInstance⟩
  have hmeas : AEStronglyMeasurable (rapidDatum hf m 0) D01.forceTimeMeasure :=
    ((rapidDatum_continuousOn hf m 0).mono Ioi_subset_Ici_self).aestronglyMeasurable
      measurableSet_Ioi
  apply (rapidTimeDecay_memLp_one.const_mul K).mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact hbound t ht.le

theorem rapidDatum_memLp_two {f : A02.SpaceTimeField}
    (hf : MemForceRapid f) (m : ℕ) :
    MemLp (rapidDatum hf m 0) 2 D01.forceTimeMeasure := by
  obtain ⟨K, _hK, hbound⟩ := exists_rapidDatum_time_bound hf m
  let _ : SecondCountableTopologyEither ℝ (RealVectorSobolev (m : ℝ)) :=
    ⟨Or.inl inferInstance⟩
  have hmeas : AEStronglyMeasurable (rapidDatum hf m 0) D01.forceTimeMeasure :=
    ((rapidDatum_continuousOn hf m 0).mono Ioi_subset_Ici_self).aestronglyMeasurable
      measurableSet_Ioi
  apply (rapidTimeDecay_memLp_two.const_mul K).mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact hbound t ht.le

/-- **G2.** Every rapidly decreasing force belongs to the ambient manuscript force class. -/
theorem memForceR_of_memForceRapid {f : A02.SpaceTimeField}
    (hf : MemForceRapid f) : D01.MemForceR f := by
  refine ⟨hf.1, fun m => ⟨rapidDatum hf m 0, rapidDatum_isSobolevPath hf m,
    rapidDatum_contDiffOn hf m 0, rapidDatum_memLp_one hf m, rapidDatum_memLp_two hf m⟩⟩

/-- Set-level spelling of G2. -/
theorem forceClassRapid_subset_forceClassR : forceClassRapid ⊆ forceClassR := by
  intro f hf
  exact memForceR_of_memForceRapid hf

/-! ## 5. Compact support implies rapid decay -/

/-- A compact spacetime support has a compact common spatial projection. -/
theorem compact_spatial_projection {f : A02.SpaceTimeField}
    (hf : HasCompactSupport f) :
    IsCompact (Prod.snd '' tsupport f) :=
  hf.image continuous_snd

/-- A field is zero away from the spatial projection of its spacetime support. -/
theorem supportedIn_spatial_projection {f : A02.SpaceTimeField} :
    NavierStokes.CompactSpatialForceDecay.SupportedIn (Prod.snd '' tsupport f) f := by
  intro t _ x hx
  apply image_eq_zero_of_notMem_tsupport
  intro htx
  exact hx ⟨(t, x), htx, rfl⟩

/-- Compact spacetime support supplies a uniform finite future-time cutoff. -/
theorem compactFutureTimeSupport_of_hasCompactSupport {f : A02.SpaceTimeField}
    (hf : HasCompactSupport f) : CompactFutureTimeSupport f := by
  obtain ⟨B, hB⟩ := bddAbove_def.mp
    ((hf.image continuous_fst).bddAbove : BddAbove (Prod.fst '' tsupport f))
  refine ⟨max B 0 + 1, by positivity, ?_⟩
  intro t ht x
  apply image_eq_zero_of_notMem_tsupport
  intro htx
  have htB : t ≤ B := hB t ⟨(t, x), htx, rfl⟩
  linarith [le_max_left B 0]

/-- Every compactly supported manuscript force is rapidly decreasing. -/
theorem memForceRapid_of_memForceCompact {f : A02.SpaceTimeField}
    (hf : D01.MemForceCompact f) : MemForceRapid f := by
  rcases hf with ⟨hfs, hsupport⟩
  refine ⟨hfs.contDiffOn, ?_⟩
  intro N k
  let S : Set Space := Prod.snd '' tsupport f
  obtain ⟨C, hC, hb⟩ := NavierStokes.CompactSpatialForceDecay.jet_decay
    (S := S) (compact_spatial_projection hsupport.1) hfs.contDiffOn
    supportedIn_spatial_projection (compactFutureTimeSupport_of_hasCompactSupport hsupport.1)
    k (N : ℝ)
  refine ⟨C, ?_⟩
  intro t ht x
  have hp : 0 < 1 + ‖x‖ + t := by positivity
  have hb' := hb t ht x
  rw [Real.rpow_natCast] at hb'
  calc
    (1 + ‖x‖ + t) ^ N *
        ‖iteratedFDerivWithin ℝ k f futureDomain (t, x)‖
        ≤ (1 + ‖x‖ + t) ^ N * (C / (1 + ‖x‖ + t) ^ N) :=
      mul_le_mul_of_nonneg_left hb' (pow_nonneg hp.le N)
    _ = C := by field_simp

/-! ## 6. Rapid decay is stable under compact corrections -/

/-- The sum of two rapidly decreasing forces is rapidly decreasing. -/
theorem memForceRapid_add {f g : A02.SpaceTimeField}
    (hf : MemForceRapid f) (hg : MemForceRapid g) : MemForceRapid (f + g) := by
  refine ⟨hf.1.add hg.1, ?_⟩
  intro N k
  obtain ⟨Cf, hCf⟩ := hf.2 N k
  obtain ⟨Cg, hCg⟩ := hg.2 N k
  refine ⟨Cf + Cg, ?_⟩
  intro t ht x
  have hz : (t, x) ∈ futureDomain := ⟨ht, mem_univ x⟩
  have hbase : 0 ≤ (1 + ‖x‖ + t) ^ N := pow_nonneg (by positivity) N
  have hfk : ContDiffWithinAt ℝ (k : WithTop ℕ∞) f futureDomain (t, x) :=
    (hf.1 (t, x) hz).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)
  have hgk : ContDiffWithinAt ℝ (k : WithTop ℕ∞) g futureDomain (t, x) :=
    (hg.1 (t, x) hz).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)
  rw [iteratedFDerivWithin_add_apply hfk hgk
    ((uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ) hz]
  calc
    (1 + ‖x‖ + t) ^ N *
        ‖iteratedFDerivWithin ℝ k f futureDomain (t, x) +
          iteratedFDerivWithin ℝ k g futureDomain (t, x)‖
        ≤ (1 + ‖x‖ + t) ^ N *
          (‖iteratedFDerivWithin ℝ k f futureDomain (t, x)‖ +
            ‖iteratedFDerivWithin ℝ k g futureDomain (t, x)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) hbase
    _ = (1 + ‖x‖ + t) ^ N *
          ‖iteratedFDerivWithin ℝ k f futureDomain (t, x)‖ +
        (1 + ‖x‖ + t) ^ N *
          ‖iteratedFDerivWithin ℝ k g futureDomain (t, x)‖ := by ring
    _ ≤ Cf + Cg := add_le_add (hCf t ht x) (hCg t ht x)

/-- **G3.** Adding a spacetime-compact correction preserves the rapid class. -/
theorem memForceRapid_of_compact_difference (g f : A02.SpaceTimeField)
    (hg : MemForceRapid g)
    (hfg : D01.MemForceCompact (fun z => f z - g z)) : MemForceRapid f := by
  have hsum := memForceRapid_add hg (memForceRapid_of_memForceCompact hfg)
  convert hsum using 1
  ext z
  simp

/-! ## 7. Schwartz initial data lie in `X_R` -/

/-- The three complex Schwartz components associated with a real vector-valued Schwartz map. -/
def complexComponents (a : SchwartzMap Space Space) (i : Fin 3) : SchwartzMap Space ℂ :=
  SchwartzMap.postcompCLM (Complex.ofRealCLM.comp (EuclideanSpace.proj i)) a

@[simp] theorem complexComponents_apply (a : SchwartzMap Space Space) (i : Fin 3) (x : Space) :
    complexComponents a i x = (a x i : ℂ) := rfl

/-- A vector-valued Schwartz map has an angular Sobolev datum at every real order. -/
theorem isSobolevDatum_schwartz (s : ℝ) (a : SchwartzMap Space Space) :
    D01.IsSobolevDatum s (⇑a) (B01.spatialDatum s (complexComponents a)) := by
  have h := B01.spatialDatum_isSobolevDatum s (complexComponents a)
  convert h using 1
  funext x
  ext i
  simp [B01.spatialVector]

/-- **G4.** The rapid-decay initial class is contained in the ambient initial class. -/
theorem initialClassSchwartz_subset_initialClassR :
    initialClassSchwartz ⊆ A02.initialClassR := by
  intro a ha
  rcases ha with ⟨⟨φ, rfl⟩, hsol⟩
  refine ⟨⟨φ.smooth (⊤ : ℕ∞), ?_⟩, hsol⟩
  intro m
  exact ⟨B01.spatialDatum (m : ℝ) (complexComponents φ),
    isSobolevDatum_schwartz (m : ℝ) φ⟩

/-! ## 8. The zero force norm -/

/-- The all-zero datum path realizes the all-zero physical force. -/
theorem isSobolevPath_zero (s : ℝ) :
    D01.IsSobolevPath s (0 : A02.SpaceTimeField) (fun _ => 0) :=
  fun _ _ => D01.isSobolevDatum_zero s

/-- **G5, strengthened to every time exponent.** -/
theorem forceSobolevENorm_zero (q : ℝ≥0∞) (s : ℝ) :
    D01.forceSobolevENorm q s (0 : A02.SpaceTimeField) = 0 := by
  apply le_antisymm
  · calc
      D01.forceSobolevENorm q s (0 : A02.SpaceTimeField)
          ≤ D01.Homogeneous.bochnerDatumENorm q s (fun _ => 0) :=
        iInf_le (fun G : {G : ℝ → RealVectorSobolev s //
          D01.IsSobolevPath s (0 : A02.SpaceTimeField) G ∧
            AEStronglyMeasurable G D01.forceTimeMeasure} =>
              D01.Homogeneous.bochnerDatumENorm q s G.1)
          ⟨fun _ => 0, isSobolevPath_zero s, stronglyMeasurable_const.aestronglyMeasurable⟩
      _ = 0 := eLpNorm_zero
  · exact bot_le

/-- The exact q=1/q=2 spelling requested by the density branch. -/
theorem forceSobolevENorm_zero_of_one_or_two (q : ℝ≥0∞) (_hq : q = 1 ∨ q = 2) (s : ℝ) :
    D01.forceSobolevENorm q s (0 : A02.SpaceTimeField) = 0 :=
  forceSobolevENorm_zero q s

/-- The pointwise algebra used when the density proof chooses its centre itself. -/
theorem sub_self_force (g : A02.SpaceTimeField) : (fun z => g z - g z) = 0 := by
  funext z
  exact sub_self (g z)

end NSFormalization.Section4.R41
