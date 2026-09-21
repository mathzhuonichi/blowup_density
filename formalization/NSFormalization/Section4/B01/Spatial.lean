import NSFormalization.Section4.B01.Separated

/-!
# B01 unit 8: real compact-smooth spatial density in `H^s`

This module discharges the `B01` obligation `spatialApprox` of `research/B01/Spec.lean:250`
(unit 8 of `research/B01/COMPARISON.md:152`), the field of `BochnerApproxAPI` packaging stages
1–3 of the proof of Proposition 4.6 (`paper/sections/04-whole-space.tex:231-239,249`): every
order-`s` real-vector Sobolev datum `A` is approximated, in the datum norm, by the datum of a
physical `C_c^∞(R³;R³)` real vector field, for every real `s`.

The construction is componentwise, in the manuscript's phrasing "take real parts of each
component" (`04-whole-space.tex:249`):

* `SD:59` `dense_compact_weightedFourierLp s` gives, for each component target
  `realSobolevInclusion s (A_c i)`, a compactly supported smooth `ψ i` with
  `‖weightedFourierLp s (ψ i) - realSobolevInclusion s (A_c i)‖` small (`A_c` = the cycles reading
  of `A`);
* the datum of the physical field `x ↦ Re (ψ i x)` is
  `realProjectionTo s (weightedFourierLp s (ψ i))` (`RPD:21`), via
  `weightedFourierLp_realPart`, `sobolevRealization_weightedFourierLp` and `ARS:89`
  `angularRealization_cyclesToAngularReal`, assembled by `FHB` into `RealVectorSobolev s` and
  transported to the angular convention by `ARVB:15` `cyclesToAngularRealVector`;
* the datum-norm error is controlled by the `RPD:34` operator-norm-`≤1` of `realProjectionTo`, the
  finite-product triangle inequality (`FHB` `reconstruction`), and the `ARVB:24`
  `cyclesToAngularRealVector_norm_le` constant `frequencyUnit ^ |s|`.

## Restated `Contracts.V1.Data` predicates

`IsSobolevDatum` is reused from `Section4/D01/SmoothDatum.lean`, which restates it token-for-token
from `Contracts/V1/Data.lean:160`; `SpatialField := Space → Space` (`Data.lean:99`).  The
conformance file `research/B01/axioms_u68.lean` discharges the spec field through the resulting
definitional equality.
-/

noncomputable section

namespace NSFormalization.Section4.B01

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source NSFormalization.Source.RealSobolev
open NSFormalization.Source.FiniteHilbertBochner
open NSFormalization.Section4.D01
open scoped ContDiff ENNReal SchwartzMap

/-! ## 0. Spatial assembly and datum

`SpatialField := Space → Space` (`Contracts.V1.Data:99`) is reused from `B01/Separated.lean`. -/

/-- Assemble three real scalar spatial fields into a Euclidean three-vector field, the spatial
analogue of `Paper3.physicalVector`. -/
def spatialVector (g : Fin 3 → Space → ℝ) : SpatialField :=
  fun x => WithLp.toLp 2 (fun i => g i x)

@[simp] theorem spatialVector_apply (g : Fin 3 → Space → ℝ) (x : Space) (i : Fin 3) :
    spatialVector g x i = g i x := rfl

theorem spatialVector_smooth (g : Fin 3 → Space → ℝ) (hg : ∀ i, ContDiff ℝ ∞ (g i)) :
    ContDiff ℝ ∞ (spatialVector g) :=
  (contDiff_piLp 2).mpr hg

theorem spatialVector_support (g : Fin 3 → Space → ℝ) :
    tsupport (spatialVector g) ⊆ ⋃ i, tsupport (g i) := by
  apply closure_minimal
  · intro x hx
    by_contra hn
    have he : spatialVector g x = 0 := by
      ext i
      show g i x = 0
      exact image_eq_zero_of_notMem_tsupport (fun hi => hn (mem_iUnion.mpr ⟨i, hi⟩))
    exact hx he
  · exact isClosed_iUnion_of_finite (fun i => isClosed_tsupport (g i))

theorem spatialVector_compact (g : Fin 3 → Space → ℝ)
    (hc : ∀ i, HasCompactSupport (g i)) : HasCompactSupport (spatialVector g) :=
  (isCompact_iUnion hc).of_isClosed_subset (isClosed_tsupport _) (spatialVector_support g)

/-- The assembled cycles-convention datum vector of three Schwartz approximants: the real
projections of `weightedFourierLp s (ψ i)`, packaged into `RealVectorSobolev s`. -/
def spatialCyclesVector (s : ℝ) (ψ : Fin 3 → SchwartzMap Space ℂ) : RealVectorSobolev s :=
  WithLp.toLp 2 (fun i => realProjectionTo s (weightedFourierLp s (ψ i)))

@[simp] theorem spatialCyclesVector_apply (s : ℝ) (ψ : Fin 3 → SchwartzMap Space ℂ) (i : Fin 3) :
    spatialCyclesVector s ψ i = realProjectionTo s (weightedFourierLp s (ψ i)) := rfl

/-- The order-`s` angular real-vector datum assembled from three compactly supported smooth
scalar approximants `ψ i`: the manuscript convention change (`ARVB:15`) of `spatialCyclesVector`. -/
def spatialDatum (s : ℝ) (ψ : Fin 3 → SchwartzMap Space ℂ) : RealVectorSobolev s :=
  cyclesToAngularRealVector s (spatialCyclesVector s ψ)

theorem spatialDatum_eq (s : ℝ) (ψ : Fin 3 → SchwartzMap Space ℂ) :
    spatialDatum s ψ = cyclesToAngularRealVector s (spatialCyclesVector s ψ) := rfl

/-- The assembled datum realizes exactly the physical field `x ↦ Re (ψ i x)`: the pairing content
of `Data.IsSobolevDatum`. -/
theorem spatialDatum_isSobolevDatum (s : ℝ) (ψ : Fin 3 → SchwartzMap Space ℂ) :
    IsSobolevDatum s (spatialVector (fun i x => (ψ i x).re)) (spatialDatum s ψ) := by
  intro i ψt
  show angularRealization s
    ((cyclesToAngularRealVector s (spatialCyclesVector s ψ) i : RealSobolevHilbert s)
      : FourierData) ψt = _
  rw [cyclesToAngularRealVector_apply, angularRealization_cyclesToAngularReal]
  show sobolevRealization s
    ((realProjectionTo s (weightedFourierLp s (ψ i)) : RealSobolevHilbert s) : FourierData) ψt = _
  have hcoe : ((realProjectionTo s (weightedFourierLp s (ψ i)) : RealSobolevHilbert s)
      : FourierData) = realProjection (weightedFourierLp s (ψ i)) := rfl
  rw [hcoe, ← weightedFourierLp_realPart, sobolevRealization_weightedFourierLp,
    SchwartzMap.coe_apply]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [realPartSchwartz_apply]
  rfl

/-! ## 1. Finite-product norm bound -/

/-- The Euclidean product norm is bounded by the sum of the coordinate norms. -/
theorem norm_le_sum_coord (s : ℝ) (v : RealVectorSobolev s) :
    ‖v‖ ≤ ∑ i, ‖v i‖ := by
  calc ‖v‖ = ‖∑ i, insert i (coord i v)‖ := by rw [reconstruction v]
    _ ≤ ∑ i, ‖insert i (coord i v)‖ := norm_sum_le _ _
    _ = ∑ i, ‖v i‖ := Finset.sum_congr rfl (fun i _ => norm_insert i (coord i v))

/-! ## 2. Unit 8: `spatialApprox` (`research/B01/Spec.lean:250`) -/

set_option maxHeartbeats 400000 in
/-- **Unit 8, `spatialApprox`.**  Every order-`s` real-vector Sobolev datum `A` is approximated in
the datum norm, to arbitrary precision `η`, by the datum `H` of a physical `C_c^∞(R³;R³)` real
vector field `h`.  Every real `s`; no threshold.  `paper/sections/04-whole-space.tex:231-239,249`.

The `set_option maxHeartbeats 400000 in` (the `Section4/A03/RealAngularProduct.lean:111` idiom;
measured floor 350000) covers only this theorem: the `rw [spatialDatum_eq, map_sub, …]` and
`rw [← ofReal_norm]` steps trigger heavy `RealVectorSobolev`/`cyclesToAngularRealVector` defeq. -/
theorem spatialApprox (s : ℝ) (A : RealVectorSobolev s) (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ (h : SpatialField) (H : RealVectorSobolev s),
      ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧ IsSobolevDatum s h H ∧ ‖H - A‖ₑ < η := by
  have hCpos : (0 : ℝ) < frequencyUnit ^ |s| := Real.rpow_pos_of_pos frequencyUnit_pos _
  set A_c : RealVectorSobolev s := (cyclesToAngularRealVector s).symm A with hAc
  -- choose the real precision δ
  obtain ⟨δ, hδpos, hδ⟩ :
      ∃ δ : ℝ, 0 < δ ∧ (η ≠ ⊤ → frequencyUnit ^ |s| * (3 * δ) < η.toReal) := by
    by_cases hηtop : η = ⊤
    · exact ⟨1, one_pos, fun h => absurd hηtop h⟩
    · have hηr : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hηtop
      have hden : (0 : ℝ) < 3 * (frequencyUnit ^ |s| + 1) := by positivity
      have hdpos : (0 : ℝ) < η.toReal / (3 * (frequencyUnit ^ |s| + 1)) := div_pos hηr hden
      refine ⟨η.toReal / (3 * (frequencyUnit ^ |s| + 1)), hdpos, fun _ => ?_⟩
      have hmul : (η.toReal / (3 * (frequencyUnit ^ |s| + 1))) * (3 * (frequencyUnit ^ |s| + 1))
          = η.toReal := div_mul_cancel₀ _ hden.ne'
      nlinarith [hmul, hdpos, hCpos]
  -- per component: a compact smooth ψ i with weightedFourierLp close to the cycles target
  have hex : ∀ i : Fin 3, ∃ ψ : SchwartzMap Space ℂ, HasCompactSupport (ψ : Space → ℂ) ∧
      ‖weightedFourierLp s ψ - realSobolevInclusion s (A_c i)‖ < δ := by
    intro i
    obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.mp
      (dense_compact_weightedFourierLp s (realSobolevInclusion s (A_c i))) δ hδpos
    obtain ⟨ψ, hψc, rfl⟩ := hy
    exact ⟨ψ, hψc, by rw [norm_sub_rev, ← dist_eq_norm]; exact hdist⟩
  choose ψ hψc hψδ using hex
  refine ⟨spatialVector (fun i x => (ψ i x).re), spatialDatum s ψ, ?_, ?_,
    spatialDatum_isSobolevDatum s ψ, ?_⟩
  · exact spatialVector_smooth _ fun i => Complex.reCLM.contDiff.comp ((ψ i).smooth ⊤)
  · exact spatialVector_compact _ fun i =>
      (hψc i).comp_left (g := Complex.re) Complex.zero_re
  -- the datum-norm estimate
  · have hcomp : ∀ i : Fin 3, ‖spatialCyclesVector s ψ i - A_c i‖ ≤ δ := by
      intro i
      rw [spatialCyclesVector_apply,
        show realProjectionTo s (weightedFourierLp s (ψ i)) - A_c i
          = realProjectionTo s (weightedFourierLp s (ψ i) - realSobolevInclusion s (A_c i)) from by
            rw [map_sub, realProjectionTo_inclusion]]
      exact (realProjectionTo_norm_le s _).trans (hψδ i).le
    have hsum : ‖spatialCyclesVector s ψ - A_c‖ ≤ 3 * δ := by
      refine (norm_le_sum_coord s _).trans ?_
      calc ∑ i, ‖(spatialCyclesVector s ψ - A_c) i‖
          ≤ ∑ _i : Fin 3, δ := Finset.sum_le_sum (fun i _ => hcomp i)
        _ = 3 * δ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num
    have hHA : spatialDatum s ψ - A = cyclesToAngularRealVector s (spatialCyclesVector s ψ - A_c) := by
      rw [spatialDatum_eq, map_sub, hAc, ContinuousLinearEquiv.apply_symm_apply]
    have hnorm : ‖spatialDatum s ψ - A‖ ≤ frequencyUnit ^ |s| * (3 * δ) := by
      rw [hHA]
      exact (cyclesToAngularRealVector_norm_le s _).trans
        (mul_le_mul_of_nonneg_left hsum hCpos.le)
    rw [← ofReal_norm]
    by_cases hηtop : η = ⊤
    · rw [hηtop]; exact ENNReal.ofReal_lt_top
    · rw [← ENNReal.ofReal_toReal hηtop]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)).mpr
        (lt_of_le_of_lt hnorm (hδ hηtop))

end NSFormalization.Section4.B01
