import NSFormalization.Section3.T11.LocalExistence
import NSFormalization.Section3.T11.CriterionBridge

/-!
# Persistence: order transport and the common-horizon induction

`PeriodicSobolev` stores weighted coefficients. Equality of its underlying
sequences at different orders is NOT persistence of the physical field.
`IsPeriodicReweight` is the canonical relation expressing that persistence.
-/
noncomputable section
namespace NSFormalization.Section3.T11

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
open scoped ContDiff ENNReal NNReal BigOperators

local instance persistenceNormedGroup : NormedAddCommGroup (PeriodicSobolev 3) :=
  realPeriodicSubmodule.normedAddCommGroup
local instance persistenceNormedSpace : NormedSpace ℝ (PeriodicSobolev 3) :=
  realPeriodicSubmodule.normedSpace

/-- Positivity of the inhomogeneous weight, including the zero frequency. -/
theorem persistence_weight_pos (k : PeriodicFrequency) :
    0 < periodicFrequencyWeight k := by
  unfold periodicFrequencyWeight
  positivity

/-- Order transport is reflexive. -/
theorem persistence_reweight_refl (s : ℝ) (A : PeriodicSobolev s) :
    IsPeriodicReweight s s A A := by
  intro i k
  simp

/-- Order transport composes by adding the exponents, not by carrier equality. -/
theorem persistence_reweight_trans {s r q : ℝ}
    {A : PeriodicSobolev s} {B : PeriodicSobolev r} {D : PeriodicSobolev q}
    (hAB : IsPeriodicReweight s r A B) (hBD : IsPeriodicReweight r q B D) :
    IsPeriodicReweight s q A D := by
  intro i k
  rw [hBD i k, hAB i k, smul_smul, ← Real.rpow_add (persistence_weight_pos k)]
  congr 2
  ring

/-- The descending multiplier is bounded by one at every real order. -/
theorem persistence_down_weight_le {s r : ℝ} (h : r ≤ s) (k : PeriodicFrequency) :
    |periodicFrequencyWeight k ^ ((r - s) / 2)| ≤ 1 := by
  rw [abs_of_pos (Real.rpow_pos_of_pos (persistence_weight_pos k) _)]
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · unfold periodicFrequencyWeight
    have : 0 ≤ 4 * Real.pi ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2 := by positivity
    linarith
  · linarith

/-- Genuine bounded inclusion from a higher to a lower Sobolev order. -/
def persistenceDown (s r : ℝ) (h : r ≤ s) :
    PeriodicSobolev s →L[ℝ] PeriodicSobolev r :=
  torusMultiplierCLM s r (fun k ↦ periodicFrequencyWeight k ^ ((r-s)/2))
    1 zero_le_one (persistence_down_weight_le h)
    (fun k ↦ by rw [torus_weight_neg])

/-- The inclusion has the correct weight ratio. -/
theorem persistenceDown_reweight (s r : ℝ) (h : r ≤ s) (A : PeriodicSobolev s) :
    IsPeriodicReweight s r A (persistenceDown s r h A) := by
  intro i k
  rfl

/-- A continuous path is bounded on every compact subset of its time domain. -/
theorem persistence_compact_bound {s T : ℝ} {v : ℝ → PeriodicSobolev s}
    (hv : ContinuousOn v (Ico 0 T)) (K : Set ℝ) (hK : IsCompact K)
    (hKT : K ⊆ Ico 0 T) : ∃ B : ℝ, ∀ t ∈ K, ‖v t‖ ≤ B := by
  exact hK.exists_bound_of_continuousOn (hv.mono hKT)

/-- Diagnostic only: the literal weighted-coefficient equality in the lane brief
holds by index erasure. This theorem establishes NO gain of physical regularity. -/
theorem persistence_literal_target {ν T : ℝ} (C : TorusTwoSpaceContract ν)
    (A : PeriodicSobolev 3) (P u : ℝ → PeriodicSobolev 3)
    (hu : TorusForcedMildOn C A P T u) :
    ∀ m : ℕ, ∃ u_m : ℝ → PeriodicSobolev m,
      (∀ t ∈ Ico 0 T, ∀ i k, (u_m t).1 i k = (u t).1 i k) ∧
      ContinuousOn u_m (Ico 0 T) ∧
      (∀ K : Set ℝ, IsCompact K → K ⊆ Ico 0 T →
        ∃ B : ℝ, ∀ t ∈ K, ‖u_m t‖ ≤ B) := by
  intro m
  have hc := hu.continuous_path.mono Ico_subset_Icc_self
  exact ⟨u, fun _ _ _ _ ↦ rfl, hc, persistence_compact_bound hc⟩

/-- Data of one physical field at different orders obey the weight relation. -/
theorem persistence_reweight_of_data {s r : ℝ} {z : SpatialField}
    {A : PeriodicSobolev s} {B : PeriodicSobolev r}
    (hA : IsPeriodicDatum s z A) (hB : IsPeriodicDatum r z B) :
    IsPeriodicReweight s r A B := by
  intro i k
  rw [hB.2.2 i k, hA.2.2 i k, smul_smul,
    ← Real.rpow_add (persistence_weight_pos k)]
  congr 2
  ring

/-- Reweighting transports the actual physical datum predicate. -/
theorem persistence_datum_of_reweight {s r : ℝ} {z : SpatialField}
    {A : PeriodicSobolev s} {B : PeriodicSobolev r}
    (hA : IsPeriodicDatum s z A) (hAB : IsPeriodicReweight s r A B) :
    IsPeriodicDatum r z B := by
  refine ⟨hA.1, hA.2.1, ?_⟩
  intro i k
  rw [hAB i k, hA.2.2 i k, smul_smul,
    ← Real.rpow_add (persistence_weight_pos k)]
  congr 2
  ring

/-- Nonzero constant modes are genuine realizations at all orders. -/
theorem persistence_constant_reweight (s r b : ℝ) (c : Space) :
    IsPeriodicReweight s r (b • torusConstantDatum s c) (b • torusConstantDatum r c) :=
  persistence_reweight_of_data (torusConstantDatum_smul s b c) (torusConstantDatum_smul r b c)

/-- An explicit nonstationary, nonzero-force mild solution. This tests the
actual heat and convection symbols of any supplied two-space contract. -/
theorem persistence_constant_mild {ν T : ℝ} (C : TorusTwoSpaceContract ν)
    (hT : 0 ≤ T) (c : Space) :
    TorusForcedMildOn C (torusConstantDatum 3 c) (fun _ ↦ torusConstantDatum 3 c) T
      (fun t ↦ (1 + t) • torusConstantDatum 3 c) := by
  let A := torusConstantDatum 3 c
  change TorusForcedMildOn C A (fun _ ↦ A) T (fun t ↦ (1+t) • A)
  have hheat (t : ℝ≥0) : C.analytic.linearEvolution t A = A := by
    apply Subtype.ext
    ext i k
    rw [C.linear_symbol]
    by_cases hk : k = 0
    · subst k
      simp [torusHeatSymbol, NSFormalization.Paper1.PeriodicHeatMultiplier.heatSymbol,
        NSFormalization.Paper1.PeriodicHeatMultiplier.laplaceEigenvalue,
        ← torus_weight_eq, periodicFrequencyWeight]
    · simp [A, torusConstantDatum, lp.single_apply, hk]
  have hQ : C.analytic.bilinear A A = 0 := by
    apply Subtype.ext
    ext i k
    rw [C.bilinear_symbol, torusProjectedConvectionSymbol_constants]
    rfl
  have hQpath (s : ℝ) : C.analytic.bilinear ((1+s) • A) ((1+s) • A) = 0 := by
    simp [map_smul, hQ]
  have hD (t s : ℝ) :
      C.analytic.duhamelIntegrand t (fun t ↦ (1+t) • A) s = 0 := by
    simp only [MNS2.EndpointSafeTwoSpaceDuhamelContract.duhamelIntegrand,
      MNS2.endpointSafeTwoSpaceDuhamelIntegrand, hQpath, map_zero]
  refine ⟨hT, ((continuous_const.add continuous_id).smul continuous_const).continuousOn,
    by simp, ?_, ?_, ?_⟩
  · intro t ht
    simpa only [hheat] using (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ A) volume 0 t)
  · intro t ht
    change IntervalIntegrable (fun s ↦ C.analytic.duhamelIntegrand t
      (fun t ↦ (1+t) • A) s) volume 0 t
    simp only [hD]
    exact intervalIntegrable_const
  · intro t ht
    change (1+t) • A = C.analytic.linearEvolution ⟨t, ht.1⟩ A +
      (∫ s in (0 : ℝ)..t, C.analytic.linearEvolution (Real.toNNReal (t-s)) A) -
      ∫ s in (0 : ℝ)..t, C.analytic.duhamelIntegrand t (fun t ↦ (1+t) • A) s
    simp only [hheat, hD, intervalIntegral.integral_const,
      sub_zero, intervalIntegral.integral_zero]
    simp only [add_smul, one_smul, add_left_inj]
    exact (hheat ⟨t, ht.1⟩).symm

/-- The ONE unresolved analytic input: a half-order gain for an already
continuous order-r realization of a forced mild solution. The interval includes
zero and retains the original T. This is a one-step regularity lemma, not an
all-order existence assertion. Its intended proof uses H^r × H^r → H^(r-1)
and the integrable gain-3/2 heat kernel (t-s)^(-3/4).

This input includes the endpoint Duhamel argument; a fractional multiplier
estimate alone does not discharge it. U9d1's analytic follow-up must prove it. -/
def TorusHalfStepInput : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (C : TorusTwoSpaceContract ν)
    (a : SpatialField) (g : SpaceTimeField) (T : ℝ),
    a ∈ initialClassT → ContDiff ℝ ∞ g → IsPeriodicOn univ g → 0 < T →
    ∀ (A : PeriodicSobolev 3) (F P u : ℝ → PeriodicSobolev 3),
      IsPeriodicDatum 3 a A → IsPeriodicSobolevPath 3 g F →
      (∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t)) →
      TorusForcedMildOn C A P T u →
      ∀ r : ℝ, 3 ≤ r → ∀ v : ℝ → PeriodicSobolev r,
        ContinuousOn v (Ico 0 T) →
        (∀ t ∈ Ico 0 T, IsPeriodicReweight 3 r (u t) (v t)) →
        ∃ w : ℝ → PeriodicSobolev (r + 1 / 2),
          ContinuousOn w (Ico 0 T) ∧
          ∀ t ∈ Ico 0 T, IsPeriodicReweight r (r + 1 / 2) (v t) (w t)

/-- Iteration of the single analytic input, with no shrinkage of the horizon. -/
theorem persistence_halfOrder_ladder (H : TorusHalfStepInput)
    (ν : ℝ) (hν : 0 < ν) (C : TorusTwoSpaceContract ν)
    (a : SpatialField) (g : SpaceTimeField) (T : ℝ)
    (ha : a ∈ initialClassT) (hg : ContDiff ℝ ∞ g) (hp : IsPeriodicOn univ g)
    (hT : 0 < T) (A : PeriodicSobolev 3) (F P u : ℝ → PeriodicSobolev 3)
    (hA : IsPeriodicDatum 3 a A) (hF : IsPeriodicSobolevPath 3 g F)
    (hP : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    (hu : TorusForcedMildOn C A P T u) :
    ∀ n : ℕ, ∃ v : ℝ → PeriodicSobolev (3 + (n : ℝ) / 2),
      ContinuousOn v (Ico 0 T) ∧
      ∀ t ∈ Ico 0 T, IsPeriodicReweight 3 (3 + (n : ℝ) / 2) (u t) (v t) := by
  intro n
  induction n with
  | zero =>
    refine ⟨u, hu.continuous_path.mono Ico_subset_Icc_self, ?_⟩
    intro t ht
    convert persistence_reweight_refl 3 (u t) using 1
    norm_num
  | succ n ih =>
    obtain ⟨v, hv, he⟩ := ih
    obtain ⟨w, hw, hew⟩ := H ν hν C a g T ha hg hp hT A F P u hA hF hP hu
      (3 + (n : ℝ) / 2) (by have := Nat.cast_nonneg (α := ℝ) n; linarith) v hv he
    refine ⟨w, hw, ?_⟩
    intro t ht
    have hh := persistence_reweight_trans (he t ht) (hew t ht)
    convert hh using 1
    push_cast
    ring

/-- Physical-coefficient persistence, conditional on exactly one half-step
input. This uses the canonical reweight relation rather than identifying
weighted sequences. It does not assert time smoothness or pressure recovery. -/
theorem torusForcedMildOn_persistence (H : TorusHalfStepInput)
    (ν : ℝ) (hν : 0 < ν) (C : TorusTwoSpaceContract ν)
    (a : SpatialField) (g : SpaceTimeField) (T : ℝ)
    (ha : a ∈ initialClassT) (hg : ContDiff ℝ ∞ g) (hp : IsPeriodicOn univ g)
    (hT : 0 < T) (A : PeriodicSobolev 3) (F P u : ℝ → PeriodicSobolev 3)
    (hA : IsPeriodicDatum 3 a A) (hF : IsPeriodicSobolevPath 3 g F)
    (hP : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    (hu : TorusForcedMildOn C A P T u) :
    ∀ m : ℕ, ∃ u_m : ℝ → PeriodicSobolev m,
      (∀ t ∈ Ico 0 T, IsPeriodicReweight 3 (m : ℝ) (u t) (u_m t)) ∧
      ContinuousOn u_m (Ico 0 T) ∧
      (∀ K : Set ℝ, IsCompact K → K ⊆ Ico 0 T →
        ∃ B : ℝ, ∀ t ∈ K, ‖u_m t‖ ≤ B) := by
  intro m
  obtain ⟨v, hv, he⟩ := persistence_halfOrder_ladder H ν hν C a g T ha hg hp hT
    A F P u hA hF hP hu (2 * m)
  have hle : (m : ℝ) ≤ 3 + ((2 * m : ℕ) : ℝ) / 2 := by push_cast; linarith
  let D := persistenceDown (3 + ((2 * m : ℕ) : ℝ) / 2) m hle
  have hc : ContinuousOn (fun t ↦ D (v t)) (Ico 0 T) :=
    D.continuous.comp_continuousOn hv
  refine ⟨fun t ↦ D (v t), ?_, hc, persistence_compact_bound hc⟩
  intro t ht
  exact persistence_reweight_trans (he t ht) (persistenceDown_reweight _ _ hle (v t))

end NSFormalization.Section3.T11
