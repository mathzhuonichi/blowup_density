import NSFormalization.Section4.A01.EulerPairing
import NSFormalization.Section4.D01.FiniteOrderNorm
import NSFormalization.Section4.A04.Forcing
import NSFormalization.Section4.A01.ForceCap

/-!
# A01 unit A3 row **A3-L1·k** — the order-2 norm cap `Kbnd` (lane 147)

`research/A01/A3_SPLIT.md` row **A3-L1·k**, the last hypothesis of
`Section4/A01/GronwallInstance.lean`.  Lane 140 (`EulerPairing.lean`) supplies the *qualitative*
weak-derivative predicate `HasWeakDerivsL2 (⇑U) m` for the ordinary `L²` observation `U` of the
cylinder solution; lane 145 (`D01/FiniteOrderNorm.lean`) supplies the *quantitative* datum
constructor `‖A‖² ≤ 256·M` at order `2`.  This module glues the two and turns a mild sup-bound
`‖u‖ ≤ R` into the Grönwall integral cap `Kbnd := 256·R²·T₀`.

## What is proved here

1. **`hasWeakDerivsL2Bound_of_cylinder`** — the *quantitative twin* of
   `EulerPairing.hasWeakDerivsL2_of_cylinder`: for the order-`(q+1)` cylinder value `u`
   (angle-invariant) and its ordinary `L²` observation `U` (`ordinaryLift U = value 1 u`),
   `D01.HasWeakDerivsL2Bound (⇑U) (‖u‖²) m` — **constant 1**, `M := ‖u‖²`.  The bound is threaded
   through lane 140's `hasWeakDerivsL2_of_word` induction re-run here (each descended derivative
   word has `L²` norm `≤ ‖u‖`, the sup norm of the word-indexed Sobolev array, and `ordinaryLift`
   is an isometry).
2. **`sobolevENorm_two_toReal_le` / `sobolevNormAt_two_le_of_cylinder`** — the *order-2 norm
   comparison*: at `m = 2` (needs `q ≥ 4`; the consumer has `hq : 6 ≤ q`),
   `(sobolevENorm 2 (⇑U)).toReal ≤ 16·‖u‖`, via `D01.norm_isSobolevDatum_le_two` (`‖A‖² ≤ 256·M`),
   `A04.Forcing.sobolevENorm_eq` (`sobolevENorm s z = ‖A‖ₑ`) and `√`-bookkeeping.  Time-indexed as
   `∀ t, sobolevNormAt 2 v t ≤ 16·‖u t‖` for any space-time field `v` whose time-`t` slice is
   `⇑(U t)`.
3. **`sobolevNormAt_two_sq_le_of_sup` / `kbnd_of_sup_bound`** — the *cap*: from the `ContinuousMap`
   sup-bound `‖u‖ ≤ R` on `Icc 0 T`, the order-2 driver is bounded pointwise
   `sobolevNormAt 2 v t ^ 2 ≤ 256·R²` (unconditional), and — given the tree's continuity of the
   order-2 norm along the path — its running integral is capped by `Kbnd := 256·R²·T₀`, exactly
   `GronwallInstance.highOrder_bddAbove_of_kbnd`'s `hkbnd` shape.

## Slice / continuity conventions (what `exists_local_shape_of_aprioriBound` does *not* give)

`exists_local_shape_of_aprioriBound` (`Horizon.lean`) delivers `u : C(Icc 0 T, SobolevSpace 1 (q+1))`
and `U : C(Icc 0 T, EulerMeanSolenoidal.L2)` with `∀ t, ordinaryLift (U t) = value 1 (u t)` and
`‖u‖ ≤ R`; it produces **no** `SpaceTimeField` and **no** time-continuity of the Sobolev norm.  So
deliverables 2–3 carry two explicit hypotheses naming exactly the still-open carrier/energy bridge:
`hslice : ∀ t, (fun x => v (↑t, x)) =ᵐ[volume] ⇑(U t)` (the space-time field is the path's slices,
a.e. — an `Lp` representative is defined only up to a.e., the B1 hand-off shape) and, for
the integral cap, `hcont : ContinuousOn (fun s => sobolevNormAt 2 v s) (Ico 0 T)` — the *exact*
shape `A04.continuousOn_sobolevNormAt_velocity w 2` produces once `v = w.velocity` for a
`ClassicalSolutionR w` (the mild⟹energy bridge, `A3_SPLIT.md` §4 note).  The unconditional weaker
pointwise bound `sobolevNormAt_two_sq_le_of_sup` needs neither and is delivered in full.

No `sorry`, no `axiom`; `#print axioms` is standard (`research/A01/axioms_order_two_cap.lean`).
-/

noncomputable section

namespace NSFormalization.Section4.A01

open Set MeasureTheory
open NSFormalization.Section4.D01
open NSFormalization.Section4.A04 (sobolevNormAt sobolevENorm_eq)
open NSFormalization.Paper3 (RealVectorSobolev)
open NavierStokes.ProblemStatement (Space coordinateVector)
open NSFormalization.Section4.A02 (SpaceTimeField)
open scoped LineDeriv SchwartzMap ComplexConjugate

open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerCylinderSobolev EulerPressureSpatialRegularity
open NSFormalization.Source.OrdinaryCylinderDescent NSFormalization.Source.ForcedCylinderLocal

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-! ## 1. Quantitative Euler twin (deliverable 1) -/

/-- Each derivative word of a cylinder Sobolev array is bounded by the array norm (the
`SobolevSpace` norm is the sup norm on the finite word-indexed product). -/
theorem norm_word_le {q n : ℕ} (u : SobolevSpace 1 q) (hn : n ≤ q) (w : Fin n → Fin 4) :
    ‖word 1 u hn w‖ ≤ ‖u‖ :=
  norm_le_pi_norm (u : SobolevWord q → LiftL2 1) _

/-- The descended ordinary `L²` field of a derivative word has `L²`-square norm `≤ ‖u‖²`
(`ordinaryLift` is a linear isometry, so `‖Zw‖ = ‖word 1 u hn w‖ ≤ ‖u‖`). -/
theorem eLpNorm_descend_le {q n : ℕ} (u : SobolevSpace 1 q) (hn : n ≤ q) (w : Fin n → Fin 4)
    (Zw : EulerMeanSolenoidal.L2) (hZw : ordinaryLift Zw = word 1 u hn w) :
    (eLpNorm (⇑Zw) 2 volume).toReal ^ 2 ≤ ‖u‖ ^ 2 := by
  have h1 : (eLpNorm (⇑Zw) 2 volume).toReal = ‖Zw‖ := (Lp.norm_def Zw).symm
  have h2 : ‖Zw‖ = ‖word 1 u hn w‖ := by rw [← hZw, ordinaryLift.norm_map]
  rw [h1, h2]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_word_le u hn w) 2

/-- **Deliverable 1 (word level).**  The quantitative twin of `hasWeakDerivsL2_of_word`, threading
the uniform bound `M := ‖u‖²` (constant 1) through lane 140's descent induction. -/
theorem hasWeakDerivsL2Bound_of_word {q : ℕ} (u : SobolevSpace 1 q)
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 q (0, θ) u = u) :
    ∀ (m n : ℕ) (hn : n ≤ q) (_hnm : n + m + 3 ≤ q) (w : Fin n → Fin 4)
      (Zw : EulerMeanSolenoidal.L2), ordinaryLift Zw = word 1 u hn w →
      HasWeakDerivsL2Bound (⇑Zw) (‖u‖ ^ 2) m
  | 0, _n, hn, _hnm, w, Zw, hZw => ⟨Lp.memLp Zw, eLpNorm_descend_le u hn w Zw hZw⟩
  | (k + 1), n, hn, hnm, w, Zw, hZw => by
      refine ⟨⟨Lp.memLp Zw, eLpNorm_descend_le u hn w Zw hZw⟩, fun j => ?_⟩
      have hlt : n < q := by omega
      have hn1 : n + 1 ≤ q := hlt
      obtain ⟨Zc, hZc⟩ := exists_descend u hu (Fin.cons j.succ w) hn1 (by omega)
      refine ⟨⇑Zc, ?_, ?_⟩
      · exact hasWeakDerivsL2Bound_of_word u hu k (n + 1) hn1 (by omega) (Fin.cons j.succ w) Zc hZc
      · intro i ψ
        have hderiv := word_hasDerivAt 1 u hlt w j.succ
        have e1 : word 1 u hlt.le w = ordinaryLift Zw := hZw.symm
        have e2 : word 1 u (Nat.succ_le_of_lt hlt) (Fin.cons j.succ w) = ordinaryLift Zc := hZc.symm
        rw [e1, e2] at hderiv
        exact weakDeriv_pairing_of_lift_hasDerivAt j Zw Zc hderiv i ψ

/-- **Deliverable 1 (cylinder level).**  For the order-`(q+1)` cylinder value `u` and its ordinary
`L²` observation `U`, `HasWeakDerivsL2Bound (⇑U) (‖u‖²) m` for every `m ≤ q − 2` — constant 1. -/
theorem hasWeakDerivsL2Bound_of_cylinder {q : ℕ} (u : SobolevSpace 1 (q + 1))
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (U : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u)
    (m : ℕ) (hm : m + 3 ≤ q + 1) :
    HasWeakDerivsL2Bound (⇑U) (‖u‖ ^ 2) m := by
  refine hasWeakDerivsL2Bound_of_word u hu m 0 (Nat.zero_le _) (by omega) Fin.elim0 U ?_
  rw [hU]; rfl

/-! ## 2. Order-2 norm comparison (deliverable 2) -/

/-- **Deliverable 2 (single slice).**  The order-2 manuscript norm of `⇑U` is `≤ 16·‖u‖`.  From
`HasWeakDerivsL2Bound (⇑U) (‖u‖²) 2` (deliverable 1, needs `q ≥ 4`), `D01`'s constructor gives a
datum `A` with `‖A‖² ≤ 256·‖u‖²`, `A04.sobolevENorm_eq` identifies `sobolevENorm 2 (⇑U) = ‖A‖ₑ`,
and `√`-bookkeeping gives `‖A‖ ≤ 16·‖u‖`.  The bound is **not** the `⊤ ↦ 0` vacuous one: the proof
goes through a genuine datum `A`, so `sobolevENorm 2 (⇑U) ≠ ⊤` (recorded separately as
`sobolevENorm_two_ne_top`). -/
theorem sobolevENorm_two_toReal_le {q : ℕ} (u : SobolevSpace 1 (q + 1))
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (U : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u) (hq : 4 ≤ q) :
    (sobolevENorm ((2 : ℕ) : ℝ) (⇑U)).toReal ≤ 16 * ‖u‖ := by
  have hbound : HasWeakDerivsL2Bound (⇑U) (‖u‖ ^ 2) 2 :=
    hasWeakDerivsL2Bound_of_cylinder u hu U hU 2 (by omega)
  obtain ⟨A, hA, _⟩ := exists_isSobolevDatum_norm_le 2 (⇑U) (‖u‖ ^ 2) hbound
  have hbridge : sobolevENorm ((2 : ℕ) : ℝ) (⇑U) = ‖A‖ₑ := sobolevENorm_eq hA
  have hA256 : ‖A‖ ^ 2 ≤ 256 * ‖u‖ ^ 2 :=
    norm_isSobolevDatum_le_two (⇑U) (‖u‖ ^ 2) hbound A hA
  have hle : ‖A‖ ≤ 16 * ‖u‖ := by
    nlinarith [hA256, sq_nonneg (‖A‖ - 16 * ‖u‖), norm_nonneg A, norm_nonneg u]
  rw [hbridge]
  simpa [Real.enorm_eq_ofReal (norm_nonneg A), ENNReal.toReal_ofReal (norm_nonneg A)] using hle

/-- **Non-vacuity of the order-2 comparison (F2).**  Under the same hypotheses as
`sobolevENorm_two_toReal_le`, `sobolevENorm 2 (⇑U)` is **finite** (`≠ ⊤`), so the `.toReal` bound is
a genuine real inequality, not the `⊤ ↦ 0` vacuity the A3-L1·k row warned about.  Four lines from the
module's own ingredients: the datum `A` of deliverable 1 has finite enorm and equals `sobolevENorm`. -/
theorem sobolevENorm_two_ne_top {q : ℕ} (u : SobolevSpace 1 (q + 1))
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (U : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u) (hq : 4 ≤ q) :
    sobolevENorm ((2 : ℕ) : ℝ) (⇑U) ≠ ⊤ := by
  obtain ⟨A, hA, _⟩ := exists_isSobolevDatum_norm_le 2 (⇑U) (‖u‖ ^ 2)
    (hasWeakDerivsL2Bound_of_cylinder u hu U hU 2 (by omega))
  rw [sobolevENorm_eq hA]
  simp

/-- **Deliverable 2 (time-indexed).**  For a space-time field `v` whose time-`t` slice **agrees a.e.**
with `⇑(U t)` (`hslice`, the B1 hand-off `velocity t =ᵐ ⇑(U t)` — an `Lp` representative is defined
only up to a.e.), the order-2 norm at time `t` is `≤ 16·‖u t‖`.  This is the shape
`GronwallInstance`'s `sobolevNormAt 2 w.velocity ·` consumes.  The a.e. slice is transferred to the
datum by `IsSobolevDatum.congr_field` (same move as `EulerPairing.exists_isSobolevDatum_m_of_ae`);
the constant is unchanged. -/
theorem sobolevNormAt_two_le_of_cylinder {q : ℕ} {T : ℝ}
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t)) (hq : 4 ≤ q)
    (v : SpaceTimeField)
    (hslice : ∀ t : Icc (0 : ℝ) T, (fun x : Space => v (↑t, x)) =ᵐ[volume] ⇑(U t)) :
    ∀ t : Icc (0 : ℝ) T, sobolevNormAt (2 : ℝ) v ↑t ≤ 16 * ‖u t‖ := by
  intro t
  have hbound : HasWeakDerivsL2Bound (⇑(U t)) (‖u t‖ ^ 2) 2 :=
    hasWeakDerivsL2Bound_of_cylinder (u t) (fun θ => hu θ t) (U t) (hU t) 2 (by omega)
  obtain ⟨A, hA, _⟩ := exists_isSobolevDatum_norm_le 2 (⇑(U t)) (‖u t‖ ^ 2) hbound
  have hAz : IsSobolevDatum ((2 : ℕ) : ℝ) (fun x : Space => v (↑t, x)) A :=
    IsSobolevDatum.congr_field hA (hslice t).symm
  have hA256 : ‖A‖ ^ 2 ≤ 256 * ‖u t‖ ^ 2 :=
    norm_isSobolevDatum_le_two (⇑(U t)) (‖u t‖ ^ 2) hbound A hA
  have hle : ‖A‖ ≤ 16 * ‖u t‖ := by
    nlinarith [hA256, sq_nonneg (‖A‖ - 16 * ‖u t‖), norm_nonneg A, norm_nonneg (u t)]
  have hfin : (sobolevENorm ((2 : ℕ) : ℝ) (fun x : Space => v (↑t, x))).toReal ≤ 16 * ‖u t‖ := by
    rw [sobolevENorm_eq hAz]
    simpa [Real.enorm_eq_ofReal (norm_nonneg A), ENNReal.toReal_ofReal (norm_nonneg A)] using hle
  exact hfin

/-! ## 3. The cap (deliverable 3) -/

/-- **Deliverable 3 (unconditional pointwise bound).**  Under the `ContinuousMap` sup-bound
`‖u‖ ≤ R`, the order-2 driver is bounded pointwise by `256·R²` at every time in `Icc 0 T`.  Needs
no integrability. -/
theorem sobolevNormAt_two_sq_le_of_sup {q : ℕ} {T : ℝ}
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t)) (hq : 4 ≤ q)
    (v : SpaceTimeField)
    (hslice : ∀ t : Icc (0 : ℝ) T, (fun x : Space => v (↑t, x)) =ᵐ[volume] ⇑(U t))
    {R : ℝ} (hR : ‖u‖ ≤ R) :
    ∀ t : Icc (0 : ℝ) T, sobolevNormAt (2 : ℝ) v ↑t ^ 2 ≤ 256 * R ^ 2 := by
  intro t
  have h1 : sobolevNormAt (2 : ℝ) v ↑t ≤ 16 * ‖u t‖ :=
    sobolevNormAt_two_le_of_cylinder u U hu hU hq v hslice t
  have h2 : ‖u t‖ ≤ R := le_trans (ContinuousMap.norm_coe_le_norm u t) hR
  have h0 : 0 ≤ sobolevNormAt (2 : ℝ) v ↑t := sobolevNormAt_nonneg (2 : ℝ) v ↑t
  have h16 : sobolevNormAt (2 : ℝ) v ↑t ≤ 16 * R := le_trans h1 (by linarith)
  have hsq := pow_le_pow_left₀ h0 h16 2
  nlinarith [hsq]

/-- **Deliverable 3 (the cap).**  From the sup-bound `‖u‖ ≤ R` and continuity of the order-2 norm
along the path (`hcont`, the exact shape `A04.continuousOn_sobolevNormAt_velocity w 2` produces),
the running order-2 energy is capped by `Kbnd := 256·R²·T₀` on `Ico 0 T₀` — exactly
`GronwallInstance.highOrder_bddAbove_of_kbnd`'s `hkbnd` hypothesis. -/
theorem kbnd_of_sup_bound {q : ℕ} {T : ℝ}
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t)) (hq : 4 ≤ q)
    (v : SpaceTimeField)
    (hslice : ∀ t : Icc (0 : ℝ) T, (fun x : Space => v (↑t, x)) =ᵐ[volume] ⇑(U t))
    {R : ℝ} (hR : ‖u‖ ≤ R)
    (hcont : ContinuousOn (fun s => sobolevNormAt (2 : ℝ) v s) (Ico (0 : ℝ) T))
    {T₀ : ℝ} (_hT₀ : 0 < T₀) (hT₀T : T₀ ≤ T) :
    ∀ t ∈ Ico (0 : ℝ) T₀,
      (∫ s in (0 : ℝ)..t, sobolevNormAt (2 : ℝ) v s ^ 2) ≤ 256 * R ^ 2 * T₀ := by
  have hRnn : 0 ≤ R := le_trans (norm_nonneg u) hR
  have hpt := sobolevNormAt_two_sq_le_of_sup u U hu hU hq v hslice hR
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := ht.1
  have htT : t < T := lt_of_lt_of_le ht.2 hT₀T
  have hsub : uIcc (0 : ℝ) t ⊆ Ico (0 : ℝ) T := by
    rw [uIcc_of_le ht0]
    exact fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 htT⟩
  have hII : IntervalIntegrable (fun s => sobolevNormAt (2 : ℝ) v s ^ 2) volume 0 t :=
    ((hcont.pow 2).mono hsub).intervalIntegrable
  have hle_pt : ∀ s ∈ Icc (0 : ℝ) t, sobolevNormAt (2 : ℝ) v s ^ 2 ≤ 256 * R ^ 2 := by
    intro s hs
    have hsT : s ≤ T := le_trans hs.2 htT.le
    have := hpt ⟨s, hs.1, hsT⟩
    simpa using this
  calc (∫ s in (0 : ℝ)..t, sobolevNormAt (2 : ℝ) v s ^ 2)
      ≤ ∫ _s in (0 : ℝ)..t, (256 * R ^ 2) :=
        intervalIntegral.integral_mono_on ht0 hII intervalIntegrable_const hle_pt
    _ = t * (256 * R ^ 2) := by rw [intervalIntegral.integral_const]; ring
    _ ≤ T₀ * (256 * R ^ 2) := by
        apply mul_le_mul_of_nonneg_right ht.2.le; positivity
    _ = 256 * R ^ 2 * T₀ := by ring

end NSFormalization.Section4.A01
