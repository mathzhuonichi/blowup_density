import NSFormalization.Section4.A01.CarrierWords

/-!
# A01 unit A3 row (i), piece (d) — the `L²`-level descent of an angle-invariant lift (lane 153)

Lane 151 (`CarrierWords.lean`) discharges lane 149's `hword_jet` bound for every order the *jet-level*
descent reaches, `n + 3 ≤ q + 1` (i.e. `n ≤ q − 2`), because `exists_descend` loses three orders: the
jet-level descent `exists_ordinary_value` takes the `θ = 0` slice of a continuous `H³` representative,
and a raw `LiftL2 1` element has no pointwise slice.  The **top three orders** `n ∈ {q−1, q, q+1}` need
piece **(d)**: an `L²`-level descent with **no** jet loss.

## What is proved

* **`exists_ordinaryLift_of_invariant`** — piece (d), exactly `DescentL2` of the probe
  `research/A01/probes/probe151_descent_L2.lean`:
  ```
  ∀ g : LiftL2 1, (∀ θ, translation 1 (0, θ) g = g) → ∃ G : EulerMeanSolenoidal.L2, ordinaryLift G = g
  ```
  Every angle-invariant `L²` cylinder field is the `ordinaryLift` of a `θ`-independent ordinary `L²`
  field, with no jet / regularity hypothesis.

## The route (averaging / Fubini, no Fourier)

`EulerMeanSolenoidal.L2 = Lp Space 2 volume` carries no solenoidal / mean constraint at this level, so
(d) is a pure disintegration.  `LiftL2 1 = Lp Vector3 2 (liftMeasure 1)` with
`liftMeasure 1 = (volume : Measure Vector3).prod (volume : Measure (AddCircle 1))` a genuine product
measure.  Take the strongly-measurable representative `g₀` of `g` and let `G₀ x := ∫ θ, g₀ (x, θ) ∂volume`
be the `θ`-average (`AddCircle 1` has total mass one).  The a.e. invariance of `g` under every angular
translation transports to `g₀` (`translation_ae`, `measurePreserving_translation`); the swap
`∀ θ, ∀ᵐ x` → `∀ᵐ x, ∀ᵐ θ` is `Measure.ae_ae_comm` (measurability of the graph set by
`measurableSet_eq_fun`, `g₀` strongly measurable).  For a.e. `pt = (x, ω)` the constant, the
`ae`-invariant integrand, and the Haar translation invariance `integral_add_left_eq_self` give
`g₀ pt = G₀ pt.1`.  Hence `⇑g =ᵐ G₀ ∘ Prod.fst`; `G₀ ∈ L²(volume)` by `memLp_map_measure_iff` through
`ordinaryProjection_measurePreserving` (`map Prod.fst (liftMeasure 1) = volume`), and
`ordinaryLift (toLp G₀) = g` by `ordinaryLift_ae` + `Lp.ext`.  This folds the "an `AddCircle`-invariant
`L²` function is a.e. constant" fact into the product argument, so no standalone circle lemma is needed.

`#print axioms` is the standard three for every declaration (`research/A01/axioms_l2_descent.lean`).
-/

noncomputable section

namespace NSFormalization.Section4.A01

open Set MeasureTheory
open NSFormalization.Section4.D01
open NavierStokes.ProblemStatement (Space coordinateVector)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerCylinderSobolev EulerPressureSpatialRegularity
open EulerLpTranslation
open NSFormalization.Source.OrdinaryCylinderDescent
open scoped ENNReal ContDiff LineDeriv

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

local instance instIsProbAddCircleOne :
    IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
  constructor
  simp [AddCircle.measure_univ]

/-- **Piece (d).**  Every angle-invariant `L²` cylinder field is the `ordinaryLift` of a
`θ`-independent ordinary `L²` field on `ℝ³`, with no jet / regularity hypothesis. -/
theorem exists_ordinaryLift_of_invariant (g : LiftL2 1)
    (hginv : ∀ θ : AddCircle (1 : ℝ), translation 1 ((0 : Vector3), θ) g = g) :
    ∃ G : EulerMeanSolenoidal.L2, ordinaryLift G = g := by
  -- A strongly-measurable representative of `g`.
  obtain ⟨g₀, hg₀sm, hg₀ae⟩ :
      ∃ g₀ : LiftDomain 1 → Space, StronglyMeasurable g₀ ∧ (⇑g) =ᵐ[liftMeasure 1] g₀ :=
    ⟨(Lp.aestronglyMeasurable g).mk (⇑g),
      (Lp.aestronglyMeasurable g).stronglyMeasurable_mk,
      (Lp.aestronglyMeasurable g).ae_eq_mk⟩
  -- a.e. angular invariance of the representative
  have hinv0 : ∀ θ : AddCircle (1 : ℝ),
      ∀ᵐ x ∂(liftMeasure 1), g₀ x = g₀ (x + ((0 : Vector3), θ)) := by
    intro θ
    have h1 : (⇑g) =ᵐ[liftMeasure 1] fun x => (⇑g) (x + ((0 : Vector3), θ)) := by
      have h := translation_ae 1 ((0 : Vector3), θ) g
      rw [hginv θ] at h
      exact h
    have h2 : (fun x => (⇑g) (x + ((0 : Vector3), θ)))
        =ᵐ[liftMeasure 1] fun x => g₀ (x + ((0 : Vector3), θ)) :=
      (measurePreserving_translation 1 ((0 : Vector3), θ)).quasiMeasurePreserving.ae hg₀ae
    filter_upwards [hg₀ae, h1, h2] with x hx hx1 hx2
    rw [← hx, hx1, hx2]
  -- swap the a.e. quantifiers via Fubini for null sets
  have hmeas : MeasurableSet {z : AddCircle (1 : ℝ) × LiftDomain 1 |
      g₀ z.2 = g₀ (z.2 + ((0 : Vector3), z.1))} := by
    have hm : Measurable (fun z : AddCircle (1 : ℝ) × LiftDomain 1 =>
        z.2 + ((0 : Vector3), z.1)) :=
      measurable_snd.add (measurable_const.prodMk measurable_fst)
    exact measurableSet_eq_fun (hg₀sm.measurable.comp measurable_snd) (hg₀sm.measurable.comp hm)
  have hswap : ∀ᵐ pt ∂(liftMeasure 1), ∀ᵐ θ ∂(volume : Measure (AddCircle (1 : ℝ))),
      g₀ pt = g₀ (pt + ((0 : Vector3), θ)) :=
    (Measure.ae_ae_comm hmeas).mp (ae_of_all _ hinv0)
  -- the `θ`-average
  set G₀ : Space → Space := fun x => ∫ θ, g₀ (x, θ) ∂(volume : Measure (AddCircle (1 : ℝ)))
    with hG₀def
  -- slice constancy: `g₀ pt = G₀ pt.1` a.e.
  have hgG0 : ∀ᵐ pt ∂(liftMeasure 1), g₀ pt = G₀ pt.1 := by
    filter_upwards [hswap] with pt hpt
    calc g₀ pt
        = ∫ _θ : AddCircle (1 : ℝ), g₀ pt ∂volume := by rw [integral_const]; simp
      _ = ∫ θ, g₀ (pt + ((0 : Vector3), θ)) ∂volume := integral_congr_ae hpt
      _ = ∫ θ, g₀ (pt.1, pt.2 + θ) ∂volume := by
            refine integral_congr_ae (ae_of_all _ (fun θ => ?_))
            show g₀ (pt + ((0 : Vector3), θ)) = g₀ (pt.1, pt.2 + θ)
            rw [show pt + ((0 : Vector3), θ) = (pt.1, pt.2 + θ) from by simp [Prod.add_def]]
      _ = ∫ θ, g₀ (pt.1, θ) ∂volume :=
            integral_add_left_eq_self (fun θ => g₀ (pt.1, θ)) pt.2
      _ = G₀ pt.1 := by simp only [hG₀def]
  have hgfst : (⇑g) =ᵐ[liftMeasure 1] fun pt => G₀ pt.1 := hg₀ae.trans hgG0
  -- `G₀ ∈ L²(volume)`
  have hG₀aesm : AEStronglyMeasurable G₀ volume := by
    rw [hG₀def]
    exact hg₀sm.aestronglyMeasurable.integral_prod_right'
  have hmap : Measure.map (Prod.fst : LiftDomain 1 → Space) (liftMeasure 1) = volume :=
    ordinaryProjection_measurePreserving.map_eq
  have hMemLp : MemLp G₀ 2 volume := by
    have hiff := memLp_map_measure_iff (p := 2) (μ := liftMeasure 1)
      (f := (Prod.fst : LiftDomain 1 → Space)) (g := G₀)
      (by rw [hmap]; exact hG₀aesm) measurable_fst.aemeasurable
    rw [hmap] at hiff
    rw [hiff]
    exact (Lp.memLp g).ae_eq hgfst
  -- assemble
  refine ⟨hMemLp.toLp G₀, ?_⟩
  apply Lp.ext
  have h1 := ordinaryLift_ae (hMemLp.toLp G₀)
  have h2 : (fun x : LiftDomain 1 => (⇑(hMemLp.toLp G₀)) x.1)
      =ᵐ[liftMeasure 1] fun x => G₀ x.1 :=
    ordinaryProjection_measurePreserving.quasiMeasurePreserving.ae (MemLp.coeFn_toLp hMemLp)
  filter_upwards [h1, h2, hgfst] with x hx1 hx2 hx3
  rw [hx1, hx2, hx3]

/-! ## Consequence for the words — the top three orders, with no `n + 3 ≤ q + 1` restriction -/

/-- **Item 2 (a).**  Using the `L²`-level descent in place of `exists_descend`, every spatial
derivative word of an angle-invariant cylinder Sobolev field descends to an ordinary `L²` field, for
**every** order `n ≤ q + 1` (no jet loss).  The word is itself angle-invariant, exactly as in
`exists_descend`'s `hinv`, by `congrArg` against `hu` (`sobolevTranslation` acts by `translation` on
each derivative coordinate, `liftOperator_apply`). -/
theorem word_descent_ae_top {q : ℕ} (u : SobolevSpace 1 (q + 1))
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (n : ℕ) (hn : n ≤ q + 1) (w : Fin n → Fin 3) :
    ∃ Zw : EulerMeanSolenoidal.L2, ordinaryLift Zw = word 1 u hn (fun i => (w i).succ) := by
  refine exists_ordinaryLift_of_invariant _ (fun θ => ?_)
  exact congrArg
    (fun v : SobolevSpace 1 (q + 1) =>
      v.val ⟨⟨n, Nat.lt_succ_of_le hn⟩, fun i => (w i).succ⟩) (hu θ)

/-- **Item 2, the descent identity extended to all orders.**  The descent-to-classical-jet a.e.
identity of `CarrierWords.word_descent_ae`, now with **no** `n + 3 ≤ q + 1` restriction: the only use
of the order bound there was to feed `exists_descend` the tail word, which `word_descent_ae_top` now
supplies for every order.  `descent_step_ae` and `word_hasDerivAt` carry no order bound (`word_hasDerivAt`
needs only `n < q + 1`), so the induction closes verbatim. -/
theorem word_descent_ae_full {q : ℕ} (u : SobolevSpace 1 (q + 1))
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (U : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u)
    (Z : SmoothL2Field Space) (hUz : (⇑U) =ᵐ[volume] Z.field) :
    ∀ (n : ℕ) (hn : n ≤ q + 1) (w : Fin n → Fin 3) (Zw : EulerMeanSolenoidal.L2),
      ordinaryLift Zw = word 1 u hn (fun i => (w i).succ) →
      (⇑Zw) =ᵐ[volume] (wordField Z w).field := by
  intro n
  induction n with
  | zero =>
    intro hn w Zw hZw
    have hwemp : (fun i => ((w : Fin 0 → Fin 3) i).succ) = (Fin.elim0 : Fin 0 → Fin 4) :=
      Subsingleton.elim _ _
    have hval : word 1 u hn (fun i => (w i).succ) = value 1 u := by
      rw [hwemp]; rfl
    have hZU : Zw = U := ordinaryLift.injective (by rw [hZw, hval, hU])
    subst hZU
    exact hUz
  | succ n ih =>
    intro hn w Zw hZw
    have hlt : n < q + 1 := by omega
    have hn' : n ≤ q + 1 := by omega
    obtain ⟨Zw', hZw'⟩ := word_descent_ae_top u hu n hn' (Fin.tail w)
    have hIH := ih hn' (Fin.tail w) Zw' hZw'
    have hcons : Fin.cons ((w 0).succ) (fun i => ((Fin.tail w) i).succ)
        = fun i => (w i).succ := by
      funext i
      refine Fin.cases ?_ ?_ i
      · simp
      · intro k; simp [Fin.tail]
    have hderiv := word_hasDerivAt 1 u hlt (fun i => ((Fin.tail w) i).succ) ((w 0).succ)
    rw [hcons] at hderiv
    rw [← hZw', ← hZw] at hderiv
    exact descent_step_ae (wordField Z (Fin.tail w)) (w 0) Zw' Zw hIH hderiv

/-- **Item 2 (b) — `hword_jet` for ALL orders, unconditional.**  The full `hword_jet` bound holds for
every word `w : Fin n → Fin 4` with `n ≤ q + 1`, removing the `n + 3 ≤ q + 1` restriction of
`CarrierWords.hword_jet_of_descent`.  Same case split: angular words vanish
(`word_eq_zero_of_mem_zero`); spatial words `w i = (w' i).succ` descend via `word_descent_ae_top`,
`word_descent_ae_full` identifies `⇑Zw` with the jet component of `Z.field`, and the norm chain
(`ordinaryLift.norm_map` / `Lp.norm_def` / `eLpNorm_congr_ae` / `eLpNorm_jet_component_le`) closes it,
with `Z.integrable` giving finiteness for the `.toReal` monotonicity.  This discharges lane 149's
`hword_jet` for **all** `n ≤ q + 1`. -/
theorem hword_jet_full {q : ℕ} (u : SobolevSpace 1 (q + 1))
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (U : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u)
    (Z : SmoothL2Field Space) (hUz : (⇑U) =ᵐ[volume] Z.field) :
    ∀ (n : ℕ) (hn : n ≤ q + 1) (w : Fin n → Fin 4),
      ‖word 1 u hn w‖ ≤ (eLpNorm (iteratedFDeriv ℝ n Z.field) 2 volume).toReal := by
  intro n hn w
  by_cases hex : ∃ k, w k = 0
  · rw [word_eq_zero_of_mem_zero u hu n hn w hex, norm_zero]
    exact ENNReal.toReal_nonneg
  · have hne : ∀ i, w i ≠ 0 := fun i hi => hex ⟨i, hi⟩
    set w' : Fin n → Fin 3 := fun i => (w i).pred (hne i) with hw'def
    have hw_eq : w = fun i => (w' i).succ := by
      funext i; simp only [hw'def, Fin.succ_pred]
    obtain ⟨Zw, hZw⟩ := word_descent_ae_top u hu n hn w'
    have hae : (⇑Zw) =ᵐ[volume]
        fun x => iteratedFDeriv ℝ n Z.field x (fun i => coordinateVector (w' i)) := by
      have h := word_descent_ae_full u hu U hU Z hUz n hn w' Zw hZw
      refine h.trans (Filter.EventuallyEq.of_eq ?_)
      funext x
      exact wordField_field Z n w' x
    have hjet_fin : eLpNorm (iteratedFDeriv ℝ n Z.field) 2 volume ≠ ⊤ := (Z.integrable n).2.ne
    calc ‖word 1 u hn w‖
        = ‖word 1 u hn (fun i => (w' i).succ)‖ := by rw [hw_eq]
      _ = ‖ordinaryLift Zw‖ := by rw [hZw]
      _ = ‖Zw‖ := ordinaryLift.norm_map Zw
      _ = (eLpNorm (⇑Zw) 2 volume).toReal := Lp.norm_def Zw
      _ = (eLpNorm (fun x => iteratedFDeriv ℝ n Z.field x (fun i => coordinateVector (w' i)))
            2 volume).toReal := by rw [eLpNorm_congr_ae hae]
      _ ≤ (eLpNorm (iteratedFDeriv ℝ n Z.field) 2 volume).toReal :=
            ENNReal.toReal_mono hjet_fin (eLpNorm_jet_component_le n Z.field w')

end NSFormalization.Section4.A01
