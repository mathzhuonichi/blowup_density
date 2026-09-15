import NSFormalization.Section4.A01.OrderTwoCap
import NSFormalization.Section4.A01.GronwallInstance
import NSFormalization.Section4.D01.DatumToJets

/-!
# A01 unit A3 — residual a-priori rows (iii) endpoint widening and (ii) converse (lane 149)

`research/A01/REVIEW_ORDER_TWO_CAP.md` §"Residual-row audit" lists the rows between an assumed
sup-bound `‖u‖ ≤ R` and `HasAprioriBound` (`Horizon.lean:106`).  Lane 147 (`OrderTwoCap.lean`)
closed the *arithmetic* of row A3-L1·k (`kbnd_of_sup_bound`, `Kbnd := 256·R²·T₀`) and the *forward*
order-2 comparison `sobolevNormAt 2 (⇑(U t)) ≤ 16·‖u t‖`.  This module closes two of the residual
rows, up to one isolated named gap:

## Deliverable (iii) — the `Ico → Icc` endpoint widening for `T₀ < T`

* **`kbnd_of_sup_bound_Icc`** — the exact `kbnd_of_sup_bound` cap on the *closed* window
  `Icc 0 T₀`, under `T₀ < T` (in place of lane 147's `0 < T₀`, `T₀ ≤ T` on `Ico 0 T₀`).  Same
  explicit constant `256·R²·T₀`.  Pure interval bookkeeping: for `t ≤ T₀ < T` the endpoint `T₀`
  lies in `Ico 0 T`, so `sobolevNormAt_two_sq_le_of_sup` (lane 147, unconditional) and the
  continuity input remain available *at* `T₀`; the running-integral bound then closes on `Icc 0 T₀`
  by the same `intervalIntegral.integral_mono_on` argument.
* **`highOrder_bddAbove_of_kbnd_Icc` / `highOrder_bddAbove_all_orders_of_kbnd_Icc`** — the matching
  widening of `GronwallInstance.highOrder_bddAbove_of_kbnd`'s conclusion to `Icc 0 T₀`, keeping the
  **same** explicit bound `(‖u(0)‖_{H^m} + ‖f‖_{L¹_tH^m})·exp(Cgron m ν·Kbnd)`.  The input `hkbnd`
  is asked on an *intermediate* horizon `Ico 0 T₁`, `T₀ < T₁ ≤ T` (review note N1): this lets a
  caller keep `Kbnd = 256·R²·T₁` from `kbnd_of_sup_bound` at horizon `T₁`, so the exponential
  constant does not degrade to `256·R²·T`; `T₁ := T` is the full-horizon special case.  The
  conclusion is `highOrder_bddAbove_of_kbnd` at horizon `T₁` restricted along `Icc 0 T₀ ⊆ Ico 0 T₁`.
* **`kbnd_of_sup_bound_Icc_endpoint`** — the cap at the closed endpoint `T₀ = T`
  (`∀ t ∈ Icc 0 T, ∫₀ᵗ … ≤ 256·R²·T`), same constant, via a.e.-continuity on `Ioo 0 t` +
  `Integrable.mono'` for endpoint integrability.

**On the `T₀ = T` endpoint of row (iii) (review note N3).**  It splits three ways: (a) the *cap* at
`T₀ = T` is now provided (`kbnd_of_sup_bound_Icc_endpoint`, S); (b) the **Grönwall output** at
`t = T` is the genuine hard eq:criterion endpoint (L) — `highContinuationIntegral` needs `t < T`,
and the closed boundary needs the energy identity at `T`, not interval bookkeeping; (c) the
endpoint the a-priori sup-bound *actually* needs (`‖u‖ ≤ R` on the closed `Icc 0 T`) is **free at
the cylinder level** — `u` is a `ContinuousMap`, so a bound on `{t : ↑t < T}` extends to the
endpoint by continuity (reviewer probe `rev149_cylinder_endpoint.lean`), and is not an energy-side
obligation at all.

## Deliverable (ii) — the converse norm comparison, up to one named gap

The a-priori bound is on the cylinder-array sup-norm `‖u‖_{SobolevSpace 1 (q+1)}`; the Grönwall
output lives on the energy norm `sobolevNormAt`.  The converse turns an energy bound back into a
cylinder-array bound.

* **`sobolevSpace_norm_le_of_forall_word`** (backbone, proved) — the `SobolevSpace 1 q` norm is the
  sup over derivative words: `(∀ n hn w, ‖word 1 u hn w‖ ≤ C) → ‖u‖ ≤ C` (`0 ≤ C`), by
  `pi_norm_le_iff_of_nonneg` on the word-indexed product carrier.
* **`eLpNorm_iteratedFDeriv_le_sobolevENorm_toReal`** (the reverse embedding, proved) — for a
  smooth field `z ∈ H^{q+1}` (`sobolevENorm (q+1) z ≠ ⊤`) and `n ≤ q+1`, the order-`n` Fréchet-jet
  `L²` norm is bounded by the order-`(q+1)` energy norm with the explicit, `n`-uniform constant
  `jetSobolevConst (q+1)` (`DatumToJets.lean`, one `(2π)^{q+1}` factor).  This is the direction the
  brief flags as "the reverse `eLpNorm(∂^α) ≤ ‖A_k‖` bound"; it exists in the tree **for smooth
  fields via `iteratedFDeriv`**.
* **`sobolevSpace_norm_le_sobolevENorm` / `sobolevSpace_norm_le_sobolevNormAt`** — the converse:
  `‖u‖ ≤ jetSobolevConst (q+1) · (sobolevENorm (q+1) z).toReal` (constant `jetSobolevConst (q+1)`,
  `t`-free), for a smooth `H^{q+1}` field `z` — downstream, the classical velocity slice
  `fun x => v(t,x)`, whose smoothness (`contDiff_slice`) and datum (`ClassicalSolutionR.sobolev`)
  make `hz`/`hfin` free.
* **`sobolevENorm_congr_ae` / `sobolevSpace_norm_le_sobolevENorm_ordinary`** (review note N5) — the
  energy norm is an a.e. invariant, so the converse may be *stated* on the ordinary `L²`
  observation `⇑U` verbatim as the audit's row (ii) asks (`‖u‖ ≤ jetSobolevConst (q+1) ·
  (sobolevENorm (q+1) (⇑U)).toReal`); the *proof* still routes through a smooth slice `z =ᵐ ⇑U`.

### The isolated gap `hword_jet`

The converse carries **one** hypothesis:
`hword_jet : ∀ n (hn : n ≤ q+1) w, ‖word 1 u hn w‖ ≤ (eLpNorm (iteratedFDeriv ℝ n z) 2 volume).toReal`,
i.e. each cylinder derivative word's `L²` norm is bounded by the smooth slice's order-`n` Fréchet
jet `L²` norm.  This is the **carrier bridge** (row (i) / B1-B2): the descent
`EulerPairing.exists_descend` produces the words at the *lift* level (`word_hasDerivAt`,
translation-orbit derivatives), and the identification of that descent with the ordinary-space
classical spatial derivative of the physical velocity slice is not in the tree.  `SmoothDatum.lean`
records the datum-to-datum order shift (unit U1b(ii)) as untouched; the descent-to-classical-jet
identity is the same missing analytic content, phrased directly on the word so that the top-order
words (which `exists_descend`'s `n + 3 ≤ q + 1` requirement cannot reach — the 3-order jet loss)
are covered by the hypothesis rather than by a descent.  Everything except `hword_jet` is proved.

`#print axioms` is standard for every declaration (`research/A01/axioms_apriori_rows.lean`).
-/

noncomputable section

namespace NSFormalization.Section4.A01

open Set MeasureTheory
open NSFormalization.Section4.D01
open NSFormalization.Section4.A04 (sobolevNormAt sobolevENorm_eq MemL1Hm HasSmoothSobolevPath)
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR initialClassR)
open NSFormalization.Paper3 (RealVectorSobolev)
open NavierStokes.ProblemStatement (Space coordinateVector)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerCylinderSobolev EulerPressureSpatialRegularity
open NSFormalization.Source.OrdinaryCylinderDescent NSFormalization.Source.ForcedCylinderLocal
open scoped ENNReal ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-! ## 1. Deliverable (iii): the `Ico → Icc` endpoint widening (`T₀ < T`) -/

/-- **(iii) cap on the closed window.**  Under the hypotheses of `kbnd_of_sup_bound` with `T₀ < T`
in place of `0 < T₀ ≤ T`, the order-2 running-energy cap holds on the *closed* window `Icc 0 T₀`,
with the same explicit constant `256·R²·T₀`.  For `t ≤ T₀ < T` the endpoint stays inside `Ico 0 T`,
so the pointwise bound `sobolevNormAt_two_sq_le_of_sup` and the continuity input `hcont` are
available at every `t ∈ Icc 0 T₀`, and the interval-integral comparison closes as on `Ico 0 T₀`. -/
theorem kbnd_of_sup_bound_Icc {q : ℕ} {T : ℝ}
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t)) (hq : 4 ≤ q)
    (v : SpaceTimeField)
    (hslice : ∀ t : Icc (0 : ℝ) T, (fun x : Space => v (↑t, x)) =ᵐ[volume] ⇑(U t))
    {R : ℝ} (hR : ‖u‖ ≤ R)
    (hcont : ContinuousOn (fun s => sobolevNormAt (2 : ℝ) v s) (Ico (0 : ℝ) T))
    {T₀ : ℝ} (hT₀T : T₀ < T) :
    ∀ t ∈ Icc (0 : ℝ) T₀,
      (∫ s in (0 : ℝ)..t, sobolevNormAt (2 : ℝ) v s ^ 2) ≤ 256 * R ^ 2 * T₀ := by
  have hRnn : 0 ≤ R := le_trans (norm_nonneg u) hR
  have hpt := sobolevNormAt_two_sq_le_of_sup u U hu hU hq v hslice hR
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := ht.1
  have htT : t < T := lt_of_le_of_lt ht.2 hT₀T
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
        apply mul_le_mul_of_nonneg_right ht.2; positivity
    _ = 256 * R ^ 2 * T₀ := by ring

/-- **(iii) cap at the endpoint `T₀ = T`** (review note N3 / row iii-a′).  The lane's `T₀ < T` is
needed only to get interval-integrability out of `hcont` (continuity on the half-open `Ico 0 T`);
the pointwise bound `sobolevNormAt_two_sq_le_of_sup` is already **unconditional** on the closed
`Icc 0 T`, so at the closed endpoint integrability follows from a.e.-continuity on `Ioo 0 t`
(`Ioo_ae_eq_Ioc`) plus the pointwise bound (`Integrable.mono'`).  Same constant `256·R²·T`.  Only
the *Grönwall output* at `t = T` (`highContinuationIntegral` needs `t < T`) remains the hard
eq:criterion endpoint of row (iii). -/
theorem kbnd_of_sup_bound_Icc_endpoint {q : ℕ} {T : ℝ}
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t)) (hq : 4 ≤ q)
    (v : SpaceTimeField)
    (hslice : ∀ t : Icc (0 : ℝ) T, (fun x : Space => v (↑t, x)) =ᵐ[volume] ⇑(U t))
    {R : ℝ} (hR : ‖u‖ ≤ R)
    (hcont : ContinuousOn (fun s => sobolevNormAt (2 : ℝ) v s) (Ico (0 : ℝ) T)) :
    ∀ t ∈ Icc (0 : ℝ) T,
      (∫ s in (0 : ℝ)..t, sobolevNormAt (2 : ℝ) v s ^ 2) ≤ 256 * R ^ 2 * T := by
  have hRnn : 0 ≤ R := le_trans (norm_nonneg u) hR
  have hpt := sobolevNormAt_two_sq_le_of_sup u U hu hU hq v hslice hR
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := ht.1
  have htT : t ≤ T := ht.2
  have hle_pt : ∀ s ∈ Icc (0 : ℝ) t, sobolevNormAt (2 : ℝ) v s ^ 2 ≤ 256 * R ^ 2 := by
    intro s hs
    have := hpt ⟨s, hs.1, le_trans hs.2 htT⟩
    simpa using this
  have hmeas : AEStronglyMeasurable (fun s => sobolevNormAt (2 : ℝ) v s ^ 2)
      (volume.restrict (Ioc (0 : ℝ) t)) := by
    have hsub : Ioo (0 : ℝ) t ⊆ Ico (0 : ℝ) T := fun s hs => ⟨hs.1.le, lt_of_lt_of_le hs.2 htT⟩
    have h1 : AEStronglyMeasurable (fun s => sobolevNormAt (2 : ℝ) v s ^ 2)
        (volume.restrict (Ioo (0 : ℝ) t)) :=
      ((hcont.pow 2).mono hsub).aestronglyMeasurable measurableSet_Ioo
    rwa [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at h1
  have hII : IntervalIntegrable (fun s => sobolevNormAt (2 : ℝ) v s ^ 2) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht0]
    refine Integrable.mono' (g := fun _ : ℝ => 256 * R ^ 2)
      (integrableOn_const (by simp)) hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have h0 : 0 ≤ sobolevNormAt (2 : ℝ) v s ^ 2 := sq_nonneg _
    rw [Real.norm_of_nonneg h0]
    exact hle_pt s ⟨hs.1.le, hs.2⟩
  calc (∫ s in (0 : ℝ)..t, sobolevNormAt (2 : ℝ) v s ^ 2)
      ≤ ∫ _s in (0 : ℝ)..t, (256 * R ^ 2) :=
        intervalIntegral.integral_mono_on ht0 hII intervalIntegrable_const hle_pt
    _ = t * (256 * R ^ 2) := by rw [intervalIntegral.integral_const]; ring
    _ ≤ T * (256 * R ^ 2) := by apply mul_le_mul_of_nonneg_right htT; positivity
    _ = 256 * R ^ 2 * T := by ring

/-- **(iii) conclusion widening, one order.**  `GronwallInstance.highOrder_bddAbove_of_kbnd`'s
explicit high-order bound, widened to the *closed* window `Icc 0 T₀`, with the same constant
`(sobolevNormAt m w.velocity 0 + ‖f‖_{L¹_tH^m})·exp(Cgron m ν·Kbnd)`.  The cap `hkbnd` is taken on
an *intermediate* horizon `Ico 0 T₁` with `T₀ < T₁ ≤ T` (review note N1): this lets a caller keep
`Kbnd = 256·R²·T₁` from `kbnd_of_sup_bound` at horizon `T₁`, rather than being forced up to
`256·R²·T`.  `T₁ := T` recovers the full-horizon form.  The bound is `highOrder_bddAbove_of_kbnd`
at horizon `T₁` restricted along `Icc 0 T₀ ⊆ Ico 0 T₁`. -/
theorem highOrder_bddAbove_of_kbnd_Icc
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f) (hf1 : MemL1Hm f)
    (w : ClassicalSolutionR ν a f T) (hpath : HasSmoothSobolevPath T w.velocity)
    {m : ℕ} (hm : 3 ≤ m) {T₀ T₁ Kbnd : ℝ} (hT₀ : 0 ≤ T₀) (hT₀T₁ : T₀ < T₁) (hT₁T : T₁ ≤ T)
    (hkbnd : ∀ t ∈ Ico (0 : ℝ) T₁,
        (∫ s in (0 : ℝ)..t, sobolevNormAt 2 w.velocity s ^ 2) ≤ Kbnd) :
    ∀ t ∈ Icc (0 : ℝ) T₀,
      sobolevNormAt (m : ℝ) w.velocity t ≤
        (sobolevNormAt (m : ℝ) w.velocity 0 + (A04.forceSobolevENormL1 (m : ℝ) f).toReal)
          * Real.exp (A04.Cgron m ν * Kbnd) := by
  have hbase := highOrder_bddAbove_of_kbnd hν ha hf hf1 w hpath hm
    (lt_of_le_of_lt hT₀ hT₀T₁) hT₁T hkbnd
  intro t ht
  exact hbase t ⟨ht.1, lt_of_le_of_lt ht.2 hT₀T₁⟩

/-- **(iii) conclusion widening, all orders (`BddAbove`).**  The all-orders `BddAbove` conclusion of
`highOrder_bddAbove_all_orders_of_kbnd`, widened to the closed window `Icc 0 T₀`, with the cap
`hkbnd` on the intermediate horizon `Ico 0 T₁` (`T₀ < T₁ ≤ T`, review note N1).  Constant-free
(`BddAbove`), by `Icc 0 T₀ ⊆ Ico 0 T₁` and monotonicity of `BddAbove`. -/
theorem highOrder_bddAbove_all_orders_of_kbnd_Icc
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f) (hf1 : MemL1Hm f)
    (w : ClassicalSolutionR ν a f T) (hpath : HasSmoothSobolevPath T w.velocity)
    {T₀ T₁ Kbnd : ℝ} (hT₀ : 0 ≤ T₀) (hT₀T₁ : T₀ < T₁) (hT₁T : T₁ ≤ T)
    (hkbnd : ∀ t ∈ Ico (0 : ℝ) T₁,
        (∫ s in (0 : ℝ)..t, sobolevNormAt 2 w.velocity s ^ 2) ≤ Kbnd) :
    ∀ m : ℕ, 3 ≤ m →
      BddAbove ((fun t => sobolevNormAt (m : ℝ) w.velocity t) '' Icc (0 : ℝ) T₀) := by
  intro m hm
  have hbase := highOrder_bddAbove_all_orders_of_kbnd hν ha hf hf1 w hpath
    (lt_of_le_of_lt hT₀ hT₀T₁) hT₁T hkbnd m hm
  refine hbase.mono ?_
  rintro x ⟨t, ht, rfl⟩
  exact ⟨t, ⟨ht.1, lt_of_le_of_lt ht.2 hT₀T₁⟩, rfl⟩

/-! ## 2. Deliverable (ii): the converse norm comparison -/

/-- **(ii) backbone.**  The `SobolevSpace 1 q` norm is the sup over derivative words: if every word
`word 1 u hn w` has norm `≤ C` (`0 ≤ C`), then `‖u‖ ≤ C`.  The cylinder Sobolev space is a closed
submodule of the word-indexed product `SobolevWord q → LiftL2 1` with the inherited sup (Pi) norm,
and `word 1 u hn w` is the coordinate at the word `⟨⟨n, _⟩, w⟩`, so this is
`pi_norm_le_iff_of_nonneg`. -/
theorem sobolevSpace_norm_le_of_forall_word {q : ℕ} (u : SobolevSpace 1 q) {C : ℝ} (hC : 0 ≤ C)
    (hw : ∀ (n : ℕ) (hn : n ≤ q) (w : Fin n → Fin 4), ‖word 1 u hn w‖ ≤ C) :
    ‖u‖ ≤ C := by
  refine (pi_norm_le_iff_of_nonneg hC).mpr ?_
  rintro ⟨⟨n, hlt⟩, w⟩
  exact hw n (Nat.le_of_lt_succ hlt) w

/-- **(ii) the reverse embedding (proved).**  For a smooth field `z` that is `H^{q+1}`
(`sobolevENorm (q+1) z ≠ ⊤`), the order-`n` Fréchet-jet `L²` norm (`n ≤ q+1`) is bounded by the
order-`(q+1)` energy norm with the explicit, `n`-uniform constant `jetSobolevConst (q+1)`.

Route (`DatumToJets.lean`): `eLpNorm (iteratedFDeriv ℝ n z)` is one summand of
`jetSobolevENorm (q+1) z`, and `jetSobolevENorm_le_sobolevENorm` bounds the whole jet sum by
`jetSobolevConst (q+1) · sobolevENorm (q+1) z`.  The `.toReal` step uses the `H^{q+1}` finiteness
`hfin` (without it, `sobolevENorm (q+1) z = ⊤` makes the real bound false via `⊤.toReal = 0`). -/
theorem eLpNorm_iteratedFDeriv_le_sobolevENorm_toReal (q n : ℕ) (hn : n ≤ q + 1)
    {z : Space → Space} (hz : ContDiff ℝ ∞ z) (hfin : sobolevENorm ((q + 1 : ℕ) : ℝ) z ≠ ⊤) :
    (eLpNorm (iteratedFDeriv ℝ n z) 2 volume).toReal
      ≤ jetSobolevConst (q + 1) * (sobolevENorm ((q + 1 : ℕ) : ℝ) z).toReal := by
  have hle1 : eLpNorm (iteratedFDeriv ℝ n z) 2 volume ≤ jetSobolevENorm (q + 1) z := by
    rw [jetSobolevENorm]
    exact Finset.single_le_sum (f := fun j => eLpNorm (iteratedFDeriv ℝ j z) 2 volume)
      (fun j _ => bot_le) (Finset.mem_range.mpr (by omega))
  have hEN : eLpNorm (iteratedFDeriv ℝ n z) 2 volume
      ≤ ENNReal.ofReal (jetSobolevConst (q + 1)) * sobolevENorm ((q + 1 : ℕ) : ℝ) z :=
    hle1.trans (jetSobolevENorm_le_sobolevENorm (q + 1) hz)
  have hrhs_top :
      ENNReal.ofReal (jetSobolevConst (q + 1)) * sobolevENorm ((q + 1 : ℕ) : ℝ) z ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  calc (eLpNorm (iteratedFDeriv ℝ n z) 2 volume).toReal
      ≤ (ENNReal.ofReal (jetSobolevConst (q + 1)) * sobolevENorm ((q + 1 : ℕ) : ℝ) z).toReal :=
        ENNReal.toReal_mono hrhs_top hEN
    _ = jetSobolevConst (q + 1) * (sobolevENorm ((q + 1 : ℕ) : ℝ) z).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (jetSobolevConst_pos (q + 1)).le]

/-- **(ii) converse, single slice.**  For a smooth `H^{q+1}` field `z` (downstream: the classical
velocity slice `fun x => v(t,x)`), the cylinder-array norm is bounded by the order-`(q+1)` energy
norm with the explicit `t`-free constant `jetSobolevConst (q+1)`:
`‖u‖ ≤ jetSobolevConst (q+1) · (sobolevENorm (q+1) z).toReal`.

The single hypothesis `hword_jet` is the carrier-bridge gap (module header): each cylinder word's
`L²` norm is bounded by the smooth slice's order-`|w|` Fréchet-jet `L²` norm — the
descent-to-classical-jet identity, phrased on the word so that the top-order words (beyond the
descent's 3-order jet reach) are also covered.  Everything else is `sobolevSpace_norm_le_of_forall_word`
composed with `eLpNorm_iteratedFDeriv_le_sobolevENorm_toReal`. -/
theorem sobolevSpace_norm_le_sobolevENorm {q : ℕ} (u : SobolevSpace 1 (q + 1))
    {z : Space → Space} (hz : ContDiff ℝ ∞ z) (hfin : sobolevENorm ((q + 1 : ℕ) : ℝ) z ≠ ⊤)
    (hword_jet : ∀ (n : ℕ) (hn : n ≤ q + 1) (w : Fin n → Fin 4),
        ‖word 1 u hn w‖ ≤ (eLpNorm (iteratedFDeriv ℝ n z) 2 volume).toReal) :
    ‖u‖ ≤ jetSobolevConst (q + 1) * (sobolevENorm ((q + 1 : ℕ) : ℝ) z).toReal := by
  refine sobolevSpace_norm_le_of_forall_word u
    (mul_nonneg (jetSobolevConst_pos (q + 1)).le ENNReal.toReal_nonneg) (fun n hn w => ?_)
  exact (hword_jet n hn w).trans (eLpNorm_iteratedFDeriv_le_sobolevENorm_toReal q n hn hz hfin)

/-- **(ii) converse, time-indexed.**  For a `ContinuousMap` cylinder path `u` and a space-time
field `v` whose every time-`t` slice is a smooth `H^{q+1}` field, the cylinder-array norm at time
`t` is bounded by the order-`(q+1)` energy norm at that time, with the same `t`-free constant:
`‖u t‖ ≤ jetSobolevConst (q+1) · sobolevNormAt (q+1) v t`.  This is the shape a Grönwall energy cap
feeds back into the cylinder sup-bound (`HasAprioriBound`), modulo the same `hword_jet` gap. -/
theorem sobolevSpace_norm_le_sobolevNormAt {q : ℕ} {T : ℝ}
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1))) (v : SpaceTimeField)
    (hz : ∀ t : Icc (0 : ℝ) T, ContDiff ℝ ∞ (fun x : Space => v (↑t, x)))
    (hfin : ∀ t : Icc (0 : ℝ) T, sobolevENorm ((q + 1 : ℕ) : ℝ) (fun x : Space => v (↑t, x)) ≠ ⊤)
    (hword_jet : ∀ (t : Icc (0 : ℝ) T) (n : ℕ) (hn : n ≤ q + 1) (w : Fin n → Fin 4),
        ‖word 1 (u t) hn w‖
          ≤ (eLpNorm (iteratedFDeriv ℝ n (fun x : Space => v (↑t, x))) 2 volume).toReal) :
    ∀ t : Icc (0 : ℝ) T,
      ‖u t‖ ≤ jetSobolevConst (q + 1) * sobolevNormAt ((q + 1 : ℕ) : ℝ) v ↑t := by
  intro t
  exact sobolevSpace_norm_le_sobolevENorm (u t) (hz t) (hfin t) (hword_jet t)

/-- **(N5) a.e. invariance of the energy norm.**  The datum norm reads the field only through the
Bochner pairings of `IsSobolevDatum`, so it is invariant under a.e. equality of the field
(`IsSobolevDatum.congr_field`, `CarrierBridge.lean:79`). -/
theorem sobolevENorm_congr_ae {s : ℝ} {z z' : Space → Space} (h : z =ᵐ[volume] z') :
    sobolevENorm s z = sobolevENorm s z' := by
  refine le_antisymm ?_ ?_
  · simp only [sobolevENorm]
    exact le_iInf fun A => sobolevENorm_le_of_isSobolevDatum (IsSobolevDatum.congr_field A.2 h.symm)
  · simp only [sobolevENorm]
    exact le_iInf fun A => sobolevENorm_le_of_isSobolevDatum (IsSobolevDatum.congr_field A.2 h)

/-- **(ii) converse on the ordinary `L²` carrier (N5).**  The audit's original row-(ii) shape: the
cylinder-array norm bounded by the order-`(q+1)` energy norm of the ordinary `L²` observation `⇑U`
itself.  The *proof* still routes through a smooth `H^{q+1}` slice `z =ᵐ[volume] ⇑U` (only a smooth
field has the `DatumToJets` reverse bound), but the datum norm is an a.e. invariant
(`sobolevENorm_congr_ae`), so the *statement* is on `⇑U`.  Same constant `jetSobolevConst (q+1)`;
same isolated gap `hword_jet`. -/
theorem sobolevSpace_norm_le_sobolevENorm_ordinary {q : ℕ} (u : SobolevSpace 1 (q + 1))
    (U : EulerMeanSolenoidal.L2)
    {z : Space → Space} (hz : ContDiff ℝ ∞ z) (hzU : z =ᵐ[volume] ⇑U)
    (hfin : sobolevENorm ((q + 1 : ℕ) : ℝ) (⇑U) ≠ ⊤)
    (hword_jet : ∀ (n : ℕ) (hn : n ≤ q + 1) (w : Fin n → Fin 4),
        ‖word 1 u hn w‖ ≤ (eLpNorm (iteratedFDeriv ℝ n z) 2 volume).toReal) :
    ‖u‖ ≤ jetSobolevConst (q + 1) * (sobolevENorm ((q + 1 : ℕ) : ℝ) (⇑U)).toReal := by
  have hcongr : sobolevENorm ((q + 1 : ℕ) : ℝ) z = sobolevENorm ((q + 1 : ℕ) : ℝ) (⇑U) :=
    sobolevENorm_congr_ae hzU
  rw [← hcongr]
  exact sobolevSpace_norm_le_sobolevENorm u hz (by rw [hcongr]; exact hfin) hword_jet

end NSFormalization.Section4.A01
