import NSFormalization.Section4.C01.EnergySpec
import NSFormalization.Paper1.ScalarEnergy

/-!
# Section 4 · C01 — the ordinary energy inequality and eq:RL2 (rows `energyDifferentialBound`, `l2Bound`)

Two consequences of the ordinary energy identity `energyIdentity_l2Sq`
(`Section4/C01/EnergySpec.lean`, the clamp-free `l2Sq`/`slice`/`pairing` form of lane 150's
`energyIdentity_classical_unconditional`), rows `energyDifferentialBound` (`Spec.lean:364`) and
`l2Bound` = eq:RL2 (`Spec.lean:383`, `paper/sections/04-whole-space.tex:118-121`) of
`research/C01/ENERGY_SPLIT.md`.

* **`energyDifferentialBound`** — the Cauchy–Schwarz form of the identity,
  `(‖u(t)‖₂²)' + 2ν‖∇u(t)‖₂² ≤ 2‖f(t)‖₂‖u(t)‖₂`, at every interior time, for any real `E'`
  that is the derivative there.  `HasDerivAt.unique` pins `E'` to the identity's value, the
  dissipation and the identity's `−2ν‖∇u‖²` cancel, and `⟨u,f⟩ ≤ ‖u‖₂‖f‖₂` is Cauchy–Schwarz
  in `L²` (`real_inner_le_norm` on the carrier-B `toLp`s, through the `norm_toLp_sq_eq_l2Sq`
  and `pairing_eq_inner` bridges of `Vocabulary.lean`).

* **`l2Bound`** (eq:RL2) — `‖u(t)‖₂ ≤ ‖a‖₂ + ∫₀ᵗ‖f(s)‖₂ ds =: K(t)`.  The scalar
  regularized-division argument `Paper1.sqrt_energy_le_primitive` (`ScalarEnergy.lean:22`) is
  generalized here to `sqrt_energy_le_primitive'`: its `E 0 = 0 ∧ N 0 = 0` requirement is
  replaced by `√(E 0) ≤ N 0`, which is what the ordinary energy estimate satisfies
  (`√(E 0) = ‖a‖₂ = K(0)`, via `ClassicalSolutionR.initial`).  The four analytic inputs are:
  the differential bound above (dissipation discarded), the interval-integrability and FTC
  derivative of the forcing primitive (from `forceTimeRegularity`), and the continuity of the
  energy `s ↦ l2Sq (slice u s)` on `[0,t]` **including the left endpoint** —
  `velocityL2Sq_continuousOn`, the velocity analogue of `forceTimeRegularity`'s continuity,
  built from `ClassicalSolutionR.sobolev`'s order-0 continuous datum path through the same
  `continuous_jetOfDatum_zero` / `l2Norm_eq_norm_jetOfDatum` machinery (`ForceSlices.lean`).

## The `gradientSq` used here, and the V3 contract bridge

The gradient term is the local **raw-integral** `gradientSq z = ∫∑ᵢ‖∂ᵢz‖²`
(`= ∫ x, ∑ i, ‖fderiv ℝ z x (coordinateVector i)‖²`), the exact shape `energyIdentity_l2Sq`
carries.  The `verification`-side V3 contract will state `energyDifferentialBound` with the
registered `Contracts.V1.gradientTensor` form `∫‖∇z‖²`; identifying the two needs the **same**
single `PiLp.norm_sq_eq_of_L2` bridge the V2 contract already used for `energyIdentity`'s
gradient term, discharged in the binding (`gradientTensor` is a `Contracts.V1` object, not
importable here).  `pairing`, `l2Sq`, `l2Norm`, `slice`, `energyBudget` are `rfl`-equal to
their `Spec.lean` counterparts.
-/

noncomputable section

open Set MeasureTheory Filter Topology
open EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
open NavierStokes.ProblemStatement
open NSFormalization.Paper3
open scoped RealInnerProductSpace ContDiff

namespace NSFormalization.Section4.C01

open NSFormalization.Section4.A02 (ClassicalSolutionR MemForceR)
open NSFormalization.Section4.D01 (contDiff_slice jetOfDatum)

variable {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField} {T : ℝ}

/-! ## 0. The remaining spec-local `def`s (`research/C01/Spec.lean:185,218-225`) -/

/-- `research/C01/Spec.lean:185`, the raw-integral form of `‖∇z‖₂²`:
`∫ x, ∑ i, ‖∂ᵢz(x)‖²`.  This is the value `energyIdentity_l2Sq` carries; the contract's
`gradientSq` (through `Contracts.V1.gradientTensor`) equals it by `PiLp.norm_sq_eq_of_L2`,
discharged in the V3 binding (see the module header). -/
def gradientSq (z : A02.SpatialField) : ℝ :=
  ∫ x, ∑ i : Fin 3, ‖fderiv ℝ z x (coordinateVector i)‖ ^ 2

/-- `research/C01/Spec.lean:218-219`, the forcing primitive `∫₀ᵗ‖f(s)‖₂ ds`. -/
def forcePrimitive (f : A02.SpaceTimeField) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, l2Norm (slice f s)

/-- `research/C01/Spec.lean:224-225`, `K(t) = ‖a‖₂ + ∫₀ᵗ‖f(s)‖₂ ds`. -/
def energyBudget (a : A02.SpatialField) (f : A02.SpaceTimeField) (t : ℝ) : ℝ :=
  l2Norm a + forcePrimitive f t

/-! ## 1. Nonnegativity and the `l2Sq = l2Norm²` identity -/

theorem l2Sq_nonneg (z : A02.SpatialField) : 0 ≤ l2Sq z := by
  show (0 : ℝ) ≤ ∫ x, ‖z x‖ ^ 2
  exact integral_nonneg fun x => sq_nonneg _

theorem gradientSq_nonneg (z : A02.SpatialField) : 0 ≤ gradientSq z := by
  show (0 : ℝ) ≤ ∫ x, ∑ i : Fin 3, ‖fderiv ℝ z x (coordinateVector i)‖ ^ 2
  exact integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _

theorem l2Sq_eq_sq_l2Norm (z : A02.SpatialField) : l2Sq z = l2Norm z ^ 2 := by
  show l2Sq z = Real.sqrt (l2Sq z) ^ 2
  rw [Real.sq_sqrt (l2Sq_nonneg z)]

/-! ## 2. `l2Norm` of a slice is the `Lp` norm of its carrier-B packaging -/

theorem l2Norm_eq_norm_toLp_velocity (w : ClassicalSolutionR ν a f T) {t : ℝ}
    (htv : t ∈ Ico (0 : ℝ) T) :
    l2Norm (slice w.velocity t) = ‖(velocitySliceField w htv).toLp‖ := by
  have h : ‖(velocitySliceField w htv).toLp‖ ^ 2 = l2Sq (slice w.velocity t) :=
    norm_toLp_sq_eq_l2Sq (velocitySliceField w htv)
  show Real.sqrt (l2Sq (slice w.velocity t)) = ‖(velocitySliceField w htv).toLp‖
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

theorem l2Norm_eq_norm_toLp_force (hf : MemForceR f) {t : ℝ} (ht0 : (0 : ℝ) ≤ t) :
    l2Norm (slice f t) = ‖(forceSliceField hf ht0).toLp‖ := by
  have h : ‖(forceSliceField hf ht0).toLp‖ ^ 2 = l2Sq (slice f t) :=
    norm_toLp_sq_eq_l2Sq (forceSliceField hf ht0)
  show Real.sqrt (l2Sq (slice f t)) = ‖(forceSliceField hf ht0).toLp‖
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

/-- Cauchy–Schwarz in `L²`: `⟨u(t), f(t)⟩ ≤ ‖f(t)‖₂‖u(t)‖₂`, through the carrier-B inner
product (`pairing_eq_inner`) and `real_inner_le_norm`. -/
theorem pairing_le_l2Norm_mul (w : ClassicalSolutionR ν a f T) (hf : MemForceR f) {t : ℝ}
    (htv : t ∈ Ico (0 : ℝ) T) (ht0 : (0 : ℝ) ≤ t) :
    pairing (slice w.velocity t) (slice f t)
      ≤ l2Norm (slice f t) * l2Norm (slice w.velocity t) := by
  have hpair : pairing (slice w.velocity t) (slice f t)
      = ⟪(velocitySliceField w htv).toLp, (forceSliceField hf ht0).toLp⟫ :=
    pairing_eq_inner (velocitySliceField w htv) (forceSliceField hf ht0)
  rw [hpair, l2Norm_eq_norm_toLp_velocity w htv, l2Norm_eq_norm_toLp_force hf ht0]
  calc ⟪(velocitySliceField w htv).toLp, (forceSliceField hf ht0).toLp⟫
        ≤ ‖(velocitySliceField w htv).toLp‖ * ‖(forceSliceField hf ht0).toLp‖ :=
        real_inner_le_norm _ _
    _ = ‖(forceSliceField hf ht0).toLp‖ * ‖(velocitySliceField w htv).toLp‖ := mul_comm _ _

/-! ## 3. The ordinary energy inequality (row `energyDifferentialBound`) -/

/-- **Row `energyDifferentialBound`** (`research/C01/Spec.lean:364-370`,
`paper/sections/04-whole-space.tex:117-121`):

  `(‖u(t)‖₂²)' + 2ν‖∇u(t)‖₂² ≤ 2‖f(t)‖₂‖u(t)‖₂`,

for any real `E'` that is the derivative of the `L²` energy at the interior time `t`.  `E'` is
pinned to the identity's value by `HasDerivAt.unique`; the `−2ν‖∇u‖²` of the identity and the
`+2ν‖∇u‖²` here cancel, leaving `2⟨u,f⟩`, which Cauchy–Schwarz bounds.  Stated with the local
raw-integral `gradientSq` (see header); `0 < ν` and `a ∈ initialClassR` are not needed. -/
theorem energyDifferentialBound (w : ClassicalSolutionR ν a f T) (hf : MemForceR f) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) T) (E' : ℝ)
    (hderiv : HasDerivAt (fun s => l2Sq (slice w.velocity s)) E' t) :
    E' + 2 * ν * gradientSq (slice w.velocity t)
      ≤ 2 * l2Norm (slice f t) * l2Norm (slice w.velocity t) := by
  have hid := energyIdentity_l2Sq w hf ht
  have hE' : E' = -2 * ν * gradientSq (slice w.velocity t)
      + 2 * pairing (slice w.velocity t) (slice f t) := hderiv.unique hid
  have hkey : E' + 2 * ν * gradientSq (slice w.velocity t)
      = 2 * pairing (slice w.velocity t) (slice f t) := by rw [hE']; ring
  rw [hkey]
  have hcs := pairing_le_l2Norm_mul w hf (Ioo_subset_Ico_self ht) (le_of_lt ht.1)
  have hassoc : 2 * l2Norm (slice f t) * l2Norm (slice w.velocity t)
      = 2 * (l2Norm (slice f t) * l2Norm (slice w.velocity t)) := by ring
  rw [hassoc]
  linarith [hcs]

/-! ## 4. Continuity of the `L²` energy in time (endpoint `t = 0` included) -/

/-- The velocity analogue of `forceTimeRegularity`'s continuity conjunct: `t ↦ ‖u(t)‖₂` is
continuous on the whole lifespan `[0,T)`, endpoint `t = 0` included, from
`ClassicalSolutionR.sobolev`'s order-0 continuous datum path. -/
theorem velocityL2Norm_continuousOn (w : ClassicalSolutionR ν a f T) :
    ContinuousOn (fun s => l2Norm (slice w.velocity s)) (Ico (0 : ℝ) T) := by
  obtain ⟨G, hGc, hGd⟩ := w.sobolev 0
  have hnorm : Continuous
      (fun A : RealVectorSobolev ((0 : ℕ) : ℝ) => ‖jetOfDatum 0 0 (le_refl 0) A‖) :=
    continuous_norm.comp continuous_jetOfDatum_zero
  have hcomp : ContinuousOn (fun s => ‖jetOfDatum 0 0 (le_refl 0) (G s)‖) (Ico (0 : ℝ) T) :=
    hnorm.comp_continuousOn hGc
  refine hcomp.congr (fun s hs => ?_)
  exact l2Norm_eq_norm_jetOfDatum (contDiff_slice w.velocity_smooth hs) (hGd s hs)

/-- `s ↦ ‖u(s)‖₂²` is continuous on `[0,T)`, obtained by squaring the previous. -/
theorem velocityL2Sq_continuousOn (w : ClassicalSolutionR ν a f T) :
    ContinuousOn (fun s => l2Sq (slice w.velocity s)) (Ico (0 : ℝ) T) := by
  refine ((velocityL2Norm_continuousOn w).pow 2).congr (fun s _ => ?_)
  exact l2Sq_eq_sq_l2Norm (slice w.velocity s)

/-! ## 5. The generalized scalar regularized-division lemma -/

/-- **Generalization of `Paper1.sqrt_energy_le_primitive`** (`ScalarEnergy.lean:22`): its
`E 0 = 0 ∧ N 0 = 0` hypotheses are replaced by the single `√(E 0) ≤ N 0`, which is what the
ordinary energy estimate satisfies (there with equality, `√(E 0) = ‖a‖₂ = K(0)`).  Same
regularized square root `√(E x + δ²)` and antitone-comparison proof; only the endpoint bound
`G 0 ≤ δ` changes, using `E 0 ≤ (N 0)²` from `√(E 0) ≤ N 0`.  No edit to `Paper1/`. -/
theorem sqrt_energy_le_primitive' {S : ℝ} {E E' N b : ℝ → ℝ}
    (hS : 0 ≤ S) (hE : ContinuousOn E (Icc 0 S)) (hN : ContinuousOn N (Icc 0 S))
    (hEN0 : Real.sqrt (E 0) ≤ N 0)
    (hEnonneg : ∀ t ∈ Icc 0 S, 0 ≤ E t)
    (hb : ∀ t ∈ Ioo 0 S, 0 ≤ b t)
    (hdE : ∀ t ∈ Ioo 0 S, HasDerivAt E (E' t) t)
    (hdN : ∀ t ∈ Ioo 0 S, HasDerivAt N (b t) t)
    (hineq : ∀ t ∈ Ioo 0 S, E' t ≤ 2 * b t * Real.sqrt (E t)) :
    ∀ t ∈ Icc 0 S, Real.sqrt (E t) ≤ N t := by
  intro t ht
  apply le_of_forall_pos_le_add
  intro δ hδ
  let G : ℝ → ℝ := fun x => Real.sqrt (E x + δ ^ 2) - N x
  have hpos (x : ℝ) (hx : x ∈ Icc 0 S) : 0 < E x + δ ^ 2 := by nlinarith [hEnonneg x hx]
  have hgcont : ContinuousOn G (Icc 0 S) := ((hE.add continuousOn_const).sqrt).sub hN
  have hderiv (x : ℝ) (hx : x ∈ Ioo 0 S) :
      HasDerivAt G (E' x / (2 * Real.sqrt (E x + δ ^ 2)) - b x) x :=
    (((hdE x hx).add_const (δ ^ 2)).sqrt (ne_of_gt (hpos x ⟨hx.1.le, hx.2.le⟩))).sub (hdN x hx)
  have hG : AntitoneOn G (Icc 0 S) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 S) hgcont
    · intro x hx
      exact (hderiv x (by simpa only [interior_Icc] using hx)).hasDerivWithinAt
    · intro x hx
      have hx' : x ∈ Ioo 0 S := by simpa only [interior_Icc] using hx
      have hs : 0 < Real.sqrt (E x + δ ^ 2) :=
        Real.sqrt_pos.mpr (hpos x ⟨hx'.1.le, hx'.2.le⟩)
      have hmono : Real.sqrt (E x) ≤ Real.sqrt (E x + δ ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg δ])
      have hdiv : E' x / (2 * Real.sqrt (E x + δ ^ 2)) ≤ b x := by
        apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt (E x + δ ^ 2))).mpr
        nlinarith [hineq x hx', mul_nonneg (hb x hx') (sub_nonneg.mpr hmono)]
      exact sub_nonpos.mpr hdiv
  have hbound := hG ⟨le_rfl, hS⟩ ht ht.1
  have hE0nn : 0 ≤ E 0 := hEnonneg 0 ⟨le_rfl, hS⟩
  have hN0nn : 0 ≤ N 0 := le_trans (Real.sqrt_nonneg _) hEN0
  have hsq : E 0 ≤ N 0 ^ 2 := by
    nlinarith [Real.sq_sqrt hE0nn, hEN0, Real.sqrt_nonneg (E 0)]
  have hG0 : G 0 ≤ δ := by
    show Real.sqrt (E 0 + δ ^ 2) - N 0 ≤ δ
    have hle : Real.sqrt (E 0 + δ ^ 2) ≤ N 0 + δ := by
      rw [show N 0 + δ = Real.sqrt ((N 0 + δ) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
      exact Real.sqrt_le_sqrt (by nlinarith [mul_nonneg hN0nn hδ.le])
    linarith
  have hGt : G t ≤ δ := le_trans hbound hG0
  have hfinal : Real.sqrt (E t + δ ^ 2) ≤ N t + δ := by
    simp only [G] at hGt; linarith
  exact (Real.sqrt_le_sqrt (by nlinarith [sq_nonneg δ])).trans hfinal

/-! ## 6. eq:RL2 (row `l2Bound`) -/

/-- **Row `l2Bound` = eq:RL2** (`research/C01/Spec.lean:383-387`,
`paper/sections/04-whole-space.tex:118-121`):

  `‖u(t)‖₂ ≤ ‖a‖₂ + ∫₀ᵗ‖f(s)‖₂ ds = energyBudget a f t`,

at every presingular time.  Obtained from `energyDifferentialBound` (dissipation discarded) by
the generalized scalar lemma `sqrt_energy_le_primitive'`, applied on `[0,t]`: the energy is
continuous there (`velocityL2Sq_continuousOn`, endpoint included), the forcing primitive is
continuous and has FTC derivative `‖f(s)‖₂` (`forceTimeRegularity`), and the endpoint value is
`√(E 0) = ‖a‖₂ = energyBudget a f 0` (`ClassicalSolutionR.initial`). -/
theorem l2Bound (w : ClassicalSolutionR ν a f T) (hf : MemForceR f) (hν : 0 < ν) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) T) :
    l2Norm (slice w.velocity t) ≤ energyBudget a f t := by
  have hg_cont : ContinuousOn (fun r => l2Norm (slice f r)) (Ici (0 : ℝ)) :=
    (forceTimeRegularity f hf).2
  -- continuity of the energy on `[0,t]`
  have hsub_ico : Icc (0 : ℝ) t ⊆ Ico (0 : ℝ) T :=
    fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
  have hE : ContinuousOn (fun s => l2Sq (slice w.velocity s)) (Icc 0 t) :=
    (velocityL2Sq_continuousOn w).mono hsub_ico
  -- continuity of the budget on `[0,t]`
  have huicc : uIcc (0 : ℝ) t = Icc 0 t := uIcc_of_le ht.1
  have hg_int : IntegrableOn (fun r => l2Norm (slice f r)) (uIcc 0 t) volume := by
    rw [huicc]; exact (hg_cont.mono fun r hr => hr.1).integrableOn_Icc
  have hprim_cont : ContinuousOn (fun x => ∫ r in (0 : ℝ)..x, l2Norm (slice f r)) (uIcc 0 t) :=
    intervalIntegral.continuousOn_primitive_interval hg_int
  rw [huicc] at hprim_cont
  have hN : ContinuousOn (energyBudget a f) (Icc 0 t) := continuousOn_const.add hprim_cont
  -- endpoint value `√(E 0) = energyBudget a f 0`
  have hEN0 : Real.sqrt (l2Sq (slice w.velocity 0)) ≤ energyBudget a f 0 := by
    have hslice0 : slice w.velocity 0 = a := funext fun x => w.initial x
    have hfp0 : forcePrimitive f 0 = 0 := by
      show (∫ s in (0 : ℝ)..(0 : ℝ), l2Norm (slice f s)) = 0
      exact intervalIntegral.integral_same
    rw [hslice0]
    show Real.sqrt (l2Sq a) ≤ l2Norm a + forcePrimitive f 0
    rw [hfp0, add_zero]
    exact le_of_eq rfl
  -- the FTC derivative of the budget on `(0,t)`
  have hdN : ∀ s ∈ Ioo (0 : ℝ) t, HasDerivAt (energyBudget a f) (l2Norm (slice f s)) s := by
    intro s hs
    have hci : Ici (0 : ℝ) ∈ 𝓝 s := mem_of_superset (Ioi_mem_nhds hs.1) Ioi_subset_Ici_self
    have hcs : ContinuousAt (fun r => l2Norm (slice f r)) s := hg_cont.continuousAt hci
    have hsub_uicc : uIcc (0 : ℝ) s ⊆ Ici (0 : ℝ) := by
      rw [uIcc_of_le hs.1.le]; exact fun r hr => hr.1
    have hii : IntervalIntegrable (fun r => l2Norm (slice f r)) volume 0 s :=
      (hg_cont.mono hsub_uicc).intervalIntegrable
    have hmeas : StronglyMeasurableAtFilter (fun r => l2Norm (slice f r)) (𝓝 s) :=
      ⟨Ioi 0, Ioi_mem_nhds hs.1,
        (hg_cont.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi⟩
    have hprim : HasDerivAt (fun u => ∫ r in (0 : ℝ)..u, l2Norm (slice f r))
        (l2Norm (slice f s)) s :=
      intervalIntegral.integral_hasDerivAt_right hii hmeas hcs
    exact hprim.const_add (l2Norm a)
  -- the differential inequality, dissipation discarded
  have hineq : ∀ s ∈ Ioo (0 : ℝ) t,
      (-2 * ν * gradientSq (slice w.velocity s) + 2 * pairing (slice w.velocity s) (slice f s))
        ≤ 2 * l2Norm (slice f s) * Real.sqrt (l2Sq (slice w.velocity s)) := by
    intro s hs
    have hsT : s ∈ Ioo (0 : ℝ) T := ⟨hs.1, lt_trans hs.2 ht.2⟩
    have hderivE : HasDerivAt (fun σ => l2Sq (slice w.velocity σ))
        (-2 * ν * gradientSq (slice w.velocity s)
          + 2 * pairing (slice w.velocity s) (slice f s)) s :=
      energyIdentity_l2Sq w hf hsT
    have hbound := energyDifferentialBound w hf hsT _ hderivE
    have hdiss : 0 ≤ 2 * ν * gradientSq (slice w.velocity s) :=
      mul_nonneg (mul_nonneg (by norm_num) hν.le) (gradientSq_nonneg _)
    have hstep : (-2 * ν * gradientSq (slice w.velocity s)
        + 2 * pairing (slice w.velocity s) (slice f s))
        ≤ 2 * l2Norm (slice f s) * l2Norm (slice w.velocity s) :=
      le_trans (le_add_of_nonneg_right hdiss) hbound
    calc (-2 * ν * gradientSq (slice w.velocity s)
            + 2 * pairing (slice w.velocity s) (slice f s))
          ≤ 2 * l2Norm (slice f s) * l2Norm (slice w.velocity s) := hstep
      _ = 2 * l2Norm (slice f s) * Real.sqrt (l2Sq (slice w.velocity s)) := rfl
  -- assemble
  have key := sqrt_energy_le_primitive' (S := t)
    (E := fun s => l2Sq (slice w.velocity s)) (N := energyBudget a f)
    (b := fun s => l2Norm (slice f s))
    (E' := fun s => -2 * ν * gradientSq (slice w.velocity s)
      + 2 * pairing (slice w.velocity s) (slice f s))
    ht.1 hE hN hEN0
    (fun s _ => l2Sq_nonneg _)
    (fun s _ => Real.sqrt_nonneg _)
    (fun s hs => energyIdentity_l2Sq w hf ⟨hs.1, lt_trans hs.2 ht.2⟩)
    hdN hineq
  have hres := key t ⟨ht.1, le_rfl⟩
  exact hres

end NSFormalization.Section4.C01
