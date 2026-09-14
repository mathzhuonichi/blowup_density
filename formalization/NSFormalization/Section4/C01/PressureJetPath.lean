import NSFormalization.Section4.C01.JetPaths
import NSFormalization.Section4.D01.FiniteOrderNorm
import Euler.OrdinaryAdvectionLimit

/-!
# C01 unit E4b — time-continuity of the pressure-gradient jets (the `hB` clause of E4)

Lane `148-C01-e4b-pressure-jets`, sub-row **E4b** of `research/C01/ENERGY_SPLIT.md`, the
analytic half of route (a) for row **E4** left open by lane 146 (`JetPaths.lean`, row E4a).

Row E4a built the momentum residual `h := f − (u·∇)u + νΔu` as a carrier-B
`EulerLpTranslation.SmoothL2Field` path over `[0,S]` with jets continuous in time
(`residualPath_jetLp_continuous`) and recorded
`∂ₜu = h − ∇p` at interior times
(`temporalDerivative_eq_residual_sub_pressureGradient`).  What was missing — the
`hB` hypothesis that `EulerOrdinarySobolev.wordEnergy_hasDerivWithinAt`
(`Euler/OrdinaryWordTime.lean`) consumes — is the **time-continuity of the `∇p(t,·)` `L²`
jets**, equivalently of the `∂ₜu(t,·)` jets.  Because `∇p(t,·)` and `∂ₜu(t,·)` are packaged
as `SmoothL2Field` only at *interior* times `t ∈ Ioo 0 T` (D01 P2 runs through the PDE), the
window is shifted off the endpoint to a compact `[c,S] ⊂ (0,T)` with `0 < c ≤ S < T`
(review 146, note N3).

## What is proved here

* **Glue (a) — jet control of the finite-order weak-derivative bound.**
  `norm_jetLp_mapField_le`, `norm_directionalField_jetLp_le` and
  `hasWeakDerivsL2Bound_of_jetLp_sq_le`: for a `SmoothL2Field Space` `Z` with
  `∀ k ≤ m, ‖Z.jetLp k‖² ≤ M`, the finite-order predicate
  `D01.HasWeakDerivsL2Bound Z.field M m` holds — the input that `FiniteOrderNorm`'s
  `norm_isSobolevDatum_le_of_memLp_derivs` (`‖A‖² ≤ 16^m·M`) needs, with `M` now expressed
  through the jets so that it vanishes along a jet-continuous path.

* **Item 2 — jets ⟹ datum-path continuity (every order, no order-1 hole).**
  `norm_smoothAngularDatum_sub_sq_le` bounds the datum difference
  `‖A_{P t} − A_{P s}‖² ≤ 16^m·∑_{k≤m}‖(P t).jetLp k − (P s).jetLp k‖²` — the order-`m`
  angular datum difference is a Sobolev datum of the field difference via
  `D01.isSobolevDatum_sub` (the `SchwartzPairable` version, valid at **every** order, so the
  `2 ≤ s` gap of `A03.isSobolevDatum_sub` at order 1 is avoided), and its square norm is the
  quantitative constructor bound.  `smoothAngularDatum_path_continuous` then squeezes to
  continuity of `t ↦ D01.smoothAngularDatum m (m:ℝ) _ (P t)` for every `m`.

* **Item 3 — the pressure-gradient jets.**  `pressureGradientPath_jetLp_continuous`:
  compose item 2 (at the residual path) with the Leray-complement CLM
  `D01.Leray.lerayComplement`, pin the result to `∇p`'s order-`n` datum by
  `D01.pin_pressureGradient_datum` / `isSobolevDatum_pressureGradient_lerayComplement`
  (whose residual-field slot is exactly `residualPath_field`), then reconstruct the jets by
  `jetOfDatum_continuous` + `D01.jetOfDatum_ae` — verbatim the datum⇒jets pattern of
  `forcePath_jetLp_continuous`.

* **Item 4 — the derivative slice.**  `temporalSlicePath_jetLp_continuous`: the `hB` clause,
  `∂ₜu = h − ∇p` jets, from `residualPathIcc` jets **minus** the `∇p` jets via `jetLp_fieldSub`
  and `EulerLpSmoothCoefficientProduct.jetLp_congr` with
  `temporalDerivative_eq_residual_sub_pressureGradient`.

The remaining E4 obligations (feeding this `hB` into `wordEnergy_hasDerivWithinAt` on the
vendor's `Icc 0 T'` by translating the window, and `HasDerivWithinAt → HasDerivAt` at interior
points) are recorded in `research/C01/ATTEMPTS_E4B.md`.
-/

noncomputable section

open Set MeasureTheory Filter Topology
open EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
open NavierStokes.ProblemStatement
  (temporalDerivative advection spatialLaplacian pressureGradient coordinateVector Space)

namespace NSFormalization.Section4.C01

open NSFormalization.Section4.A02 (ClassicalSolutionR MemForceR)
open NSFormalization.Paper3 (RealVectorSobolev)

variable {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField} {c S T : ℝ}

/-! ## 1. Glue (a): jet-norm control of the finite-order weak-derivative bound -/

/-- The order-`n` postcomposition operator has norm at most `‖L‖`; the jet-level version of
`compContinuousMultilinearMapL` being norm-nonincreasing in each fixed multilinear slot. -/
theorem norm_jetPostcompose_le {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V →L[ℝ] W) (n : ℕ) :
    ‖jetPostcompose L n‖ ≤ ‖L‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
    (fun g => ContinuousLinearMap.norm_compContinuousMultilinearMap_le L g)

/-- **`mapField` is jet-norm nonincreasing by `‖L‖`.**  From `jetLp_mapField`
(`(mapField L A).jetLp n = (jetPostcompose L n).compLpL 2 volume (A.jetLp n)`),
`ContinuousLinearMap.norm_compLpL_le` and `norm_jetPostcompose_le`. -/
theorem norm_jetLp_mapField_le {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V →L[ℝ] W) (A : SmoothL2Field V) (n : ℕ) :
    ‖(mapField L A).jetLp n‖ ≤ ‖L‖ * ‖A.jetLp n‖ := by
  rw [jetLp_mapField]
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  exact (ContinuousLinearMap.norm_compLpL_le _).trans (norm_jetPostcompose_le L n)

/-- **The coordinate directional field raises the jet order by one, norm-nonincreasingly.**
`directionalField A v = mapField (apply ℝ Space v) A.derivative`, so
`‖(directionalField A v).jetLp n‖ ≤ ‖v‖·‖A.derivative.jetLp n‖ = ‖v‖·‖A.jetLp (n+1)‖`
(`norm_jetLp_mapField_le`, `‖apply ℝ Space v‖ ≤ ‖v‖`, `norm_derivative_jetLp`). -/
theorem norm_directionalField_jetLp_le (A : SmoothL2Field Space) (v : Space) (n : ℕ) :
    ‖(directionalField A v).jetLp n‖ ≤ ‖v‖ * ‖A.jetLp (n + 1)‖ := by
  have hL : ‖ContinuousLinearMap.apply ℝ Space v‖ ≤ ‖v‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) (fun φ => by
      rw [ContinuousLinearMap.apply_apply, mul_comm]; exact φ.le_opNorm v)
  calc ‖(directionalField A v).jetLp n‖
      = ‖(mapField (ContinuousLinearMap.apply ℝ Space v) A.derivative).jetLp n‖ := rfl
    _ ≤ ‖ContinuousLinearMap.apply ℝ Space v‖ * ‖A.derivative.jetLp n‖ :=
        norm_jetLp_mapField_le _ _ _
    _ ≤ ‖v‖ * ‖A.derivative.jetLp n‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    _ = ‖v‖ * ‖A.jetLp (n + 1)‖ := by rw [norm_derivative_jetLp]

/-- **Glue (a).**  If the jets of a `SmoothL2Field Space` `Z` are uniformly square-bounded by
`M` up to order `m`, then the finite-order weak-derivative predicate
`D01.HasWeakDerivsL2Bound Z.field M m` holds.  The recursion mirrors
`D01.exists_hasWeakDerivsL2Bound_smooth`, taking the coordinate directional fields as the
weak derivatives (`D01.smoothField_weakDeriv_pairing`), but keeps the *same* explicit bound
`M`: each directional field's jets are controlled by `Z`'s next jet
(`norm_directionalField_jetLp_le` with `‖coordinateVector j‖ = 1`), so the hypothesis
carries down the recursion unchanged. -/
theorem hasWeakDerivsL2Bound_of_jetLp_sq_le :
    ∀ (m : ℕ) (Z : SmoothL2Field Space) (M : ℝ),
      (∀ k, k ≤ m → ‖Z.jetLp k‖ ^ 2 ≤ M) → D01.HasWeakDerivsL2Bound Z.field M m
  | 0, Z, M, h => by
      refine ⟨Z.memLp, ?_⟩
      have e : (eLpNorm Z.field 2 volume).toReal = ‖Z.jetLp 0‖ := by
        rw [norm_jetLp_zero]; exact (Lp.norm_toLp Z.field Z.memLp).symm
      rw [e]; exact h 0 (le_refl 0)
  | (m + 1), Z, M, h => by
      refine ⟨⟨Z.memLp, ?_⟩, fun j =>
        ⟨(Z.directionalField (coordinateVector j)).field, ?_,
          fun i ψ => D01.smoothField_weakDeriv_pairing Z j i ψ⟩⟩
      · have e : (eLpNorm Z.field 2 volume).toReal = ‖Z.jetLp 0‖ := by
          rw [norm_jetLp_zero]; exact (Lp.norm_toLp Z.field Z.memLp).symm
        rw [e]; exact h 0 (Nat.zero_le _)
      · refine hasWeakDerivsL2Bound_of_jetLp_sq_le m (Z.directionalField (coordinateVector j)) M
          (fun k hk => ?_)
        have hcoord : ‖coordinateVector j‖ = 1 := by
          simp only [coordinateVector, PiLp.norm_single, norm_one]
        have hb := norm_directionalField_jetLp_le Z (coordinateVector j) k
        rw [hcoord, one_mul] at hb
        calc ‖(Z.directionalField (coordinateVector j)).jetLp k‖ ^ 2
            ≤ ‖Z.jetLp (k + 1)‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
          _ ≤ M := h (k + 1) (by omega)

/-! ## 2. Jets ⟹ datum-path continuity -/

/-- **The datum difference is quantitatively controlled by the jet difference.**  At order `m`
the angular datum difference `A_A − A_B` is a Sobolev datum of the field difference
(`D01.isSobolevDatum_sub`, the `SchwartzPairable` version, so no order restriction), and the
quantitative constructor `D01.norm_isSobolevDatum_le_of_memLp_derivs` bounds its square norm
by `16^m·∑_{k≤m}‖A.jetLp k − B.jetLp k‖²` (glue (a) supplies the `HasWeakDerivsL2Bound`). -/
theorem norm_smoothAngularDatum_sub_sq_le (m : ℕ) (A B : SmoothL2Field Space) :
    ‖D01.smoothAngularDatum m (m : ℝ) (le_refl _) A
        - D01.smoothAngularDatum m (m : ℝ) (le_refl _) B‖ ^ 2
      ≤ (16 : ℝ) ^ m * ∑ k ∈ Finset.range (m + 1), ‖A.jetLp k - B.jetLp k‖ ^ 2 := by
  set M : ℝ := ∑ k ∈ Finset.range (m + 1), ‖A.jetLp k - B.jetLp k‖ ^ 2 with hMdef
  have hsub : D01.IsSobolevDatum (m : ℝ) (A.field - B.field)
      (D01.smoothAngularDatum m (m : ℝ) (le_refl _) A
        - D01.smoothAngularDatum m (m : ℝ) (le_refl _) B) :=
    D01.isSobolevDatum_sub
      (D01.schwartzPairable_of_memLp (fun i => D01.memLp_component A.memLp i))
      (D01.schwartzPairable_of_memLp (fun i => D01.memLp_component B.memLp i))
      (D01.smoothAngularDatum_isSobolevDatum m (m : ℝ) (le_refl _) A)
      (D01.smoothAngularDatum_isSobolevDatum m (m : ℝ) (le_refl _) B)
  have hbnd : D01.HasWeakDerivsL2Bound (A.field - B.field) M m := by
    have h0 : D01.HasWeakDerivsL2Bound (fieldSub A B).field M m :=
      hasWeakDerivsL2Bound_of_jetLp_sq_le m (fieldSub A B) M (fun k hk => by
        rw [jetLp_fieldSub, hMdef]
        exact Finset.single_le_sum (f := fun j => ‖A.jetLp j - B.jetLp j‖ ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))
    have hfe : (fieldSub A B).field = A.field - B.field :=
      funext (fun x => (fieldSub_field A B x).trans (Pi.sub_apply _ _ _).symm)
    rwa [hfe] at h0
  exact D01.norm_isSobolevDatum_le_of_memLp_derivs m (A.field - B.field) M hbnd _ hsub

/-- **Item 2.**  For a carrier-B path `P` over `[c,S]` whose jets are continuous in time, the
order-`m` angular datum path is continuous in time, at **every** order `m`.  Continuity at a
point `t₀` is a squeeze: `‖A_{P t} − A_{P t₀}‖ ≤ √(16^m·∑_{k≤m}‖(P t).jetLp k − (P t₀).jetLp k‖²)`
(`norm_smoothAngularDatum_sub_sq_le`), and the bounding function is continuous in `t` with value
`0` at `t₀`. -/
theorem smoothAngularDatum_path_continuous
    (P : Icc c S → SmoothL2Field Space)
    (hP : ∀ k, Continuous (fun t => (P t).jetLp k)) (m : ℕ) :
    Continuous (fun t : Icc c S => D01.smoothAngularDatum m (m : ℝ) (le_refl _) (P t)) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  have hbndcont : Continuous (fun t : Icc c S =>
      Real.sqrt ((16 : ℝ) ^ m *
        ∑ k ∈ Finset.range (m + 1), ‖(P t).jetLp k - (P t₀).jetLp k‖ ^ 2)) :=
    Real.continuous_sqrt.comp (continuous_const.mul
      (continuous_finsetSum _ (fun k _ => (((hP k).sub continuous_const).norm.pow 2))))
  have hcont0 : Tendsto (fun t : Icc c S =>
      Real.sqrt ((16 : ℝ) ^ m *
        ∑ k ∈ Finset.range (m + 1), ‖(P t).jetLp k - (P t₀).jetLp k‖ ^ 2)) (𝓝 t₀) (𝓝 0) := by
    simpa using hbndcont.tendsto t₀
  have hsq : Tendsto (fun t : Icc c S =>
      D01.smoothAngularDatum m (m : ℝ) (le_refl _) (P t)
        - D01.smoothAngularDatum m (m : ℝ) (le_refl _) (P t₀)) (𝓝 t₀) (𝓝 0) := by
    refine squeeze_zero_norm (fun t => ?_) hcont0
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt (norm_smoothAngularDatum_sub_sq_le m (P t) (P t₀))
  exact tendsto_sub_nhds_zero_iff.mp hsq

/-! ## 3. The momentum-residual path on the interior window and the pressure-gradient jets -/

/-- The momentum residual path `h = f − (u·∇)u + νΔu` restricted to the interior window
`[c,S] ⊂ (0,T)` (the inclusion `Icc c S ↪ Icc 0 S`, well-defined since `0 < c ≤ t`). -/
def residualPathIcc (w : ClassicalSolutionR ν a f T) (hf : MemForceR f) (hc : 0 < c) (hST : S < T)
    (t : Icc c S) : SmoothL2Field Space :=
  residualPath w hf hST ⟨t.1, ⟨le_trans hc.le t.2.1, t.2.2⟩⟩

theorem residualPathIcc_field (w : ClassicalSolutionR ν a f T) (hf : MemForceR f) (hc : 0 < c)
    (hST : S < T) (t : Icc c S) (x : Space) :
    (residualPathIcc w hf hc hST t).field x
      = f (t.1, x) - advection w.velocity t.1 x + ν • spatialLaplacian w.velocity t.1 x :=
  residualPath_field w hf hST _ x

theorem residualPathIcc_jetLp_continuous (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    (hc : 0 < c) (hST : S < T) (k : ℕ) :
    Continuous (fun t : Icc c S => (residualPathIcc w hf hc hST t).jetLp k) :=
  (residualPath_jetLp_continuous w hf hST k).comp (continuous_subtype_val.subtype_mk _)

/-- Every time of the interior window `[c,S]` with `0 < c`, `S < T` is an interior time. -/
theorem mem_Ioo_of_mem_Icc (hc : 0 < c) (hST : S < T) {t : ℝ} (ht : t ∈ Icc c S) :
    t ∈ Ioo (0 : ℝ) T :=
  ⟨lt_of_lt_of_le hc ht.1, lt_of_le_of_lt ht.2 hST⟩

/-- **Item 3 (E4b).**  The pressure-gradient path has jets continuous in time on the window
`[c,S] ⊂ (0,T)`.  Route: continuity of the order-`n` residual datum path (`item 2` at the
residual path `residualPathIcc`), then the Leray-complement CLM `D01.Leray.lerayComplement`,
pinned to `∇p`'s order-`n` datum by `D01.isSobolevDatum_pressureGradient_lerayComplement`
(its residual-field slot is `residualPathIcc_field`), then the datum⇒jets reconstruction
`jetOfDatum_continuous` + `D01.jetOfDatum_ae` (the `forcePath_jetLp_continuous` pattern).

The interior window is `[c,S] ⊂ (0,T)` with `0 < c`, `S < T`; nonemptiness `c ≤ S` is not
needed (when `c > S` the index `Icc c S` is empty and continuity is vacuous). -/
theorem pressureGradientPath_jetLp_continuous
    (w : ClassicalSolutionR ν a f T) (hf : MemForceR f) (hc : 0 < c)
    (hST : S < T) (n : ℕ) :
    Continuous (fun t : Icc c S =>
      (pressureGradientField w hf (mem_Ioo_of_mem_Icc hc hST t.2)).jetLp n) := by
  have hn : n ≤ n := le_refl n
  -- item 2 at the residual path
  have hdatum : Continuous (fun t : Icc c S =>
      D01.smoothAngularDatum n (n : ℝ) (le_refl _) (residualPathIcc w hf hc hST t)) :=
    smoothAngularDatum_path_continuous (residualPathIcc w hf hc hST)
      (residualPathIcc_jetLp_continuous w hf hc hST) n
  -- push through the Leray-complement CLM
  have hleray : Continuous (fun t : Icc c S =>
      D01.Leray.lerayComplement (n : ℝ)
        (D01.smoothAngularDatum n (n : ℝ) (le_refl _) (residualPathIcc w hf hc hST t))) :=
    (D01.Leray.lerayComplement (n : ℝ)).continuous.comp hdatum
  -- the Leray-composed datum is a Sobolev datum of ∇p(t,·)
  have hisdat : ∀ t : Icc c S,
      D01.IsSobolevDatum (n : ℝ) (fun x => pressureGradient w.pressure t.1 x)
        (D01.Leray.lerayComplement (n : ℝ)
          (D01.smoothAngularDatum n (n : ℝ) (le_refl _) (residualPathIcc w hf hc hST t))) := by
    intro t
    refine D01.isSobolevDatum_pressureGradient_lerayComplement w hf
      (mem_Ioo_of_mem_Icc hc hST t.2) ?_
    have hfield : (residualPathIcc w hf hc hST t).field
        = fun x => f (t.1, x) - advection w.velocity t.1 x + ν • spatialLaplacian w.velocity t.1 x :=
      funext (fun x => residualPathIcc_field w hf hc hST t x)
    have hd := D01.smoothAngularDatum_isSobolevDatum n (n : ℝ) (le_refl _)
      (residualPathIcc w hf hc hST t)
    rwa [hfield] at hd
  -- datum ⇒ jets
  have hkey : (fun t : Icc c S =>
        (pressureGradientField w hf (mem_Ioo_of_mem_Icc hc hST t.2)).jetLp n)
      = fun t : Icc c S => D01.jetOfDatum n n hn
          (D01.Leray.lerayComplement (n : ℝ)
            (D01.smoothAngularDatum n (n : ℝ) (le_refl _) (residualPathIcc w hf hc hST t))) := by
    funext t
    apply Lp.ext
    exact (((pressureGradientField w hf (mem_Ioo_of_mem_Icc hc hST t.2)).integrable n).coeFn_toLp).trans
      (D01.jetOfDatum_ae hn (pressureGradientField w hf (mem_Ioo_of_mem_Icc hc hST t.2)).smooth
        (hisdat t)).symm
  rw [hkey]
  exact (jetOfDatum_continuous n n hn).comp hleray

/-! ## 4. The derivative slice (the `hB` clause) -/

/-- **Item 4 (the `hB` clause of E4).**  The time-derivative slice `∂ₜu(t,·)` has jets
continuous in time on `[c,S] ⊂ (0,T)`, obtained from `∂ₜu = h − ∇p`
(`temporalDerivative_eq_residual_sub_pressureGradient`): the residual jets (row E4a) minus the
`∇p` jets (E4b), via `EulerLpSmoothCoefficientProduct.jetLp_congr` and `jetLp_fieldSub`. -/
theorem temporalSlicePath_jetLp_continuous
    (w : ClassicalSolutionR ν a f T) (hf : MemForceR f) (hc : 0 < c)
    (hST : S < T) (n : ℕ) :
    Continuous (fun t : Icc c S =>
      (temporalSliceField w hf (mem_Ioo_of_mem_Icc hc hST t.2)).jetLp n) := by
  have hkey : (fun t : Icc c S =>
        (temporalSliceField w hf (mem_Ioo_of_mem_Icc hc hST t.2)).jetLp n)
      = fun t : Icc c S =>
          (residualPathIcc w hf hc hST t).jetLp n
            - (pressureGradientField w hf (mem_Ioo_of_mem_Icc hc hST t.2)).jetLp n := by
    funext t
    have hfe : (temporalSliceField w hf (mem_Ioo_of_mem_Icc hc hST t.2)).field
        = (fieldSub (residualPathIcc w hf hc hST t)
            (pressureGradientField w hf (mem_Ioo_of_mem_Icc hc hST t.2))).field := by
      funext x
      have htpos : 0 < t.1 := lt_of_lt_of_le hc t.2.1
      have heq := temporalDerivative_eq_residual_sub_pressureGradient w hf hST
        ⟨t.1, ⟨le_trans hc.le t.2.1, t.2.2⟩⟩ htpos x
      simp only [temporalSliceField_field, fieldSub_field, pressureGradientField_field]
      exact heq
    rw [EulerLpSmoothCoefficientProduct.jetLp_congr _ _ hfe n, jetLp_fieldSub]
  rw [hkey]
  exact (residualPathIcc_jetLp_continuous w hf hc hST n).sub
    (pressureGradientPath_jetLp_continuous w hf hc hST n)

end NSFormalization.Section4.C01
