import NSFormalization.Section4.A03.ScalarTameProduct
import NSFormalization.Section4.A03.VectorTameProduct
import NSFormalization.Paper3.AngularRealVectorBochner
import NSFormalization.Section4.D01.ForceClass
import NSFormalization.Section4.D01.HomogeneousWitness

/-!
# Half-order force norms are finite on the paper's force class (G3)

Task `D01`, gap **G3** of `research/R43/COMPARISON.md` §4 and
`research/D01/RECONCILIATION.md`: the smallness hypotheses of Propositions 4.3
and 4.4 (`04-whole-space.tex:97,150`) are stated with the half-order time norm
`‖f‖_{L¹_t H^{1/2}_x}` (`Contracts.V1.Data.forceSobolevENormL1 (1/2)`,
`Data.lean:231`).  Unless that norm is finite on a genuine force
`f ∈ 𝓕_ℝ` (`Contracts.V1.Data.MemForceR`, `Data.lean:544`), the hypothesis
`‖f‖ ≤ c` is met vacuously by `‖f‖ = ⊤` and the propositions say nothing.

`MemForceR` supplies datum paths only at **integer** orders `m`
(`Data.lean:546`), while `forceSobolevENorm q s` is an infimum over datum paths
at order `s` (`Data.lean:225`).  The bridge is the monotonicity of the Sobolev
norm in the order: `‖z‖_{H^s} ≤ C ‖z‖_{H^m}` for `s ≤ m`
(`01-introduction.tex:105`, "the homogeneous norm replaces the weights", read for
the inhomogeneous weights `(1+|ξ|²)^{s/2} ≤ (1+|ξ|²)^{m/2}`).  At the datum level
this is `Paper3.angularOrderLowering`, realized as the **real** order-lowering
operator `Section4.A03.lowerDatum` (`A03/RealAngularProduct.lean:140`) with the
contraction bound `A03.norm_lowerDatum_le` (`:198`); the datum it produces
realizes the same physical field (`A03.IsScalarSobolevDatum.lower`,
`A03/ScalarTameProduct.lean:114`), so it is the order-`s` datum of the same slice.

Applying it in each spatial slice turns the integer-order datum **path** of a
force into an order-`s` datum path, and — because `lowerVectorL` is a
`ContinuousLinearMap` — carries `MemLp` of the path across
(`ContinuousLinearMap.comp_memLp'`), which is exactly finite `eLpNorm`.  The
order-`s` infimum is then bounded by this finite value, so it is not `⊤`.

The result is proved for **every** real order `s ≤ m` and **both** time
exponents `q ∈ {1, 2}` (the two finiteness clauses `MemLp _ 1` and `MemLp _ 2`
of `MemForceR`), and specialized to the `s = 1/2`, `q = 1` case R43 needs.

## What is *not* here (G2 and the homogeneous half of G3)

The homogeneous twin `Data.forceHomogeneousENorm 1 (1/2) f ≠ ⊤` and the
path-level monotonicity `Data.forceHomogeneousENorm 1 (1/2) f ≤
Data.forceSobolevENormL1 (1/2) f` (G2, `04-whole-space.tex:132`) both require a
*homogeneous* datum for a general `H^∞` slice, i.e. an `L²`-multiplier
`ξ ↦ |ξ|^{1/2}(1+|ξ|²)^{-1/4}` applied to the inhomogeneous datum, together with
the identification of `angularFourierDistribution ∘ angularRealization` supplied
by `Paper3.weightedAngularFourier_realization`
(`Paper3/AngularFourierDilation.lean:192`).  The only in-tree homogeneous-datum
constructions (`Section4.D01.Homogeneous.exists_isHomogeneousSliceDatum`,
`isHomogeneousSliceDatum_compact`) cover Schwartz / compactly supported fields
only.  That multiplier construction is genuinely new Fourier analysis beyond
order monotonicity; per the task's fallback it is left as a recorded gap
(`research/D01/ATTEMPTS_HALFORDER.md`).
-/

noncomputable section

open MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source NSFormalization.Source.RealSobolev
open scoped ContDiff SchwartzMap ENNReal

namespace NSFormalization.Section4.D01

open NSFormalization.Section4.A03
  (lowerDatum coe_lowerDatum lowerConst lowerConst_pos norm_lowerDatum_le
    IsScalarSobolevDatum isSobolevDatum_iff)

/-! ## 1. Order lowering as a continuous linear map on the datum carriers

`A03.lowerDatum` is `Paper3.angularOrderLowering` corestricted to the reality
subspace.  It is `ℝ`-linear (the underlying `angularOrderLowering` is a
`ContinuousLinearMap`) and a `lowerConst`-bounded map (`A03.norm_lowerDatum_le`),
hence a `ContinuousLinearMap`; this is the form under which it transports
`MemLp` of a datum path. -/

/-- `A03.lowerDatum` as an `ℝ`-linear map on the scalar real Sobolev carrier. -/
def lowerDatumLM (s r : ℝ) (hrs : r ≤ s) : RealSobolevHilbert s →ₗ[ℝ] RealSobolevHilbert r where
  toFun := lowerDatum s r hrs
  map_add' A B := by
    refine Subtype.ext ?_
    rw [coe_lowerDatum]
    simp only [AddMemClass.coe_add, map_add, coe_lowerDatum]
  map_smul' c A := by
    refine Subtype.ext ?_
    rw [coe_lowerDatum]
    simp only [SetLike.val_smul, ContinuousLinearMap.map_smul_of_tower, coe_lowerDatum,
      RingHom.id_apply]

/-- `A03.lowerDatum` as a `ContinuousLinearMap`, with the operator bound
`A03.lowerConst`. -/
def lowerDatumL (s r : ℝ) (hrs : r ≤ s) : RealSobolevHilbert s →L[ℝ] RealSobolevHilbert r :=
  LinearMap.mkContinuous (lowerDatumLM s r hrs) (lowerConst s r)
    (fun A => norm_lowerDatum_le s r hrs A)

@[simp] theorem lowerDatumL_apply (s r : ℝ) (hrs : r ≤ s) (A : RealSobolevHilbert s) :
    lowerDatumL s r hrs A = lowerDatum s r hrs A := rfl

/-- Componentwise order lowering of a real three-vector datum, as a
`ContinuousLinearMap`, mirroring `Paper3.cyclesToAngularRealVector`
(`Paper3/AngularRealVectorBochner.lean:14`). -/
def lowerVectorL (s r : ℝ) (hrs : r ≤ s) : RealVectorSobolev s →L[ℝ] RealVectorSobolev r :=
  (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin 3 => RealSobolevHilbert r)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : Fin 3 =>
      (lowerDatumL s r hrs).comp
        ((ContinuousLinearMap.proj i).comp
          (PiLp.continuousLinearEquiv 2 ℝ
            (fun _ : Fin 3 => RealSobolevHilbert s)).toContinuousLinearMap)))

@[simp] theorem lowerVectorL_apply (s r : ℝ) (hrs : r ≤ s) (A : RealVectorSobolev s) (i : Fin 3) :
    lowerVectorL s r hrs A i = lowerDatum s r hrs (A i) := rfl

/-! ## 2. The order-lowered datum path -/

/-- Order lowering of a datum **path**: if `G` is the order-`s` datum path of `f`
then `lowerVectorL s r hrs ∘ G` is its order-`r` datum path, `r ≤ s`.
`Section4.D01.IsSobolevPath` is `Contracts.V1.Data.IsSobolevPath` (`Data.lean:174`). -/
theorem isSobolevPath_lower {s r : ℝ} (hrs : r ≤ s) {f : VelocityField}
    {G : ℝ → RealVectorSobolev s} (hG : IsSobolevPath s f G) :
    IsSobolevPath r f (fun t => lowerVectorL s r hrs (G t)) := by
  intro t ht
  rw [isSobolevDatum_iff]
  intro i
  rw [lowerVectorL_apply]
  exact ((isSobolevDatum_iff s _ (G t)).mp (hG t ht) i).lower hrs

/-! ## 3. The finiteness of the half-order force norms

The `Contracts.V1.Data.forceSobolevENorm` infimum (`Data.lean:225`) has no local
copy in tree, so it is restated here verbatim; the `bochnerDatumENorm` it uses is
the existing local copy `Section4.D01.Homogeneous.bochnerDatumENorm`
(`HomogeneousWitness.lean:620`), and `IsSobolevPath` / `forceTimeMeasure` are the
`ForceClass.lean:152,147` copies.  A `verification/Bindings`-style `rfl` bridge
to `Data.forceSobolevENorm` is discharged in `research/D01/axioms_halforder.lean`. -/

/-- `Contracts.V1.Data.forceSobolevENorm` (`Data.lean:225`), restated verbatim:
`‖f‖_{L^q(0,∞;H^s(R³))}` as the infimum over strongly measurable order-`s` datum
paths of their Bochner `L^q_t` norm. -/
def forceSobolevENorm (q : ℝ≥0∞) (s : ℝ) (f : VelocityField) : ℝ≥0∞ :=
  ⨅ G : {G : ℝ → RealVectorSobolev s //
      IsSobolevPath s f G ∧ AEStronglyMeasurable G forceTimeMeasure},
    Homogeneous.bochnerDatumENorm q s G.1

/-- `Contracts.V1.Data.forceSobolevENormL1` (`Data.lean:231`), restated: the
`q = 1` case, `‖f‖_{L¹_t H^s_x}`. -/
abbrev forceSobolevENormL1 (s : ℝ) (f : VelocityField) : ℝ≥0∞ :=
  forceSobolevENorm 1 s f

/-- **G3, inhomogeneous half.**  On a force `f ∈ 𝓕_ℝ`, the order-`s` time norm is
finite for every real `s` bounded by an integer `m` and every `q ∈ {1, 2}`,
because the order-`m` datum path (which `MemForceR` supplies with finite `L¹_t`
and `L²_t` norms) lowers to an order-`s` datum path of no larger norm.  Hence the
smallness hypotheses of Propositions 4.3/4.4 are not vacuously satisfied. -/
theorem forceSobolevENorm_ne_top {f : VelocityField} (hf : MemForceR f)
    {s : ℝ} {m : ℕ} (hsm : s ≤ (m : ℝ)) {q : ℝ≥0∞} (hq : q = 1 ∨ q = 2) :
    forceSobolevENorm q s f ≠ ⊤ := by
  obtain ⟨_, hforce⟩ := hf
  obtain ⟨G, hpath, _hcd, hL1, hL2⟩ := hforce m
  have hLq : MemLp G q forceTimeMeasure := by rcases hq with h | h <;> (subst h; assumption)
  have hmem : MemLp (fun t => lowerVectorL (m : ℝ) s hsm (G t)) q forceTimeMeasure :=
    (lowerVectorL (m : ℝ) s hsm).comp_memLp' hLq
  have hpath' : IsSobolevPath s f (fun t => lowerVectorL (m : ℝ) s hsm (G t)) :=
    isSobolevPath_lower hsm hpath
  have hle : forceSobolevENorm q s f ≤
      Homogeneous.bochnerDatumENorm q s (fun t => lowerVectorL (m : ℝ) s hsm (G t)) :=
    iInf_le (fun G : {G : ℝ → RealVectorSobolev s //
        IsSobolevPath s f G ∧ AEStronglyMeasurable G forceTimeMeasure} =>
      Homogeneous.bochnerDatumENorm q s G.1) ⟨_, hpath', hmem.aestronglyMeasurable⟩
  refine ne_top_of_le_ne_top ?_ hle
  show eLpNorm (fun t => lowerVectorL (m : ℝ) s hsm (G t)) q forceTimeMeasure ≠ ⊤
  exact hmem.eLpNorm_lt_top.ne

/-- **G3 for R43**: the `L¹_t H^{1/2}_x` force norm of Proposition 4.3's smallness
hypothesis is finite on `𝓕_ℝ`.  The `s = 1/2 ≤ 1 = m`, `q = 1` case of
`forceSobolevENorm_ne_top`. -/
theorem forceSobolevENormL1_half_ne_top {f : VelocityField} (hf : MemForceR f) :
    forceSobolevENormL1 (1 / 2) f ≠ ⊤ :=
  forceSobolevENorm_ne_top hf (m := 1) (by norm_num) (Or.inl rfl)

/-- The `L²_t H^{1/2}_x` companion, the `q = 2` case, finite for the same reason. -/
theorem forceSobolevENormL2_half_ne_top {f : VelocityField} (hf : MemForceR f) :
    forceSobolevENorm 2 (1 / 2) f ≠ ⊤ :=
  forceSobolevENorm_ne_top hf (m := 1) (by norm_num) (Or.inr rfl)

end NSFormalization.Section4.D01
