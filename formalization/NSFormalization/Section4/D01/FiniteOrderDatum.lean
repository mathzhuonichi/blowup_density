import NSFormalization.Section4.D01.LerayLowering

/-!
# The finite-order angular Sobolev datum: the order-raising step (unit D01 · C1b-m-D)

`research/A01/C1B_SPLIT.md` row **C1b-m-D** is the carrier bridge's real blocker: D01 has an
order-`0` datum constructor from a bare `MemLp` field (`OrderZeroDatum.orderZeroDatum`) and an
**all-orders** constructor from a `SmoothL2Field` (`SmoothDatum.smoothAngularDatum`), but *nothing
in between* — no constructor that takes a field of finite regularity (`MemLp 2` plus `L²`
derivatives up to order `m`) to an order-`m` datum.  This module supplies the **order-raising
step** of that finite-order constructor, together with the pointwise symbol bound and the
`L²`-assembly lemma its analytic hypothesis reduces to.

## What is proved here

`IsSobolevDatum` (restated in `SmoothDatum.lean` from `Contracts.V1.Data.lean:160`) says that
`A i : RealSobolevHilbert s` realizes the physical component `z · i` under `angularRealization s`.
The order-`s` weight `(1+‖ξ‖²)^{s/2}` lives *inside* `angularRealization s`; the same physical
field at order `s` and at order `s+1` corresponds to two *different* raw-frequency `L²` functions,
related by the multiplication operator `angularOrderLowering (s+1) s`, which multiplies the raw
Fourier datum by `sobolevBesselWeight (-1) ξ = (1+‖ξ‖²)^{-1/2}` (`Leray.angularOrderLowering_coeFn'`).
Lowering the order is bounded; **raising it is not** — the raised datum
`(1+‖ξ‖²)^{1/2}·(A i)` lies in `L²` only when the field has one more order of regularity.  This is
exactly why C1b-m-D is a real-analysis gap and not a normalization question (`C1B_SPLIT.md` §0).

The order-raising step is stated with that `L²` membership supplied as an explicit witness
(`RaisableWitness`):

* `isSobolevDatum_raise` — **the induction step.**  Given an order-`s` datum `A` of `z` and, for
  each component, the witness that `(1+‖ξ‖²)^{1/2}·(A i)` is square integrable, the componentwise
  raised element is an order-`(s+1)` datum of `z`.  No smoothness, no compact support, no `L¹`
  hypothesis; the raised datum realizes the *same* tempered distribution
  (`angularRealization_raiseHilbert`, from `Paper3.angularRealization_orderLowering`), so it is a
  datum of the same field.  The **vector order-`m` Plancherel isometry** that
  `OrderZeroDatum.lean:40-53` records as absent is **not** needed: existence of the datum does not
  need a norm identity.

* `raisableWitness_of_memLp_smul` — **the analytic assembly.**  The raising witness follows once
  each coordinate-multiplied datum `ξ ↦ (ξ j)·(A i)(ξ)` is square integrable, by dominating
  `‖(1+‖ξ‖²)^{1/2}·(A i)(ξ)‖ ≤ ‖(A i)(ξ)‖ + ∑ⱼ ‖(ξ j)·(A i)(ξ)‖` (the symbol bound below) with a
  sum of `L²` functions (`MemLp.mono'`).

* the pointwise symbol bound (`sqrt_one_add_normSq_le`, `norm_raiseIntegrand_le`): the
  induction-friendly comparison `(1+‖ξ‖²)^{1/2} ≤ 1 + ∑ⱼ |ξ j|`, from `‖ξ‖² ≤ (∑ⱼ|ξ j|)²`.

## The residual gap (C1b-m-D, still open)

What remains, to close C1b-m-D from an order-`m` datum of each `∂ⱼz`, is the **raw-frequency
Fourier identity** `(ξ j)·(A i) =ᵐ (convention constant)·(datum of ∂ⱼz)ᵢ` — the `a.e.`,
raw-multiplier form of `DerivativeDatum.isSobolevDatum_partialDeriv`
(`DerivativeDatum.lean:245`).  That module has the identity only in *operator/distribution* form
(`Paper3.angularRealization_directionalDerivative`, smoothness-free but not at the coeFn level) and
only for a `SmoothL2Field`.  Feeding its raw-multiplier form into `raisableWitness_of_memLp_smul`
would discharge the witness hypothesis and turn `isSobolevDatum_raise` into the full order-by-order
constructor.  See `research/D01/FINITE_ORDER_SPLIT.md` rows D-b / D-d2.

## Conventions

Manuscript angular normalization throughout, carried by `Paper3.angularRealization`; reality is the
conjugate-reflection symmetry of `Source.RealSobolev.realSubspace`
(`01-introduction.tex:91,94`, `02-preliminaries.tex:72`).  `sobolevBesselWeight s ξ = (1+‖ξ‖²)^{s/2}`
(`SobolevHilbertModel.lean:24`).  No norm identity is used, so no `(2π)` constant appears.
-/

noncomputable section

namespace NSFormalization.Section4.D01

open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source NSFormalization.Source.RealSobolev
open NSFormalization.Section4.D01.Leray (angularOrderLowering_coeFn')
open scoped ENNReal ComplexConjugate

/-! ## 1. The pointwise symbol bound (row D-c)

`(1+‖ξ‖²)^{1/2} ≤ 1 + ∑ⱼ |ξ j|`, the induction-friendly comparison between the inhomogeneous
Bessel weight of one order and the first-order homogeneous symbols. -/

/-- The norm of the first-order Bessel weight is `(1+‖ξ‖²)^{1/2}`. -/
theorem norm_sobolevBesselWeight_one (ξ : Space) :
    ‖sobolevBesselWeight 1 ξ‖ = Real.sqrt (1 + ‖ξ‖ ^ 2) := by
  rw [sobolevBesselWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), Real.sqrt_eq_rpow]

/-- The first-order Bessel weight is continuous (needed for measurability of the raised
integrand). -/
theorem continuous_sobolevBesselWeight_one : Continuous (sobolevBesselWeight 1) := by
  unfold sobolevBesselWeight
  refine Complex.continuous_ofReal.comp (Continuous.rpow_const ?_ ?_)
  · fun_prop
  · intro ξ; exact Or.inl (by positivity : (0 : ℝ) < 1 + ‖ξ‖ ^ 2).ne'

/-- **The symbol bound (row D-c).**  `(1+‖ξ‖²)^{1/2} ≤ 1 + ∑ⱼ |ξ j|`.  Mathlib's japanese-bracket
bound `sqrt_one_add_norm_sq_le` gives `√(1+‖ξ‖²) ≤ 1 + ‖ξ‖`, and the tree's
`EulerMeanCutoffCurl.norm_le_sum_coordinates` gives `‖ξ‖ ≤ ∑ⱼ |ξ j|` (lane-125 review, finding 4:
this replaces the original `nlinarith` route on `∑(ξ j)² ≤ (∑|ξ j|)²`). -/
theorem sqrt_one_add_normSq_le (ξ : Space) :
    Real.sqrt (1 + ‖ξ‖ ^ 2) ≤ 1 + ∑ j : Fin 3, |ξ j| :=
  (sqrt_one_add_norm_sq_le ξ).trans
    (by gcongr; exact EulerMeanCutoffCurl.norm_le_sum_coordinates ξ)

/-- **The raised-integrand domination (row D-c).**  Pointwise, the raised datum integrand is bounded
by the datum plus its coordinate multiples: `‖(1+‖ξ‖²)^{1/2}·w‖ ≤ ‖w‖ + ∑ⱼ |ξ j| · ‖w‖`. -/
theorem norm_raiseIntegrand_le (h : FourierData) (ξ : Space) :
    ‖sobolevBesselWeight 1 ξ • (h : Space → ℂ) ξ‖
      ≤ ‖(h : Space → ℂ) ξ‖ + ∑ j : Fin 3, |ξ j| * ‖(h : Space → ℂ) ξ‖ := by
  rw [norm_smul, norm_sobolevBesselWeight_one, ← Finset.sum_mul]
  have h1 := mul_le_mul_of_nonneg_right (sqrt_one_add_normSq_le ξ) (norm_nonneg ((h : Space → ℂ) ξ))
  rwa [add_mul, one_mul] at h1

/-! ## 2. The raising witness and its analytic assembly (rows D-d1 hyp · D-d2 reduction)

`RaisableWitness h` is the single analytic input of the order-raising step: the raised datum
`(1+‖ξ‖²)^{1/2}·h` is square integrable.  `raisableWitness_of_memLp_smul` reduces it to the
square integrability of each coordinate multiple `ξ ↦ (ξ j)·h(ξ)`. -/

/-- The order-raising witness: `(1+‖ξ‖²)^{1/2}·h(ξ)` is square integrable.  This is precisely the
"one more order of regularity" of the field, packaged on the raw Fourier datum. -/
def RaisableWitness (h : FourierData) : Prop :=
  MemLp (fun ξ => sobolevBesselWeight 1 ξ • (h : Space → ℂ) ξ) 2 volume

/-- **The analytic assembly (row D-d2 reduction).**  The raising witness for `h` holds as soon as
each coordinate-multiplied datum `ξ ↦ (ξ j)·h(ξ)` is square integrable: dominate the raised
integrand (`norm_raiseIntegrand_le`) by the `L²` sum of `h` and its coordinate multiples. -/
theorem raisableWitness_of_memLp_smul (h : FourierData)
    (hcoord : ∀ j : Fin 3, MemLp (fun ξ => (ξ j : ℂ) • (h : Space → ℂ) ξ) 2 volume) :
    RaisableWitness h := by
  have hhL2 : MemLp (fun ξ => (h : Space → ℂ) ξ) 2 volume := Lp.memLp h
  set F : Space → ℝ :=
    fun ξ => ‖(h : Space → ℂ) ξ‖ + ∑ j : Fin 3, ‖(ξ j : ℂ) • (h : Space → ℂ) ξ‖ with hF
  have hsum : MemLp (fun ξ => ∑ j : Fin 3, ‖(ξ j : ℂ) • (h : Space → ℂ) ξ‖) 2 volume := by
    simp only [Fin.sum_univ_three]
    exact ((hcoord 0).norm.add (hcoord 1).norm).add (hcoord 2).norm
  have hFmem : MemLp F 2 volume := hhL2.norm.add hsum
  have haesm : AEStronglyMeasurable
      (fun ξ => sobolevBesselWeight 1 ξ • (h : Space → ℂ) ξ) volume :=
    continuous_sobolevBesselWeight_one.aestronglyMeasurable.smul (Lp.aestronglyMeasurable h)
  refine MemLp.mono' hFmem haesm ?_
  filter_upwards with ξ
  rw [hF]
  refine (norm_raiseIntegrand_le h ξ).trans (le_of_eq ?_)
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]

/-! ## 3. The order-raising step (row D-d1 · the induction step)

Given an order-`s` datum of `z` and the raising witnesses, produce an order-`(s+1)` datum of `z`.
This is `DerivativeDatum.isSobolevDatum_partialDeriv` run *in reverse* — order lowering by
multiplication by `(1+‖ξ‖²)^{-1/2}` is inverted on its domain, which is where the witness bites. -/

/-- The raised element lies in the reality subspace: `(1+‖ξ‖²)^{1/2}` is a real, even multiplier, so
it commutes with conjugate reflection and preserves conjugate symmetry.  (`realSubspace` does not
depend on the order, so orders `s` and `s+1` share the subspace.) -/
theorem raise_mem {s : ℝ} (a : RealSobolevHilbert s) (hg : RaisableWitness (a : FourierData)) :
    (hg.toLp _) ∈ realSubspace (s + 1) := by
  rw [mem_realSubspace_iff]
  apply Lp.ext
  have hqmp : Measure.QuasiMeasurePreserving (fun ξ : Space => -ξ) volume volume :=
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving
  have hHeq : (realSymmetry (a : FourierData) : Space → ℂ)
      =ᵐ[volume] ((a : FourierData) : Space → ℂ) := by
    rw [(mem_realSubspace_iff s _).mp (SetLike.coe_mem a)]
  filter_upwards [realSymmetry_ae (hg.toLp _), hg.coeFn_toLp, hqmp.ae hg.coeFn_toLp,
    realSymmetry_ae (a : FourierData), hHeq] with ξ eSg eg egN eSh eHeq
  rw [eSg, egN, eg, smul_eq_mul, map_mul, smul_eq_mul]
  have hconjh : (starRingEnd ℂ) (((a : FourierData) : Space → ℂ) (-ξ))
      = ((a : FourierData) : Space → ℂ) ξ := by rw [← eSh, eHeq]
  rw [hconjh]
  have hw : (starRingEnd ℂ) (sobolevBesselWeight 1 (-ξ)) = sobolevBesselWeight 1 ξ := by
    simp [sobolevBesselWeight, norm_neg]
  rw [hw]

/-- Raise a real angular Sobolev datum element by one order, given the `L²` raising witness. -/
def raiseHilbert {s : ℝ} (a : RealSobolevHilbert s) (hg : RaisableWitness (a : FourierData)) :
    RealSobolevHilbert (s + 1) :=
  ⟨hg.toLp _, raise_mem a hg⟩

@[simp] theorem coe_raiseHilbert {s : ℝ} (a : RealSobolevHilbert s)
    (hg : RaisableWitness (a : FourierData)) :
    ((raiseHilbert a hg : RealSobolevHilbert (s + 1)) : FourierData) = hg.toLp _ := rfl

/-- **The raised datum realizes the same tempered distribution.**  Lowering the raised element back
to order `s` recovers `a` (the raising is an exact right inverse of the order-`(s+1)→s` lowering on
its domain), and `Paper3.angularRealization_orderLowering` says lowering preserves the realized
distribution. -/
theorem angularRealization_raiseHilbert {s : ℝ} (a : RealSobolevHilbert s)
    (hg : RaisableWitness (a : FourierData)) :
    angularRealization (s + 1) ((raiseHilbert a hg : RealSobolevHilbert (s + 1)) : FourierData) =
      angularRealization s (a : FourierData) := by
  rw [coe_raiseHilbert]
  have hlow : angularOrderLowering (s + 1) s (by linarith) (hg.toLp _) = (a : FourierData) := by
    apply Lp.ext
    filter_upwards [angularOrderLowering_coeFn' (s + 1) s (by linarith) (hg.toLp _), hg.coeFn_toLp]
      with ξ e1 e2
    rw [e1, e2, smul_smul]
    have hmul : sobolevBesselWeight (s - (s + 1)) ξ * sobolevBesselWeight 1 ξ = 1 := by
      have := congrFun (sobolevBesselWeight_mul (s - (s + 1)) 1) ξ
      simp only [Pi.mul_apply] at this
      rw [this]; norm_num [sobolevBesselWeight]
    rw [hmul, one_smul]
  rw [← angularRealization_orderLowering (s + 1) s (by linarith) (hg.toLp _), hlow]

/-- **The order-raising step (row D-d1, the induction step of the finite-order constructor).**  If
`A` is an order-`s` angular real-vector Sobolev datum of `z` and each component has the `L²`
raising witness, then the componentwise raised element is an order-`(s+1)` datum of `z`.  No
smoothness, no compact support, no `L¹`; no vector Plancherel isometry (existence of the datum needs
no norm identity).  This is the reverse of `DerivativeDatum.isSobolevDatum_partialDeriv`; combined
with the raw-frequency Fourier identity (the residual gap) it is the missing finite-order
constructor `C1b-m-D`. -/
theorem isSobolevDatum_raise {s : ℝ} {z : Space → Space} {A : RealVectorSobolev s}
    (hA : IsSobolevDatum s z A) (hg : ∀ i : Fin 3, RaisableWitness ((A i : FourierData))) :
    IsSobolevDatum (s + 1) z (WithLp.toLp 2 (fun i => raiseHilbert (A i) (hg i))) := by
  intro i ψ
  have hcoe : ((WithLp.toLp 2 (fun i => raiseHilbert (A i) (hg i)) : RealVectorSobolev (s + 1)) i
      : FourierData) = ((raiseHilbert (A i) (hg i) : RealSobolevHilbert (s + 1)) : FourierData) := rfl
  rw [hcoe, angularRealization_raiseHilbert (A i) (hg i)]
  exact hA i ψ

end NSFormalization.Section4.D01
