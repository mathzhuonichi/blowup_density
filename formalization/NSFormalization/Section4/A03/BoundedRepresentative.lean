import Euler.EulerProof
import NSFormalization.Section4.A03.SmoothJets

/-!
# `‖z‖_∞ ≤ C‖z‖_{H²}` for smooth fields with square-integrable jets

Second clause of `eq:Rproduct`, Lemma A.1 ("Sobolev multiplication and
embeddings", `lem:calculus`), `paper/sections/appendix-a-local-theory.tex:12`,
restricted to `R³` and stated on the truncated jet class `SmoothL2UpTo 2`
(smooth, with the Fréchet jets of order at most two square integrable), which is
the manuscript's `v ∈ H²` for a smooth field and exactly what the proof route
uses.

Consumers.  `paper/sections/04-whole-space.tex:53` (Theorem 4.2's lifespan step,
"An extension through `T` would be bounded in `C_tH²` on a neighborhood of `T`,
hence bounded in `L^∞_x` by `eq:Rproduct`"), and, composed with an order shift,
the uniqueness coefficient `‖∇u₂‖_∞` of `appendix-a-local-theory.tex:120-123`.

## Route

The manuscript proves the clause by absolute Fourier convergence
(`appendix-a-local-theory.tex:44-50`: Cauchy–Schwarz gives `‖v̂‖₁ ≤ C‖v‖_{H²}`
because `∫_{R³}⟨ξ⟩^{-4}dξ < ∞`, and absolute convergence of the Fourier
inversion integral then bounds `v` pointwise).  The in-tree realization of that
route is `NSFormalization.Paper3.sobolevBoundedRepresentative`
(`formalization/NSFormalization/Paper3/SobolevBoundedRepresentative.lean:34`)
with the constant `NSFormalization.Source.BesselH2Fourier.besselConstant`
(`formalization/NSFormalization/Source/BesselH2Fourier.lean:39`), which is the
manuscript's `(∫⟨ξ⟩^{-4})^{1/2}`.  That route is **not** used here: it lands in
`BoundedContinuousFunction Space ℂ` and is stated about an abstract
`SobolevHilbert` datum, so a consumer holding a physical field must first
produce the datum and then identify the representative with the field.

This module takes the **Fourier-free-in-statement** route instead, exactly as
lane 019 does for Lemma B.1: the pointwise bound is the vendor's
`EulerSmoothSobolev.smooth_pointwise_le_H2`
(`vendor/NavierStokesAndEuler/Euler/EulerProof.lean:8238-8239`), an
everywhere-pointwise estimate for any smooth function into a complex Hilbert
space, with no compact support hypothesis and with the jet `L²` sum
`EulerSmoothSobolev.tensorSobolevNorm 2` on the right.  The real three-vector
case is obtained by the vendor's isometric complexification
`EulerSobolev.complexify 3` (`EulerProof.lean:5600`), which is the same
three-line reduction as the vendor's own real wrapper
`EulerOrdinarySobolev.real_pointwise_H2`
(`vendor/NavierStokesAndEuler/Euler/OrdinaryWordBounds.lean:67`); that wrapper is
reproved here rather than imported because it is phrased on the bundled
`SmoothL2Field` structure and drags in the `Gevrey`/`OrdinarySobolevL4` import
closure, while the three lines below need only `Euler.EulerProof`.

## The norm on the right

`jetENorm 2 z = ∑_{j≤2} ‖ |D^j z| ‖_{L²}` sums, over the three orders `j ≤ 2`,
the `L²` norms of the full Fréchet jets, each jet measured in the *operator*
norm of a `j`-multilinear map on `R³`.  The manuscript **defines** its norm on
the Fourier side: `‖z‖²_{H^s(R³)} = ∫_{R³}(1+|ξ|²)^s|ẑ(ξ)|²dξ`
(`paper/sections/01-introduction.tex:85-86`) for the angular transform
`ẑ(ξ) = (2π)^{-3/2}∫e^{-ix·ξ}z(x)dx` of `:91`, components summed in squares
(`:103`).  Three links, each costing only factors of `3` and `2`, connect the
two:

1. the angular transform is an `L²` isometry and sends `∂^α` to `(iξ)^α` with no
   `2π`, so `∫(1+|ξ|²)^2|ẑ|²` is a fixed positive combination of
   `∑_{|α|≤2}‖∂^αz‖₂²`;
2. for a `j`-multilinear map `T` on `R³`,
   `max_w |T(e_w)| ≤ ‖T‖ ≤ ∑_w |T(e_w)|` over the `3^j` coordinate words `w` of
   length `j` (the right inequality is the vendor's
   `EulerSobolevDerivativeNorm.multilinear_norm_le_coordinate_sum`,
   `vendor/NavierStokesAndEuler/Euler/EulerProof.lean:6202`), and the entries
   `T(e_w)` of `iteratedFDeriv ℝ j z` are the `∂^α z` with `|α| = j`;
3. an `ℓ¹` sum over the three orders `j ≤ 2` is within `√3` of the `ℓ²` sum.

Every factor depends only on the dimension `3` and on the order `2`, which is
what `appendix-a-local-theory.tex:10` allows: `C` depends on the order and the
fixed domain, never on the field.  The constant below is therefore *a* constant
of the manuscript's clause, not the manuscript's numerical value.

No Fourier transform occurs in any *statement* of this file — both sides of
every theorem below are physical-space quantities — so the manuscript's angular
normalization `(2π)^{-3/2}∫e^{-ix·ξ}` (`01-introduction.tex:91`) and Mathlib's
cycles normalization `e^{-2πix·ξ}` cannot differ here.  They do meet in link 1,
which is where the manuscript's own right-hand side lives.  The vendor constant
contains `(2π)^{-2}` internally; only its positivity is exported.
-/

noncomputable section

open MeasureTheory
open NavierStokes.ProblemStatement
open EulerSobolev EulerSmoothSobolev
open scoped ContDiff ENNReal

namespace NSFormalization.Section4.A03

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `paper/sections/01-introduction.tex:94`, the inhomogeneous Sobolev norm of
order `m` in **jet form**: the sum over orders `j ≤ m` of the `L²` norms of the
Fréchet jets.  `ℝ≥0∞`-valued and never routed through `.toReal`, so a field with
a non-square-integrable jet makes it `⊤` rather than making a bound vacuous.

This is the `ℝ≥0∞` counterpart of the vendor's
`EulerSmoothSobolev.tensorSobolevNorm` (`Euler/EulerProof.lean:8090-8092`) and
of `EulerSmoothSobolev.realTensorSobolevNorm` (`:8348-8350`); see the module
docstring for its universal-constant comparison with the manuscript's
`‖·‖_{H^m}`. -/
def jetENorm (m : ℕ) (z : Space → F) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (m + 1), eLpNorm (iteratedFDeriv ℝ j z) 2 volume

/-- The constant `C` of `appendix-a-local-theory.tex:12`
(`‖v‖_∞ ≤ C‖v‖_{H²}`), in the jet normalization of `jetENorm`.  It is the
vendor's `EulerSmoothSobolev.smoothEmbeddingConstant`
(`Euler/EulerProof.lean:8227-8230`) plus one, so that positivity is available
without unfolding `embeddingConstant` and `unitBumpCoefficient`; the vendor
proves that constant nonnegative but not positive.  Same device as
`NSFormalization.Section4.A05.gradientL6Const`. -/
def boundedRepresentativeConst : ℝ := smoothEmbeddingConstant + 1

theorem boundedRepresentativeConst_pos : 0 < boundedRepresentativeConst := by
  have := smoothEmbeddingConstant_nonneg
  simp only [boundedRepresentativeConst]
  linarith

/-- The real three-vector form of the vendor's
`EulerSmoothSobolev.smooth_pointwise_le_H2` (`Euler/EulerProof.lean:8238`),
obtained through the isometric complexification `EulerSobolev.complexify 3`
(`:5600`).  Same reduction as `EulerOrdinarySobolev.real_pointwise_H2`
(`Euler/OrdinaryWordBounds.lean:67`), restated for a bare function instead of a
bundled `SmoothL2Field`.

Only the jets of order `0`, `1` and `2` are used, which is why the hypothesis is
`∀ j ≤ 2` rather than the all-order `SmoothL2`. -/
theorem norm_le_tensorSobolevNorm (z : Space → Space) (hz : ContDiff ℝ ∞ z)
    (hL2 : ∀ j ≤ 2, MemLp (iteratedFDeriv ℝ j z) 2 volume) (x : Space) :
    ‖z x‖ ≤ smoothEmbeddingConstant *
      ∑ j ∈ Finset.range 3, (eLpNorm (iteratedFDeriv ℝ j z) 2 volume).toReal := by
  have hb := smooth_pointwise_le_H2 (complexify 3 ∘ z) ((complexify 3).contDiff.comp hz)
    (fun j hj => complexification_tensor_memLp 3 j z hz (hL2 j hj)) x
  rw [Function.comp_apply, (complexify 3).norm_map,
    complexification_sobolevNorm 3 2 z hz] at hb
  simpa [realTensorSobolevNorm] using hb

/-- On the jet class the `ℝ≥0∞` jet norm is the `ENNReal.ofReal` of the vendor's
real one: every jet of order at most `m` is square integrable, so no summand is
`⊤`.  Only the orders that actually occur in the sum are required, which is why
the hypothesis is `SmoothL2UpTo m` and not `SmoothL2`. -/
theorem ofReal_tensorSobolevNorm (m : ℕ) {z : Space → F} (hz : SmoothL2UpTo m z) :
    ENNReal.ofReal (∑ j ∈ Finset.range (m + 1),
        (eLpNorm (iteratedFDeriv ℝ j z) 2 volume).toReal) = jetENorm m z := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
  refine Finset.sum_congr rfl fun j hj => ?_
  exact ENNReal.ofReal_toReal (hz.jetMemLp (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).eLpNorm_ne_top

/-- `appendix-a-local-theory.tex:12` eq:Rproduct, second clause, in the
**everywhere-pointwise** form: `‖z(x)‖ ≤ C‖z‖_{H²}` at every point of `R³`.

This is the bounded-representative statement of the manuscript with the
representative already discharged: a `SmoothL2UpTo` field is continuous, so it
*is* its own continuous representative and the bound holds at every point, not
merely almost everywhere.

The hypothesis is the truncated class at order two — smooth with the jets of
order `0`, `1` and `2` square integrable — which is what the manuscript assumes
(`v ∈ H²`, plus smoothness in place of the representative) and all the proof
route uses.  `SmoothL2.upTo` recovers the instance for an all-order field. -/
theorem enorm_le_jetENorm {z : Space → Space} (hz : SmoothL2UpTo 2 z) (x : Space) :
    ‖z x‖ₑ ≤ ENNReal.ofReal boundedRepresentativeConst * jetENorm 2 z := by
  set S : ℝ := ∑ j ∈ Finset.range 3, (eLpNorm (iteratedFDeriv ℝ j z) 2 volume).toReal with hS
  have hS0 : (0 : ℝ) ≤ S := Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hp : ‖z x‖ ≤ boundedRepresentativeConst * S :=
    (norm_le_tensorSobolevNorm z hz.contDiff (fun j hj => hz.jetMemLp hj) x).trans
      (mul_le_mul_of_nonneg_right (by simp only [boundedRepresentativeConst]; linarith) hS0)
  calc ‖z x‖ₑ = ENNReal.ofReal ‖z x‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (boundedRepresentativeConst * S) := ENNReal.ofReal_le_ofReal hp
    _ = ENNReal.ofReal boundedRepresentativeConst * jetENorm 2 z := by
        rw [ENNReal.ofReal_mul boundedRepresentativeConst_pos.le,
          ofReal_tensorSobolevNorm 2 hz]

/-- `appendix-a-local-theory.tex:12` eq:Rproduct, second clause, as the
essential-supremum bound `‖z‖_{L^∞(R³)} ≤ C‖z‖_{H²}` that
`paper/sections/04-whole-space.tex:53` consumes.  Immediate from the pointwise
bound, since an everywhere bound is an almost-everywhere bound. -/
theorem eLpNormTop_le_jetENorm {z : Space → Space} (hz : SmoothL2UpTo 2 z) :
    eLpNorm z ⊤ volume ≤ ENNReal.ofReal boundedRepresentativeConst * jetENorm 2 z := by
  rw [eLpNorm_exponent_top, eLpNormEssSup]
  exact essSup_le_of_ae_le _ (Filter.Eventually.of_forall (enorm_le_jetENorm hz))

end NSFormalization.Section4.A03
