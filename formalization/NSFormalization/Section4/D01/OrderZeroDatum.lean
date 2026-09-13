import NSFormalization.Section4.D01.SmoothDatum

/-!
# The order-0 Plancherel seed (unit D01 / P2 sub-lemma SL7a)

`Contracts.V1.Data.IsSobolevDatum` (restated at `SmoothDatum.lean` as
`NSFormalization.Section4.D01.IsSobolevDatum`) says that a real Euclidean three-vector
field `z` *has* the order-`s` angular Sobolev datum `A` when the tempered distribution
`angularRealization s (A i)` pairs with every Schwartz test exactly as the physical
component `z · i`.

`SmoothDatum.exists_isSobolevDatum_of_contDiff_memLp` produces such a datum at every real
order, but only from a field all of whose spatial jets are square integrable
(`SmoothL2Field`); it therefore cannot *seed* order 0 from a bare `L²` field.  This module
supplies the missing entry point:

```
MemLp z 2 volume → ∃ A : RealVectorSobolev 0, IsSobolevDatum 0 z A
```

with no smoothness, no compact support and — crucially — **no `L¹` hypothesis**.  This is
what lets P2 seed a datum for `∇p` from `ClassicalSolutionR.pressure_gradient`
(order-0 `MemLp` only), and it is the missing constructor for I03 U7c.  The datum is
produced by the explicit `orderZeroDatum hz` and proved to realize `z` by
`isSobolevDatum_orderZeroDatum`; `exists_isSobolevDatum_zero_of_memLp` is the `∃` corollary.

## Route

At order `0` the Sobolev weight `(1+‖ξ‖²)^0` is trivial, so `Paper3.sobolevRealization_zero`
identifies the cycles-convention realization with Mathlib's genuine `L²` inverse Fourier
transform embedded in distributions, with no `L¹` assumption.  The order-0 cycles datum of a
component is therefore its `L²` Fourier transform `𝓕 (componentLp hz i)`
(`MeasureTheory.Lp.fourierTransformₗᵢ`).  The transform of a real-valued `L²` function is
conjugate-symmetric — `SmoothDatum.fourier_conjugation`, proved by density with no `L¹`
hypothesis — so it lies in `Source.RealSobolev.realSubspace`, and
`Paper3.cyclesToAngularReal` transports it to the manuscript's angular convention without
changing the physical distribution.  The three components are assembled with
`Paper3.cyclesToAngularRealVector`, and `Lp.toTemperedDistribution_apply` closes the pairing.

## Scope: the norm identity is NOT proved here

This module proves only the *realization* (`IsSobolevDatum`), i.e. existence of the datum.
The Plancherel **norm identity** `‖orderZeroDatum hz‖ = ‖z‖_{L²}` (which holds with constant
exactly `1` at order `0`) is deliberately **not** proved here.  It is a separate ~25-50-line
item that belongs in `Paper3`, needing two pieces absent from the tree: an order-0 vector
isometry `cyclesToAngularRealVector_symm_norm_le` (only the scalar
`cyclesToAngularReal_symm_norm_le` exists, and the `ofSubmodules`/`restrictScalars`
unification is heartbeat-heavy — hence `AngularRealVectorBochner.lean`'s raised
`maxHeartbeats`), and the Euclidean-valued Pythagorean `L²` identity
`eLpNorm z 2 volume ^ 2 = ∑ i, eLpNorm (fun x => (z x i : ℝ)) 2 volume ^ 2`.  `orderZeroDatum`
is exposed as a named `def` precisely so that identity can be *stated* against it later
(I03 U7c's `sobolevENorm 0 = eLpNorm 2` wants it; `A04/Forcing.lean` `sobolevENorm_eq`
supplies the other half).  `Lp.norm_fourier_eq` (Plancherel, unconditional) is the easy half.
-/

noncomputable section

namespace NSFormalization.Section4.D01

open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source.RealSobolev

variable {z : Space → Space}

/-- The `i`-th real component of a square-integrable field is a complex `L²` function. -/
theorem memLp_component (hz : MemLp z 2 volume) (i : Fin 3) :
    MemLp (fun x : Space => ((z x i : ℝ) : ℂ)) 2 volume :=
  (Complex.ofRealCLM.comp (EuclideanSpace.proj i)).comp_memLp' hz

/-- Its `L²` class in the Fourier-datum carrier. -/
def componentLp (hz : MemLp z 2 volume) (i : Fin 3) : FourierData :=
  (memLp_component hz i).toLp (fun x => ((z x i : ℝ) : ℂ))

theorem componentLp_ae (hz : MemLp z 2 volume) (i : Fin 3) :
    (componentLp hz i : Space → ℂ) =ᵐ[volume] fun x => ((z x i : ℝ) : ℂ) :=
  (memLp_component hz i).coeFn_toLp

/-- A real function equals its own conjugate a.e., so its `L²` class is conjugation-fixed. -/
theorem conjugation_componentLp (hz : MemLp z 2 volume) (i : Fin 3) :
    conjugation (componentLp hz i) = componentLp hz i := by
  apply Lp.ext
  filter_upwards [conjugation_ae (componentLp hz i), componentLp_ae hz i] with x h1 h2
  rw [h1, h2]
  exact Complex.conj_ofReal _

/-- Hence the `L²` Fourier transform of the component is conjugate-symmetric: it lands in the
closed real subspace. -/
theorem fourier_componentLp_mem (hz : MemLp z 2 volume) (i : Fin 3) :
    (𝓕 (componentLp hz i)) ∈ realSubspace 0 := by
  rw [mem_realSubspace_iff, ← fourier_conjugation (componentLp hz i), conjugation_componentLp hz i]

/-- **SL7a — the order-0 datum, exposed.**  The explicit order-0 angular real-vector Sobolev
datum of a square-integrable real Euclidean three-vector field: the componentwise `L²` Fourier
transform, projected into the real subspace and transported to the angular convention. -/
def orderZeroDatum (hz : MemLp z 2 volume) : RealVectorSobolev 0 :=
  cyclesToAngularRealVector 0
    (WithLp.toLp 2 (fun i => realProjectionTo 0 (𝓕 (componentLp hz i))))

/-- **SL7a — the realization.**  `orderZeroDatum hz` pairs with every Schwartz test exactly as
the physical field, i.e. it is the order-0 datum of `z` in the sense of
`Contracts.V1.Data.IsSobolevDatum`.  No smoothness, no compact support, no `L¹` hypothesis. -/
theorem isSobolevDatum_orderZeroDatum (hz : MemLp z 2 volume) :
    IsSobolevDatum 0 z (orderZeroDatum hz) := by
  intro i ψ
  unfold orderZeroDatum
  rw [angularRealization_cyclesToAngularRealVector]
  show sobolevRealization 0 (realProjection (𝓕 (componentLp hz i))) ψ
      = ∫ x : Space, ψ x * ((z x i : ℝ) : ℂ)
  rw [realProjection_eq_self (fourier_componentLp_mem hz i), sobolevRealization_zero,
    fourierInv_fourier_eq, Lp.toTemperedDistribution_apply]
  refine integral_congr_ae ?_
  filter_upwards [componentLp_ae hz i] with x hx
  rw [hx, smul_eq_mul]

/-- **SL7a — the `∃` corollary.**  Every real square-integrable Euclidean three-vector field
has an order-0 angular real-vector Sobolev datum. -/
theorem exists_isSobolevDatum_zero_of_memLp (hz : MemLp z 2 volume) :
    ∃ A : RealVectorSobolev 0, IsSobolevDatum 0 z A :=
  ⟨orderZeroDatum hz, isSobolevDatum_orderZeroDatum hz⟩

end NSFormalization.Section4.D01
