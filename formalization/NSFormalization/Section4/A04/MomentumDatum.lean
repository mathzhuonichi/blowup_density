import NSFormalization.Section4.A04.TimeDerivative
import NSFormalization.Section4.D01.Pressure
import NSFormalization.Section4.A03.VectorTameProduct

/-!
# A04 unit G1, sub-lemma SL2: the momentum equation in datum form

`research/A04/G1_SPLIT.md` sub-lemma **SL2**.  The energy identity eq:Rhigh
(`Spec.lean` `energyIdentityHigh`) pairs the projected momentum equation
`∂ₜu = νΔu − (u·∇)u − ∇p + f` against `u` in `H^m`, on the D01 datum carrier
`RealVectorSobolev (m:ℝ)`.  SL2 is the transport of that pointwise equation to the
carrier: with `G` the D1 datum path of `u`, `deriv G t` (the abstract Hilbert-space
time derivative, identified by SL1/D2 with the datum of `∂ₜu(t,·)`) equals
`ν • L − N − P + F`, where `L, N, P, F` are the order-`m` data of `Δu(t,·)`,
`(u·∇)u(t,·)`, `∇p(t,·)`, `f(t,·)`.

This is exactly the `hmom` hypothesis `inner_energy_assembly` / `inner_energy_Rhigh`
(`Section4/A04/HighEnergy.lean`, SL8) consume: instantiated at
`E = RealVectorSobolev (m:ℝ)` with `Gt := deriv G t`, `momentum_datum` is the
proof of `hmom` with no glue (see `research/A04/axioms_sl2.lean`).

## The route

The residual field `NavierStokesR3.ProblemStatement.navierStokesResidual`
(`vendor/…/NavierStokes/R3/ProblemStatement.lean:57`) is
`∂ₜu + (u·∇)u − νΔu + ∇p`; `ClassicalSolutionR.momentum` sets it equal to `f`.
`D01.temporalDerivative_slice_eq` (`D01/Pressure.lean`) is that residual rearranged,
`∂ₜu = f − (u·∇)u + νΔu − ∇p`, one `abel`.  Since `deriv (fun r => u(r,x)) t` is
*definitionally* `temporalDerivative u t x` (both `fderiv ℝ (fun r => u(r,x)) t 1`),
the datum-side field of D2 is literally the momentum residual.

The proof then reads:

* **SL1/D2** (`timeDeriv_isSobolevDatum`) gives `deriv G t` is the datum of
  `x ↦ ∂ₜu(t,x)`.
* **datum linearity** builds `ν • L − N − P + F` as the datum of the rearranged
  right-hand side `x ↦ νΔu − (u·∇)u − ∇p + f`, through the vector
  `isSobolevDatum_smul` (added below), `A03.isSobolevDatum_sub` and
  `A03.isSobolevDatum_add`.  The local-integrability side conditions of the A03
  algebra are discharged from `A03.locIntField_of_memLp` and the `MemLp` of each
  slice (`D01.memLp_of_isSobolevDatum` on the slice's smoothness and its datum),
  the slices being smooth by `D01.laplacian_slice_smoothL2`,
  `D01.advection_slice_smoothL2`, `D01.contDiff_pressureGradient_slice` and
  `D01.forceSlice_smoothL2_of_memForceR`.
* **uniqueness** (`A03.IsSobolevDatum.unique`, D01 unit L1): the two data of the
  one field agree, so `deriv G t = ν • L − N − P + F`.

## Hypotheses beyond `2 ≤ m`

* `MemForceR f` — needed only to make the force slice `f(t,·)` smooth (hence
  `MemLp`), through `D01.forceSlice_smoothL2_of_memForceR`.
* `hP : IsSobolevDatum m (∇p(t,·)) P` — the **pressure datum at order `m`**, the
  D01 obligation **P2** that `D01/Pressure.lean` documents is *not* available
  unconditionally from `ClassicalSolutionR` (it is the Leray-regularity gap
  L9(c)).  Taken as an explicit hypothesis, exactly as C01 does.  `L, N, F` and
  their datum hypotheses are likewise taken as inputs so that the same `L, N, P, F`
  feed the other G1 sub-lemmas (SL3's `hlap`, SL4's `hpr`, SL7's `hF` norm); they
  could instead be constructed from the class through
  `D01.memHInfty_iff_smoothSquareIntegrableJets` and the slice lemmas above.

## Datum-linearity lemmas

`A03.isSobolevDatum_add` / `A03.isSobolevDatum_sub` (vector) and
`A03.IsSobolevDatum.unique` already exist.  The scalar-multiple companion
`isSobolevDatum_smul` was **absent** and is added here (scalar helper
`isScalarSobolevDatum_smul`, vector `isSobolevDatum_smul`), together with the
negation `isSobolevDatum_neg`.  The scalar `smul` is proved from the raw datum
definition: `Paper3.angularRealization` is `ℂ`-linear, so a real scalar passes
through it by `LinearMapClass.map_smul_of_tower`, and the physical side scales by
`MeasureTheory.integral_smul`; no `2 ≤ s` and no local integrability are needed
(unlike the additive lemmas, which pin the bounded representative).

## Reuse

`timeDeriv_isSobolevDatum` is A04's (SL1/D2); `laplacian_slice_smoothL2`,
`advection_slice_smoothL2`, `forceSlice_smoothL2_of_memForceR`,
`contDiff_pressureGradient_slice`, `memLp_of_isSobolevDatum`,
`temporalDerivative_slice_eq` are D01's; `isSobolevDatum_iff`,
`IsSobolevDatum.component`, `IsSobolevDatum.unique`, `isSobolevDatum_add`,
`isSobolevDatum_sub`, `locIntField_of_memLp`, `IsScalarSobolevDatum` are A03's;
`angularRealization`, `RealVectorSobolev`, `RealSobolevHilbert`, `FourierData` are
Paper3/`Source.RealSobolev`'s; `ClassicalSolutionR`, `MemForceR`, `SpaceTimeField`,
`SpatialField` are A02's.  Nothing is copied.
-/

noncomputable section

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source.RealSobolev
open scoped ContDiff ENNReal Topology

namespace NSFormalization.Section4.A04

open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR MemForceR)
open NSFormalization.Section4.D01
  (IsSobolevDatum memLp_of_isSobolevDatum contDiff_pressureGradient_slice
   laplacian_slice_smoothL2 advection_slice_smoothL2 forceSlice_smoothL2_of_memForceR
   temporalDerivative_slice_eq)
open NSFormalization.Section4.A03
  (IsScalarSobolevDatum isSobolevDatum_iff IsSobolevDatum.component IsSobolevDatum.unique
   isSobolevDatum_add isSobolevDatum_sub locIntField_of_memLp)

/-! ## 1. Scalar multiplication of Sobolev data

The additive datum lemmas (`A03.isScalarSobolevDatum_add/sub`) already exist; the
scalar multiple by a real constant does not.  It is proved from the raw datum
definition, which is why it needs neither `2 ≤ s` nor local integrability: the
distributional side scales because `angularRealization` is `ℂ`-linear (real
scalar through `LinearMapClass.map_smul_of_tower`), the physical side because the
Bochner integral is `ℝ`-linear (`integral_smul`). -/

/-- **The datum of a real scalar multiple, scalar case.**  `c • A` is the order-`s`
datum of `c · a`. -/
theorem isScalarSobolevDatum_smul {s : ℝ} (c : ℝ) {a : Space → ℝ} {A : RealSobolevHilbert s}
    (hA : IsScalarSobolevDatum s a A) :
    IsScalarSobolevDatum s (fun x => c * a x) (c • A) := by
  intro ψ
  show angularRealization s ((c • A : RealSobolevHilbert s) : FourierData) ψ = _
  have hco : ((c • A : RealSobolevHilbert s) : FourierData)
      = c • ((A : RealSobolevHilbert s) : FourierData) := rfl
  rw [hco, LinearMapClass.map_smul_of_tower, smul_apply, hA ψ, ← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Complex.real_smul]
  push_cast
  ring

/-- **The datum of a real scalar multiple, vector case.**  `c • A` is the order-`s`
datum of `x ↦ c • F x`.  Componentwise from `isScalarSobolevDatum_smul`
(`(c • F x) i = c · F x i`, `(c • A) i = c • A i`). -/
theorem isSobolevDatum_smul {s : ℝ} (c : ℝ) {F : Space → Space} {A : RealVectorSobolev s}
    (hA : IsSobolevDatum s F A) : IsSobolevDatum s (fun x => c • F x) (c • A) := by
  refine (isSobolevDatum_iff s _ (c • A)).mpr (fun i => ?_)
  show IsScalarSobolevDatum s (fun x => c * F x i) (c • A i)
  exact isScalarSobolevDatum_smul c (IsSobolevDatum.component hA i)

/-- **The datum of a negation, scalar case.**  `-A` is the order-`s` datum of `-a`
(`c = -1`). -/
theorem isScalarSobolevDatum_neg {s : ℝ} {a : Space → ℝ} {A : RealSobolevHilbert s}
    (hA : IsScalarSobolevDatum s a A) : IsScalarSobolevDatum s (fun x => - a x) (- A) := by
  simpa using isScalarSobolevDatum_smul (-1 : ℝ) hA

/-- **The datum of a negation, vector case.**  `-A` is the order-`s` datum of
`x ↦ - F x`. -/
theorem isSobolevDatum_neg {s : ℝ} {F : Space → Space} {A : RealVectorSobolev s}
    (hA : IsSobolevDatum s F A) : IsSobolevDatum s (fun x => - F x) (- A) := by
  simpa using isSobolevDatum_smul (-1 : ℝ) hA

/-! ## 2. SL2: the momentum equation in datum form -/

/-- **SL2 — the momentum equation in datum form.**  On a forced viscous classical
solution `w` with a real admissible force `f`, for `2 ≤ m`, a `C^∞`-in-time datum
path `G` of the velocity slices, and an interior time `t`:

`deriv G t = ν • L − N − P + F`   in `RealVectorSobolev (m:ℝ)`,

where `L, N, P, F` are the order-`m` data of the Laplacian slice `Δu(t,·)`, the
advection slice `(u·∇)u(t,·)`, the pressure-gradient slice `∇p(t,·)` and the force
slice `f(t,·)`.  This is the `hmom` hypothesis of `inner_energy_assembly` /
`inner_energy_Rhigh` at `Gt := deriv G t`.

The pressure datum `hP` is the D01 obligation **P2**, unavailable unconditionally
(the Leray-regularity gap), so it is an explicit hypothesis; `hL`, `hN`, `hF` are
inputs too, shared with the other G1 sub-lemmas.  `MemForceR f` is used only for
the smoothness (hence `MemLp`) of the force slice. -/
theorem momentum_datum
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {m : ℕ} (hm : 2 ≤ m)
    {G : ℝ → RealVectorSobolev (m : ℝ)}
    (hGd : ∀ t ∈ Ico (0 : ℝ) T, IsSobolevDatum (m : ℝ) (fun x => w.velocity (t, x)) (G t))
    (hGc : ContDiffOn ℝ ∞ G (Ico (0 : ℝ) T))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    {L N P F : RealVectorSobolev (m : ℝ)}
    (hL : IsSobolevDatum (m : ℝ) (fun x => spatialLaplacian w.velocity t x) L)
    (hN : IsSobolevDatum (m : ℝ) (fun x => advection w.velocity t x) N)
    (hP : IsSobolevDatum (m : ℝ) (fun x => pressureGradient w.pressure t x) P)
    (hF : IsSobolevDatum (m : ℝ) (fun x => f (t, x)) F) :
    deriv G t = ν • L - N - P + F := by
  have hsR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  -- SL1/D2: `deriv G t` is the datum of `x ↦ ∂ₜu(t,x)`.
  have hderiv := (timeDeriv_isSobolevDatum w hm hGd hGc ht).2
  -- smoothness (hence `MemLp`) of each physical slice
  have hcL := (laplacian_slice_smoothL2 w ht).1
  have hcN := (advection_slice_smoothL2 w ht).1
  have hcP := contDiff_pressureGradient_slice w.pressure_smooth ⟨le_of_lt ht.1, ht.2⟩
  have hcF := (forceSlice_smoothL2_of_memForceR hf (le_of_lt ht.1)).1
  have mL := memLp_of_isSobolevDatum hcL hL
  have mN := memLp_of_isSobolevDatum hcN hN
  have mP := memLp_of_isSobolevDatum hcP hP
  have mF := memLp_of_isSobolevDatum hcF hF
  have mνL : MemLp (fun x => ν • spatialLaplacian w.velocity t x) 2 volume := mL.const_smul ν
  -- datum linearity: `ν • L − N − P + F` is a datum of the rearranged RHS
  have dνL : IsSobolevDatum (m : ℝ) (fun x => ν • spatialLaplacian w.velocity t x) (ν • L) :=
    isSobolevDatum_smul ν hL
  have d1 := isSobolevDatum_sub hsR (locIntField_of_memLp mνL) (locIntField_of_memLp mN) dνL hN
  have m1 : MemLp
      (fun x => ν • spatialLaplacian w.velocity t x - advection w.velocity t x) 2 volume :=
    mνL.sub mN
  have d2 := isSobolevDatum_sub hsR (locIntField_of_memLp m1) (locIntField_of_memLp mP) d1 hP
  have m2 : MemLp (fun x => ν • spatialLaplacian w.velocity t x - advection w.velocity t x
      - pressureGradient w.pressure t x) 2 volume := m1.sub mP
  have d3 := isSobolevDatum_add hsR (locIntField_of_memLp m2) (locIntField_of_memLp mF) d2 hF
  -- the rearranged RHS is `x ↦ ∂ₜu(t,x)` (momentum, `abel`), and
  -- `deriv (fun r => u(r,x)) t` is definitionally `temporalDerivative u t x`
  have hM : IsSobolevDatum (m : ℝ)
      (fun x => deriv (fun r => w.velocity (r, x)) t) (ν • L - N - P + F) := by
    have hfield : (fun x : Space => deriv (fun r => w.velocity (r, x)) t)
        = (fun x : Space => ν • spatialLaplacian w.velocity t x - advection w.velocity t x
            - pressureGradient w.pressure t x + f (t, x)) := by
      funext x
      show temporalDerivative w.velocity t x = _
      rw [temporalDerivative_slice_eq w ht x]; abel
    rw [hfield]; exact d3
  -- uniqueness (D01 unit L1)
  exact IsSobolevDatum.unique hderiv hM

end NSFormalization.Section4.A04
