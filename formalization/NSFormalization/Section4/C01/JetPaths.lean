import NSFormalization.Section4.C01.MomentumCarrierB
import NSFormalization.Section4.C01.Evolution
import Euler.SmoothEulerEvolution

/-!
# C01 unit E4a — the time-continuous carrier-B jet paths of the momentum residual

Lane `146-C01-jet-paths`, sub-row **E4a** of `research/C01/ENERGY_SPLIT.md`.  This is
the cheap half of the route-(a) programme for row **E4** identified in
`research/C01/REVIEW_E3E4.md` §6(c): the momentum equation of a classical solution
`w : ClassicalSolutionR ν a f T` is

  `∂ₜu = f − (u·∇)u + νΔu − ∇p`   (`D01.temporalDerivative_slice_eq`, `Pressure.lean:196`),

so the *derivative path* `s ↦ ∂ₜu(s,·)` that row E4 (and E5) must feed to
`EulerOrdinarySobolev.wordEnergy_hasDerivWithinAt` splits as

  `∂ₜu = h − ∇p`,   `h := f − (u·∇)u + νΔu`   (the **momentum residual**).

Over a compact subwindow `[0,S] ⊂ [0,T)` (`S < T`), this module builds the three
`SmoothL2Field`-valued paths on the right and proves each has **jets continuous in
time** — the hypothesis `hB` of the vendor energy machinery.  It does **not** build
the `∇p` leg (a genuine analysis obligation booked as E4b; see
`research/C01/ATTEMPTS_JET_PATHS.md`).

## What is proved here

Index type is `Icc (0:ℝ) S`, mirroring `velocityField`.

* `forcePath hf` / `forcePath_jetLp_continuous` — the force slice path `f(t,·)`, and
  its jet-continuity, the line-by-line mirror of `velocityField_jetLp_continuous`
  using `MemForceR`'s datum path (whose `ContDiffOn ℝ ∞ G futureTimes` is **stronger**
  than the velocity's `ContinuousOn`).
* `advectionPath w hST` / `advectionPath_jetLp_continuous` — the advection path
  `(u·∇)u`, jet-continuity by instantiating the vendor fact
  `EulerSmoothEulerEvolution.advection_jet_continuous` (`SmoothEulerEvolution.lean:29`)
  at the velocity path and transporting jets across the field equality with
  `EulerLpSmoothCoefficientProduct.jetLp_congr`.
* `sumField_jetLp_continuous` / `laplacianField_jetLp_continuous` — a general
  `sumField`/Laplacian jet-continuity, mirroring the `SmoothL2Field ℂ` versions of
  `Source.PhysicalBesselSobolev` (`:83,105`, which cannot be instantiated at `Space`);
  the Laplacian is `sumField Finset.univ` of a double `directionalField`, so it
  composes `continuous_jetLp_directionalField` (`LpSmoothFieldAlgebra.lean:147`) twice
  with `continuous_jetLp_addField` over `Finset.univ (Fin 3)`.
* `laplacianPath w hST` / `laplacianPath_jetLp_continuous`, and the `ν`-scaled
  `viscousPath w hST` / `viscousPath_jetLp_continuous` (via
  `mapField (ν • id)` and `continuous_jetLp_mapField`, `LpSmoothFieldAlgebra.lean:119`).
* `residualPath w hf hST` / `residualPath_jetLp_continuous` — the momentum residual
  `f − (u·∇)u + νΔu` as an `SmoothL2Field` path with jets continuous in time, together
  with the pointwise field identity `residualPath_field` and, at interior times,
  `temporalDerivative_eq_residual_sub_pressureGradient`:
  `∂ₜu(t,·) = residualPath t − ∇p(t,·)`.

## What is *not* closed here (row E4b)

The remaining E4 obligation is the **jet-continuity in time of `∇p(s,·)`** (equivalently
of `∂ₜu(s,·)`).  It is *not* an assembly of the paths above: `∇p = (I−P)h` at the datum
level, so its continuity needs a *two-directional bridge* between "carrier-B jets
continuous in `t`" and "an order-`m` datum path continuous in `t`", pushed through the
Leray complement CLM `D01.Leray.lerayComplement`.  The precise obligation, and the tree
lemmas that exist for each direction, are recorded in
`research/C01/ATTEMPTS_JET_PATHS.md`.
-/

noncomputable section

open Set MeasureTheory
open EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerSmoothLimit
open NSFormalization.Source.OrdinaryViscousStability
open ContinuousLinearMap
open NavierStokes.ProblemStatement (temporalDerivative advection spatialLaplacian pressureGradient)
open scoped ContDiff

namespace NSFormalization.Section4.C01

open NSFormalization.Section4.A02 (ClassicalSolutionR MemForceR)

variable {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField} {S T : ℝ}

/-! ## 1. The force path and its jet continuity -/

/-- **The force path.**  The force slice `f(t,·)` over the compact slab `[0,S]`, as a
path of carrier-B `SmoothL2Field Space`, from `forceSliceField` (D01
`forceSlice_smoothL2_of_memForceR`).  Independent of any solution and of `S < T`: the
force is smooth with `L²` jets on all of `[0,∞)`. -/
def forcePath (hf : MemForceR f) (t : Icc (0 : ℝ) S) : SmoothL2Field Space :=
  forceSliceField hf t.2.1

@[simp] theorem forcePath_field (hf : MemForceR f) (t : Icc (0 : ℝ) S) :
    (forcePath hf t).field = fun x => f (t.1, x) := rfl

/-- **The force jet-continuity, the `hB`-shape clause for the force leg.**  Each
order-`n` `L²` jet of the force path is continuous in time.  Line-by-line mirror of
`velocityField_jetLp_continuous`: `MemForceR`'s order-`n` datum path `G_n` is
`ContDiffOn ℝ ∞` on `futureTimes = Ici 0` (stronger than the velocity's `ContinuousOn`),
`D01.jetOfDatum n n` reconstructs the order-`n` jet from it continuously
(`jetOfDatum_continuous`) and equals `jetLp n` as an `Lp` element by
`D01.jetOfDatum_ae`. -/
theorem forcePath_jetLp_continuous (hf : MemForceR f) (n : ℕ) :
    Continuous (fun t : Icc (0 : ℝ) S => (forcePath hf t).jetLp n) := by
  obtain ⟨G, hpath, hGc, _, _⟩ := hf.2 n
  have hkey : (fun t : Icc (0 : ℝ) S => (forcePath hf t).jetLp n)
      = fun t : Icc (0 : ℝ) S => D01.jetOfDatum n n (le_refl n) (G t.1) := by
    funext t
    apply Lp.ext
    exact (((forcePath hf t).integrable n).coeFn_toLp).trans
      (D01.jetOfDatum_ae (le_refl n) (forcePath hf t).smooth (hpath t.1 t.2.1)).symm
  rw [hkey]
  exact (jetOfDatum_continuous n n (le_refl n)).comp
    (hGc.continuousOn.comp_continuous continuous_subtype_val fun t => t.2.1)

/-! ## 2. The advection path and its jet continuity -/

/-- **The advection path.**  The nonlinear term `(u·∇)u` over the slab, as the vendor
carrier-B field `advectionField` of the velocity path with itself. -/
def advectionPath (w : ClassicalSolutionR ν a f T) (hST : S < T) (t : Icc (0 : ℝ) S) :
    SmoothL2Field Space :=
  advectionField (velocityField w hST t) (velocityField w hST t)

/-- The advection path is the manuscript `advection u`: `(advectionPath …).field x =
advection u t x` (`rfl` after `advectionField_field`, both being
`fderiv u(t,·) x (u(t,x))`). -/
theorem advectionPath_field (w : ClassicalSolutionR ν a f T) (hST : S < T)
    (t : Icc (0 : ℝ) S) (x : Space) :
    (advectionPath w hST t).field x = advection w.velocity t.1 x := by
  rw [advectionPath, advectionField_field]
  rfl

/-- **The advection jet-continuity.**  Each order-`n` `L²` jet of the advection path is
continuous in time.  The vendor's `EulerSmoothEulerEvolution.advection` of the velocity
path has the same field (`advection_field` = `advectionField_field` at `A = B = u`), so
its jets agree by `EulerLpSmoothCoefficientProduct.jetLp_congr`, and its jet-continuity
is `EulerSmoothEulerEvolution.advection_jet_continuous` (`SmoothEulerEvolution.lean:29`)
fed the velocity jet-continuity `velocityField_jetLp_continuous`. -/
theorem advectionPath_jetLp_continuous (w : ClassicalSolutionR ν a f T) (hST : S < T)
    (n : ℕ) :
    Continuous (fun t : Icc (0 : ℝ) S => (advectionPath w hST t).jetLp n) := by
  have hU := velocityField_jetLp_continuous w hST
  have hkey : (fun t : Icc (0 : ℝ) S => (advectionPath w hST t).jetLp n)
      = fun t => (EulerSmoothEulerEvolution.advection (velocityField w hST) hU t).jetLp n := by
    funext t
    apply EulerLpSmoothCoefficientProduct.jetLp_congr
    funext x
    rw [advectionPath, advectionField_field, EulerSmoothEulerEvolution.advection_field]
  rw [hkey]
  exact EulerSmoothEulerEvolution.advection_jet_continuous (velocityField w hST) hU n

/-! ## 3. Laplacian jet continuity: a general `sumField` tool, then the paths -/

/-- **General `sumField` jet-continuity.**  If every summand path has jets continuous in
time then so does their finite `sumField`.  This is the `SmoothL2Field V` (any `V`)
generalisation of `Source.PhysicalBesselSobolev.continuous_jetLp_sumField` (`:83`), which
is stated only for `SmoothL2Field ℂ` and so cannot be instantiated at `Space`.  Proof by
`Finset` induction, using `continuous_jetLp_addField` (`LpSmoothFieldAlgebra.lean:128`)
at each step and `field_ext` to peel one summand.  Named `sumField_jetLp_continuous` (not
`continuous_jetLp_sumField`) so that a module which `open`s both this namespace and
`Source.PhysicalBesselSobolev` sees no bare-name clash with the `ℂ` version (LESSONS-109). -/
theorem sumField_jetLp_continuous {K ι : Type*} [TopologicalSpace K]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (I : Finset ι) (A : ι → K → SmoothL2Field V)
    (hA : ∀ i n, Continuous (fun t => (A i t).jetLp n)) (n : ℕ) :
    Continuous (fun t => (sumField I (fun i => A i t)).jetLp n) := by
  classical
  induction I using Finset.induction_on generalizing n with
  | empty =>
    have he (t : K) : sumField ∅ (fun i => A i t) = (zeroField : SmoothL2Field V) := by
      apply field_ext
      funext x
      simp [sumField_field, zeroField]
    simp_rw [he]
    exact continuous_const
  | @insert i I hi ih =>
    have he (t : K) : sumField (insert i I) (fun j => A j t) =
        addField (A i t) (sumField I (fun j => A j t)) := by
      apply field_ext
      funext x
      simp [sumField_field, addField_field, Finset.sum_insert hi]
    simp_rw [he]
    exact continuous_jetLp_addField _ _ (hA i) ih n

/-- **General Laplacian jet-continuity.**  If a path has jets continuous in time, so does
its `laplacianField` (`OrdinaryViscousStability.lean:12`, `sumField Finset.univ` of the
double directional derivative), by `sumField_jetLp_continuous` fed
`continuous_jetLp_directionalField` (`LpSmoothFieldAlgebra.lean:147`) applied twice.
Mirror of `Source.PhysicalBesselSobolev.continuous_jetLp_laplacianField` (`:105`) for
`SmoothL2Field Space`. -/
theorem laplacianField_jetLp_continuous {K : Type*} [TopologicalSpace K]
    (A : K → SmoothL2Field Space) (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) (n : ℕ) :
    Continuous (fun t => (laplacianField (A t)).jetLp n) := by
  apply sumField_jetLp_continuous
  intro i m
  exact continuous_jetLp_directionalField _
    (continuous_jetLp_directionalField A hA (axis i)) (axis i) m

/-- **The Laplacian path.**  `Δu` over the slab, as the vendor carrier-B `laplacianField`
of the velocity path. -/
def laplacianPath (w : ClassicalSolutionR ν a f T) (hST : S < T) (t : Icc (0 : ℝ) S) :
    SmoothL2Field Space :=
  laplacianField (velocityField w hST t)

/-- The Laplacian path is the manuscript `spatialLaplacian u`, from `laplacianField_field`
(`= Δ u.field`) and `EulerMeanVectorIdentities.vector_laplacian_eq_sum`. -/
theorem laplacianPath_field (w : ClassicalSolutionR ν a f T) (hST : S < T)
    (t : Icc (0 : ℝ) S) (x : Space) :
    (laplacianPath w hST t).field x = spatialLaplacian w.velocity t.1 x := by
  rw [laplacianPath, laplacianField_field,
    congrFun (EulerMeanVectorIdentities.vector_laplacian_eq_sum
      (velocityField w hST t).field (velocityField w hST t).smooth) x]
  rfl

/-- **The Laplacian jet-continuity.** -/
theorem laplacianPath_jetLp_continuous (w : ClassicalSolutionR ν a f T) (hST : S < T)
    (n : ℕ) :
    Continuous (fun t : Icc (0 : ℝ) S => (laplacianPath w hST t).jetLp n) :=
  laplacianField_jetLp_continuous (fun t => velocityField w hST t)
    (velocityField_jetLp_continuous w hST) n

/-! ## 4. The `ν`-scaled Laplacian (viscous) path -/

/-- **The viscous path.**  `νΔu` over the slab, as `mapField (ν • id)` of the Laplacian
path (the vendor scaling of `OrdinaryViscousUniqueness.lean:16`).  `ν` is fixed by the
solution `w : ClassicalSolutionR ν a f T`. -/
def viscousPath (w : ClassicalSolutionR ν a f T) (hST : S < T) (t : Icc (0 : ℝ) S) :
    SmoothL2Field Space :=
  mapField (ν • ContinuousLinearMap.id ℝ Space) (laplacianPath w hST t)

@[simp] theorem viscousPath_field (w : ClassicalSolutionR ν a f T) (hST : S < T)
    (t : Icc (0 : ℝ) S) (x : Space) :
    (viscousPath w hST t).field x = ν • spatialLaplacian w.velocity t.1 x := by
  rw [viscousPath, mapField_field, smul_apply, ContinuousLinearMap.id_apply,
    laplacianPath_field]

/-- **The viscous jet-continuity**, via `continuous_jetLp_mapField`
(`LpSmoothFieldAlgebra.lean:119`). -/
theorem viscousPath_jetLp_continuous (w : ClassicalSolutionR ν a f T) (hST : S < T)
    (n : ℕ) :
    Continuous (fun t : Icc (0 : ℝ) S => (viscousPath w hST t).jetLp n) :=
  continuous_jetLp_mapField _ _ (laplacianPath_jetLp_continuous w hST) n

/-! ## 5. The momentum residual path -/

/-- **The momentum residual path** `h := f − (u·∇)u + νΔu` over the slab, as an
`SmoothL2Field Space` path (vendor `fieldSub`/`addField` of the force, advection and
viscous paths). -/
def residualPath (w : ClassicalSolutionR ν a f T) (hf : MemForceR f) (hST : S < T)
    (t : Icc (0 : ℝ) S) : SmoothL2Field Space :=
  addField (fieldSub (forcePath hf t) (advectionPath w hST t)) (viscousPath w hST t)

/-- The residual path's representative is the manuscript momentum residual
`f(t,·) − advection u t + ν • spatialLaplacian u t` pointwise. -/
theorem residualPath_field (w : ClassicalSolutionR ν a f T) (hf : MemForceR f) (hST : S < T)
    (t : Icc (0 : ℝ) S) (x : Space) :
    (residualPath w hf hST t).field x
      = f (t.1, x) - advection w.velocity t.1 x + ν • spatialLaplacian w.velocity t.1 x := by
  rw [residualPath, addField_field, fieldSub_field, forcePath_field,
    advectionPath_field, viscousPath_field]

/-- **The residual jet-continuity, `hB` for the residual leg.**  Each order-`n` `L²` jet
of the residual path is continuous in time, from the three component jet-continuities via
`continuous_jetLp_addField` and the negation `mapField`. -/
theorem residualPath_jetLp_continuous (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    (hST : S < T) (n : ℕ) :
    Continuous (fun t : Icc (0 : ℝ) S => (residualPath w hf hST t).jetLp n) := by
  refine continuous_jetLp_addField _ _ ?_ (viscousPath_jetLp_continuous w hST) n
  intro m
  refine continuous_jetLp_addField (fun t => forcePath hf t)
    (fun t => fieldNeg (advectionPath w hST t)) (forcePath_jetLp_continuous hf) ?_ m
  intro k
  exact continuous_jetLp_mapField _ _ (advectionPath_jetLp_continuous w hST) k

/-- **The derivative-path split at interior times (the E4a payoff).**  At an interior
time `t.1 ∈ (0,T)`, the time derivative of the velocity is the momentum residual minus
the pressure gradient: `∂ₜu(t,·) = residualPath t − ∇p(t,·)` pointwise.  This is
`D01.temporalDerivative_slice_eq` (`Pressure.lean:196`) rewritten through
`residualPath_field`; it exhibits the derivative path `s ↦ ∂ₜu(s,·)` that row E4 owes as
`residualPath − (the ∇p path booked as E4b)`. -/
theorem temporalDerivative_eq_residual_sub_pressureGradient
    (w : ClassicalSolutionR ν a f T) (hf : MemForceR f) (hST : S < T)
    (t : Icc (0 : ℝ) S) (htpos : 0 < t.1) (x : Space) :
    temporalDerivative w.velocity t.1 x
      = (residualPath w hf hST t).field x - pressureGradient w.pressure t.1 x := by
  have ht : t.1 ∈ Ioo (0 : ℝ) T := ⟨htpos, lt_of_le_of_lt t.2.2 hST⟩
  rw [residualPath_field, D01.temporalDerivative_slice_eq w ht x]

end NSFormalization.Section4.C01
