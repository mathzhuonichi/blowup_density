import NSFormalization.Section4.A02.SolutionClass
import NSFormalization.Section3.T23.BoxIntegration
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Canonical T23 domain vocabulary, copied verbatim from research/T23/Spec.lean.
The canonical record is shared by boundary integration and uniqueness modules. -/

noncomputable section
namespace NSFormalization.Section3.T23
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NavierStokesR3.ProblemStatement (navierStokesResidual)
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open scoped ContDiff

/-- `03-torus.tex:638-642`: the manuscript's closed-spacetime-slab smoothness
convention — "restriction of a `C∞` field from an open neighborhood of that
slab" (this also fixes smoothness at edges and corners of a box).  Encoded as
the literal restriction: an open `N` covering the slab `I × cl Ω` on which the
(total) field is genuinely `C∞`.

Non-vacuity: `ContDiffOn ℝ ∞ f N` on the open `N` is real smoothness, not the
closed-set `ContDiffOn` on `cl Ω`; it is the honest reading of the convention. -/
def SmoothOnClosedSlab {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : Set ℝ) (Ω : Set Space) (f : SpaceTime → E) : Prop :=
  ∃ N : Set SpaceTime, IsOpen N ∧ I ×ˢ closure Ω ⊆ N ∧ ContDiffOn ℝ ∞ f N

/-- `03-torus.tex:632-634`: concrete regular-level-set encoding of a bounded
smooth domain (adopted from Draft A per `RECONCILIATION.md` §3 "Take from A" 1).
A `C∞` defining function `φ` with `Ω = {φ < 0}` and nonvanishing boundary
gradient.  The box-vs-smooth distinction governs only the *assumed* reference's
elliptic regularity (`:645`), which the corollary takes as a hypothesis; but
statement fidelity (`CLAUDE.md` rule 2) keeps the paper's disjunction.

Non-vacuity: it carries an actual `C∞` defining function and a nonzero boundary
derivative, not an unconstrained proposition; owner question `RECONCILIATION.md`
§4.3 flags this encoding. -/
def IsRegularLevelDomain (Ω : Set Space) : Prop :=
  ∃ φ : Space → ℝ, ContDiff ℝ ∞ φ ∧ Ω = {x | φ x < 0} ∧
    ∀ x ∈ frontier Ω, fderiv ℝ φ x ≠ 0

/-- `03-torus.tex:632-634`: coordinate-box domain (adopted from Draft A).

Non-vacuity: the stored lower and upper corners have strict coordinate
separation, so `Ω` is a genuine open box. -/
def IsBoxDomain (Ω : Set Space) : Prop :=
  ∃ lo hi : Fin 3 → ℝ, (∀ i, lo i < hi i) ∧
    Ω = {x : Space | ∀ i : Fin 3, lo i < x i ∧ x i < hi i}

/-- `03-torus.tex:632-633`: the paper's disjunctive domain class — `Ω ⊂ R³` is a
bounded box or a bounded smooth domain.  Adopted from Draft A's disjunction
(`RECONCILIATION.md` §3 "Take from A" 1), with Draft B's explicit `Ω.Nonempty`
folded in (the smooth branch `{φ < 0}` may be empty; openness already gives
measurability).  The box-vs-smooth disjunction is kept for statement fidelity.

Non-vacuity: a genuine conjunction of openness, boundedness, nonemptiness, and
the honest box-or-smooth disjunction on `Ω`; it is neither `True` nor an
unfolding. -/
def IsBoundedBoxOrSmoothDomain (Ω : Set Space) : Prop :=
  IsOpen Ω ∧ Bornology.IsBounded Ω ∧ Ω.Nonempty ∧
    (IsBoxDomain Ω ∨ IsRegularLevelDomain Ω)

/-- `02-preliminaries.tex:9` and `03-torus.tex:640-644`: the bounded-domain
initial class — smooth on `cl Ω` (slab convention at `t=0`), divergence free in
`Ω`, and no-slip on `∂Ω`.  The torus analogue is `initialClassT`.

Non-vacuity: three concrete clauses; the divergence reuses the registered
`spatialDivergence` of the constant-in-time extension. -/
def initialClassOmega (Ω : Set Space) : Set SpatialField :=
  {a | ContDiffOn ℝ ∞ a (closure Ω) ∧
    (∀ x ∈ Ω, spatialDivergence (fun z : SpaceTime => a z.2) 0 x = 0) ∧
    (∀ x ∈ frontier Ω, a x = 0)}

/-- `03-torus.tex:638-642`: the bounded-domain force class `𝓕(Ω)` — smooth on
`cl Ω × [0,T']` for every finite `T'` (slab convention, "`g` on each finite
closed slab"), with temporal support compact in `(0,∞)`.  The torus analogue is
`MemForceT`; periodicity is dropped and smoothness is over `cl Ω`.

Non-vacuity: the smoothness conjunct is universal over `T'`, and the temporal
support conjunct is a genuine compact-in-`(0,∞)` witness. -/
def MemForceOmega (Ω : Set Space) (f : SpaceTimeField) : Prop :=
  (∀ T' : ℝ, SmoothOnClosedSlab (Icc (0 : ℝ) T') Ω f) ∧
    ∃ K : Set ℝ, IsCompact K ∧ K ⊆ Ioi 0 ∧ tsupport f ⊆ K ×ˢ (univ : Set Space)

/-- `03-torus.tex:638-642`: the bounded-domain reference/inserted force class. -/
def forceClassOmega (Ω : Set Space) : Set SpaceTimeField := {f | MemForceOmega Ω f}

/-! ## 1. Bounded-domain classical no-slip solutions -/

/-- `03-torus.tex:640-648` and `02-preliminaries.tex:28-36`: a classical
no-slip solution of Navier–Stokes on the bounded domain `Ω` over `[0,T)`, at
viscosity `ν`, initial velocity `a`, force `g`, with the equation and
incompressibility holding *in* `Ω`, no-slip on `∂Ω`, and the pressure fixed by
zero spatial mean over `Ω` (`:644`, "Pressure may be normalized by zero spatial
mean").  This is the paper's assumed *compatible reference* (`:648`).

**Structure exception** (`CLAUDE.md`): a genuinely new bounded-domain solution
record, mirroring the registered torus `ClassicalSolutionT`
(`Contracts/V1/TorusLocalTheory.lean`) field-for-field with `univ → cl Ω`,
periodicity/`sobolev` dropped, no-slip added, and the equation restricted to
`Ω`.  The local implementation candidate is
`Paper1/BoundaryCorollary.lean:28` `BoundedReference` / `:42` `BoundedFlow`
(cite only; that module has a `sorry`). -/
structure ClassicalSolutionOmega (ν : ℝ) (Ω : Set Space) (a : SpatialField)
    (g : SpaceTimeField) (T : ℝ) where
  /-- `02-preliminaries.tex:28-36`: the velocity field. -/
  velocity : SpaceTimeField
  /-- `02-preliminaries.tex:28,84-88` and `03-torus.tex:644`: the scalar
  pressure, ultimately fixed by the zero-`Ω`-mean gauge. -/
  pressure : SpaceTimeScalar
  /-- `02-preliminaries.tex:32-36`: the horizon is a genuine positive
  interval.  Non-vacuity: a strict inequality. -/
  horizon_pos : 0 < T
  /-- `03-torus.tex:637-643`: velocity smoothness on `[0,T) × cl Ω` in the
  slab-neighborhood convention.  Non-vacuity: `SmoothOnClosedSlab` gives a real
  open-neighborhood `C∞` extension. -/
  velocity_smooth : SmoothOnClosedSlab (Ico (0 : ℝ) T) Ω velocity
  /-- `03-torus.tex:637-643`: pressure smoothness on the same slab. -/
  pressure_smooth : SmoothOnClosedSlab (Ico (0 : ℝ) T) Ω pressure
  /-- `01-introduction.tex:4-7` and `03-torus.tex:634-646`: `u(0,·)=a` on `Ω`.
  Exact quantifier order: `∀ x ∈ Ω`.  Non-vacuity: pointwise equality of
  physical vectors on the domain. -/
  initial : ∀ x ∈ Ω, velocity (0, x) = a x
  /-- `03-torus.tex:643` "incompressibility hold in `Ω`": `div u = 0` in `Ω`.
  Exact quantifier order: `∀ t ∈ Ico 0 T, ∀ x ∈ Ω`.  Non-vacuity: the
  registered physical divergence vanishes pointwise. -/
  divergence : ∀ t ∈ Ico (0 : ℝ) T, ∀ x ∈ Ω, spatialDivergence velocity t x = 0
  /-- `03-torus.tex:644` "The equation … hold in `Ω`": the momentum equation at
  interior times, inside `Ω`.  Exact quantifier order: `∀ t ∈ Ioo 0 T,
  ∀ x ∈ Ω`.  Non-vacuity: the NS residual equals `g` pointwise at `ν`. -/
  momentum : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ Ω,
    navierStokesResidual ν velocity pressure t x = g (t, x)
  /-- `03-torus.tex:644` "`v|_{∂Ω}=0`": no-slip on the boundary.  Exact
  quantifier order: `∀ t ∈ Ico 0 T, ∀ x ∈ frontier Ω`.  Non-vacuity: the
  velocity vanishes pointwise on `∂Ω = frontier Ω`. -/
  no_slip : ∀ t ∈ Ico (0 : ℝ) T, ∀ x ∈ frontier Ω, velocity (t, x) = 0
  /-- `03-torus.tex:644`: the pressure gauge `∫_Ω p(t)=0`.  Exact quantifier
  order: `∀ t ∈ Ico 0 T`.  Non-vacuity: an actual set-integral equation over
  `Ω`. -/
  pressure_gauge : ∀ t ∈ Ico (0 : ℝ) T, (∫ x in Ω, pressure (t, x)) = 0


/-- The slab-neighborhood convention gives ordinary smooth spatial derivatives,
including at boundary points and at time zero. -/
theorem SmoothOnClosedSlab.contDiffAt_slice
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Set ℝ} {Ω : Set Space} {f : SpaceTime → E}
    (hf : SmoothOnClosedSlab I Ω f) {t : ℝ} (ht : t ∈ I)
    {x : Space} (hx : x ∈ closure Ω) :
    ContDiffAt ℝ ∞ (fun y => f (t, y)) x := by
  obtain ⟨N, hN, hsub, hs⟩ := hf
  exact (hs.contDiffAt (hN.mem_nhds (hsub ⟨ht, hx⟩))).comp x
    (contDiffAt_const.prodMk contDiffAt_id)

/-- Compact-domain smoothness supplies the integrability needed by the real
Bochner energy integral; no integrability premise is added to the solution. -/
theorem difference_energy_integrable {ν T₁ T₂ : ℝ} {Ω : Set Space}
    {a : SpatialField} {g : SpaceTimeField}
    (hΩ : Bornology.IsBounded Ω)
    (u₁ : ClassicalSolutionOmega ν Ω a g T₁)
    (u₂ : ClassicalSolutionOmega ν Ω a g T₂)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) (min T₁ T₂)) :
    IntegrableOn (fun x => ‖u₁.velocity (t, x) - u₂.velocity (t, x)‖ ^ 2) Ω := by
  have h₁ : ContinuousOn (fun x => u₁.velocity (t, x)) (closure Ω) := fun x hx =>
    (u₁.velocity_smooth.contDiffAt_slice ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩ hx).continuousAt.continuousWithinAt
  have h₂ : ContinuousOn (fun x => u₂.velocity (t, x)) (closure Ω) := fun x hx =>
    (u₂.velocity_smooth.contDiffAt_slice ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_right _ _)⟩ hx).continuousAt.continuousWithinAt
  exact (((h₁.sub h₂).norm.pow 2).integrableOn_compact hΩ.isCompact_closure).mono_set
    subset_closure

/-- On an open domain, continuous velocities with zero squared L² difference
agree pointwise. This is the final measure-to-pointwise step, not uniqueness. -/
theorem eqOn_of_integral_norm_sub_sq_eq_zero {Ω : Set Space} (hΩ : IsOpen Ω)
    {v w : Space → Space} (hv : ContinuousOn v Ω) (hw : ContinuousOn w Ω)
    (hi : IntegrableOn (fun x => ‖v x - w x‖ ^ 2) Ω)
    (hz : (∫ x in Ω, ‖v x - w x‖ ^ 2) = 0) : EqOn v w Ω := by
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖v x - w x‖) hi).mp hz
  have heq : v =ᵐ[volume.restrict Ω] w := by
    filter_upwards [hae] with x hx
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hx))
  exact Measure.eqOn_open_of_ae_eq heq hΩ hv hw

/-- A classical solution has a single spatial derivative bound on every compact
subslab. The constant is obtained from the raw neighborhood-smoothness field. -/
theorem ClassicalSolutionOmega.spatialDerivative_bound
    {ν T : ℝ} {Ω : Set Space} {a : SpatialField} {g : SpaceTimeField}
    (u : ClassicalSolutionOmega ν Ω a g T) (hΩ : Bornology.IsBounded Ω)
    {S : ℝ} (hS : S < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) S, ∀ x ∈ closure Ω,
      ‖spatialDerivative u.velocity t x‖ ≤ C := by
  obtain ⟨N, hN, hsub, hu⟩ := u.velocity_smooth
  have hsub' : Icc (0 : ℝ) S ×ˢ closure Ω ⊆ N := by
    intro z hz
    exact hsub ⟨⟨hz.1.1, lt_of_le_of_lt hz.1.2 hS⟩, hz.2⟩
  have hc : ContinuousOn (fderiv ℝ u.velocity) (Icc (0 : ℝ) S ×ˢ closure Ω) :=
    (hu.continuousOn_fderiv_of_isOpen hN (by simp)).mono hsub'
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hΩ.isCompact_closure).exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ht x hx
  have hd := ((hu.contDiffAt (hN.mem_nhds (hsub' ⟨ht, hx⟩))).differentiableAt
    (by simp)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  change ‖fderiv ℝ (u.velocity ∘ fun y => (t, y)) x‖ ≤ _
  rw [hd.fderiv]
  calc
    ‖(fderiv ℝ u.velocity (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ Space)‖ ≤
        ‖fderiv ℝ u.velocity (t, x)‖ * ‖ContinuousLinearMap.inr ℝ ℝ Space‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ C := by simpa only [ContinuousLinearMap.norm_inr, mul_one] using hC (t, x) ⟨ht, hx⟩
    _ ≤ max C 0 := le_max_left _ _

/-- Boundary integration by parts for scalar C¹ fields. This is the sole
missing domain-specific analytic input for regular-level domains; boxes are
proved below. Smoothness means ordinary neighborhood smoothness at every
point of the closure, and only the first factor must vanish on the frontier. -/
def IBP (Ω : Set Space) : Prop :=
  ∀ (f g : Space → ℝ),
    (∀ x ∈ closure Ω, ContDiffAt ℝ 1 f x) →
    (∀ x ∈ closure Ω, ContDiffAt ℝ 1 g x) →
    (∀ x ∈ frontier Ω, f x = 0) → ∀ j : Fin 3,
    (∫ x in Ω, f x * fderiv ℝ g x (coordinateVector j)) =
      -(∫ x in Ω, fderiv ℝ f x (coordinateVector j) * g x)

/-- The Spec's open Euclidean boxes satisfy boundary integration by parts. -/
theorem ibp_box {Ω : Set Space} (hΩ : IsBoxDomain Ω) : IBP Ω := by
  obtain ⟨a, b, hab, rfl⟩ := hΩ
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  let U : Set (Fin 3 → ℝ) := Set.univ.pi (fun i => Ioo (a i) (b i))
  let Ω : Set Space := {x | ∀ i, a i < x i ∧ x i < b i}
  have heU : e ⁻¹' Ω = U := by ext x; simp [e, Ω, U]
  have hcl : closure U = Icc a b := by
    simp only [U, closure_pi_set, closure_Ioo (hab _).ne, pi_univ_Icc]
  have hecl : e ⁻¹' closure Ω = Icc a b := by
    exact (e.toHomeomorph.preimage_closure Ω).trans ((congrArg closure heU).trans hcl)
  have hefr : e ⁻¹' frontier Ω = frontier U := by
    exact (e.toHomeomorph.preimage_frontier Ω).trans (congrArg frontier heU)
  have hfr : frontier (Icc a b) ⊆ frontier U := by
    rw [← hcl]
    exact frontier_closure_subset
  have hint (F : Space → ℝ) :
      (∫ x in Ω, F x) = ∫ y in Icc a b, F (e y) := by
    rw [← (PiLp.volume_preserving_toLp (Fin 3)).setIntegral_preimage_emb
      e.toHomeomorph.measurableEmbedding F Ω]
    change (∫ y in e ⁻¹' Ω, F (e y)) = _
    rw [heU]
    exact setIntegral_congr_set Measure.univ_pi_Ioo_ae_eq_Icc
  intro f g hf hg hz j
  have hc (q : Space → ℝ) (hq : ∀ x ∈ closure Ω, ContDiffAt ℝ 1 q x) :
      ∀ y ∈ Icc a b, ContDiffAt ℝ 1 (q ∘ e) y := by
    intro y hy
    exact (hq (e y) (show y ∈ e ⁻¹' closure Ω by rwa [hecl])).comp y e.contDiff.contDiffAt
  have hd (q : Space → ℝ) (hq : ∀ x ∈ closure Ω, ContDiffAt ℝ 1 q x)
      (y : Fin 3 → ℝ) (hy : y ∈ Icc a b) :
      fderiv ℝ (q ∘ e) y (Pi.single j 1) = fderiv ℝ q (e y) (coordinateVector j) := by
    have h := ((hq (e y) (show y ∈ e ⁻¹' closure Ω by rwa [hecl])).differentiableAt
      one_ne_zero).hasFDerivAt.comp y e.hasFDerivAt
    rw [h.fderiv]
    rfl
  have h := box_integral_mul_fderiv_eq_neg a b hab (f ∘ e) (g ∘ e) (hc f hf) (hc g hg)
    (fun y hy => hz (e y) (show y ∈ e ⁻¹' frontier Ω by rw [hefr]; exact hfr hy)) j
  change (∫ x in Ω, _) = -(∫ x in Ω, _)
  rw [hint, hint]
  convert h using 1
  · apply setIntegral_congr_fun measurableSet_Icc
    intro y hy
    exact congrArg (fun z => f (e y) * z) (hd g hg y hy).symm
  · congr 1
    apply setIntegral_congr_fun measurableSet_Icc
    intro y hy
    exact congrArg (fun z => z * g (e y)) (hd f hf y hy).symm
end NSFormalization.Section3.T23
