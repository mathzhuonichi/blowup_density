import Contracts.V1.RegularityPartial

/-!
# A01 whole-space local theory, version 2

This contract registers the existence half of `prop:local` on `R³`
(`paper/sections/02-preliminaries.tex:105`, derived in
`paper/sections/appendix-a-local-theory.tex:60-107`).  It exposes one named,
positive local horizon, a classical solution on that horizon, and all four
clauses of `research/A01/Spec.lean:167-230`'s
`ManuscriptLocalRegularity` for that same solution.

Version two extends the frozen `A01.regularity_partial` API.  Its inherited
`projected` and `pressure_potential` fields hold for every classical solution;
the new `regularity` field packages those clauses together with
`sobolev_smooth` and `pressure_recovery` for the selected local solution.

## Deliberate narrowing of the quantitative horizon clause

The manuscript sentence at `research/A01/Spec.lean:338-344 (the draft transcription; the manuscript's appendix-a-local-theory.tex:147-150 itself states an H¹ bound for one fixed force on [0,S+δ])`, citing Tao's
H¹ local theory, uses an H¹ datum bound and an L¹-in-time H¹ force bound for
one fixed force on `[0,S+δ]`; the draft specification transcribed it with the
force quantified after `∃ δ` (one duration for the whole force ball) — that
stronger, force-uniform reading is the draft's, not the manuscript's (review 212).  The registered V2
field is strictly narrower: the force is fixed before the duration is chosen,
and the datum is bounded in H⁷.  It does not prove cross-force uniformity and it
does not prove the manuscript's H¹ statement.

This is the owner-approved interface needed by the implemented continuation
route.  A04 restarts the same underlying force and obtains H⁷ bounds for the
restart data by Grönwall.  Its actual uniformity over restart times
`t₀ ∈ [0,S]` and the shifted forces of that one force is proved separately by
`Section4/A04/RestartFixedForce.lean` (lane 215), using compact-time force
bounds.  The stronger manuscript H¹ statement is retained below as the
unregistered predicate `ManuscriptHorizonLowerBoundH1`, explicitly marked open.

Every definition copied from the draft specification is repeated literally in
this contract; `Bindings.LocalTheoryV2` supplies an `rfl` correspondence for
each implementation-side copy.  `ClassicalSolutionR` is reused from
`Contracts.V1.Data`, as required by the contract boundary.
-/

noncomputable section

namespace BlowupDensity.Contracts.V2.LocalTheory

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space SpaceTime coordinateVector
  temporalDerivative spatialLaplacian pressureGradient)
open NSFormalization.Paper3 (RealVectorSobolev)
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal

/-! ## Specification-local definitions -/

/-- `research/A01/Spec.lean:103-105`, the tensor divergence
`∇·(u⊗u)`, copied verbatim from the draft specification. -/
def convectionDivergence (u : SpaceTimeField) (t : ℝ) (x : Space) : Space :=
  ∑ j : Fin 3,
    fderiv ℝ (fun y : Space => (u (t, y) j) • u (t, y)) x (coordinateVector j)

/-- `research/A01/Spec.lean:119-122`: differentiability and symmetry of the
spatial Jacobian, copied verbatim from the draft specification. -/
def HasSymmetricJacobian (G : SpatialField) : Prop :=
  Differentiable ℝ G ∧
    ∀ x : Space, ∀ i j : Fin 3,
      (fderiv ℝ G x (coordinateVector i)) j = (fderiv ℝ G x (coordinateVector j)) i

/-- `research/A01/Spec.lean:142-145`, the Helmholtz-gradient characterization
of `(I-P)w`, copied verbatim from the draft specification. -/
def IsLerayComplement (w G : SpatialField) : Prop :=
  MemLp G 2 (volume : Measure Space) ∧
    HasSymmetricJacobian G ∧
    IsSolenoidal (fun x : Space => w x - G x)

/-! ## The four manuscript regularity clauses -/

/-- The four clauses of `research/A01/Spec.lean:167-230`, imposed on one
classical solution and one common horizon.  The structure and its fields below
are copied token-for-token from that specification. -/
structure ManuscriptLocalRegularity (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (T : ℝ) (u : ClassicalSolutionR ν a f T) : Prop where
  /-- `appendix-a-local-theory.tex:71-76`: "repeated time differentiation gives
  `C^j_tH^k_x` regularity for all `j,k`, including one-sided derivatives at the
  initial time".  For every integer order `m` the velocity has an order-`m`
  angular datum at every time of `[0,T)`, and that datum path is `C^∞` in time
  on `[0,T)`.  `Ico 0 T` is `UniqueDiffOn`, so the derivative at `t = 0` is the
  one-sided one and no negative-time extension is differentiated — the same
  convention `MemForceR` uses on `futureTimes` (`Data.lean:537`).

  This strictly strengthens `ClassicalSolutionR.sobolev`, which asks only for
  `ContinuousOn`; the datum is unique (`research/D01/RECONCILIATION.md` unit
  L1), so the two paths coincide wherever both exist. -/
  sobolev_smooth : ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
    (∀ t ∈ Ico (0 : ℝ) T,
        IsSobolevDatum (m : ℝ) (fun x : Space => u.velocity (t, x)) (G t)) ∧
      ContDiffOn ℝ ∞ G (Ico (0 : ℝ) T)
  /-- `02-preliminaries.tex:90` eq:Rpressure,
  `∇p = (I−P)(f − ∇·(u⊗u)) =: G`: the pressure gradient of the solution *is*
  the Helmholtz gradient part of the forced convection residual, at every time
  of `[0,T)` including `t = 0`.

  Stated at `t = 0` as well as at interior times, because
  `02-preliminaries.tex:90` prescribes the pressure of a classical solution
  everywhere on its interval, while `ClassicalSolutionR.momentum` is imposed on
  `Ioo 0 T` only.  On `Ioo 0 T` this clause is D01 unit **L9(c)**
  (`research/D01/RECONCILIATION.md:160`, "eq:Rpressure ⟺ `momentum` given
  `divergence` and `∇p ∈ L²`"), so the genuine increment of this field is the
  `t = 0` endpoint; the redundancy is kept so that the manuscript's own
  prescription is readable in one place. -/
  pressure_recovery : ∀ t ∈ Ico (0 : ℝ) T,
    IsLerayComplement
      (fun x : Space => f (t, x) - convectionDivergence u.velocity t x)
      (fun x : Space => pressureGradient u.pressure t x)
  /-- `02-preliminaries.tex:81` eq:projected,
  `∂_tu − νΔu = −P∇·(u⊗u) + P f`, with the force `P f` of
  `appendix-a-local-theory.tex:76-77`.

  Written as `P(f − ∇·(u⊗u)) = (f − ∇·(u⊗u)) − ∇p`, which is what the previous
  clause makes it: by `pressure_recovery` the subtracted field is exactly the
  Leray complement of `f − ∇·(u⊗u)`, so this line and that one together are
  eq:projected, with no Leray operator appearing as data.

  Imposed at interior times, matching `ClassicalSolutionR.momentum`: the
  upstream `temporalDerivative` is a two-sided `fderiv` in time and need not
  exist at `t = 0` for a field smooth only on `[0,T) × R³`
  (`research/D01/RECONCILIATION.md` §1.6). -/
  projected : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
    temporalDerivative u.velocity t x - ν • spatialLaplacian u.velocity t x =
      (f (t, x) - convectionDivergence u.velocity t x) -
        pressureGradient u.pressure t x
  /-- `02-preliminaries.tex:96-100`: the scalar pressure may be taken to be the
  explicit radial potential `p(x,t) = ∫₀¹G(rx,t)·x dr` of its own gradient,
  the manuscript's chosen representative inside the gauge class.

  The solution's `pressure` is required to differ from that potential by a
  function of time only, which is exactly `02-preliminaries.tex:31` "the scalar
  pressure is determined up to a function of time".  Together with
  `pressure_recovery` this is the manuscript's full pressure prescription:
  the gradient is fixed by eq:Rpressure and the potential fixes the gauge. -/
  pressure_potential : PressureGaugeEquivOn (Ico (0 : ℝ) T)
    (pressurePotential (fun z : SpaceTime => pressureGradient u.pressure z.1 z.2))
    u.pressure

/-! ## Version-two contract -/

/-- The registered A01 local-theory API.  It structurally extends the frozen
version-one partial regularity contract, so its two arbitrary-solution facts
remain available unchanged. -/
structure LocalTheoryAPI extends
    BlowupDensity.Contracts.V1.RegularityPartial.ManuscriptLocalRegularityPartialAPI where
  /-- The named common horizon `T₀(ν,a,f)`.  Its positivity is carried by the
  returned `ClassicalSolutionR.horizon_pos`. -/
  horizon : ℝ → SpatialField → SpaceTimeField → ℝ
  /-- A classical solution on `[0,T₀)` for every Section-4 datum.  As in the
  draft specification, the force class is narrowed from merely smooth forcing
  to `MemForceR`, the class actually quantified over downstream. -/
  solution : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
    0 < ν → a ∈ initialClassR → MemForceR f →
      ClassicalSolutionR ν a f (horizon ν a f)
  /-- The complete manuscript regularity bundle on the same selected horizon
  and for the same selected solution. -/
  regularity : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f),
      ManuscriptLocalRegularity ν a f (horizon ν a f) (solution ν a f hν ha hf)
  /-- **Owner-approved V2 narrowing of the draft spec (research/A01/Spec.lean:338-344); Appendix A:147-150 itself bounds one fixed force in H¹.**

  The paper invokes Tao's forced H¹ theory: an H¹ datum bound together with an
  `L¹_t H¹_x` force bound for one fixed force; the draft specification quantified
  the force after `∃ δ` (δ uniform across the whole force ball), which is the
  draft's reading, not the manuscript's (review 212).  This field instead fixes `f` before
  choosing δ and assumes an H⁷ bound only on the datum.  It therefore proves
  neither cross-force uniformity nor the paper's H¹ sentence.

  This exact fixed-force/H⁷ shape is sufficient for the implemented downstream
  route: A04 restarts the same underlying force and Grönwall bounds the restart
  data in H⁷.  The additional uniformity over restart times `t₀ ∈ [0,S]` and
  their shifted forces is not asserted by this field; it is proved for the
  implementation in `research/A04/REPORT_215.md` §3 / lane 215 from one
  compact-time force bound.  Cross-force uniformity is never consumed. -/
  horizon_lower_bound :
    ∀ ν, 0 < ν → ∀ f, MemForceR f → ∀ K : ℝ≥0∞, K ≠ ⊤ →
      ∃ δ > 0, ∀ a, a ∈ initialClassR → sobolevENorm 7 a ≤ K →
        δ ≤ horizon ν a f

/-- The manuscript's sentence; NOT implied by this API; open.

This is the H¹/cross-force statement of
`paper/sections/research/A01/Spec.lean:338-344 (the draft transcription; the manuscript's appendix-a-local-theory.tex:147-150 itself states an H¹ bound for one fixed force on [0,S+δ])` and
`research/A01/Spec.lean:338-344`, retained verbatim as an unregistered
predicate on a V2 record.  Proving it requires a forced quantitative H¹ local
theory on the mild stack.  No field or binding below claims it. -/
def ManuscriptHorizonLowerBoundH1 (api : LocalTheoryAPI) : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (a : SpatialField) (f : SpaceTimeField),
        a ∈ initialClassR → MemForceR f →
          sobolevENorm 1 a ≤ K → forceSobolevENormL1 1 f ≤ K →
            δ ≤ api.horizon ν a f

/-! ## Accessors -/

/-- The velocity field of the chosen local solution. -/
def LocalTheoryAPI.velocity (api : LocalTheoryAPI) {ν : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f) :
    SpaceTimeField :=
  (api.solution ν a f hν ha hf).velocity

/-- The pressure field of the chosen local solution. -/
def LocalTheoryAPI.pressure (api : LocalTheoryAPI) {ν : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f) :
    SpaceTimeScalar :=
  (api.solution ν a f hν ha hf).pressure

/-- The chosen horizon as an extended nonnegative real. -/
def LocalTheoryAPI.horizonENNReal (api : LocalTheoryAPI) (ν : ℝ) (a : SpatialField)
    (f : SpaceTimeField) : ENNReal :=
  ENNReal.ofReal (api.horizon ν a f)

end BlowupDensity.Contracts.V2.LocalTheory
