import NSFormalization.Section4.D01.RealPairing
import NSFormalization.Section4.A04.LaplacianDatum
import NSFormalization.Section4.D01.DerivativeDatum
import NSFormalization.Section4.D01.HalfOrder
import NSFormalization.Section4.A03.VectorTameProduct
import NSFormalization.Section4.A03.ScalarTameProduct
import NSFormalization.Section4.A03.RealAngularProduct
import NSFormalization.Section4.A05.SmoothJets

/-!
# A04 unit G1, sub-lemma SL3, step 3b: the Laplacian datum and the dissipation identity

Lane 088.  Step 3b closes the SL3 gap left open by `Section4/A04/LaplacianDatum.lean` (which
supplies the gradient identification `grad² = ∑ⱼ ‖D_j (datum_{m+1} u)‖²`) and by
`Section4/A04/{LaplacianPairing,RealPairing}.lean` (which supply the real skew-adjointness and
lowering-pairing identities).  It has two parts.

**Part 1 — the Laplacian datum (this file, mandatory).**  For a smooth square-integrable field
`Z` and an order-`(m+2)` angular datum `A` of `Z.field`, the order-`m` datum of the Euclidean
Laplacian `Δ(Z.field) = ∑ⱼ ∂ⱼ∂ⱼ (Z.field)` is the double directional-derivative datum summed over
the three directions, `∑ⱼ D_j (D_j A)`.  The two derivative steps reuse
`D01.isSobolevDatum_partialDeriv` (`Section4/D01/DerivativeDatum.lean:245`), which is `ℕ`-indexed
at real order `↑n + 1`; the mismatch between its output order `↑(m+1)` and the input order
`↑m + 1` of the next step is bridged by the order-congruence transport `isSobolevDatum_castOrder`
(`Nat.cast` arithmetic, `push_cast`).  The intermediate field `∂ⱼ(Z.field)` is repackaged as the
`EulerLpTranslation.SmoothL2Field` `Z.directionalField (coordinateVector j)`, whose `.field` is
`partialDeriv j Z.field` by `rfl`.  Additivity over the three directions is
`D01.isSobolevDatum_add`.  The pointwise identification of the tree's Laplacian
`NavierStokes.ProblemStatement.spatialLaplacian` (on the time-independent lift `A03.lift Z.field`)
with the second-partial sum `∑ⱼ ∂ⱼ∂ⱼ (Z.field)` is `rfl` (`spatialLaplacian_lift_eq_datumSum`).

**Part 2 — the dissipation identity `hlap`.**  With `G` the order-`m` datum of `Z.field`, `A'` its
order-`(m+1)` datum and `A` its order-`(m+2)` datum, the pairing on the real datum carrier is
`⟪G, laplacianDatum m A⟫_ℝ = -∑ⱼ ‖D_j A'‖²` (`inner_datum_laplacian`), hence
`⟪G, laplacianDatum m A⟫_ℝ ≤ -‖∇Z.field‖²_{H^m}` (`inner_datum_laplacian_le`, the `hlap` of
`inner_energy_assembly`), matching `gradientSobolevENorm_toReal_sq_eq_datum_sum`.  The route
(componentwise, on the ambient carrier via `RealPairing.realSobolev_inner_eq_ambient`, `rfl`):
`inner_sum` / `PiLp.inner_apply`, then real skew-adjointness
`Paper3.real_inner_angularDirectionalDerivative` moves one derivative onto `G`, then the two data
`G_i = Λ_{m+2→m}(A_i)` and `A'_i = Λ_{m+2→m+1}(A_i)` are identified by `isSobolevDatum_unique`
(vector lowering `D01.lowerVectorL`, `A03.IsScalarSobolevDatum.lower`), and the new
`directionalDerivative_orderLowering_comm` commutes `D_j` past the lowering so the reviewer's
lowering reconciliation `Paper3.real_inner_lowering_pairing` + `angularOrderLowering_self` closes
each component as `-‖Λ_{m+1→m}(D_j A_i)‖² = -‖(D_j A')_i‖²`.  The commutation is the genuinely new
analytic content of step 3b: it reduces to `angularMid_comm`, where the two multiplication middles
commute and their lowering symbols coincide by `lowering_mid_symbol_eq` (gap `-1` invariant) and
their directional symbols by `mid_symbol_order_independent`.

The order bookkeeping uses `D_j` at the three orders `m+2 → m+1 → m`; `derivDatumStep n j`
matches `isSobolevDatum_partialDeriv`'s output verbatim (`angularDirectionalDerivativeReal
(↑n + 1) (coordinateVector j)` on each component), so the datum assembly composes by definitional
unfolding.
-/

noncomputable section

open MeasureTheory NavierStokes.ProblemStatement

namespace NSFormalization.Section4.A04

open NSFormalization.Section4.D01
  (IsSobolevDatum isSobolevDatum_partialDeriv isSobolevDatum_add isSobolevDatum_unique
    schwartzPairable_of_isSobolevDatum SchwartzPairable sobolevENorm lowerVectorL lowerVectorL_apply)
open NSFormalization.Section4.A03
  (partialDeriv lift lowerDatum coe_lowerDatum isSobolevDatum_iff IsScalarSobolevDatum
    gradientSobolevENorm)
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Section4.A05 (SmoothL2)
open NSFormalization.Paper3
open NSFormalization.Source.RealSobolev (RealSobolevHilbert FourierData)
open EulerLpTranslation (SmoothL2Field)

/-! ## 1. Order-congruence transport and the derivative-datum step -/

/-- **Order-congruence transport of a Sobolev datum.**  A datum at order `s` is a datum at any
propositionally equal order `s'`, transporting the datum along the order equality.  Needed because
`isSobolevDatum_partialDeriv` is `ℕ`-indexed at real order `↑n + 1`, and the natural-cast orders
`↑(m+1)` and `↑m + 1` that appear when composing two derivative steps are equal only up to
`Nat.cast_succ`, not definitionally. -/
theorem isSobolevDatum_castOrder {s s' : ℝ} (h : s = s') {z : Space → Space}
    {A : RealVectorSobolev s} (hA : IsSobolevDatum s z A) :
    IsSobolevDatum s' z (h ▸ A) := by
  subst h; exact hA

/-- The datum transported along an order equality, as a function on the datum carrier. -/
noncomputable def castOrder {s s' : ℝ} (h : s = s') (A : RealVectorSobolev s) :
    RealVectorSobolev s' := h ▸ A

/-- **One derivative-datum lowering step**, `ℕ`-indexed to match `isSobolevDatum_partialDeriv`.
`derivDatumStep n j B = D_j B` sends an order-`(n+1)` datum to an order-`n` datum by the
shared directional-derivative multiplier `Paper3.angularDirectionalDerivativeReal (↑n + 1)`
applied to each component.  It is definitionally the term `isSobolevDatum_partialDeriv j n`
produces. -/
noncomputable def derivDatumStep (n : ℕ) (j : Fin 3) (B : RealVectorSobolev ((n : ℝ) + 1)) :
    RealVectorSobolev (n : ℝ) :=
  WithLp.toLp 2 fun i => angularDirectionalDerivativeReal ((n : ℝ) + 1) (coordinateVector j) (B i)

/-- The top-order cast, `↑m + 2 = ↑(m+1) + 1`. -/
theorem cast_top_order (m : ℕ) : ((m : ℝ) + 2) = (((m + 1 : ℕ) : ℝ) + 1) := by push_cast; ring

/-- The mid-order cast, `↑(m+1) = ↑m + 1`. -/
theorem cast_mid_order (m : ℕ) : (((m + 1 : ℕ) : ℝ)) = ((m : ℝ) + 1) := by push_cast; ring

/-! ## 2. The Laplacian datum -/

/-- **The order-`m` Laplacian datum** of a field with an order-`(m+2)` datum `A`:
`∑ⱼ D_j (D_j A)`, the two derivative steps taken at orders `m+2 → m+1 → m`. -/
noncomputable def laplacianDatum (m : ℕ) (A : RealVectorSobolev ((m : ℝ) + 2)) :
    RealVectorSobolev (m : ℝ) :=
  ∑ j : Fin 3,
    derivDatumStep m j (castOrder (cast_mid_order m) (derivDatumStep (m + 1) j
      (castOrder (cast_top_order m) A)))

/-- **The tree's Laplacian equals the second-partial sum, pointwise (definitional).**  The
componentwise Euclidean Laplacian `NavierStokes.ProblemStatement.spatialLaplacian` of the
time-independent lift `A03.lift Z.field` at time `0` is `∑ⱼ ∂ⱼ∂ⱼ (Z.field)`; both unfold to
`∑ⱼ fderiv ℝ (fun y => fderiv ℝ Z.field y (eⱼ)) x (eⱼ)`.  This is the equation the SL3 brief asks
to record when the tree's Laplacian and the `partialDeriv`-based sum differ syntactically. -/
theorem spatialLaplacian_lift_eq_datumSum {Z : SmoothL2Field Space} :
    (fun x => spatialLaplacian (lift Z.field) 0 x)
      = (fun x => ∑ j : Fin 3, partialDeriv j (partialDeriv j Z.field) x) := rfl

/-- **Part 1 — the Laplacian datum.**  For a smooth square-integrable field `Z` and an order-`(m+2)`
angular datum `A` of `Z.field`, the double directional-derivative datum summed over the three
directions, `laplacianDatum m A = ∑ⱼ D_j (D_j A)`, is the order-`m` angular datum of the Euclidean
Laplacian `Δ(Z.field) = spatialLaplacian (lift Z.field) 0`.

Route: `isSobolevDatum_partialDeriv` at `ℕ`-order `m+1` on `Z` (order `m+2 → m+1` datum of
`∂ⱼ(Z.field)`), then at `ℕ`-order `m` on the repackaged field `Z.directionalField (coordinateVector j)`
(order `m+1 → m` datum of `∂ⱼ∂ⱼ(Z.field)`), then `isSobolevDatum_add` over the three directions
(pairability from `schwartzPairable_of_isSobolevDatum`, orders `≥ 0`).  The two natural-cast order
mismatches are bridged by `isSobolevDatum_castOrder`. -/
theorem isSobolevDatum_laplacian {Z : SmoothL2Field Space} (m : ℕ)
    {A : RealVectorSobolev ((m : ℝ) + 2)} (hA : IsSobolevDatum ((m : ℝ) + 2) Z.field A) :
    IsSobolevDatum (m : ℝ) (fun x => spatialLaplacian (lift Z.field) 0 x) (laplacianDatum m A) := by
  -- per-direction: the order-`m` datum of `∂ⱼ∂ⱼ(Z.field)`
  have key : ∀ j : Fin 3, IsSobolevDatum (m : ℝ) (partialDeriv j (partialDeriv j Z.field))
      (derivDatumStep m j (castOrder (cast_mid_order m) (derivDatumStep (m + 1) j
        (castOrder (cast_top_order m) A)))) := by
    intro j
    have s1 : IsSobolevDatum (((m + 1 : ℕ) : ℝ)) (partialDeriv j Z.field)
        (derivDatumStep (m + 1) j (castOrder (cast_top_order m) A)) :=
      isSobolevDatum_partialDeriv j (m + 1) (isSobolevDatum_castOrder (cast_top_order m) hA)
    have s1' : IsSobolevDatum ((m : ℝ) + 1) (partialDeriv j Z.field)
        (castOrder (cast_mid_order m) (derivDatumStep (m + 1) j
          (castOrder (cast_top_order m) A))) :=
      isSobolevDatum_castOrder (cast_mid_order m) s1
    exact isSobolevDatum_partialDeriv (Z := Z.directionalField (coordinateVector j)) j m s1'
  -- pairability of each second-partial field (continuous, nonnegative order)
  have cont : ∀ j : Fin 3, Continuous (partialDeriv j (partialDeriv j Z.field)) := fun j =>
    ((Z.directionalField (coordinateVector j)).directionalField
      (coordinateVector j)).smooth.continuous
  have hpair : ∀ j : Fin 3, SchwartzPairable (partialDeriv j (partialDeriv j Z.field)) := fun j =>
    schwartzPairable_of_isSobolevDatum (Nat.cast_nonneg m) (cont j) (key j)
  -- fold the three directions with `isSobolevDatum_add`
  have h01 := isSobolevDatum_add (hpair 0) (hpair 1) (key 0) (key 1)
  have hpair01 : SchwartzPairable
      (partialDeriv 0 (partialDeriv 0 Z.field) + partialDeriv 1 (partialDeriv 1 Z.field)) :=
    schwartzPairable_of_isSobolevDatum (Nat.cast_nonneg m) ((cont 0).add (cont 1)) h01
  have h012 := isSobolevDatum_add hpair01 (hpair 2) h01 (key 2)
  -- reconcile the folded field with the Laplacian and the folded datum with `laplacianDatum`
  have hfield :
      (partialDeriv 0 (partialDeriv 0 Z.field) + partialDeriv 1 (partialDeriv 1 Z.field))
          + partialDeriv 2 (partialDeriv 2 Z.field)
        = (fun x => ∑ j : Fin 3, partialDeriv j (partialDeriv j Z.field) x) := by
    funext x; rw [Fin.sum_univ_three]; rfl
  rw [hfield] at h012
  show IsSobolevDatum (m : ℝ) _ (laplacianDatum m A)
  rw [laplacianDatum, Fin.sum_univ_three]
  exact h012


/-! ## 3. The dissipation identity (Part 2)

`⟪G, laplacianDatum m A⟫_ℝ = -∑ⱼ ‖D_j A'‖²`, hence `⟪G, L⟫ ≤ -grad²`, the `hlap` of
`A04.inner_energy_assembly`.  All inner products are moved to the ambient `Lp ℂ 2 volume` carrier
(`Paper3.realSobolev_inner_eq_ambient`, `rfl`), where the directional-derivative operator is
`L²`-skew-adjoint and commutes past the order-lowering. -/

/-- **Commutation of the directional-derivative and order-lowering middle operators.**  The two
multiplication middles commute (`ring`), their lowering symbols coincide (`lowering_mid_symbol_eq`,
gap `r - s = (r-1)-(s-1)` invariant) and their directional symbols coincide
(`mid_symbol_order_independent`). -/
theorem angularMid_comm (σ σ' s r : ℝ) (a : Space) (hrs : r ≤ s) (hrs' : r - 1 ≤ s - 1)
    (k : Lp ℂ 2 (volume : Measure Space)) :
    angularDirectionalMid σ a (angularOrderLoweringMid s r hrs k)
      = angularOrderLoweringMid (s - 1) (r - 1) hrs' (angularDirectionalMid σ' a k) := by
  apply Lp.ext
  filter_upwards [angularDirectionalMid_coeFn σ a (angularOrderLoweringMid s r hrs k),
    angularOrderLoweringMid_coeFn s r hrs k,
    angularOrderLoweringMid_coeFn (s - 1) (r - 1) hrs' (angularDirectionalMid σ' a k),
    angularDirectionalMid_coeFn σ' a k] with ξ e1 e2 e3 e4
  rw [e1, e2, e3, e4, lowering_mid_symbol_eq s r ξ, lowering_mid_symbol_eq (s - 1) (r - 1) ξ,
    show (r - 1) - (s - 1) = r - s from by ring, mid_symbol_order_independent σ σ' a ξ]
  ring

/-- **`D_j` commutes past `Λ`** on the ambient carrier, lowering both lowering orders by one:
`D_σ ∘ Λ_{s→r} = Λ_{(s-1)→(r-1)} ∘ D_{σ'}` (the directional-derivative label is immaterial by
`mid_symbol_order_independent`, so `σ`, `σ'` may differ).  Transported from `angularMid_comm`
across the unitary `U = angularFrequencyDilation`. -/
theorem directionalDerivative_orderLowering_comm (σ σ' s r : ℝ) (a : Space) (hrs : r ≤ s)
    (hrs' : r - 1 ≤ s - 1) (h : Lp ℂ 2 (volume : Measure Space)) :
    angularDirectionalDerivative σ a (angularOrderLowering s r hrs h)
      = angularOrderLowering (s - 1) (r - 1) hrs' (angularDirectionalDerivative σ' a h) := by
  rw [angularDirectionalDerivative_eq_dilation_mid σ a (angularOrderLowering s r hrs h),
    angularOrderLowering_eq_dilation_mid s r hrs h,
    angularOrderLowering_eq_dilation_mid (s - 1) (r - 1) hrs' (angularDirectionalDerivative σ' a h),
    angularDirectionalDerivative_eq_dilation_mid σ' a h,
    LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply,
    angularMid_comm σ σ' s r a hrs hrs']

/-- **The vector lowering realizes the same physical field**, so it is a datum at the lower order.
Uses the in-tree componentwise lowering CLM `D01.lowerVectorL` (`D01/HalfOrder.lean:103`,
`lowerVectorL_apply … = lowerDatum s r hrs (A i)` by `rfl`).  The three-line pointwise core is the
same as `D01.isSobolevPath_lower` (`HalfOrder.lean:120`), stated here for a single datum; switch to
the merged vector-datum lemma `D01.isSobolevDatum_lower` (lane 085, `D01/LerayLowering.lean`) once
it lands on integration. -/
theorem isSobolevDatum_lowerVectorL (s r : ℝ) (hrs : r ≤ s) {z : Space → Space}
    {A : RealVectorSobolev s} (hA : IsSobolevDatum s z A) :
    IsSobolevDatum r z (lowerVectorL s r hrs A) := by
  rw [isSobolevDatum_iff]
  intro i
  rw [lowerVectorL_apply]
  exact ((isSobolevDatum_iff s z A).mp hA i).lower hrs

theorem coe_lowerVectorL (s r : ℝ) (hrs : r ≤ s) (A : RealVectorSobolev s) (i : Fin 3) :
    (((lowerVectorL s r hrs A) i : RealSobolevHilbert r) : FourierData)
      = angularOrderLowering s r hrs ((A i : FourierData)) := by
  rw [lowerVectorL_apply, coe_lowerDatum]

/-- The `FourierData` coercion is invariant under order transport of a datum. -/
theorem castOrder_coe {s s' : ℝ} (h : s = s') (B : RealVectorSobolev s) (i : Fin 3) :
    (((castOrder h B) i : RealSobolevHilbert s') : FourierData)
      = ((B i : RealSobolevHilbert s) : FourierData) := by
  subst h; rfl

/-- The `FourierData` coercion of a `derivDatumStep` component is the ambient directional
derivative of the component. -/
theorem coe_derivDatumStep (n : ℕ) (j : Fin 3) (B : RealVectorSobolev ((n : ℝ) + 1)) (i : Fin 3) :
    (((derivDatumStep n j B) i : RealSobolevHilbert (n : ℝ)) : FourierData)
      = angularDirectionalDerivative ((n : ℝ) + 1) (coordinateVector j) ((B i : FourierData)) := by
  show ((angularDirectionalDerivativeReal ((n : ℝ) + 1) (coordinateVector j) (B i) :
    RealSobolevHilbert (n : ℝ)) : FourierData) = _
  rw [angularDirectionalDerivativeReal_coe]

/-- **Per-component reconciliation** on the ambient carrier.  With `Gi = Λ_{m+2→m}(Ai)` and
`A'i = Λ_{m+2→m+1}(Ai)`, `⟪Gi, D_j(D_j Ai)⟫_ℝ = -‖D_j A'i‖²`: skew-adjointness peels one `D_j` onto
`Gi`, the commutation turns `D_j(Λ Ai)` into `Λ(D_j Ai)`, and the lowering pairing
`real_inner_lowering_pairing` (with `angularOrderLowering_self` on the second slot) closes it. -/
theorem inner_component_reconcile (m : ℕ) (e : Space) (Gi Ai A'i : Lp ℂ 2 (volume : Measure Space))
    (hG : Gi = angularOrderLowering ((m : ℝ) + 2) (m : ℝ) (by linarith) Ai)
    (hA' : A'i = angularOrderLowering ((m : ℝ) + 2) ((m : ℝ) + 1) (by linarith) Ai) :
    (inner ℝ Gi (angularDirectionalDerivative ((m : ℝ) + 1) e
        (angularDirectionalDerivative (((m + 1 : ℕ) : ℝ) + 1) e Ai)) : ℝ)
      = - ‖angularDirectionalDerivative ((m : ℝ) + 1) e A'i‖ ^ 2 := by
  rw [real_inner_angularDirectionalDerivative ((m : ℝ) + 1) e Gi
        (angularDirectionalDerivative (((m + 1 : ℕ) : ℝ) + 1) e Ai)]
  congr 1
  rw [hG, hA',
    directionalDerivative_orderLowering_comm ((m : ℝ) + 1) (((m + 1 : ℕ) : ℝ) + 1) ((m : ℝ) + 2)
      (m : ℝ) e (by linarith) (by linarith) Ai,
    directionalDerivative_orderLowering_comm ((m : ℝ) + 1) (((m + 1 : ℕ) : ℝ) + 1) ((m : ℝ) + 2)
      ((m : ℝ) + 1) e (by linarith) (by linarith) Ai]
  set v := angularDirectionalDerivative (((m + 1 : ℕ) : ℝ) + 1) e Ai with hv
  have hpair := real_inner_lowering_pairing ((m : ℝ) + 2 - 1) ((m : ℝ) - 1) ((m : ℝ) + 2 - 1)
    (by linarith) (le_refl _) (by linarith) v
  rw [angularOrderLowering_self] at hpair
  simp only [show ((m : ℝ) - 1 + ((m : ℝ) + 2 - 1)) / 2 = (m : ℝ) from by ring] at hpair
  simp only [show ((m : ℝ) + 1 - 1) = (m : ℝ) from by ring]
  exact hpair

/-- The squared datum-carrier norm of `derivDatumStep m j A'` is the sum over the components of the
squared ambient norms of the directional derivative. -/
theorem norm_sq_derivDatumStep (m : ℕ) (j : Fin 3) (A' : RealVectorSobolev ((m : ℝ) + 1)) :
    ‖derivDatumStep m j A'‖ ^ 2
      = ∑ i : Fin 3, ‖angularDirectionalDerivative ((m : ℝ) + 1) (coordinateVector j)
          ((A' i : FourierData))‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show ‖derivDatumStep m j A' i‖ = ‖((derivDatumStep m j A' i : RealSobolevHilbert (m : ℝ)) :
    FourierData)‖ from rfl, coe_derivDatumStep]

/-- **Per-direction pairing.**  `⟪G, D_j(D_j A)⟫_ℝ = -‖D_j A'‖²`, from `inner_component_reconcile`
summed over the three components. -/
theorem inner_datum_laplacianDir (m : ℕ)
    {G : RealVectorSobolev (m : ℝ)} {A' : RealVectorSobolev ((m : ℝ) + 1)}
    {A : RealVectorSobolev ((m : ℝ) + 2)}
    (hGA : ∀ i, ((G i : RealSobolevHilbert (m : ℝ)) : FourierData)
      = angularOrderLowering ((m : ℝ) + 2) (m : ℝ) (by linarith) ((A i : FourierData)))
    (hA'A : ∀ i, ((A' i : RealSobolevHilbert ((m : ℝ) + 1)) : FourierData)
      = angularOrderLowering ((m : ℝ) + 2) ((m : ℝ) + 1) (by linarith) ((A i : FourierData)))
    (j : Fin 3) :
    (inner ℝ G (derivDatumStep m j (castOrder (cast_mid_order m) (derivDatumStep (m + 1) j
        (castOrder (cast_top_order m) A)))) : ℝ)
      = - ‖derivDatumStep m j A'‖ ^ 2 := by
  rw [norm_sq_derivDatumStep, PiLp.inner_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [realSobolev_inner_eq_ambient, coe_derivDatumStep, castOrder_coe, coe_derivDatumStep,
    castOrder_coe]
  exact inner_component_reconcile m (coordinateVector j) _ _ ((A' i : FourierData))
    (hGA i) (hA'A i)

/-- **Part 2 — the pairing identity.**  For a field `Z` with order-`m`, `-(m+1)` and `-(m+2)` data
`G`, `A'`, `A`, the real datum-carrier pairing of the order-`m` datum against the Laplacian datum is
minus the squared gradient datum sum: `⟪G, laplacianDatum m A⟫_ℝ = -∑ⱼ ‖D_j A'‖²`. -/
theorem inner_datum_laplacian (m : ℕ) {Z : SmoothL2Field Space}
    {G : RealVectorSobolev (m : ℝ)} {A' : RealVectorSobolev ((m : ℝ) + 1)}
    {A : RealVectorSobolev ((m : ℝ) + 2)}
    (hG : IsSobolevDatum (m : ℝ) Z.field G) (hA' : IsSobolevDatum ((m : ℝ) + 1) Z.field A')
    (hA : IsSobolevDatum ((m : ℝ) + 2) Z.field A) :
    (inner ℝ G (laplacianDatum m A) : ℝ) = - ∑ j : Fin 3, ‖derivDatumStep m j A'‖ ^ 2 := by
  have hGA : ∀ i, ((G i : RealSobolevHilbert (m : ℝ)) : FourierData)
      = angularOrderLowering ((m : ℝ) + 2) (m : ℝ) (by linarith) ((A i : FourierData)) := by
    intro i
    rw [isSobolevDatum_unique hG (isSobolevDatum_lowerVectorL ((m : ℝ) + 2) (m : ℝ) (by linarith) hA),
      coe_lowerVectorL]
  have hA'A : ∀ i, ((A' i : RealSobolevHilbert ((m : ℝ) + 1)) : FourierData)
      = angularOrderLowering ((m : ℝ) + 2) ((m : ℝ) + 1) (by linarith) ((A i : FourierData)) := by
    intro i
    rw [isSobolevDatum_unique hA' (isSobolevDatum_lowerVectorL ((m : ℝ) + 2) ((m : ℝ) + 1)
      (by linarith) hA), coe_lowerVectorL]
  rw [laplacianDatum, inner_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun j _ => inner_datum_laplacianDir m hGA hA'A j)

/-- **Part 2 — `hlap`.**  The `⟪G, L⟫ ≤ -grad²` dissipation bound consumed by
`A04.inner_energy_assembly`, with `L = laplacianDatum m A` the order-`m` datum of the Laplacian
(Part 1) and `grad = (gradientSobolevENorm m Z.field).toReal`.  The bound holds with equality, via
`inner_datum_laplacian` and `gradientSobolevENorm_toReal_sq_eq_datum_sum`. -/
theorem inner_datum_laplacian_le (m : ℕ) {Z : SmoothL2Field Space}
    {G : RealVectorSobolev (m : ℝ)} {A' : RealVectorSobolev ((m : ℝ) + 1)}
    {A : RealVectorSobolev ((m : ℝ) + 2)}
    (hG : IsSobolevDatum (m : ℝ) Z.field G) (hA' : IsSobolevDatum ((m : ℝ) + 1) Z.field A')
    (hA : IsSobolevDatum ((m : ℝ) + 2) Z.field A) :
    (inner ℝ G (laplacianDatum m A) : ℝ)
      ≤ - (gradientSobolevENorm (m : ℝ) Z.field).toReal ^ 2 := by
  apply le_of_eq
  rw [inner_datum_laplacian m hG hA' hA, gradientSobolevENorm_toReal_sq_eq_datum_sum m hA']
  rfl

/-- **Part 2 — the consumer-shaped `hlap`.**  The exact `hlap` of `A04.inner_energy_assembly` for a
time-`t` slice of a spacetime velocity `u`: with `G/A'/A` the order-`m`/`(m+1)`/`(m+2)` data of the
slice `fun x => u (t, x)` and `L` **any** order-`m` datum of the Laplacian slice
`fun x => spatialLaplacian u t x`, `⟪G, L⟫_ℝ ≤ -gradientSobolevNormAt m u t ²`.  The slice is
smooth and `L²` (`hsl : A05.SmoothL2 …`, supplied by `C01.velocity_slice_memHInfty_and_smoothL2` on
a `ClassicalSolutionR`), so it is packaged as an `EulerLpTranslation.SmoothL2Field` `Z` whose
`.field` is definitionally the slice — which makes the norm bridge
`gradientSobolevNormAt m u t = (gradientSobolevENorm m Z.field).toReal` hold by `rfl`.  `L` is pinned
to `laplacianDatum m A` by `isSobolevDatum_unique` (the field defeq
`spatialLaplacian u t ≡ spatialLaplacian (lift Z.field) 0` is cheap).  Stating both bridges as `have`s
is essential: inlining the `rfl` norm bridge into `exact` unfolds
`gradientSobolevENorm → columnsSobolevENorm → sobolevENorm` (an `⨅` over a subtype of data) and blows
the default heartbeat budget at `isDefEq`. -/
theorem inner_datum_laplacian_le' (m : ℕ) {u : SpaceTimeField} {t : ℝ}
    (hsl : SmoothL2 (fun x => u (t, x)))
    {G : RealVectorSobolev (m : ℝ)} {A' : RealVectorSobolev ((m : ℝ) + 1)}
    {A : RealVectorSobolev ((m : ℝ) + 2)} {L : RealVectorSobolev (m : ℝ)}
    (hG : IsSobolevDatum (m : ℝ) (fun x => u (t, x)) G)
    (hA' : IsSobolevDatum ((m : ℝ) + 1) (fun x => u (t, x)) A')
    (hA : IsSobolevDatum ((m : ℝ) + 2) (fun x => u (t, x)) A)
    (hL : IsSobolevDatum (m : ℝ) (fun x => spatialLaplacian u t x) L) :
    (inner ℝ G L : ℝ) ≤ - gradientSobolevNormAt (m : ℝ) u t ^ 2 := by
  let Z : SmoothL2Field Space := ⟨fun x => u (t, x), hsl.1, hsl.2⟩
  have hLeq : L = laplacianDatum m A :=
    isSobolevDatum_unique hL (isSobolevDatum_laplacian (Z := Z) m hA)
  have hg : gradientSobolevNormAt (m : ℝ) u t = (gradientSobolevENorm (m : ℝ) Z.field).toReal := rfl
  rw [hLeq, hg]
  exact inner_datum_laplacian_le m hG hA' hA

end NSFormalization.Section4.A04
