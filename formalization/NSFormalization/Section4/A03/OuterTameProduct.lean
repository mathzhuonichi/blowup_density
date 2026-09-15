import NSFormalization.Section4.A03.VectorTameProduct
import NSFormalization.Section4.A05.SmoothJets

/-!
# `eq:tame`, the product difference bound and the advection bound

Task `A03`, Lemma A.1 (`lem:calculus`,
`paper/sections/appendix-a-local-theory.tex:7-27`):

* `eq:tame` (`:17-18`), `‖u ⊗ u‖_{H^k} ≤ C_k‖u‖_{H²}‖u‖_{H^k}`, the clause A04
  consumes through `eq:Rhigh` (`:132-137`);
* `:51-52`, "factorization gives the corresponding product difference bound" —
  a **qualitative** claim (the same sentence is at
  `paper/originals/local/paper_3_whole_space.tex:156`, and no inequality of this
  shape is displayed anywhere under `paper/`), so the quantified form proved here,
  `‖u⊗u − v⊗v‖_{H^k} ≤ C_k(‖u‖_{H^k}+‖v‖_{H^k})‖u−v‖_{H^k}`, is **derived** from
  the factorization `u⊗u − v⊗v = (u−v)⊗u + v⊗(u−v)` and `eq:algebra`;
* the `H^m` bound for the bilinear advection `(u·∇)v` of `01-introduction.tex:83`
  eq:NS, obtained from `eq:Rproduct` applied to the summands `u_j·∂_jv`
  (`:9-11` with `:50`).

Tensors are measured as `01-introduction.tex:103` prescribes — "for vectors and
tensors we sum the squared component norms" — by `columnsSobolevENorm`, the
Euclidean assembly of the three column norms of `Contracts.V1.Data.sobolevENorm`,
i.e. the full nine-entry Frobenius quantity.

## Hypotheses

`outerProductTame` and `outerProductDifference` run on `MemHmVector k`, the
`H^k` class, exactly as `eq:tame` and `eq:algebra` do: their consumer — the mild
contraction of `prop:local` (`:110-116`) — works on the ball of `C([0,τ];H³)`,
whose elements are not `H^∞`.  Only pointwise products occur there, so no
differentiability is needed and none is assumed.

`advectionTame` is different: its statement contains a **classical** derivative
(`spatialDerivative`, i.e. `fderiv`), which `MemHmVector` does not supply, so it
is stated on the smooth jet class `SmoothL2` — which
`Section4/D01/SmoothDatum.lean` turns into data at every real order.
-/

noncomputable section

open MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source NSFormalization.Source.RealSobolev
open NSFormalization.Section4.D01 (IsSobolevDatum sobolevENorm)
open scoped ContDiff SchwartzMap ENNReal

namespace NSFormalization.Section4.A03

/-! ## 1. The tensor quantities -/

/-- The time-independent lift of a spatial field, so that the pinned upstream
`spatialDerivative` can be reused on a fixed-time slice. -/
def lift (v : Space → Space) : SpaceTime → Space := fun z => v z.2

/-- `appendix-a-local-theory.tex:50`: the `j`-th partial derivative of a spatial
field, again a spatial field. -/
def partialDeriv (j : Fin 3) (v : Space → Space) : Space → Space :=
  fun x => spatialDerivative (lift v) 0 x (coordinateVector j)

/-- `01-introduction.tex:83` eq:NS and `02-preliminaries.tex:81` eq:projected:
the bilinear advection `(u·∇)v`, as a spatial field. -/
def advectionOf (u v : Space → Space) : Space → Space :=
  fun x => spatialDerivative (lift v) 0 x (u x)

/-- `appendix-a-local-theory.tex:17` eq:tame: the `j`-th column of `u ⊗ v`. -/
def outerColumn (u v : Space → Space) (j : Fin 3) : Space → Space := fun x => (u x j) • v x

/-- Pointwise difference of two spatial fields. -/
def diffField (u v : Space → Space) : Space → Space := fun x => u x - v x

/-- `01-introduction.tex:103`: the order-`s` Sobolev norm of a `3×3` tensor
field presented by its three columns. -/
def columnsSobolevENorm (s : ℝ) (T : Fin 3 → Space → Space) : ℝ≥0∞ :=
  (∑ j : Fin 3, sobolevENorm s (T j) ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹)

/-- `appendix-a-local-theory.tex:17` eq:tame, `‖u ⊗ v‖_{H^s}`. -/
def outerSobolevENorm (s : ℝ) (u v : Space → Space) : ℝ≥0∞ :=
  columnsSobolevENorm s (outerColumn u v)

/-- `appendix-a-local-theory.tex:51-52`, `‖u⊗u − v⊗v‖_{H^s}`. -/
def outerDiffSobolevENorm (s : ℝ) (u v : Space → Space) : ℝ≥0∞ :=
  columnsSobolevENorm s (fun j => diffField (outerColumn u u j) (outerColumn v v j))

/-- `appendix-a-local-theory.tex:134` `‖∇u‖_{H^m}`. -/
def gradientSobolevENorm (s : ℝ) (v : Space → Space) : ℝ≥0∞ :=
  columnsSobolevENorm s (fun j => partialDeriv j v)

/-- The squared `.toReal` of a Frobenius column-assembly is the sum of the squared `.toReal` column
norms, whenever each column norm is finite.  Pure `ENNReal.toReal` arithmetic on the
`columnsSobolevENorm` definition; the general column family behind
`A04.gradientSobolevENorm_toReal_sq_eq_sum` (`LaplacianDatum.lean:96`).

Promoted from `Section4/A04/NonlinearColumns.lean` in lane 109; a
`NSFormalization.Section4.A04` alias is kept there for downstream. -/
theorem columnsSobolevENorm_toReal_sq_eq_sum {s : ℝ} {T : Fin 3 → Space → Space}
    (hfin : ∀ j : Fin 3, sobolevENorm s (T j) ≠ ⊤) :
    (columnsSobolevENorm s T).toReal ^ 2 = ∑ j : Fin 3, (sobolevENorm s (T j)).toReal ^ 2 := by
  unfold columnsSobolevENorm
  rw [← ENNReal.toReal_rpow,
    ← Real.rpow_natCast ((∑ j : Fin 3, sobolevENorm s (T j) ^ (2 : ℝ)).toReal ^ (2 : ℝ)⁻¹) 2,
    ← Real.rpow_mul ENNReal.toReal_nonneg]
  norm_num
  rw [ENNReal.toReal_sum (fun j _ => ENNReal.pow_ne_top (hfin j))]
  apply Finset.sum_congr rfl
  intro j _
  rw [ENNReal.toReal_pow]

/-- The Frobenius assembly is at most the sum of the three column norms:
`ℓ² ≤ ℓ¹` on three terms, a factor of at most `3` that
`appendix-a-local-theory.tex:10` leaves free. -/
theorem columnsSobolevENorm_le_sum (s : ℝ) (T : Fin 3 → Space → Space) :
    columnsSobolevENorm s T ≤ ∑ j : Fin 3, sobolevENorm s (T j) := by
  set x : Fin 3 → ℝ≥0∞ := fun j => sobolevENorm s (T j) with hx
  set S := ∑ j : Fin 3, x j with hS
  have hsq : ∑ j : Fin 3, x j ^ (2:ℝ) ≤ S ^ (2:ℝ) := by
    have hle : ∀ j : Fin 3, x j ^ (2:ℝ) ≤ x j * S := by
      intro j
      have hjs : x j ≤ S := Finset.single_le_sum (f := x) (fun _ _ => by simp) (Finset.mem_univ j)
      calc x j ^ (2:ℝ) = x j * x j := by
            rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast, sq]
        _ ≤ x j * S := by gcongr
    calc ∑ j : Fin 3, x j ^ (2:ℝ) ≤ ∑ j : Fin 3, x j * S := Finset.sum_le_sum fun j _ => hle j
      _ = S * S := by rw [← Finset.sum_mul]
      _ = S ^ (2:ℝ) := by rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast, sq]
  calc columnsSobolevENorm s T ≤ (S ^ (2:ℝ)) ^ ((2:ℝ)⁻¹) :=
        ENNReal.rpow_le_rpow hsq (by norm_num)
    _ = S := by rw [← ENNReal.rpow_mul]; norm_num

/-- Each column is dominated by the Frobenius assembly. -/
theorem le_columnsSobolevENorm (s : ℝ) (T : Fin 3 → Space → Space) (j : Fin 3) :
    sobolevENorm s (T j) ≤ columnsSobolevENorm s T := by
  have hle : sobolevENorm s (T j) ^ (2:ℝ) ≤ ∑ i : Fin 3, sobolevENorm s (T i) ^ (2:ℝ) :=
    Finset.single_le_sum (f := fun i : Fin 3 => sobolevENorm s (T i) ^ (2:ℝ))
      (fun _ _ => by simp) (Finset.mem_univ j)
  calc sobolevENorm s (T j) = (sobolevENorm s (T j) ^ (2:ℝ)) ^ ((2:ℝ)⁻¹) := by
        rw [← ENNReal.rpow_mul]; norm_num
    _ ≤ columnsSobolevENorm s T := ENNReal.rpow_le_rpow hle (by norm_num)

/-! ## 2. Three-term sums -/

theorem LocIntField.add {F G : Space → Space} (hF : LocIntField F) (hG : LocIntField G) :
    LocIntField (fun x => F x + G x) := by
  intro i
  refine ((hF i).add (hG i)).congr (Filter.Eventually.of_forall fun x => ?_)
  have hpt : (F x + G x) i = F x i + G x i := rfl
  show ((F x i : ℝ) : ℂ) + ((G x i : ℝ) : ℂ) = (((F x + G x) i : ℝ) : ℂ)
  rw [hpt]
  push_cast
  ring

theorem sobolevENorm_sum_three {s : ℝ} (hs : 2 ≤ s) {T : Fin 3 → Space → Space}
    (hT : ∀ j, LocIntField (T j)) :
    sobolevENorm s (fun x => ∑ j : Fin 3, T j x) ≤ ∑ j : Fin 3, sobolevENorm s (T j) := by
  have hfun : (fun x : Space => ∑ j : Fin 3, T j x) =
      fun x : Space => (T 0 x + T 1 x) + T 2 x := by
    funext x; simp [Fin.sum_univ_three]
  rw [hfun, Fin.sum_univ_three]
  refine le_trans (sobolevENorm_add_le hs ((hT 0).add (hT 1)) (hT 2)) ?_
  exact add_le_add (sobolevENorm_add_le hs (hT 0) (hT 1)) le_rfl

/-! ## 3. `eq:tame` -/

/-- `appendix-a-local-theory.tex:17-18` eq:tame's constant. -/
def outerTameConst (k : ℕ) : ℝ := 6 * vectorTameConst k

theorem outerTameConst_pos (k : ℕ) : 0 < outerTameConst k := by
  have := vectorTameConst_pos k
  simp only [outerTameConst]; linarith

/-- **`appendix-a-local-theory.tex:17-18` eq:tame** on the datum carrier:
`‖u ⊗ u‖_{H^k} ≤ C_k‖u‖_{H²}‖u‖_{H^k}` for every integer `k ≥ 2` (the
manuscript states `k ≥ 3`; the proof needs only `k ≥ 2`).  The low factor stays
at order **two**, which is what makes `eq:Rhigh`'s continuation criterion an
`H²` criterion. -/
theorem outerProductTame (k : ℕ) (hk : 2 ≤ k) {u : Space → Space} (hu : MemHmVector k u) :
    outerSobolevENorm (k : ℝ) u u ≤
      ENNReal.ofReal (outerTameConst k) * (sobolevENorm 2 u * sobolevENorm (k : ℝ) u) := by
  refine (columnsSobolevENorm_le_sum (k : ℝ) (outerColumn u u)).trans ?_
  have hstep : ∀ j : Fin 3, sobolevENorm (k : ℝ) (outerColumn u u j) ≤
      ENNReal.ofReal (2 * vectorTameConst k) *
        (sobolevENorm 2 u * sobolevENorm (k : ℝ) u) := by
    intro j
    have h := tameProductVector k hk (hu.component j) hu
    refine h.trans ?_
    have h1 : scalarSobolevENorm 2 (fun x => u x j) ≤ sobolevENorm 2 u :=
      scalarSobolevENorm_component_le _ _ j
    have h2 : scalarSobolevENorm (k : ℝ) (fun x => u x j) ≤ sobolevENorm (k : ℝ) u :=
      scalarSobolevENorm_component_le _ _ j
    calc ENNReal.ofReal (vectorTameConst k) *
          (scalarSobolevENorm 2 (fun x => u x j) * sobolevENorm (k : ℝ) u +
            sobolevENorm 2 u * scalarSobolevENorm (k : ℝ) (fun x => u x j))
        ≤ ENNReal.ofReal (vectorTameConst k) *
          (sobolevENorm 2 u * sobolevENorm (k : ℝ) u +
            sobolevENorm 2 u * sobolevENorm (k : ℝ) u) := by gcongr
      _ = ENNReal.ofReal (2 * vectorTameConst k) *
          (sobolevENorm 2 u * sobolevENorm (k : ℝ) u) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
          ring
  calc ∑ j : Fin 3, sobolevENorm (k : ℝ) (outerColumn u u j)
      ≤ ∑ _j : Fin 3, ENNReal.ofReal (2 * vectorTameConst k) *
          (sobolevENorm 2 u * sobolevENorm (k : ℝ) u) := Finset.sum_le_sum fun j _ => hstep j
    _ = ENNReal.ofReal (outerTameConst k) * (sobolevENorm 2 u * sobolevENorm (k : ℝ) u) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, outerTameConst,
          show (6:ℝ) * vectorTameConst k = 3 * (2 * vectorTameConst k) by ring,
          ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3), ENNReal.ofReal_ofNat]
        simp [mul_assoc, nsmul_eq_mul]

/-! ## 4. The product difference bound -/

/-- `appendix-a-local-theory.tex:51-52`'s constant. -/
def outerDiffConst (k : ℕ) : ℝ := 3 * vectorAlgebraConst k

theorem outerDiffConst_pos (k : ℕ) : 0 < outerDiffConst k := by
  have := vectorAlgebraConst_pos k
  simp only [outerDiffConst]; linarith

theorem memHmVector_diffField {k : ℕ} (hk2 : (2:ℝ) ≤ (k:ℝ)) {u v : Space → Space}
    (hu : MemHmVector k u) (hv : MemHmVector k v) : MemHmVector k (diffField u v) :=
  ⟨hu.1.sub hv.1,
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hu.2, hv.2⟩)
      (sobolevENorm_sub_le hk2 (locIntField_of_memLp hu.1) (locIntField_of_memLp hv.1))⟩

/-- **`appendix-a-local-theory.tex:51-52`, the product difference bound**:
`‖u⊗u − v⊗v‖_{H^k} ≤ C_k(‖u‖_{H^k}+‖v‖_{H^k})‖u−v‖_{H^k}`, from the
factorization `u⊗u − v⊗v = (u−v)⊗u + v⊗(u−v)`. -/
theorem outerProductDifference (k : ℕ) (hk : 2 ≤ k) {u v : Space → Space}
    (hu : MemHmVector k u) (hv : MemHmVector k v) :
    outerDiffSobolevENorm (k : ℝ) u v ≤
      ENNReal.ofReal (outerDiffConst k) *
        ((sobolevENorm (k : ℝ) u + sobolevENorm (k : ℝ) v) *
          sobolevENorm (k : ℝ) (diffField u v)) := by
  have hk2 : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hd : MemHmVector k (diffField u v) := memHmVector_diffField hk2 hu hv
  refine (columnsSobolevENorm_le_sum (k : ℝ) _).trans ?_
  have hstep : ∀ j : Fin 3,
      sobolevENorm (k : ℝ) (diffField (outerColumn u u j) (outerColumn v v j)) ≤
        ENNReal.ofReal (vectorAlgebraConst k) *
          ((sobolevENorm (k : ℝ) u + sobolevENorm (k : ℝ) v) *
            sobolevENorm (k : ℝ) (diffField u v)) := by
    intro j
    have hfun : diffField (outerColumn u u j) (outerColumn v v j) =
        fun x => (fun y => (diffField u v) y j • u y) x +
          (fun y => (v y j) • (diffField u v) y) x := by
      funext x
      show (u x j) • u x - (v x j) • v x =
        (u x j - v x j) • u x + (v x j) • (u x - v x)
      rw [sub_smul, smul_sub]
      abel
    rw [hfun]
    have hF : LocIntField (fun y => (diffField u v) y j • u y) :=
      locIntField_smul ((EuclideanSpace.proj (𝕜 := ℝ) j).comp_memLp' hd.1) hu.1
    have hG : LocIntField (fun y => (v y j) • (diffField u v) y) :=
      locIntField_smul ((EuclideanSpace.proj (𝕜 := ℝ) j).comp_memLp' hv.1) hd.1
    refine (sobolevENorm_add_le hk2 hF hG).trans ?_
    have hb1 := algebraProductVector k hk (hd.component j) hu
    have hb2 := algebraProductVector k hk (hv.component j) hd
    have hc1 : scalarSobolevENorm (k : ℝ) (fun x => (diffField u v) x j) ≤
        sobolevENorm (k : ℝ) (diffField u v) := scalarSobolevENorm_component_le _ _ j
    have hc2 : scalarSobolevENorm (k : ℝ) (fun x => v x j) ≤ sobolevENorm (k : ℝ) v :=
      scalarSobolevENorm_component_le _ _ j
    calc sobolevENorm (k : ℝ) (fun y => (diffField u v) y j • u y) +
          sobolevENorm (k : ℝ) (fun y => (v y j) • (diffField u v) y)
        ≤ ENNReal.ofReal (vectorAlgebraConst k) *
            (scalarSobolevENorm (k : ℝ) (fun x => (diffField u v) x j) *
              sobolevENorm (k : ℝ) u) +
          ENNReal.ofReal (vectorAlgebraConst k) *
            (scalarSobolevENorm (k : ℝ) (fun x => v x j) *
              sobolevENorm (k : ℝ) (diffField u v)) := add_le_add hb1 hb2
      _ ≤ ENNReal.ofReal (vectorAlgebraConst k) *
            (sobolevENorm (k : ℝ) (diffField u v) * sobolevENorm (k : ℝ) u) +
          ENNReal.ofReal (vectorAlgebraConst k) *
            (sobolevENorm (k : ℝ) v * sobolevENorm (k : ℝ) (diffField u v)) := by gcongr
      _ = ENNReal.ofReal (vectorAlgebraConst k) *
            ((sobolevENorm (k : ℝ) u + sobolevENorm (k : ℝ) v) *
              sobolevENorm (k : ℝ) (diffField u v)) := by ring
  calc ∑ j : Fin 3, sobolevENorm (k : ℝ) (diffField (outerColumn u u j) (outerColumn v v j))
      ≤ ∑ _j : Fin 3, ENNReal.ofReal (vectorAlgebraConst k) *
          ((sobolevENorm (k : ℝ) u + sobolevENorm (k : ℝ) v) *
            sobolevENorm (k : ℝ) (diffField u v)) := Finset.sum_le_sum fun j _ => hstep j
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, outerDiffConst,
          ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3), ENNReal.ofReal_ofNat]
        simp [mul_assoc, nsmul_eq_mul]

/-! ## 5. The advection bound -/

theorem partialDeriv_eq_dirDeriv (j : Fin 3) (v : Space → Space) :
    partialDeriv j v = NSFormalization.Section4.A05.dirDeriv j v := rfl

theorem SmoothL2.partialDeriv {v : Space → Space} (h : SmoothL2 v) (j : Fin 3) :
    SmoothL2 (NSFormalization.Section4.A03.partialDeriv j v) :=
  NSFormalization.Section4.A05.SmoothL2.dir h j

/-- `01-introduction.tex:83` eq:NS: the advection is the sum of the three
summands `u_j·∂_jv`, by linearity of the spatial Fréchet derivative and the
coordinate expansion of `u(x)`. -/
theorem advectionOf_eq (u v : Space → Space) (x : Space) :
    advectionOf u v x = ∑ j : Fin 3, (u x j) • partialDeriv j v x := by
  have hy : u x = ∑ j : Fin 3, (u x j) • coordinateVector j := by
    ext k; simp [coordinateVector, Pi.single_apply]
  show spatialDerivative (lift v) 0 x (u x) = _
  calc spatialDerivative (lift v) 0 x (u x)
      = spatialDerivative (lift v) 0 x (∑ j : Fin 3, (u x j) • coordinateVector j) := by
        rw [← hy]
    _ = ∑ j : Fin 3, (u x j) • spatialDerivative (lift v) 0 x (coordinateVector j) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun j _ => map_smul _ _ _
    _ = ∑ j : Fin 3, (u x j) • partialDeriv j v x := rfl

/-- The constant of the advection bound. -/
def advectionConst (m : ℕ) : ℝ := 3 * vectorTameConst m

theorem advectionConst_pos (m : ℕ) : 0 < advectionConst m := by
  have := vectorTameConst_pos m
  simp only [advectionConst]; linarith

/-- **The `H^m` bound for the advection `(u·∇)v`**, `eq:Rproduct` applied
componentwise to the summands `u_j·∂_jv` (`appendix-a-local-theory.tex:9-11`
with `:50`):
`‖(u·∇)v‖_{H^m} ≤ C_m(‖u‖_{H²}‖∇v‖_{H^m} + ‖∇v‖_{H²}‖u‖_{H^m})`.

Stated on the smooth jet class because its left-hand side contains a classical
derivative. -/
theorem advectionTame (m : ℕ) (hm : 2 ≤ m) {u v : Space → Space}
    (hu : SmoothL2 u) (hv : SmoothL2 v) :
    sobolevENorm (m : ℝ) (advectionOf u v) ≤
      ENNReal.ofReal (advectionConst m) *
        (sobolevENorm 2 u * gradientSobolevENorm (m : ℝ) v +
          gradientSobolevENorm 2 v * sobolevENorm (m : ℝ) u) := by
  have hm2 : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  set T : Fin 3 → Space → Space := fun j x => (u x j) • partialDeriv j v x with hT
  have hfun : advectionOf u v = fun x => ∑ j : Fin 3, T j x := funext (advectionOf_eq u v)
  have hloc : ∀ j, LocIntField (T j) := fun j =>
    locIntField_smul ((EuclideanSpace.proj (𝕜 := ℝ) j).comp_memLp' hu.memLp)
      (hv.partialDeriv j).memLp
  rw [hfun]
  refine (sobolevENorm_sum_three hm2 hloc).trans ?_
  have hstep : ∀ j : Fin 3, sobolevENorm (m : ℝ) (T j) ≤
      ENNReal.ofReal (vectorTameConst m) *
        (sobolevENorm 2 u * gradientSobolevENorm (m : ℝ) v +
          gradientSobolevENorm 2 v * sobolevENorm (m : ℝ) u) := by
    intro j
    have h := tameProductVector m hm (hu.memHmScalar m j) ((hv.partialDeriv j).memHmVector m)
    refine h.trans ?_
    have h1 : scalarSobolevENorm 2 (fun x => u x j) ≤ sobolevENorm 2 u :=
      scalarSobolevENorm_component_le _ _ j
    have h2 : sobolevENorm (m : ℝ) (partialDeriv j v) ≤ gradientSobolevENorm (m : ℝ) v :=
      le_columnsSobolevENorm _ _ j
    have h3 : sobolevENorm 2 (partialDeriv j v) ≤ gradientSobolevENorm 2 v :=
      le_columnsSobolevENorm _ _ j
    have h4 : scalarSobolevENorm (m : ℝ) (fun x => u x j) ≤ sobolevENorm (m : ℝ) u :=
      scalarSobolevENorm_component_le _ _ j
    gcongr
  calc ∑ j : Fin 3, sobolevENorm (m : ℝ) (T j)
      ≤ ∑ _j : Fin 3, ENNReal.ofReal (vectorTameConst m) *
          (sobolevENorm 2 u * gradientSobolevENorm (m : ℝ) v +
            gradientSobolevENorm 2 v * sobolevENorm (m : ℝ) u) :=
        Finset.sum_le_sum fun j _ => hstep j
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, advectionConst,
          ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3), ENNReal.ofReal_ofNat]
        simp [mul_assoc, nsmul_eq_mul]

end NSFormalization.Section4.A03
