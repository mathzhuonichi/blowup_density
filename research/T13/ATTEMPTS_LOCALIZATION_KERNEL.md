# T13 lane 353 — LocalizationKernel attempts (positive + negative)

Module: `formalization/NSFormalization/Section3/T13/LocalizationKernel.lean`
(namespace `NSFormalization.Section3.T13`).  Base: lane 345 ⊕ lane 344 ⊕
`origin/erenup/integration-section3`.

## Shipped (proved)

### §1  Uniform lattice-tail bound
* `summable_latticeVector_rpow {p} (hp : 3 < p) : Summable (fun n : PeriodicFrequency => ‖latticeVector n‖ ^ (-p))`.
  Route: reconstruct the `ℤ³` lattice `freqLattice := span ℤ (range (Pi.basisFun ℝ (Fin 3)))`
  (the private `FrequencyLattice`/`frequencyEquiv` of `Paper1/PeriodicH2Embedding.lean`
  are not importable), get `ZLattice.summable_norm_rpow freqLattice (-p) (hr : -p < -finrank = -3)`
  in the **sup** (`Pi`) norm, then dominate the Euclidean (`EuclideanSpace`, `L²`)
  norm series by the sup one via `Real.rpow_le_rpow_of_nonpos` and
  `‖(fun i => (nᵢ:ℝ))‖_sup ≤ ‖latticeVector n‖` (from `abs_spaceCoord_le_norm`).
* `tailSum`, `tailConst`, `tailSum_lt_top (0<s)`, `tailConst_lt_top (0<s, ρ<1)`,
  `latticeTail_le_tailConst (0≤s, 0<ρ, ρ<1, ‖h‖≤ρ)`.
  Pointwise: `‖h+n‖ ≥ ‖n‖-‖h‖ ≥ ‖n‖-ρ ≥ (1-ρ)‖n‖` (uses `‖n‖≥1` for `n≠0`), then
  antitone `(·)^{-(3+2s)}` via `ENNReal.rpow_neg`+`inv_le_inv`+`rpow_le_rpow`,
  `ENNReal.mul_rpow_of_ne_top`, `ENNReal.tsum_mul_left`, `ENNReal.tsum_le_tsum`.
* `two_r_lt_one_of_closure_ball_subset (0<r, closure(ball c r) ⊆ interior cube) : 2r < 1`.
  Route: `closure_ball c r = closedBall c r`; the two points `c ± single 0 r`
  lie in the closed ball hence in `interior cube = (0,1)³`, giving `0 < c₀-r` and
  `c₀+r < 1`, so `2r < 1` by `linarith`.

### §3  Inhomogeneous ≤ L² + homogeneous
* `periodicSobolevENorm_le_l2_add_homogeneous (0<s, s≤1, smooth periodic g) :
    periodicSobolevENorm s g ≤ periodicSobolevENorm 0 g + periodicHomogeneousENorm s (meanZeroPartT g)`.
  Route: the three data (`exists_periodicDatum_smooth s`, `… 0`,
  `exists_homogeneous_datum` for `meanZeroPartT g`), then
  `As.1 = reweightDatum w 1 hw (A0.1 + Ah.1)` with
  `w k = periodicFrequencyWeight k^{s/2} / (1 + homogeneousDatumWeight s k) ≤ 1`,
  where `≤ 1` is `Real.rpow_add_le_add_rpow` (subadditivity `(1+x)^{s/2} ≤ 1 + x^{s/2}`,
  needs `s/2 ≤ 1`).  Then `reweightDatum_enorm_le'` and `enorm_add_le`.
  Uniqueness of the three data gives the norm equalities
  (`periodicSobolevENorm_eq_datum`, `homogeneousDatum_unique`).

## Norm-spelling decisions (§3)

* **`L²` term = `periodicSobolevENorm 0 g`** (coefficient side), NOT
  `eLpNorm g 2 periodicTorusMeasure`.  The brief's literal spelling
  `eLpNorm g 2 periodicTorusMeasure` does **not** type-check (`g : Space → Space`
  vs a measure on `PeriodicTorus`; the physical spelling would be
  `eLpNorm (torusLift g) 2 periodicTorusMeasure`).  The coefficient side is what
  the reweighting proof actually produces and needs no Parseval bridge.  Lane 354
  still needs one Parseval-at-0 identity
  `periodicSobolevENorm 0 (periodize f) = eLpNorm (torusLift (periodize f)) 2 periodicTorusMeasure`
  to connect this term to `endpoint_zero`'s `eLpNorm f 2 volume` (a T10 obligation,
  COMPARISON item 8).
* **`meanZeroPartT` is required**: `periodicHomogeneousENorm s g = ⊤` unless `g`
  is mean-zero (`IsPeriodicHomogeneousDatum` carries `IsMeanZeroT`), so the
  homogeneous term must be taken of `meanZeroPartT g`.
* Hypothesis `s ≤ 1` (not `s < 1`) — the subadditivity only needs `s/2 ≤ 1`.

## NOT shipped — §2 kernel comparison `iTorus_periodize_le` (gap)

Target (brief): for `0<s<1`, `0<r`, `closure(ball c r) ⊆ interior cube`, `f`
smooth with `SupportedInBall c r f`:
`ITorus s (periodize f) ≤ IReal s f + 4 * tailConst s (2r) * (eLpNorm f 2 volume)^2`.

**Why the stated constant is insufficient (negative result).**
On the cube `periodize f = f`, and `periodicKernel s (x-y) = fractionalRadialKernel s (x-y) + latticeTail s (x-y)`.
The tail contribution is `T = ∫_{Q}∫_{Q} ‖f x - f y‖² · latticeTail s (x-y)`.
`‖f x - f y‖²` is nonzero only when `x ∈ ball ∨ y ∈ ball`.  After
`‖f x - f y‖² ≤ 2‖f x‖² + 2‖f y‖²` and symmetry, `T ≤ 4 ∫_{x∈ball}‖f x‖² ∫_{y∈Q} latticeTail s (x-y)`.
For `x ∈ ball` and `y ∈ Q` the difference `x-y` ranges over `ball - Q`, whose
Euclidean norm can reach `≈ √3`, **not** `≤ 2r`.  So `latticeTail_le_tailConst`
(which needs `‖x-y‖ ≤ ρ = 2r < 1`) applies only on the sub-region `x,y ∈ ball`,
and cannot bound the `x∈ball, y∈Q\ball` region.  The paper (`03-torus.tex:79-92`)
uses instead the geometric separation `d = dist(closure B, ∂Q) > 0`:
`|x - y + n| ≥ d` for `x∈B̄, y∈Q, n≠0` (each coordinate with `nᵢ≠0` gives
`|xᵢ-yᵢ+nᵢ| ≥ δ` where `B̄ ⊆ [δ,1-δ]³`), plus `|x-y+n| ≥ |n|/2` for `|n|>2√3`,
yielding a finite `C_{s,d}` and the bound `T ≤ 4 C_{s,d} ‖f‖₂²`.
So the honest statement's constant is `C_{s,d}` (depending on `d`), not
`tailConst s (2r)`.  Reporting this as a hypothesis/constant strengthening per
the brief's escape clause rather than shipping a false-as-stated theorem.

**Residual lemmas needed for a correct §2 (exact statements).**
1. `∃ δ, 0 < δ ∧ closure (ball c r) ⊆ {x | ∀ i, δ ≤ x i ∧ x i ≤ 1 - δ}`
   (compactness of the closed ball inside the open cube).
2. `tailGeomConst s c r : ℝ≥0∞`, `tailGeomConst_lt_top`, and
   `∀ x ∈ B̄, ∀ y ∈ Q, latticeTail s (x - y) ≤ tailGeomConst s c r`
   (the two-case `≥ δ` / `≥ |n|/2` geometric bound + summability).
3. `iTorus_singular_le : ∫_{Q}∫_{Q} ‖f x - f y‖² · fractionalRadialKernel s (x-y) ≤ IReal s f`
   — substitute `y = x + h` in the inner integral (translation-invariant
   `lintegral`), Tonelli to swap `∫_x ∫_h`, then enlarge both domains to `ℝ³`.
4. `iTorus_periodize_le : ITorus s (periodize f) ≤ IReal s f + 4 * tailGeomConst s c r * (eLpNorm f 2 volume)^2`.
   Assemble: `periodize f = f` on `Q` (`periodize_eq_of_mem_cube`, 344),
   split `periodicKernel = fractionalRadialKernel + latticeTail` at `n=0`, use (3)
   for the singular part and (2) + the ball/support vanishing + the
   `2‖f x‖²+2‖f y‖²` bound for the tail part, `|Q|=1`.

None of items 1–4 are shipped.  Item 3 (the singular change of variables) and
item 2 (the geometric constant + its summability) are each substantial
`lintegral` developments; a full §2 is its own lane.
