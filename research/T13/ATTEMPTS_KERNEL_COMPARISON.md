# T13 lane 354 — KernelComparison attempts (positive + negative)

Module: `formalization/NSFormalization/Section3/T13/KernelComparison.lean`
(namespace `NSFormalization.Section3.T13`).  Base: lane 353's
`LocalizationKernel.lean` (⊕ 344/345).  Goal: the four residual items of
`ATTEMPTS_LOCALIZATION_KERNEL.md` (§2 of `03-torus.tex:73-98`).

## Statement fidelity check (before proving)

Checked each brief statement against `03-torus.tex:79-92`:

* Item 1 (`exists_separation`): matches `d = dist(B̄,∂Q) > 0` (line 80).  `d` is
  realized concretely by `separationRadius c r = min_i min(cᵢ-r, 1-cᵢ-r)`.
* Item 2 (`tailGeomConst`, `latticeTail_le_tailGeomConst`): matches
  `sup_{x∈B̄,y∈Q} ∑_{n≠0}|x-y+n|^{-3-2s} ≤ C_{s,d}` (lines 85-88).  **The
  lead-suggested constant `tailGeomConst s c r` was verified and adopted**; it
  is an explicit `ℝ≥0∞` expression in `s,δ` (see below), not a hard target.
* Item 3 (`iTorus_singular_le`): matches "the `n=0` term of `I_𝕋(z_𝕋)` is at
  most `I_ℝ(z_ℝ)`" (lines 89-90).
* Item 4 (`iTorus_periodize_le`): matches `eq:localization`, with `4C_{s,d}‖z‖²`
  (lines 91-94) spelled `4·tailGeomConst s c r·(eLpNorm f 2 volume)²`.

All four are **true as written**; no counterexample.  The only elaboration is
making the constant explicit.

## Shipped (proved)

### §0 helpers
* `latticeVector_norm_ge_one` (public re-derivation; lane 353's is `private`).
* `latticeTail_neg`: evenness `latticeTail s (-h) = latticeTail s h` via the
  self-inverse `Equiv` `n ↦ -n` on `{n // n ≠ 0}` and `‖-v‖ = ‖v‖`.

### §1 separation (item 1)
* `ball_coord_bounds`: `0 < cᵢ-r ∧ cᵢ+r < 1` per coordinate (generalizes lane
  353's `two_r_lt_one_of_closure_ball_subset` to all `i`, via the points
  `c ± single i r ∈ closedBall ⊆ interior cube = (0,1)³`).
* `separationRadius := Finset.univ.inf' _ (fun i => min (cᵢ-r) (1-cᵢ-r))`;
  `separationRadius_le` (`Finset.inf'_le`), `separationRadius_pos`
  (`Finset.lt_inf'_iff` + `ball_coord_bounds`), `closedBall_coord_sep`
  (`|xᵢ-cᵢ| ≤ ‖x-c‖ ≤ r` ⟹ `δ ≤ xᵢ ≤ 1-δ`).
* `exists_separation`: `∃ δ>0, closure(ball) ⊆ {x | ∀ i, δ ≤ xᵢ ≤ 1-δ}`.

### §2 geometry (item 2)
* `norm_sub_le_sqrt3`: `‖x-y‖ ≤ √3` for `x,y ∈ Q` (each `|xᵢ-yᵢ| ≤ 1`,
  `EuclideanSpace.norm_eq` + `Real.sqrt_le_sqrt`).
* `tailGeomC0 c r := min (1/2) (separationRadius c r / (2√3))`, `tailGeomC0_pos`.
* **`geom_norm_lower`** — the crux: `tailGeomC0 c r · ‖latticeVector n‖ ≤
  ‖(x-y)+latticeVector n‖` for `x∈B̄, y∈Q, n≠0`.  Two sub-bounds,
  `‖·‖ ≥ δ` (coordinate separation, via the bad coordinate `nᵢ≠0`:
  `nᵢ≥1 ⟹ wᵢ ≥ δ`; `nᵢ≤-1 ⟹ wᵢ ≤ -δ`) and `‖·‖ ≥ ‖n‖-√3` (reverse triangle),
  fused by a case split on `2√3 ≤ ‖n‖`: large `‖n‖` uses `‖n‖-√3 ≥ ‖n‖/2 ≥ c₀‖n‖`
  (needs `c₀ ≤ 1/2`); small `‖n‖ ≤ 2√3` uses `c₀‖n‖ ≤ (δ/(2√3))·2√3 = δ` (needs
  `c₀ ≤ δ/(2√3)`).
* `tailGeomConst s c r := (ofReal (tailGeomC0 c r))^(-(3+2s)) · tailSum s`;
  `tailGeomConst_lt_top` (mirrors `tailConst_lt_top`, needs `c₀>0`);
  `latticeTail_le_tailGeomConst` (per-term `ℝ≥0∞` `rpow` estimate, mirrors
  `latticeTail_le_tailConst` with `geom_norm_lower` in place of `(1-ρ)‖n‖`).

### §3 singular part (item 3)
* `iTorus_singular_le`: `∫_Q∫_Q ‖f x-f y‖²·frac(x-y) ≤ I_ℝ(f)`.  Chain:
  enlarge inner `y`-domain to `ℝ³` (`setLIntegral_le_lintegral`); inner shift
  `∫_u ‖f x-f u‖²·frac(x-u) = ∫_h ‖f x-f(x-h)‖²·frac(h)` (`lintegral_whole_shift`,
  lane 345); enlarge outer `x`-domain to `ℝ³`; Tonelli
  (`lintegral_lintegral_swap` on `measurable_prod_diff`); translate the inner
  `x`-integral by `+h` (`lintegral_add_right_eq_self`, Haar) turning
  `‖f x-f(x-h)‖²` into `‖f(x+h)-f x‖²`, the `I_ℝ` integrand.  Only `Continuous f`
  is used.

### §4-6 assembly (item 4)
* Measurability: `measurable_latticeTail`, `measurable_prod_frac`,
  `measurable_prod_tail`, `measurable_inner_frac`
  (`Measurable.lintegral_prod_right`).
* `periodicKernel_split`: `periodicKernel = frac + latticeTail` (splits `n=0`
  via `ENNReal.tsum_eq_add_tsum_ite 0` and `tsum_subtype`).
* `volume_fundamentalCube = 1` (`PiLp.volume_preserving_toLp`,
  `toSpace_preimage_fundamentalCube`, `volume_pi_pi`, `Real.volume_Icc`).
* `sq_eLpNorm_two`: `(eLpNorm f 2 volume)² = ∫⁻ ‖f‖²` (the `‖f‖₂²` spelling
  bridge; `eLpNorm'` unfold + `ENNReal.rpow` algebra + `‖·‖ₑ = ofReal‖·‖`).
* `iTorus_periodize_le`: on `Q`, `periodize f = f` (`periodize_eq_of_mem_cube`,
  344); split kernel; singular part `≤ I_ℝ` (item 3); tail part bounded by
  `‖f x-f y‖² ≤ 2‖f x‖²+2‖f y‖²`, `latticeTail(x-y) ≤ tailGeomConst` on the
  support (item 2, with `latticeTail_neg` for the `y∈B̄` case), `|Q|=1`, giving
  `4·tailGeomConst·∫_Q‖f‖² ≤ 4·tailGeomConst·(eLpNorm f 2 volume)²`.

## Negative notes / friction (what had to change)

* **Mathlib name drift under this pin (`v4.34.0-rc2`).**  The monotone-mul
  lemmas are renamed: `mul_le_mul_left'`→`mul_le_mul_right`,
  `mul_le_mul_right'`→`mul_le_mul_left` (`a*b ≤ a*c` vs `b*a ≤ c*a`).  The old
  primed names are **not** in scope ("Unknown identifier").
* `ENNReal.tsum_eq_add_tsum_ite` (not the additive-group `tsum_eq_add_tsum_ite`,
  which needs subtraction ENNReal lacks) is the right split lemma.
* `tsum_subtype`'s subtype `↥{n | n≠0}` is only **defeq**, not syntactically
  equal, to `latticeTail`'s `{n // n≠0}`.  A `rw [tsum_subtype …]` **fails**
  ("did not find an occurrence"); stating it as a typed `have`
  (`hlt : latticeTail s h = ∑' x, indicator … x := tsum_subtype …`) lets
  elaboration close the defeq.
* `ENNReal.ofReal_rpow_of_nonneg : ofReal x ^ p = ofReal (x^p)` goes **forward**
  (turns `(ofReal x)^p` into `ofReal(x^p)`); an initial `←` was wrong.
* `lintegral_add_right_eq_self` needs the measure pinned
  (`(μ := (volume : Measure Space))`) or the `IsAddRightInvariant` instance
  search is stuck on a metavariable.
* `rw [IReal]` on a bare `def` occurrence fails ("Failed to rewrite using
  equation theorems"); the surrounding `lintegral_congr` already unfolds it, so
  the `rw` was simply dropped.

## Nothing left open

All four items are shipped with the standard three axioms.  The remaining
`localization` `LocalizationAPI` field is lane 359's assembly (it also needs the
Parseval-at-0 bridge `periodicSobolevENorm 0 (periodize f) = eLpNorm …`, a T10
obligation), sketched in the probe's consumer `example`.
