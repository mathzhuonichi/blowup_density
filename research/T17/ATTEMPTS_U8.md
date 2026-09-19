# T17 U8 attempts — `spatialVolumeConst` / `force_spatial_volume` / `force_time_length`

Lane 431, module `formalization/NSFormalization/Section3/T17/ForceVolume.lean`.

## Successful route

The measured objects are the projections of `tsupport (torusSpaceTimeLift f)`,
where `torusSpaceTimeLift f z = f (z.1, torusRepr z.2)` reads the field at the
canonical `(0,1]³` representative of a torus point (`Correction.lean:52-61`).
Lane 425's `force_support` controls `tsupport f` in periodic Euclidean space, so
the lane is two steps.

* **Support transfer** (`tsupport_torusSpaceTimeLift_subset`).  A point of
  `Function.support (torusSpaceTimeLift f)` has
  `torusRepr z.2 ∈ periodicSet (ball x₀ ρ)`, i.e.
  `torusRepr z.2 - latticeVector k ∈ ball x₀ ρ`; since `torusPoint` kills
  lattice vectors (`torusPoint_sub_latticeVector`) and inverts `torusRepr`
  (`T13.torusPoint_torusRepr`), this puts `z.2 ∈ torusPoint '' ball x₀ ρ`.  The
  target is then enlarged to `Icc a b ×ˢ torusPoint '' closedBall x₀ ρ`, which
  is **closed** (`isClosed_Icc.prod` on a continuous image of a compact set), so
  `closure_minimal` carries the inclusion to `tsupport`.
* **Haar/Lebesgue set bridge** (`measure_torusPoint_image_le`): for compact
  `A ⊆ R³`, `periodicTorusMeasure (torusPoint '' A) ≤ volume A`.  Take
  `g = (periodicSet A).indicator 1`.  It is unit-periodic
  (`indicator_periodicSet_isPeriodicSpatial`), so `T13.torusLift_torusPoint`
  evaluates `torusLift g (torusPoint a) = g a = 1` for every `a ∈ A`, i.e. the
  lift is `≥ 1` on the whole image, with no representative arithmetic.  Then
  T15's measure-free change of variables `lintegral_enorm_torusLift` (at `q = 1`)
  moves the Haar integral to `∫⁻ x in fundamentalCube`, `fundamentalCube` is
  swapped for `halfOpenCube` by `T13.fundamentalCube_ae_eq_halfOpenCube`, the
  integrand is majorised pointwise by
  `∑' n, A.indicator 1 (x + latticeVector n)` (the frequency `-k` absorbs the
  witness `k` of `x ∈ periodicSet A`), and `lintegral_tsum` +
  `T13.lintegral_eq_tsum_halfOpenCube` fold the sum back into
  `∫⁻ x, A.indicator 1 x = volume A`.

The two quantitative bounds are then Mathlib's
`EuclideanSpace.volume_closedBall_fin_three` on `closedBall x₀ (ε·θR)` and
`Real.volume_Icc` on `Icc (T - 2ε²) (T + 2ε²)`.  The constants are the
manuscript's: `spatialVolumeConst θR = π·4/3·θR³` and `4`.

`hv : ContDiff ℝ ∞ v` (the documented G1 premise, `research/T17/SPEC_ISSUES.md`)
is inherited **only** through lane 425's `force_support`; no step of this lane
uses the regularity of the reference again.  The only other premise beyond
lane 425's is `0 ≤ θR`, which is `T16.LocalPotentialAPI.theta_radius_pos` — data
already fixed by the cutoff record, not a new hypothesis, and needed because
`ENNReal.ofReal` would otherwise erase a negative constant.

## What did not work, and why

1. **The "hard direction" `torusPoint x = torusPoint y → ∃ k, x - y = latticeVector k`.**
   This is what one needs if the bound on `periodicTorusMeasure (torusPoint '' A)`
   is obtained by pulling the image back to the `Ioc (0,1]³` representative and
   using `A.indicator 1` as the test function: one must know that
   `torusRepr (torusPoint a)` differs from `a` by a lattice vector.  It is true
   but costs a coordinatewise `QuotientAddGroup.eq_iff_sub_mem` plus a choice
   over `Fin 3` to assemble the frequency.  Replaced entirely by testing against
   `(periodicSet A).indicator 1`, whose unit periodicity makes
   `T13.torusLift_torusPoint` applicable: the representative never appears.
2. **Translating the ball into the fundamental cube.**  Since `ε·θR < r < 1/2`,
   the closed ball fits in a cube of side `1` after a translation, and
   `T13.periodicTorusMeasure_isAddRightInvariant` would then reduce the bound to
   a single-copy statement.  Rejected: it needs `Set.image_add_right`,
   `measure_preimage_add_right`, and the coordinate bound
   `|x i - c i| ≤ ‖x - c‖` on `EuclideanSpace` (no ready-made
   `PiLp.norm_apply_le_norm` at this pin), and it produces a lemma restricted to
   small balls.  The lattice-sum proof is the same length and gives the general
   compact-set statement, which U9/U10 can reuse.
3. **`measure_iUnion_le` on `periodicSet A = ⋃ k, (A + latticeVector k)`.**  The
   set-level version of the same argument needs a `Equiv.neg` reindexing of
   `T13.lintegral_eq_tsum_halfOpenCube`, `Measure.restrict_apply` bookkeeping and
   measurability of `periodicSet A`.  The pointwise majorant used instead
   (`indicator (periodicSet A) 1 x ≤ ∑' n, indicator A 1 (x + latticeVector n)`)
   needs none of these: `lintegral_mono` is everywhere-pointwise.
4. **Keeping the manuscript's open ball in the target of the lift.**
   `torusPoint '' ball x₀ ρ` is not closed, and `torusRepr` is discontinuous, so
   the inclusion for `Function.support` cannot be pushed through the `closure`
   in `tsupport`.  Enlarging to `closedBall` fixes this and costs nothing:
   `volume (closedBall x₀ ρ) = volume (ball x₀ ρ)`, so the constant is
   unchanged.  (Lane 425's `force_support`, which is about the *Euclidean*
   support, does keep the open ball.)
5. **`funext` on `Space`.**  At this pin `Space = EuclideanSpace ℝ (Fin 3)` is a
   `WithLp` structure, not a Pi type, so `funext` fails with
   "could not unify the conclusion of `@funext`".  All the lattice-vector
   identities use `PiLp.ext` instead.  (`funext` *does* work for
   `PeriodicTorus = Fin 3 → UnitAddCircle`, which is a genuine Pi type.)
6. **Reusing T13's `latticeVector` spelling.**  `T16.periodicSet` is defined with
   `T16.latticeVector`; the two definitions are `rfl`-equal but not syntactically
   equal, so lemmas proved about `T13.latticeVector` simply do not fire under
   `rw` inside a `periodicSet` membership goal ("Did not find an occurrence of
   the pattern").  §0 therefore restates the lattice algebra in the T16 spelling
   and crosses over once, in `latticeVector_eq`, exactly where
   `T13.lintegral_eq_tsum_halfOpenCube` is invoked.
7. **`push_cast` on `((-k) i : ℝ)`.**  It leaves `↑((-k) i) = -↑(k i)` untouched;
   `Pi.neg_apply` has to be rewritten first.
8. **An unconditional `spatialVolumeConst_nonneg`.**  Definitions such as
   `π·4/3·|θR|³` or `π·4/3·(max θR 0)³` make the nonnegativity field
   hypothesis-free, but distort the manuscript constant.  Rejected: the honest
   constant is `π·4/3·θR³`, and `0 ≤ θR` is available at assembly as
   `theta_radius_pos`.

## Negative probes

* `research/T17/probes/rev431_wrong_volume_exponent.lean` — `ε³` mutated to `ε²`;
  expected to fail, and does (type mismatch on the `ENNReal.ofReal` argument).
* `research/T17/probes/rev431_wrong_time_length.lean` — `4ε²` mutated to `2ε²`;
  expected to fail, and does.
