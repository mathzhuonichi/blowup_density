# Lane 345 — `torus_identity` attempts log

Target: the `torus_identity` field of `research/T13/probes/api_on_canonical.lean`
(`03-torus.tex:53-72`).  Delivered in
`formalization/NSFormalization/Section3/T13/TorusIdentity.lean`.
**No named input**: the field is proved outright.

## Route actually taken (the paper's own proof)

1. `fundamentalCube` (`[0,1]³`) is replaced by the half-open representative
   `halfOpenCube` (`[0,1)³`) up to a null set
   (`fundamentalCube_ae_eq_halfOpenCube`).
2. `lintegral_eq_tsum_halfOpenCube`: the half-open cube tiles `R³` exactly.
   This avoids Mathlib's `ZSpan`/`IsAddFundamentalDomain` subgroup indexing
   altogether: the tiling is proved from
   `∑'_n 1_{D}(x - n) = 1`, whose unique nonzero term is `n i = ⌊x i⌋`
   (`mem_halfOpenCube_iff`, `tsum_indicator_halfOpenCube`).  With
   `lintegral_sub_right_eq_self` this gives
   `∫⁻ g = ∑'_n ∫⁻_{D} g(· + n)` for every measurable nonnegative `g`.
3. `lintegral_cube_periodicKernel`: unfolding `periodicKernel` and reindexing
   `n ↦ -n` turns the inner cube integral against the periodized kernel into a
   whole-space integral against `fractionalRadialKernel`.
4. `lintegral_whole_shift` (`lintegral_sub_left_eq_self`) makes it an integral
   in the difference variable `h`, and `lintegral_swap_diff` (Tonelli) pulls the
   `h` integral outside.
5. `cubeIntegral_diff_norm_sq`: Parseval at fixed shift.  Needed the Fourier
   translation rule `periodicFourierCoeff_shift`, proved on the torus
   (`torusLift_sub_shift` + Haar right-invariance + `mFourier_add_point`)
   rather than on the cube.
6. `kernelIntegral_eq`: rotation + dilation.  Rotation uses
   `Submodule.reflection_sub` (the reflection exchanging two vectors of equal
   norm) and `LinearIsometryEquiv.measurePreserving`; dilation uses
   `Measure.map_addHaar_smul` through `lintegral_comp_smul_space`.
7. `exists_homogeneous_datum` / `periodicHomogeneousENorm_sq_smooth`: the T10
   homogeneous datum of `meanZeroPartT f` is built explicitly as the `ℓ²`
   sequence `|2πk|^s f̂_i(k)`; the infimum in `periodicHomogeneousENorm`
   collapses because the datum is unique (`homogeneousDatum_unique`).
8. `cFrac_lt_top`: near-field bound `|e^{ih₁}-1|² ≤ 4|h|²` with
   `integrableOn_ball_of_norm_le_rpow`, far-field bound `≤ 4` with
   `finite_integral_one_add_norm` (`1+‖h‖ ≤ 2‖h‖` for `‖h‖ ≥ 1`).

## Paths tried and abandoned

- **Mathlib `ZSpan.isAddFundamentalDomain` + `IsAddFundamentalDomain.lintegral_eq_tsum`.**
  Correct, but the acting group is `↥(span ℤ (range b))`, so every lattice sum
  would have to be reindexed from that subgroup to `PeriodicFrequency`, and
  `Zspan.fundamentalDomain b` still needs the null-set comparison with
  `fundamentalCube`.  The hand-rolled tiling (item 2) is shorter and needs no
  new instance.
- **Cube-side translation invariance for the Fourier coefficient.**  Proving
  `cubeIntegral (g(· - h)) = cubeIntegral g` directly needs a Bochner analogue
  of the tiling; going through the torus quotient (`torusPoint`,
  `torusLift_sub_shift`) and `integral_add_right_eq_self` is a few lines
  instead.  `periodicTorusMeasure.IsAddRightInvariant` does not resolve by
  instance search and is supplied by the named theorem
  `periodicTorusMeasure_isAddRightInvariant` (`change` to `Measure.pi …`,
  exactly as T10's probability instance does).
- **`fun_prop` for `Measurable (fun h ↦ ‖h‖ ^ a)` with `a < 0`** fails
  (`Real.continuous_rpow_const` wants `0 ≤ a`); `measurability` succeeds.
  `fun_prop` also reports `function expected, got f : SpatialField` on goals
  mentioning a `SpatialField` variable, so those measurability side goals are
  discharged by explicit `Continuous.measurable` terms.
- **`rw` with higher-order patterns** (`lintegral_comp_smul_space _`,
  `lintegral_add_right_eq_self`) fails to match beta-redexes; every such step
  passes the integrand lambda explicitly or goes through `show … from h`.
- **Heartbeats.** `exists_homogeneous_datum`,
  `periodicHomogeneousENorm_sq_smooth` and `torus_identity_smooth` need
  `set_option maxHeartbeats 400000 in`; all other declarations are default.
  The first draft kept the datum construction and the norm computation in one
  declaration and hit the 200k `whnf` timeout — splitting out
  `homogeneousDatum_norm_sq` (a statement about *any* datum with the explicit
  coefficients) fixed it.

## Residual gap

`research/T13/probes/torus_identity_closes.lean` supplies non-vacuity by a
nonconstant smooth periodic single mode `x ↦ cos(2π x₁) e₁` and by the
*per-frequency* evaluation of both sides at `k = e₁`
(`∫⁻ |1 - e^{-2πi h₁}|² K_s = (2π)^{2s} c_s` and
`homogeneousDatumWeight s e₁ ^ 2 = (2π)^{2s}`).  The fully explicit value of
`ITorus s (cos(2π x₁) e₁)` (namely `c_s (4π²)^s / 2`) is **not** computed: it
needs `periodicFourierCoeff` of a character (orthogonality) plus additivity and
scalar homogeneity of `periodicFourierCoeff`, none of which is in the tree.
That is a bounded follow-up, not an obstacle to the field itself.
