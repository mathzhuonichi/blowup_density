# T13 lane 359 — assembly attempts (positive + negative)

Assembling `localization` (`eq:localization`) and the full `LocalizationAPI`
from the six proved pieces (lanes 344/345/348/353/354 + lane 363 Parseval-at-0).
Module: `formalization/NSFormalization/Section3/T13/Assembly.lean`.

## What worked (final route)

* **Square root in `ℝ≥0∞`, no `toReal`.**  The brief anticipated a `toReal` +
  `Real.sqrt_add_le` route.  Instead the whole homogeneous step stays in
  `ℝ≥0∞`: from `c_s·x² ≤ c_s·a² + 4·Tg·b²`, with `sK := (4·Tg/c_s)^{1/2}`,
  expand `c_s·(a+sK·b)² = c_s·a² + 4·Tg·b² + 2·c_s·a·sK·b` by `ring`
  (`ℝ≥0∞` is a `CommSemiring`; the middle cross term is automatically `≥ 0`),
  drop it with `le_self_add`, cancel `c_s` (`0 < c_s < ⊤`), and take the
  monotone square root `enn_le_of_sq_le : A² ≤ B² → A ≤ B` (`ENNReal.rpow` at
  exponent `1/2`).  `enn_le_of_sq_le` needs **no** finiteness of `A`, `B`.
  Only `c_s ≠ 0, ≠ ⊤` (to cancel and to form `sK`) and `Tg < ⊤` (to make `sK`,
  hence `C`, finite) are used.

* **`sK² = 4·Tg/c_s`** via `← ENNReal.rpow_natCast … 2`, `← ENNReal.rpow_mul`,
  `norm_num` on `(1/2)·2 = 1`; then `c_s·sK² = 4·Tg` via `ENNReal.div_eq_inv_mul`
  + `ENNReal.mul_inv_cancel`.

* **Cancelling `c_s`** in `c_s·x² ≤ c_s·(a+sK·b)²`: multiply both sides by
  `c_s⁻¹` with `gcongr` (discharges `c_s·x² ≤ …` from the context hypothesis),
  then `c_s⁻¹·(c_s·u) = u` via `ENNReal.inv_mul_cancel`.

* **Item 8 (`torus_cube_L2`).**  The physical `L²` Haar/cube identity is proved
  through the already-existing upstream Bochner bridge
  `NSFormalization.Paper1.integral_torusLift : ∫ torusLift g dHaar = cubeIntegral g`
  (apply at `g = ‖v·‖²`, `E = ℝ`) plus `lintegral_fundamentalCube_ofReal`
  (lane 345).  `∫⁻ ofReal = ofReal ∫` needs
  `Integrable (‖torusLift v·‖²) periodicTorusMeasure`, obtained from
  `memLp_torusLift_space hv 2` and `MemLp.integrable_norm_pow (p := 2)` (with
  `by simpa` to reconcile `(2 : ℝ≥0∞)` with `((2:ℕ) : ℝ≥0∞)`).  The two
  `torusLift` integrands are definitionally equal (T10's `torusLift` is an
  `abbrev` for `Paper1.torusLift`), so the final step is `rfl`.

* **`eLpNorm_two_sq`** (measure-agnostic `eLpNorm u 2 μ ^ 2 = ∫⁻ ofReal ‖u·‖²`):
  a direct generalisation of `KernelComparison.sq_eLpNorm_two`; used to turn the
  `eLpNorm` identity into the `lintegral` identity and back through
  `le_antisymm (enn_le_of_sq_le …) (enn_le_of_sq_le …)`.

* **`periodize f` smooth + periodic.**  T13's spatial `periodize` is bridged to
  the upstream spacetime `NavierStokes.PeriodicLocalization.periodize` of the
  time-constant lift `fun z ↦ f z.2` (`periodize_eq_vendor`, using
  `latticeVector n = lattice n`).  Smoothness reuses the upstream
  `contDiff_periodize` with the origin-centred `SupportedInCube 1` bound
  (`tsupport f ⊆ [0,1]³ ⇒ |z.2 i| ≤ 1`); periodicity reuses
  `unitSpatialPeriodsOn_periodize` (unconditional).

## Pitfalls hit and fixed

1. **`eLpNorm_two_sq` measure argument.**  Copying `sq_eLpNorm_two` verbatim
   left the `rpow_natCast` rewrite target without `∂μ` (it defaulted to
   `volume`, triggering a `MeasureSpace α` synthesis failure and a
   "did not find pattern").  Fix: write the target `lintegral` with the explicit
   `∂μ`.

2. **`lintegral_torusLift_normSq` last step.**  After
   `rw [← Paper1.integral_torusLift …]` the two Bochner integrals are
   definitionally equal but not auto-closed; an explicit `rfl` is needed.

3. **Namespacing.**  `one_ne_top` and `periodicSobolevENorm_zero_eq` are not in
   the opened namespaces — use `ENNReal.one_ne_top` and
   `NSFormalization.Section3.T15.periodicSobolevENorm_zero_eq`.

4. **`set sK` folding.**  `homogeneous_bound` returns the raw
   `(4·tailGeomConst s c r / cFrac s)^{1/2}` expression; after `set sK := …` in
   `localization`, fold it in the imported hypothesis with `rw [← hsKdef] at hHom`
   before the final `calc`.

## Nothing left open

All six `LocalizationAPI` fields are proved; `localizationAPI : LocalizationAPI`
type-checks and the probe closes the record by `exact`.  Gates: build 0 errors,
`lake env lean` on module + probe + axioms exit 0, `make check` exit 0, all 11
declarations `[propext, Classical.choice, Quot.sound]`.
