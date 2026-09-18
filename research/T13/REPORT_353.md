# REPORT 353 — T13 localization kernel estimates (§1, §3; §2 open)

Branch `erenup/353-T13-localization-kernel`.  No named inputs, no `sorry`/
`axiom`/`native_decide`, no placeholder or alias definitions.

## 1. What was proved

New module `formalization/NSFormalization/Section3/T13/LocalizationKernel.lean`
(namespace `NSFormalization.Section3.T13`) proves three of the concrete analytic
estimates behind `eq:localization` (`paper/sections/03-torus.tex:73-92`).  None
is a `LocalizationAPI` field; lane 354 assembles them with `torus_identity`
(345), `endpoint_zero`/`constant_pos_finite` (344) and `wholeSpace_identity`
(348).

**(a) Uniform lattice-tail bound** (`:80-89`).
- `summable_latticeVector_rpow {p : ℝ} (hp : (3:ℝ) < p) : Summable (fun n : PeriodicFrequency => ‖latticeVector n‖ ^ (-p))`.
- `tailSum (s : ℝ) : ℝ≥0∞ := ∑' n : {n // n ≠ 0}, (ENNReal.ofReal ‖latticeVector n.1‖) ^ (-(3 + 2*s))`.
- `tailConst (s ρ : ℝ) : ℝ≥0∞ := (ENNReal.ofReal (1 - ρ)) ^ (-(3 + 2*s)) * tailSum s`.
- `tailSum_lt_top {s} (hs : 0 < s) : tailSum s < ⊤`.
- `tailConst_lt_top {s ρ} (hs : 0 < s) (hρ : ρ < 1) : tailConst s ρ < ⊤`.
- `latticeTail_le_tailConst {s ρ} (hs : 0 ≤ s) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {h : Space} (hh : ‖h‖ ≤ ρ) : latticeTail s h ≤ tailConst s ρ`.
  Constant realised: `tailConst s ρ = (ofReal (1-ρ))^{-(3+2s)} · ∑_{n≠0}(ofReal ‖n‖)^{-(3+2s)}`.

**(b) Geometric consequence** (`:79-80`).
- `two_r_lt_one_of_closure_ball_subset {c r} (hr : 0 < r) (hball : closure (Metric.ball c r) ⊆ interior fundamentalCube) : 2 * r < 1`.

**(c) Inhomogeneous ≤ L² + homogeneous on T³** (`:73-78`).
- `periodicSobolevENorm_le_l2_add_homogeneous {s} (hs : 0 < s) (hs1 : s ≤ 1) {g : SpatialField} (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicSpatial g) : periodicSobolevENorm s g ≤ periodicSobolevENorm 0 g + periodicHomogeneousENorm s (meanZeroPartT g)`.

## 2. What is in Lean now

`LocalizationKernel.lean`, 8 public declarations, all with axioms exactly
`[propext, Classical.choice, Quot.sound]` (`research/T13/axioms_localization_kernel.lean`).

Reused: `ZLattice.summable_norm_rpow` (lattice convergence, exponent `3+2s>3`);
`ConstantEndpoints` (`latticeVector_zero`, `abs_spaceCoord_le_norm`,
`interior_fundamentalCube`); `TorusIdentity` (`exists_homogeneous_datum`,
`homogeneousDatum_unique`, `homogeneousDatumWeight_{zero,nonneg}`,
`periodicFourierCoeff_meanZeroPart`); `CriterionBridge`
(`exists_periodicDatum_smooth`, `periodicSobolevENorm_eq_datum`); `T12`
(`reweightDatum`, `reweightDatum_apply`, `reweightDatum_enorm_le'`);
`Real.rpow_add_le_add_rpow` (coefficientwise subadditivity `(1+x)^{s/2} ≤ 1 + x^{s/2}`).

Probe `research/T13/probes/localization_kernel_closes.lean` instantiates §1 (on
`latticeTail (1/2) 0 ≤ tailConst (1/2) (3/4)`, `tailSum`/`tailConst` finite),
`two_r_lt_one` on the explicit admissible ball `ball probeCenter (3/8)`, and §3
on the nonconstant smooth periodic mode `probeMode x = cos(2π x₀) e₀`.  A final
`example` records lane 354's assembly step: §3 followed by `add_le_add hL2 hHom`
(the `L²` and homogeneous bounds it will supply).

## 3. Gap

**§2 kernel comparison `iTorus_periodize_le` is NOT shipped.**  As stated in the
brief,
`ITorus s (periodize f) ≤ IReal s f + 4 * tailConst s (2r) * (eLpNorm f 2 volume)^2`,
the constant is mathematically insufficient: after `periodize f = f` on the cube
and the split `periodicKernel = fractionalRadialKernel + latticeTail`, the tail
double integral `∫_Q∫_Q ‖f x - f y‖² latticeTail s (x-y)` is supported where
`x ∈ ball ∨ y ∈ ball`; in the region `x ∈ ball, y ∈ Q\ball` the argument `x-y`
has Euclidean norm up to `≈ √3`, so `latticeTail_le_tailConst` (which needs
`‖x-y‖ ≤ 2r < 1`) does not apply.  The paper uses the geometric separation
`d = dist(closure B, ∂Q) > 0`, giving a different constant `C_{s,d}`.  This is a
constant/hypothesis strengthening (`4·tailConst s (2r)` → `4·C_{s,d}`), so it was
not shipped as a false-as-stated theorem.

Exact residual lemmas (statements in `research/T13/ATTEMPTS_LOCALIZATION_KERNEL.md`,
"NOT shipped — §2"): (1) `∃ δ>0, closure(ball c r) ⊆ [δ,1-δ]³`; (2) a finite
geometric tail constant `tailGeomConst s c r` with the uniform bound
`∀ x∈B̄, y∈Q, latticeTail s (x-y) ≤ tailGeomConst s c r` (two-case `≥δ` / `≥|n|/2`
+ summability); (3) the singular change of variables
`∫_Q∫_Q ‖f x - f y‖² fractionalRadialKernel s (x-y) ≤ IReal s f`
(substitute `y=x+h`, Tonelli, enlarge domains); (4) the assembly.

**§3 `L²`-spelling note.**  The `L²` term is the coefficient-side
`periodicSobolevENorm 0 g` — the brief's `eLpNorm g 2 periodicTorusMeasure` does
not type-check for `g : Space → Space`.  Lane 354 needs a Parseval-at-0 identity
to connect `periodicSobolevENorm 0 (periodize f)` to `endpoint_zero`'s
`eLpNorm f 2 volume` (T10 obligation, COMPARISON item 8).

## 4. Commands and results

```
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T13.LocalizationKernel
  → Build completed successfully; module 0 errors (1 harmless `if_neg` deprecation warning)
cd verification && lake env lean ../formalization/NSFormalization/Section3/T13/LocalizationKernel.lean
  → 0 errors (style linter notes only)
cd verification && lake env lean ../research/T13/axioms_localization_kernel.lean
  → 8 declarations, each `[propext, Classical.choice, Quot.sound]`
cd verification && lake env lean ../research/T13/probes/localization_kernel_closes.lean
  → 0 errors
make check (worktree root)
  → architecture checks OK; 13 contract-policy tests OK; 45 work items consistent
```
