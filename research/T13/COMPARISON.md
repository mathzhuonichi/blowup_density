# T13 uniform localization — reconciled comparison

This comparison merges the independent lane-265 Draft A and lane-266 Draft B
under the binding rulings in `research/T13/RECONCILIATION.md`.  The target is
`paper/sections/03-torus.tex:22-98`: `lem:localization`, its two
Gagliardo/Fourier identities, and its endpoint rider.

## T10 reuse strategy

Lean cannot import `research/T10/Spec.lean` because `research/` is not a module
root.  `Spec.lean` therefore imports T10's public imports
(`Contracts.V1.Data` and `Mathlib.Analysis.Fourier.AddCircleMulti`) plus the
registered whole-space norm module `Contracts.V1.HomogeneousNorm`, and copies
only the needed T10 declarations verbatim under their original namespace
`BlowupDensity.T10.Draft`.  The copy is marked

```lean
/- copied verbatim from research/T10/Spec.lean:46-203 (selected declarations);
must stay identical until T01.torus_data is registered -/
```

T13 then refers to `PeriodicSobolev`, `IsPeriodicDatum`,
`periodicSobolevENorm`, `IsPeriodicHomogeneousDatum`,
`periodicHomogeneousENorm`, `meanT`, `meanZeroPartT`, `IsMeanZeroT`,
`torusLift`, and `periodicFourierCoeff` by their T10 names.  No third periodic
datum model is introduced.  Once `T01.torus_data` is registered, the temporary
copy should be deleted and replaced by the registered import.

## Paper clause → Lean field, provenance, and ruling

| Paper clause | Reconciled Lean declaration / field | Draft A provenance | Draft B provenance | Binding ruling |
|---|---|---|---|---|
| Fixed coordinate chart and ball (`03-torus.tex:23,53,79-80`) | `fundamentalCube`; binders `c r`, `0 < r`, `closure (ball c r) ⊆ interior fundamentalCube` | Fixed `(0,1)³` chart via `openFundamentalCube` and a set-valued `IsCoordinateBall` | Arbitrary translated `Q a` and `AdmissibleBall a c r` | Fix `[0,1]³`, the cube behind T10's `(0,1]³` representative; retain only center and positive radius. |
| Zero extension supported in the ball (`03-torus.tex:23`) | `SupportedInBall c r f := tsupport f ⊆ ball c r` | `tsupport zR ⊆ B` | Same predicate with explicit `c,r` | Keep topological support and the explicit ball parameters.  The API hypotheses pair `ContDiff ℝ ∞ f ∧ SupportedInBall c r f`. |
| Periodization (`03-torus.tex:23`) | `periodize f x = ∑' n, f (x-latticeVector n)` | Function `spatialPeriodization` plus relation `IsSpatialPeriodization zR zT` | Direct function `periodize` | Keep B's function shape, specialize it to the fixed T10 lattice, and make the agreement/uniqueness statement a proof lemma rather than an API field. |
| Singular power and `c_s` (`03-torus.tex:35-39`) | `fractionalRadialKernel`, `cFrac`; `constant_pos_finite` | Defined `cFrac`; positivity/finiteness only listed as a proof obligation | Defined `c_s`; API field `constant_pos_finite` | Keep the concrete constant and B's field name.  Use `ℝ≥0∞` and preserve the singular value rather than totalizing divergence through `.toReal`. |
| Whole-space identity (`03-torus.tex:40-51`) | `IReal`; `wholeSpace_identity` | `real_gagliardo_identity`, registered homogeneous norm, no explicit finiteness conjunct | `wholeSpace_identity`, registered homogeneous norm, explicit finiteness | Keep B's field name and finiteness conclusion; keep the vector and registered-norm choices shared by both. |
| Periodic kernel and identity (`03-torus.tex:53-72`) | `periodicKernel`, `ITorus`; `torus_identity` with `periodicHomogeneousENorm s (meanZeroPartT f)` | Fixed cube; zero mode suppressed implicitly by a local homogeneous weight | Translated cube; explicit `removeMean`; local homogeneous seminorm | Use the fixed cube and T10's homogeneous norm.  Because T10 requires an actually mean-zero realization, subtract the T10 mean explicitly. |
| Inhomogeneous estimate (`03-torus.tex:22-28,73-96`) | `localization` | `uniform_localization`; fixed cube; `C : ℝ≥0`; relation-valued periodization; whole `L²` written as `sobolevENorm 0` | `localization`; translated cube; positive `C : ℝ`; function-valued periodization; `eLpNorm f 2 volume` | Keep B's field name and direct function, A's fixed cube, a positive finite real `C`, T10's `periodicSobolevENorm`, and the registered whole-space norms.  `C` is chosen before `f`. |
| Uniformity as support shrinks (`03-torus.tex:29,95-96`) | Quantifier order `s,c,r,C,f` in `localization` | `C` before both `zR,zT` | `C` before every `f` | Preserve the shared uniform order: `C=C_{s,B}` cannot depend on the actual smaller support or the field. |
| Order-zero endpoint (`03-torus.tex:29,96-98`) | `endpoint_zero` | First conjunct of `endpoint_identities` using squared integrals | Separate physical `eLpNorm` equality | Keep B's separate field and physical `L²` norm, on the fixed cube. |
| Order-one endpoint (`03-torus.tex:29,96-98`) | `endpoint_one` | Second conjunct of `endpoint_identities` using squared gradient integrals | Separate `gradientENorm` equality | Keep B's separate field and the full Hilbert--Schmidt gradient norm; do not identify it with the inhomogeneous `H¹` norm. |
| Tail summability and bound (`03-torus.tex:80-89`) | `latticeTail` definition only | Tail defined; bounds listed under proof obligations | `lattice_summable` and `tail_bound` fields | Follow the lead: both are internal proof lemmas, not consumer API fields. |
| Exponent range and codomain | Every fractional field assumes `0 < s` and `s < 1`; all fields are for `SpatialField` | `0 < s < 1`; real three-vectors | Same | Keep the shared range and vector-valued statement.  Endpoints are separate and have no contradictory fractional hypothesis. |

The reconciled `LocalizationAPI : Prop` has exactly the six required fields:
`constant_pos_finite`, `wholeSpace_identity`, `torus_identity`, `localization`,
`endpoint_zero`, and `endpoint_one`.  Every field has a concrete proposition
and an explicit non-vacuity comment.

## Normalizations and representation choices

- The fundamental cube is the fixed closed set `[0,1]³`.  T10's `torusLift`
  chooses `(0,1]³`; the boundary difference is null and must be handled by the
  cube/Haar bridge in the proof.
- `periodize` is the actual `ℤ³` lattice sum.  The API only applies it to a
  smooth field with topological support strictly inside one cube, where the
  sum is locally finite.
- `IReal`, `ITorus`, `periodicKernel`, `latticeTail`, and `cFrac` are
  `ℝ≥0∞`-valued.  This keeps divergence visible as `⊤`.
- The numerator in `cFrac` is exactly `|exp(i h₁)-1|²`; there is no `2π` in
  this whole-space constant.  T10's periodic homogeneous weight is
  `|2πk|^s`, so the paper's torus factor is retained.
- The localization right side is exactly
  `eLpNorm f 2 volume + dotHomogeneousENorm s f`.  The left side is T10's
  `periodicSobolevENorm s (periodize f)`.
- All physical fields are `Space → Space`; Euclidean norms sum the three
  component squares.  No divergence-free hypothesis is added.

## Proof dependencies

The following refines §4 of `RECONCILIATION.md`.  Names already present in the
T10 specification are written exactly; references such as “T10 item 2” mean
the numbered “Needs a lemma” list in `research/T10/COMPARISON.md`.

1. **The constant.**  Prove measurability of
   `fractionalRadialKernel` and the `cFrac` integrand, then the near-zero bound
   by `r^(1-2s)` and the far-field bound by `4*r^(-1-2s)`.  These give both
   halves of `constant_pos_finite`.  This is T13-specific and is not a T10
   obligation.

2. **Whole-space Gagliardo/Fourier identity.**  Use unitary Plancherel,
   Tonelli, rotations, and dilation componentwise.  The exact existing D01
   realization inputs are
   `NSFormalization.Section4.D01.Homogeneous.isHomogeneousSliceDatum_compact`
   and
   `NSFormalization.Section4.D01.Homogeneous.enorm_of_isHomogeneousSliceDatum`;
   the public norm is
   `BlowupDensity.Contracts.V1.HomogeneousNorm.dotHomogeneousENorm`.
   A short infimum bridge is still required to turn those realization lemmas
   into the registered norm equality.
   **Status (lane 348, 2026-09-18): discharged.**  Shipped as
   `NSFormalization.Section3.T13.WholeSpaceIdentity.wholeSpace_identity`; the
   infimum bridge is `dotHomogeneousENorm_eq_homogeneousFourierENorm`, Plancherel
   is `lintegral_angularFourier_sq`, the kernel rotation/dilation is
   `lintegral_kernel_smul`.  Axioms `[propext, Classical.choice, Quot.sound]`.

3. **Cube, Haar, and Fourier bridge.**  Identify the fixed-cube integrals with
   T10's `torusLift` and `periodicFourierCoeff`.  This is exactly T10 “Needs a
   lemma” item 1.  The usable T10 API endpoints are
   `TorusDataAPI.torusLift_injective`, `TorusDataAPI.torusLift_surjective`,
   `TorusDataAPI.parseval_forward`, and `TorusDataAPI.parseval_backward`.
   The proof also needs the null-boundary comparison between `[0,1]³` and the
   `(0,1]³` representative.

4. **Periodic homogeneous identity.**  Apply translation-difference Parseval
   componentwise, Tonelli for the nonnegative sum/integral, and the exact
   `2πk` multiplier.  T10 `TorusDataAPI.datum_unique` controls realization
   uniqueness.  `TorusDataAPI.mean_decomposition` identifies
   `meanZeroPartT`, and `TorusDataAPI.meanZero_datum` removes the zero mode on
   the inhomogeneous side.  The required full-gradient/frequency identity is
   T10 item 2; real weighted-data existence at arbitrary `s` is item 3;
   conjugate-reflection preservation is item 4; and identification of the
   zero coefficient with `meanT` is item 5.  T10 currently exposes no
   homogeneous-datum existence/norm field, so the proof lane must either prove
   that lemma locally or extend the eventual T10 binding before discharging
   `torus_identity`.

5. **Periodization and single-copy geometry.**  Prove that compact support in
   the admissible ball makes the lattice sum locally finite, smooth, and
   `IsPeriodicSpatial`; on the fixed cube it agrees with the zero extension,
   and it is the unique periodic field with that agreement.  This is the
   function-version replacement for Draft A's relation and supplies the
   endpoint mechanism.

6. **Kernel tail and clearance.**  Establish lattice summability for
   `3+2s>3`, positivity of
   `dist (closure (ball c r)) (frontier fundamentalCube)`, the near/far split,
   and the uniform bounds for both `x-y` and `y-x`.  These are the discarded
   Draft-B fields `lattice_summable` and `tail_bound`, now ordinary lemmas.

7. **Difference-integral comparison.**  Split off the zero lattice term,
   prove it is bounded by `IReal`, and bound the remaining terms by
   `4*C_{s,d}*‖f‖₂²`.  The estimate is uniform because `d` depends on the
   fixed ball and cube, not on the actual support.

8. **From homogeneous to inhomogeneous norm.**  Prove
   `(1+r²)^s ≤ 1+r^(2s)` for `0<s<1`, combine T10's order-zero Parseval facts
   with the periodic homogeneous identity, and take square roots.  This again
   uses T10 items 2, 3, and 5; `TorusDataAPI.parseval_forward` alone is not
   enough because `periodicSobolevENorm s` is an infimum over order-`s`
   weighted data.

9. **Endpoints.**  Use the single-copy identity for `f` and for every spatial
   derivative to prove `endpoint_zero` and `endpoint_one`.  The cube/Haar
   identification from T10 item 1 gives the alternate T10 torus-norm spelling
   if consumers need it.

## Open questions for the owner

1. T10's `periodicHomogeneousENorm` deliberately returns `⊤` unless its input
   has an `IsPeriodicHomogeneousDatum`, whose definition includes
   `IsMeanZeroT`.  The spec therefore writes
   `periodicHomogeneousENorm s (meanZeroPartT f)` literally.  Should the future
   T10 contract add a dedicated homogeneous existence/norm theorem for smooth
   periodic mean-zero fields, or should that bridge remain private to T13?
2. Should the eventual T13 contract expose the periodization agreement and
   uniqueness theorem as a public theorem next to the six-field API?  The
   reconciliation requires it as a lemma but correctly excludes it from the
   record fields.
3. `fractionalRadialKernel` takes the natural ENNReal value `⊤` at its lattice
   singularities; Draft B's `Real.rpow` spelling totalized those points to
   zero.  The integrals agree after null-set lemmas.  Which pointwise convention
   should be frozen in the eventual contract?
4. The endpoint fields use `volume.restrict fundamentalCube`, while T10's
   physical norm uses Haar measure through `torusLift`.  Should both endpoint
   spellings be registered, or only the current cube form plus a binding
   theorem to T10 Haar norms?

## T10 amendment 1 (lead, 2026-09-17)

The verbatim T10 copies in `Spec.lean` (`IsPeriodicDatum`,
`IsPeriodicHomogeneousDatum`) were re-synchronized with
`research/T10/RECONCILIATION.md` §5 (Haar-integrability conjunct).  No T13
field changes meaning: all localization fields quantify over smooth fields.

## §1 status — Proved by lane 345

- **`torus_identity`**: PROVED (lane 345, no named input).
  `formalization/NSFormalization/Section3/T13/TorusIdentity.lean`,
  `NSFormalization.Section3.T13.torus_identity`; the API field closes by
  `example` in `research/T13/probes/torus_identity_closes.lean`.  Proof
  dependency items 3 (cube/Haar/Fourier bridge, via
  `lintegral_fundamentalCube_ofReal` and `fundamentalCube_ae_eq_halfOpenCube`)
  and 4 (periodic homogeneous identity, via `exists_homogeneous_datum`,
  `homogeneousDatum_unique`, `periodicHomogeneousENorm_sq_smooth`) are
  discharged locally, so the open question 1 for the owner ("should T10 expose
  a homogeneous existence/norm theorem?") is answered privately in T13 for now.
  Item 1 is covered only in its finiteness half (`cFrac_lt_top`); positivity of
  `c_s` remains with lane 344.  Reusable by-products: `kernelIntegral_eq`
  (rotation + dilation), `lintegral_eq_tsum_halfOpenCube` (single-copy
  unfolding), `periodicFourierCoeff_shift` (Fourier translation).
  Record: `research/T13/REPORT_345.md`, `research/T13/ATTEMPTS_TORUS_IDENTITY.md`.
## Proved by lane 344 (2026-09-18)

Module `formalization/NSFormalization/Section3/T13/ConstantEndpoints.lean`
(namespace `NSFormalization.Section3.T13`) proves three of the six
`LocalizationAPI` fields verbatim, with no named input:

| Field | Status | Where |
|---|---|---|
| `constant_pos_finite` | **proved** (`0 < s < 1`) | `cFrac_pos`, `cFrac_lt_top` → `constant_pos_finite` |
| `wholeSpace_identity` | open (lanes 345/346) | — |
| `torus_identity` | open (lanes 345/346) | — |
| `localization` | open (lanes 345/346) | — |
| `endpoint_zero` | **proved** | `endpoint_zero_eq` → `endpoint_zero` |
| `endpoint_one` | **proved** | `endpoint_one_eq` → `endpoint_one` |

This settles "Proof dependencies" item 1 (the constant: measurability, the
near-zero `r^{1-2s}` bound and the far-field `4·r^{-1-2s}` bound, both halves of
`constant_pos_finite`) and item 9 (the endpoints). It also supplies the
single-copy half of item 5 as reusable lemmas for the remaining lanes:

* `interior_fundamentalCube : interior fundamentalCube = {x | ∀ i, 0 < x i ∧ x i < 1}`
  (plus `isClosed_fundamentalCube`, `measurableSet_fundamentalCube`,
  `convex_fundamentalCube`, `volume_frontier_fundamentalCube`);
* `eq_zero_of_mem_cube`, `periodize_eq_of_mem_cube` (agreement on the whole
  closed cube `[0,1]³`) and `periodize_eventuallyEq` (neighbourhood version on
  the interior, which is what derivatives need);
* `tsupport_subset_cube`, `fderiv_eq_zero_of_notMem_tsupport`.

Item 5's remaining obligations (local finiteness, smoothness and
`IsPeriodicSpatial` of `periodize f`, and uniqueness of the periodic extension)
are **not** in lane 344.

Open question 4 of this file is untouched: the endpoints are registered here
only in the `volume.restrict fundamentalCube` spelling; no bridge to T10's Haar
norms is proved.

Probe: `research/T13/probes/constant_endpoints_closes.lean` (copies the record
verbatim, closes the three fields, and instantiates both endpoints on an
explicit nonzero `ContDiffBump`-based field in `ball ((½,½,½)) (3/8)`).
Axioms: `research/T13/axioms_constant_endpoints.lean` — 35 declarations, all
`[propext, Classical.choice, Quot.sound]`.
Notes: `research/T13/ATTEMPTS_CONSTANT_ENDPOINTS.md`, report `research/T13/REPORT_344.md`.

## §2/§3 kernel-estimate status — lane 353 (2026-09-18)

Module `formalization/NSFormalization/Section3/T13/LocalizationKernel.lean`
(namespace `NSFormalization.Section3.T13`) ships three of the concrete analytic
estimates behind `eq:localization` (no `LocalizationAPI` field; lane 354
assembles).  Axioms of all public declarations: `[propext, Classical.choice,
Quot.sound]`.

| Estimate | Status | Declarations |
|---|---|---|
| Uniform lattice-tail bound (`:80-89`) | **proved** | `summable_latticeVector_rpow`, `tailSum`, `tailConst`, `tailSum_lt_top`, `tailConst_lt_top`, `latticeTail_le_tailConst` |
| `2r < 1` from the admissible ball (`:79-80`) | **proved** | `two_r_lt_one_of_closure_ball_subset` |
| Inhomogeneous ≤ `L²` + homogeneous on `T³` (`:73-78`) | **proved** | `periodicSobolevENorm_le_l2_add_homogeneous` |
| Kernel comparison `ITorus ≤ IReal + tail·‖f‖²` (`:79-94`) | **lane 354** | — (clearance constant `C_{s,d}`) |

The §3 estimate uses the **coefficient-side** `L²` norm `periodicSobolevENorm 0 g`
(the physical `eLpNorm g 2 periodicTorusMeasure` in the brief does not
type-check for `g : Space → Space`); the **assembly lane 359** supplies the
Parseval-at-0 bridge to reach `endpoint_zero`'s `eLpNorm f 2 volume` (item 8;
T10 already has `sobolevENorm_zero_eq`).

The §2 kernel comparison is **lane 354's** (running on this branch, with the
geometric constant `C_{s,d}`), not lane 353's: the brief's constant
`4·tailConst s (2r)·‖f‖₂²` is insufficient because on the full cube×cube tail
integral one point may be in the ball and the other far (`‖x-y‖ ≰ 2r`); the
paper uses the geometric separation `d = dist(closure B, ∂Q)` instead.  Exact
residual lemmas in `research/T13/ATTEMPTS_LOCALIZATION_KERNEL.md`
("NOT shipped — §2").

Records: `research/T13/ATTEMPTS_LOCALIZATION_KERNEL.md`,
`research/T13/axioms_localization_kernel.lean` (8 declarations),
probe `research/T13/probes/localization_kernel_closes.lean`,
report `research/T13/REPORT_353.md`.
## §1 status — Proved by lane 345

- **`torus_identity`**: PROVED (lane 345, no named input).
  `formalization/NSFormalization/Section3/T13/TorusIdentity.lean`,
  `NSFormalization.Section3.T13.torus_identity`; the API field closes by
  `example` in `research/T13/probes/torus_identity_closes.lean`.  Proof
  dependency items 3 (cube/Haar/Fourier bridge, via
  `lintegral_fundamentalCube_ofReal` and `fundamentalCube_ae_eq_halfOpenCube`)
  and 4 (periodic homogeneous identity, via `exists_homogeneous_datum`,
  `homogeneousDatum_unique`, `periodicHomogeneousENorm_sq_smooth`) are
  discharged locally, so the open question 1 for the owner ("should T10 expose
  a homogeneous existence/norm theorem?") is answered privately in T13 for now.
  Item 1 is covered only in its finiteness half (`cFrac_lt_top`); positivity of
  `c_s` remains with lane 344.  Reusable by-products: `kernelIntegral_eq`
  (rotation + dilation), `lintegral_eq_tsum_halfOpenCube` (single-copy
  unfolding), `periodicFourierCoeff_shift` (Fourier translation).
  Record: `research/T13/REPORT_345.md`, `research/T13/ATTEMPTS_TORUS_IDENTITY.md`.
