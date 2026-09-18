# T22 — proof-lane split (`eq:restriction-norm`, `eq:zero-extension`, `03-torus.tex:600-630`; cor:boundary `:632-667`)

Lead-facing, 2026-09-18. Target = the reconciled `BoundedDomainNormAPI` (`research/T22/Spec.lean:114-167`,
**3 fields**) over the bounded-domain vocabulary `restrictDatum` (`Spec.lean:62`), `domainSobolevENorm`
(`:72`, the `eq:restriction-norm` quotient infimum, a `def` not a field), `restrictField` (`:81`),
`zeroExtension` (`:89`, `Ω.indicator`), `IsCutoffDatum` (`:99`, the `smulLeftCLM` graph). All ℝ³/domain,
no torus object (`RECONCILIATION.md §3`; T10 is a DAG predecessor, **not** an analytic provider —
`COMPARISON.md §5`). Design = `COMPARISON.md` "Proof dependencies" (§§1-4). House style =
`research/T17/T17_SPLIT.md`, `research/T13/…`. Size: **S** ≤ ~100 lines · **M** one self-contained lemma
with a known proof · **L** a multi-file analytic campaign. Model: `codex-sol` = reuse/algebra/bookkeeping,
`Opus` = analytic core.

## 0. Ground rules

**Peeling rule** (T11/T15/T17). A unit ends in a `theorem` whose statement **is** a `BoundedDomainNormAPI`
field verbatim, or a lemma **directly consumed** by one. A unit that cannot close from the tree names
**exactly one** input hypothesis as a `def … : Prop` in `Section3/T22/`, written out here, non-tautological,
satisfiable at a nonzero reference, discharged by a named later unit. **No named input for the hard analytic
units.** In this split every unit closes from the registered tree or an earlier T22 unit, so **no unit needs
a named input** — the peel budget is unused (like T13, unlike T15/T17).

**Verbatim field targets** (three `theorem`s, one per field):
- `orderZero` (`Spec.lean:125-128`): `domainSobolevENorm Ω 0 (restrictField Ω z) = eLpNorm z 2 (volume.restrict Ω)`
  under `IsOpen Ω`, `ContDiffOn ℝ ∞ z Ω`. Both sides may be `⊤`.
- `cutoffMultiplier` (`Spec.lean:140-144`): `∀ s χ`, smooth compact `χ`, `∃ C>0, ∀ A, ∃ B, IsCutoffDatum s χ A B ∧ ‖B‖ₑ ≤ ofReal C * ‖A‖ₑ`.
- `zeroExtensionComparison` (`Spec.lean:160-167`): for `K ⋐ Ω`, `∀ s, ∃ C>0, ∀ z` smooth with `tsupport (E₀z) ⊆ K`,
  `domainSobolevENorm Ω s (restrictField Ω z) ≤ sobolevENorm s (E₀z) ≤ ofReal C * domainSobolevENorm Ω s (restrictField Ω z)`.

**Two classes of field** (the task's bookkeeping-vs-new-analysis split):

- **Pure bookkeeping / algebra** (`rfl`-level bridges, restriction/extension algebra, `eLpNorm` monotonicity
  under zero extension, `⨅` inequalities): the **left** conjunct of `zeroExtensionComparison` (E₀z is one
  admissible extension → `domainSobolevENorm ≤`), the restriction bridge `restrictDatum Ω s A = restrictField Ω z`,
  the global-smoothness/compact-support of `E₀z`, the distributional identity `χ·A = E₀z`, and the `⨅`-bookkeeping
  wrapping the **right** conjunct once the multiplier constant is in hand. Units **U-B1, U-B2, U-B3, U-Z1, U-REG**.
- **Genuinely new analysis** (no reusable in-tree proof; this is what T22 owes):
  1. **the fixed-cutoff `H^s(ℝ³)` multiplier bound** `cutoffMultiplier` — the whole two-sided ε-uniform
     `eq:zero-extension` comparison reduces to it (`03-torus.tex:616-624`). Weight ratio + Fourier convolution +
     Young `L¹∗L²→L²` for **every real `s`** (`COMPARISON.md §3`). Units **U-A1, U-A2, U-A3**.
  2. **the order-0 vector Plancherel + `L²(Ω)` quotient identity** `orderZero` — the order-0 datum norm identity
     that D01 explicitly leaves unproved (`OrderZeroDatum.lean` scope note), plus the restriction/zero-extension
     `L²` isometry (`COMPARISON.md §2`). Units **U-A4, U-A5**.

**Registered facts already in the tree** (`COMPARISON.md §1`; use these exact spellings):
`Data.IsSobolevDatum` (`verification/Contracts/V1/Data.lean:160`), `Data.sobolevENorm` (`:189`);
`D01.sobolevENorm_le_of_isSobolevDatum` (`SmoothDatum.lean:318`) — the single lever for every `⨅` bound;
`DatumLemmasAPI.smoothJets_exists_datum` (`DatumLemmas.lean:160`), `smoothJets_sobolevENorm_ne_top` (`:169`),
`isSobolevDatum_unique` (`:284`); `A01.IsSobolevDatum.congr_field` (`CarrierBridge.lean:79`, a.e.-congruence of the
field); `D01.orderZeroDatum`/`exists_isSobolevDatum_zero_of_memLp` (`OrderZeroDatum.lean:96,118`, existence only);
`Source.YoungConvolution.eLpNorm_convolution_one_two`/`memLp_convolution_one_two` (`YoungConvolution.lean:28,65`).

**Implementation candidates (T22 row) and their real status:**
- `Paper1/LocalizationBoundary.lean` is the **domain fractional-kernel** module: `domainL2Sq_le_whole` (`:64`),
  `domainL2Sq_eq_whole_of_compl_eq_zero` (`:73`) — restriction monotonicity / zero-extension agreement at `L²`,
  reusable *content* for U-A5 (they are on `∫‖·‖²`, need an `eLpNorm` bridge); `fractionalKernelFar_le_l2_density`
  (`:339`), `integral_fractionalKernelFar_restrict_le_l2` (`:369`), `integral_fractionalKernelNear_le` (`:312`),
  `periodicSobolevNorm_periodize_interpolation_complex` (`:189`) — the Gagliardo near/far split **only for
  `0<s<1`**. Same fractional-radial kernel as T13 `WholeSpaceIdentity.wholeSpace_identity` (`:509`) /
  `TorusIdentity.torus_identity` (`TorusIdentity.lean:1174`) / `ConstantEndpoints.endpoint_zero,_one` (`:407,:416`).
  **These cover only `s∈(0,1)`; the T22 fields quantify over all real `s`, so the general route is the Fourier
  multiplier (U-A1–A3), and the fractional-kernel modules serve at most as an independent `0<s<1` cross-check —
  do not build the field on them.**
- `Paper1/BoundaryCorollary.lean` (`IsDomainExtension:15`, `domainSobolevNorm:20`, `domainForceNorm:24`,
  `bounded_energy_restriction:64`) has a **`sorry` at `:90`** — **never import this module** (hook-enforced); its
  spellings are informative only.
- `Paper1/BoundaryReferenceRestriction.lean` (no-slip/reference restriction) belongs to `cor:boundary`'s
  boundary-value bookkeeping, not to this norm layer; out of scope for T22.
- `Contracts/V1/HomogeneousPartial.lean` `annularRestriction/annularSmoothing/annularSchwartz` (`:233,:242,:254`)
  are frequency-annulus density, **not** the spatial cutoff multiplier (`COMPARISON.md §3`); `dotHomogeneousENorm`
  (`HomogeneousNorm.lean:31`) is the **homogeneous** `Ḣ^s` norm — T22 uses **inhomogeneous** `sobolevENorm`; both
  are red herrings for these fields.

## 1. Units

- **U-B1 — restriction bridge** (bookkeeping). New `Section3/T22/RestrictBridge.lean`.
  **Status (lane 383, 2026-09-18): COMPLETE.** The canonical vocabulary is in
  `Section3/T22/Domain.lean`; both `restrictDatum_eq_restrictField` and
  `domainSobolevENorm_le_sobolevENorm` close with the standard three axioms.
  Target (consumed by `orderZero` **and** `zeroExtensionComparison` left conjunct): `restrictDatum_eq_restrictField`
  — if `IsSobolevDatum s (zeroExtension Ω z) A` then `restrictDatum Ω s A = restrictField Ω z`. Route: for a
  `DomainTest ψ` (tsupport ⊆ Ω), `angularRealization s (A i) ψ.1 = ∫ x, ψ.1 x * (E₀z x i)` (`IsSobolevDatum`); split
  the integral on `Ω`/`Ωᶜ`, `E₀z = z` on `Ω` and `ψ.1 = 0` off `tsupport ⊆ Ω`, giving `∫ x in Ω, ψ.1 x * z x i =
  restrictField Ω z i ψ`. Corollary `domainSobolevENorm_le_sobolevENorm` (the **left conjunct** as a standalone
  lemma) via the two `⨅` families. **S–M, codex-sol.** Deps: —.

- **U-B2 — zero-extension regularity** (bookkeeping). New `Section3/T22/ZeroExtRegularity.lean`.
  Target (consumed by U-Z1 and U-A5): `contDiff_zeroExtension` + `hasCompactSupport_zeroExtension` — from
  `ContDiffOn ℝ ∞ z Ω`, `IsOpen Ω`, `IsCompact K`, `K ⊆ Ω`, `tsupport (zeroExtension Ω z) ⊆ K`, derive
  `ContDiff ℝ ∞ (zeroExtension Ω z)` and `HasCompactSupport`. Route: `zeroExtension Ω z = Ω.indicator z` agrees
  with the `ContDiffOn` field on the open `Ω` and is `=ᶠ 0` on the open `(tsupport)ᶜ`; these two opens cover ℝ³
  (`tsupport ⊆ K ⊆ Ω`), so glue with `ContDiffOn.contDiff_of_...`/`contDiffOn_of_locally`. Hence `MemLp (E₀z) 2`
  and `SmoothSquareIntegrableJets (E₀z)` (compact support) → a datum at every `s` via `smoothJets_exists_datum`.
  **M, codex-sol.** Deps: —.

- **U-B3 — cutoff datum identity** (bookkeeping). New `Section3/T22/CutoffDatum.lean`.
  Target (consumed by U-Z1): (a) `exists_cutoff` — `∃ χ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Ω ∧
  (χ = 1 on a nbhd of K)` from `K ⋐ Ω` (Mathlib `exists_contDiff_...`/`IsCompact.exists_isCompact_...` +
  `exists_smooth_tsupport_subset`); (b) `isCutoffDatum_realizes_zeroExtension` — if `IsCutoffDatum s χ A B`,
  `restrictDatum Ω s A = restrictField Ω z`, `tsupport (E₀z) ⊆ K`, and `χ=1` near `K`, then
  `IsSobolevDatum s (E₀z) B`. Route: `angularRealization s (B i) ψ = angularRealization s (A i) (χ·ψ)`
  (`IsCutoffDatum`); `χ·ψ` has compact support ⊆ `tsupport χ ⊆ Ω`, so it is a `DomainTest` and the RHS is
  `restrictField Ω z i (χψ) = ∫ x in Ω, χ x·ψ x·z x i`; `χ=1` on `supp z ⊆ K` collapses it to `∫ ψ·(E₀z)`. **M,
  codex-sol.** Deps: —.

- **U-A1 — Peetre weight ratio** (new analysis). New `Section3/T22/WeightRatio.lean`. No named input.
  Target (consumed by `cutoffMultiplier`): `weight_ratio_le` —
  `(1+‖ξ‖²)^(s/2) ≤ C_s · (1+‖η‖²)^(s/2) · (1+‖ξ-η‖²)^(|s|/2)` for all `ξ η`, `s∈ℝ`, with `C_s` explicit
  (`2^(|s|/2)`). Route: Peetre's inequality — cases `s≥0` (submultiplicativity of `1+‖·‖²` under `ξ=η+(ξ-η)`)
  and `s<0` (apply the `s≥0` form with roles of `ξ,η` swapped and `-s`); `Real.rpow` monotonicity/`add_pow_le`.
  **M, Opus.** Deps: —.
  **[DONE — lane 386]** `Section3/T22/WeightRatio.lean`: `weight_ratio_le (s ξ η) : (1+‖ξ‖²)^(s/2) ≤
  2^(|s|/2) · (1+‖η‖²)^(s/2) · (1+‖ξ-η‖²)^(|s|/2)`, plus `peetreConst`/`peetreConst_pos`, the `peetreConst`
  form `weight_ratio_le_const`, and the datum-layer spelling `sobolevBesselWeight_norm` /
  `sobolevBesselWeight_norm_ratio_le` (via `NSFormalization.Paper3.sobolevBesselWeight`). Route as planned
  (base submultiplicativity → `Real.rpow_le_rpow`/`Real.mul_rpow` for `s≥0`; swap-and-invert for `s<0`). No
  named input. Axioms `[propext, Classical.choice, Quot.sound]`. `lake build … WeightRatio` green; `make check`
  green. Probe `research/T22/probes/weight_ratio_closes.lean`, audit `research/T22/axioms_ua1.lean`.

- **U-A2 — cutoff Fourier kernel is weighted-`L¹`** (new analysis). New `Section3/T22/CutoffKernel.lean`. No named input.
  Target (consumed by `cutoffMultiplier`): `integrable_weighted_fourier_cutoff` — for `χ` smooth compact and any
  `s`, `Integrable (fun ζ => (1+‖ζ‖²)^(|s|/2) * ‖𝓕χ ζ‖)`. Route: `χ` smooth compact ⇒ Schwartz ⇒ `𝓕χ` Schwartz
  (`SchwartzMap.fourierTransformCLM`), so `‖𝓕χ ζ‖ ≤ C_N (1+‖ζ‖)^(-N)` for every `N`; choose `N` past `|s|+3` and
  integrate against the polynomial weight (`integrable_one_add_norm`/`rpow` tails). **M–L, Opus.** Deps: —.
  **[DONE — lane 391]** `Section3/T22/CutoffKernel.lean`: master lemma `integrable_weighted_schwartz (s ψ) :
  Integrable (fun ζ => (1+‖ζ‖²)^(|s|/2) · ‖ψ ζ‖)` for any Schwartz `ψ` (`SchwartzMap.one_add_le_sup_seminorm_apply`
  at `n=0` + `norm_iteratedFDeriv_zero` for `(1+‖ζ‖)^k‖ψ ζ‖ ≤ C_k`; weight comparison `(1+‖ζ‖²)^(|s|/2) ≤
  (1+‖ζ‖)^|s|`; `integrable_one_add_norm` tail with `finrank ℝ Space = 3 < k - |s|`), then `cutoffSchwartz` (smooth
  compact `χ` complexified to a `SchwartzMap` via `NavierStokesR3.CompactSchwartz.ofCompactSupport`) and the two
  field-target spellings: `integrable_weighted_fourier_cutoff` (datum-layer `angularFourier (fun x => (χ x : ℂ))`,
  routed through the Schwartz `schwartzAngularDilation (𝓕 ·)`) and `integrable_weighted_fourier_cutoff_mathlib`
  (Mathlib `𝓕`), plus the `ENNReal`/`lintegral` form `lintegral_weighted_fourier_cutoff_ne_top`. No named input,
  no `maxHeartbeats` bump. Axioms `[propext, Classical.choice, Quot.sound]`. `lake build … CutoffKernel` green;
  `make check` green. Probe `research/T22/probes/cutoff_kernel_closes.lean` (`ContDiffBump` cutoff, `s = 1/2` and
  `s = -2`, both spellings + `ENNReal` form), audit `research/T22/axioms_ua2.lean`. **NB for U-A3:** the target
  cannot be stated for `𝓕χ` with `χ : Space → ℝ` (Mathlib `𝓕` needs a ℂ-module codomain), so the kernel is the
  transform of the complex coercion `fun x => (χ x : ℂ)` — exactly what `IsCutoffDatum`'s
  `SchwartzMap.smulLeftCLM ℂ (fun x => (χ x : ℂ))` multiplies by.

- **U-A3 — `cutoffMultiplier` (analytic core)** (new analysis). New `Section3/T22/CutoffMultiplier.lean`. No named input.
  Target: `BoundedDomainNormAPI.cutoffMultiplier` **verbatim** (`Spec.lean:140-144`). Route: put `C := C_s ·
  ∫(1+‖ζ‖²)^(|s|/2)‖𝓕χ ζ‖` (U-A1 constant × U-A2 kernel mass), `>0`. For `A : RealVectorSobolev s`, define `B`
  componentwise so that `weighted datum(B) = (weighted 𝓕χ) ∗ weighted datum(A)` in the angular normalization
  (Fourier product/convolution identity); U-A1 dominates the output weight pointwise by the kernel-weighted
  convolution, and `YoungConvolution.eLpNorm_convolution_one_two` gives `‖B‖ₑ ≤ ofReal C * ‖A‖ₑ`; `𝓕χ` real-even
  (real `χ`) preserves `realSubspace`, so `B : RealVectorSobolev s`; unfold `smulLeftCLM` to close `IsCutoffDatum
  s χ A B`. **L, Opus.** Deps: U-A1, U-A2. *(Independent `0<s<1` cross-check available from `LocalizationBoundary`
  far/near split + T13 `wholeSpace_identity`; not on the critical path.)*

- **U-A4 — order-0 vector Plancherel isometry** (new analysis). New `Section3/T22/OrderZeroIsometry.lean`. No named input.
  Target (consumed by `orderZero`): `norm_orderZeroDatum_eq` — `‖D01.orderZeroDatum hz‖ₑ = eLpNorm z 2 volume`
  for `hz : MemLp z 2 volume`. This is the identity D01 **explicitly leaves open** (`OrderZeroDatum.lean` "the norm
  identity is NOT proved here"). Route: the vector isometry `cyclesToAngularRealVector_symm_norm` (only the scalar
  `cyclesToAngularReal_symm_norm_le`, `Paper3/AngularRealSobolev.lean:84`, exists — build the `WithLp 2` vector
  version), scalar Plancherel `Lp.norm_fourier_eq`, and the Euclidean Pythagorean `L²` identity
  `eLpNorm z 2 volume ^2 = ∑ i, eLpNorm (z·i) 2 volume ^2`. **M–L, Opus.** Deps: —.
  **STATUS — DONE (2026-09-18, lane 387).** `Section3/T22/OrderZeroIsometry.lean` proves
  `norm_orderZeroDatum_eq` verbatim. The Pythagoras identity already existed in
  `Section4/D01/FiniteOrderNorm.lean` (`norm_toLp_component_sq_sum` / `eLpNorm_component_sq_sum`,
  which also carry the `≤`-half `norm_orderZeroDatum_le`), so the new content is only the *isometry*:
  the vector isometry is delivered as `cyclesToAngularRealVector_zero_norm` (forward, not `symm`) via
  the scalar `cyclesToAngularReal_zero_norm`. The direct subspace `symm` overflows even 400000
  heartbeats, so the isometry is routed through the plain-`Lp` `cyclesToAngular_zero_norm` +
  two `rfl` coercion bridges (`norm_coe_realSobolev`, `coe_cyclesToAngularReal_zero`); each
  declaration fits `maxHeartbeats 400000`, all print `[propext, Classical.choice, Quot.sound]`.
  Probe: `research/T22/probes/orderzero_isometry_closes.lean` (nonzero `ContDiffBump` field,
  both sides finite and equal). Details: `research/T22/ATTEMPTS_UA4.md`, `research/T22/REPORT_387.md`.

- **U-A5 — `orderZero` (analytic)** (new analysis). New `Section3/T22/OrderZero.lean`. No named input.
  Target: `BoundedDomainNormAPI.orderZero` **verbatim** (`Spec.lean:125-128`). Route: `≤` — any datum `A` in the
  `domainSobolevENorm Ω 0 (restrictField Ω z)` family restricts to `restrictField Ω z`; its `L²(ℝ³)` norm
  dominates the restricted-measure `eLpNorm` (`LocalizationBoundary.domainL2Sq_le_whole:64` content, via
  `eLpNorm ↔ ∫‖·‖²` at `p=2`) after U-A4 identifies `‖A‖ₑ` with `eLpNorm (its field) 2 volume`; take `⨅`. `≥` —
  extend the (locally-`L²`) restricted field by zero to `Ω`, its zero extension is an admissible order-0 datum
  (`orderZeroDatum` on the `MemLp` extension, `congr_field` for the a.e. field match) and is an **isometry** for
  the restricted measure (`domainL2Sq_eq_whole_of_compl_eq_zero:73`). `⊤=⊤` when `z ∉ L²(Ω)`: no finite-norm
  extension can restrict to `restrictField Ω z`. **L, Opus.** Deps: U-A4, U-B1.

- **U-Z1 — `zeroExtensionComparison` (assembly of the two-sided bound)** (bookkeeping over the core). New
  `Section3/T22/ZeroExtComparison.lean`. No named input. Target:
  `BoundedDomainNormAPI.zeroExtensionComparison` **verbatim** (`Spec.lean:160-167`). Route: fix `χ` (U-B3a) and set
  `C` from U-A3.cutoffMultiplier (`∃ C>0` chosen before `z`). **Left** conjunct = U-B1's
  `domainSobolevENorm_le_sobolevENorm` (E₀z has a datum by U-B2, restricts to `restrictField Ω z`). **Right**
  conjunct: for each domain-extension datum `A` (i.e. `restrictDatum Ω s A = restrictField Ω z`), apply
  `cutoffMultiplier` → `B` with `IsCutoffDatum s χ A B`, `‖B‖ₑ ≤ ofReal C * ‖A‖ₑ`; U-B3b makes `B` an
  `IsSobolevDatum s (E₀z)` witness, so `sobolevENorm s (E₀z) ≤ ‖B‖ₑ ≤ ofReal C * ‖A‖ₑ`
  (`sobolevENorm_le_of_isSobolevDatum`); take `⨅` over `A` → `≤ ofReal C * domainSobolevENorm`. **M–L, codex-sol.**
  Deps: U-A3, U-B1, U-B2, U-B3.

- **U-REG — assembly + contract/bindings/tests + non-vacuity** (bookkeeping). New `Section3/T22/Assembly.lean`
  + fresh `verification/Contracts/V1/BoundedDomainNorm.lean` (+ `Bindings`, `Tests`). Bundle the inhabitant
  `⟨orderZero (U-A5), cutoffMultiplier (U-A3), zeroExtensionComparison (U-Z1)⟩: BoundedDomainNormAPI`; rewrite
  `restrictDatum`/`domainSobolevENorm`/`restrictField`/`zeroExtension`/`IsCutoffDatum` verbatim in the contract with
  `rfl` bridges to the `Section3/T22` defs; `Tests` audits transitive axioms `[propext, Classical.choice,
  Quot.sound]` and non-vacuity (nonzero bump on a ball `K ⋐ Ω`). **M, codex-sol.** Deps: U-A3, U-A5, U-Z1.

## 2. Waves (≤ 3 concurrent per current lane cap)

| wave | units | sizes / models |
|---|---|---|
| W1 | **U-B1** restrict bridge · **U-A1** weight ratio · **U-A4** order-0 isometry | S–M sol / M Opus / M–L Opus |
| W2 | **U-B2** E₀z regularity · **U-A2** cutoff kernel · **U-A5** orderZero | M sol / M–L Opus / L Opus |
| W3 | **U-B3** cutoff identity · **U-A3** cutoffMultiplier (core) | M sol / L Opus |
| W4 | **U-Z1** zeroExtensionComparison | M–L sol |
| W5 | **U-REG** assembly + registration | M sol |

Ordering follows the two-class split: bookkeeping (U-B*) and the analytic **leaf** lemmas (U-A1, U-A2, U-A4)
start immediately; the **analytic core** U-A3 (multiplier) and U-A5 (orderZero) land next; the two-sided
`eq:zero-extension` comparison U-Z1 is pure `⨅`-bookkeeping **once U-A3 exists**, then U-REG registers.
**U-A3 is the critical path** (U-Z1 and the whole `eq:zero-extension` right inequality rewrite through it);
W2 must land U-A2 before W3 opens.

## 3. Risks

1. **U-A3 (highest).** The general-`s` Fourier multiplier is the one genuinely new campaign; no in-tree proof
   exists (`annular*` = frequency density only; `TameProduct` = integer order only). The convolution/Young
   assembly in the repository's angular normalization is the long pole. `LocalizationBoundary` + T13 give only a
   `0<s<1` cross-check, not a substitute.
2. **U-A4 vector isometry.** Only the **scalar** `cyclesToAngularReal_symm_norm_le` is in the tree; the `WithLp 2`
   vector lift and the Euclidean Pythagorean `L²` identity are new (D01 flags both as absent, and warns the
   `ofSubmodules`/`restrictScalars` unification is heartbeat-heavy — expect a raised `maxHeartbeats`).
3. **U-A5 `⊤=⊤` edge.** `orderZero` has no compact-support/`L²` hypothesis, so the identity must hold when
   `z ∉ L²(Ω)` (both sides `⊤`); the `≥` direction must show *no* finite-norm extension restricts to
   `restrictField Ω z` off `L²(Ω)`. Keep the measure bridges (`domainL2Sq_*`) as `∫‖·‖²`↔`eLpNorm` at `p=2`.
4. **Never import `BoundaryCorollary`** (`:90` sorry, hook-enforced). Re-use its content only by re-deriving in
   `Section3/T22/` or via the clean `LocalizationBoundary` lemmas.
5. **`IsCutoffDatum` `smulLeftCLM` unfolding (U-B3/U-A3).** The graph is stated through
   `SchwartzMap.smulLeftCLM ℂ (χ ·)`; confirm it is pointwise multiplication on the smooth compact `χ` before the
   distributional identity closes, or the U-B3b realization and the U-A3 graph will not match.
