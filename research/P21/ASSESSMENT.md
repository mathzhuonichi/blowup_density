# P21 / lane 499 — feasibility assessment

Status: assessment only; P6 remains Partial. No Lean theorem or registry change is proposed in this lane.

The recommended decision is (iii): retain the separate H¹-uniform restart obligation, because the registered high-order routes already prove the integral continuation conclusion used downstream. The current revised Proposition 2.1 does not itself display an H¹-uniform bound. Detailed statement, source, and effort analysis follows in this document.

## 1. Statement fidelity and exact targets

Paths below are relative to the repository root; `F` abbreviates `formalization/NSFormalization`. Line numbers refer to this checkout, not the old appendix numbering preserved in Lean comments.

### What Proposition 2.1 actually says

`paper/revised/sections/02-preliminaries.tex:149–156`:

> For each initial velocity in the stated class and each force smooth into every $H^m$ on compact time intervals ... a unique maximal smooth velocity ... If a solution is defined on $[0,S)$ ... [the squared H² integral is finite] then it extends smoothly beyond $S$.

There is **no explicit H¹-uniform lifespan clause in this current proposition**. Its proof, lines 178–182, says:

> Grönwall and [the criterion] bound every $H^m$ norm uniformly up to $S$. Tao's quantitative local existence then gives a uniform positive time when restarting at $t_0\uparrow S$; the fixed force is smooth on $[0,S+1]$.

Thus H⁷/H³ is sufficient for this proof step. The separate stronger obligation `L21_H1` is retained by the blueprint (lines 78–91) and guide (`paper/formalization_guide.tex:155–177`), inherited from the historical local-theory specification. Do not describe it as a displayed clause of the revised proposition, or silently change its status to Closed.

### Registered-vocabulary H¹ restart targets

The following are proposed **statement expressions**, not proved declarations and not kernel-checked probes. They require imports `Contracts.V2.LocalTheory`, `Contracts.V2.Continuation`, and `Contracts.V1.TorusLocalTheory`, with `Set`, `NavierStokes.ProblemStatement`, and `BlowupDensity.Contracts.V1.Data` open. Use the respective namespace openings shown. These are existence statements about smooth admissible data in an H¹ ball, **not** existence for arbitrary rough H¹ data.

Whole space, with `BlowupDensity.Contracts.V2.LocalTheory` and `BlowupDensity.Contracts.V2.Continuation` open:

```lean
∀ (ν : ℝ), 0 < ν →
  ∀ (f : SpaceTimeField), MemForceR f →
    ∀ (S : ℝ), 0 ≤ S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ t₀ ∈ Icc (0 : ℝ) S,
          ∀ (a' : SpatialField), a' ∈ initialClassR →
            sobolevENorm 1 a' ≤ K →
              ∃ w : ClassicalSolutionR ν a' (timeShift t₀ f) δ,
                ManuscriptLocalRegularity ν a' (timeShift t₀ f) δ w
```

Torus, with `BlowupDensity.Contracts.V1.TorusLocalTheory` open:

```lean
∀ (ν : ℝ), 0 < ν →
  ∀ (f : SpaceTimeField), f ∈ forceClassT →
    ∀ (S : ℝ), 0 ≤ S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ t₀ ∈ Icc (0 : ℝ) S,
          ∀ (a' : SpatialField), a' ∈ initialClassT →
            periodicSobolevENorm 1 a' ≤ K →
              ∃ w : ClassicalSolutionT ν a' (timeShiftT t₀ f) δ,
                PeriodicLocalRegularity ν a' (timeShiftT t₀ f) δ w
```

The second is exactly the field at `verification/Contracts/V1/TorusLocalTheory.lean:473–482` with `3` replaced by `1`. One δ is chosen **before both restart time and datum**. Setting S=0 gives local existence uniform on an H¹ datum ball. The regularity bundle quantifies over every order on that same δ; it is not `∀ m, ∃ δ_m`. The datum still belongs to the smooth initial class, so smoothness includes the initial endpoint. The force is fixed before δ; δ may depend on its compact-window bounds, viscosity and K, but not on the high norms of a'.

The corresponding uniform endpoint targets are:

```lean
-- Whole space; open the two V2 namespaces as above.
∀ (ν : ℝ), 0 < ν → ∀ (f : SpaceTimeField), MemForceR f →
  ∀ (S : ℝ), 0 < S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (a : SpatialField) (u : SpaceTimeField) (p : SpaceTimeScalar),
        a ∈ initialClassR → SolvesBelow ν a f S u p →
          (∀ t ∈ Ico (0 : ℝ) S,
            sobolevENorm 1 (fun x ↦ u (t, x)) ≤ K) →
              ENNReal.ofReal (S + δ) < maximalLifespanR ν a f

-- Torus; open the V1 torus namespace instead.
∀ (ν : ℝ), 0 < ν → ∀ (f : SpaceTimeField), f ∈ forceClassT →
  ∀ (S : ℝ), 0 < S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (a : SpatialField), a ∈ initialClassT →
        ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
          SolvesBelowT ν a f S u p →
            (∀ t ∈ Ico (0 : ℝ) S,
              periodicSobolevENorm 1 (fun x ↦ u (t, x)) ≤ K) →
                ∃ v : ClassicalSolutionT ν a f (S + δ),
                  (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
                    v.velocity (t, x) = u (t, x)) ∧
                  (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
                    v.pressure (t, x) = p (t, x))
```

Choose a smaller δ if needed for the strict whole-space lifespan conclusion. Whole-space pressure is unique only modulo time gauge; the registered whole-space endpoint conclusion deliberately uses lifespan, whereas torus normalized pressure agrees literally.

**Do not target an H¹ lower bound for the existing selected `A01.localHorizon'`.** Its definition uses the high datum norm; proving existence for a longer interval does not make that particular selected number larger. An eventual new API must choose a new horizon or export the existential restart theorem. `LocalTheoryAPI.horizon_lower_bound` (`verification/Contracts/V2/LocalTheory.lean:131–152`) is the fixed-force H⁷ selection guarantee; `Bindings/LocalTheoryV2.lean:87–101` wires the actual selected solution and regularity to it.

**Force quantification:** a cross-force variant can quantify `∀ K ≠ ⊤, ∃ δ > 0, ∀ a f` with `sobolevENorm 1 a ≤ K` and `forceSobolevENormL1 1 f ≤ K`, concluding existence and regularity on δ. This is a useful stronger Tao-style theorem, but is not required by the fixed-force target. `research/A01/V2_DECISION.md:25–27` explicitly corrects the earlier draft's attribution of cross-force uniformity to the manuscript. The same warning applies to stale comments in the continuation contract. A class-membership assumption alone gives no common time across unbounded forces.

### Coverage ledger

| Article content | Registered coverage | Remaining qualification |
|---|---|---|
| Positive local smooth solution, all orders on one interval | A01 V2 `solution`/`regularity`; periodic `PeriodicLocalTheoryAPI` | R³ uses `MemForceR`; T³ uses `forceClassT` for the main local API |
| Velocity uniqueness, pressure prescription, maximal development | A01 plus A02 bindings; torus local/maximal API | R³ pressure modulo gauge; torus normalized pressure |
| Finite squared-H² integral implies extension | `ContinuationV2API.extendsBeyond`, lines 121–126; `PeriodicContinuationH3API.extendsBeyond`, lines 519–530 | R³ exports strict maximal-lifespan inequality; T³ exports a larger classical solution with exact overlap |
| High norms uniformly bounded before finite endpoint | `higherOrderBound` in both continuation APIs | Supplies order 7 / 3 required by restart |
| Uniform restart from smooth data bounded only in H¹ | Neither route | Exact residuals above |
| Rough H¹ data and a full mild well-posedness theory | Neither registered smooth-solution API claims it | Larger project than P6's smooth-data conclusion |
| Every locally Sobolev-smooth force in the proposition's literal wording | Not literally quantified by these registered APIs | `MemForceR` additionally requires global L¹ and L² Sobolev paths (`Data.lean:544–550`); periodic force class is the paper's compact-time-support class. A compact-time cutoff/locality adapter is mathematically natural but is not asserted here as a registered theorem |

The force-scope qualification matters: do not say the H¹ sentence is the only conceivable gap against *all* words of the revised proposition. The graph accurately says “for the used force class” (`proof_graph.json:56,69`). A cutoff can preserve a given force on `[0,S+1]` and place it in the global class, but its smooth Sobolev-path construction and locality transfer need explicit checking if broadening registration. Periodic positive shifts need not lie in `forceClassT` because vanishing near the new initial time fails; hence the restart target returns a shifted-force solution directly.

## 2. Tao's argument and available implementation

Primary source: `reference/Tao_2013_Localisation_Compactness_Published.pdf`, printed pp. 37–40, 48–50, 52–53 (PDF page = printed page minus 23). `reference/README.md` identifies this publisher PDF and the same theorem locators. Text was extracted locally, not inferred from citation titles.

At ν=1 Tao uses `X¹ = L∞_t H¹_x ∩ L²_t H²_x` (equation (13)), with a continuous H¹ representative established in Theorem 5.1(i). The projected mild equation is

`u(t) = exp(νtΔ)a + ∫₀ᵗ exp(ν(t-s)Δ) P f(s) ds − ∫₀ᵗ exp(ν(t-s)Δ) P div(u⊗u)(s) ds`.

Tao's B convention incorporates the nonlinear sign. The linear estimate controls X¹ by the H¹ datum, L¹H¹ forcing, and L²L² nonlinear source (equation (22)). Equations (24)–(25) give

`‖∇(uv)‖_{L⁴_t L²_x} ≲ ‖u‖_{X¹} ‖v‖_{X¹}`,

`‖∇(uv)‖_{L²_t L²_x} ≲ T^(1/4) ‖u‖_{X¹} ‖v‖_{X¹}`.

Consequently the nonlinear Duhamel map has a bilinear bound `Cν T^(1/4)` in X¹ (on bounded short windows, with the periodic low mode treated). Theorems 5.1(ii), 5.4(ii), equations (45), (46), use `(‖a‖H¹ + ‖f‖L¹H¹)^4 T ≤ c` at unit viscosity. A ball of radius proportional to that sum is invariant and contractive. Difference estimates plus subdivision give uniqueness beyond the initially certified contraction ball. Tao's definition of H¹ data includes a stronger time condition on the force; the quantitative time estimate uses its L¹H¹ norm. Our smooth fixed forces satisfy the needed finite-window conditions.

**H¹ is subcritical in three dimensions.** The delicate bilinear estimate is a major formalization task, but it is inaccurate to call H¹ scaling-critical. Critical order is Ḣ¹ᐟ². A large arbitrary critical-norm ball does not yield a uniform small time merely by shrinking T in this estimate; small-data critical theory and profile-dependent lifespan are different claims.

Persistence is not “rerun Picard independently at every m.” Tao's proof of 5.1(iv), pp. 49–50, first gains `X^s`, `s<3/2`, then uses spatial embeddings to put the nonlinearity in L²H¹, gains X², and iterates to all orders on the same interval. Pressure recovery and the equation bootstrap time derivatives. The proof of 5.4(iv), p. 53, explicitly permits a in every H^k and f in every C^j_t H^k, rather than requiring Schwartz data. Arbitrary rough H¹ data cannot be smooth at t=0; smooth admissible input is essential for our stated endpoint regularity.

### Source inventory and reusable pieces

| Layer | What is actually available | Missing for Tao H¹ route |
|---|---|---|
| Abstract Picard | `vendor/HeliCorgi/Formal/EndpointSafeTwoSpacePicard.lean:8–33,609ff`: contraction on `C(Icc 0 T, X)` for a supplied two-space contract | Concrete low-order product/smoothing estimates; this is not Tao's mixed time-norm X¹ space |
| Duhamel contract | `EndpointSafeTwoSpaceDuhamel.lean:407–442`: bilinear `X →L X →L Y`, smoothing `Y →L X`, integrable time kernel | “Endpoint-safe” handles elapsed time zero by totalization, not a Sobolev endpoint theorem |
| Kept HeliCorgi R³ roots | `formalization/lakefile.toml:19–61`: Sobolev/solenoidal carriers, completeness, Leray/Stokes L² Fourier operators, H² Fourier-L¹ and weighted Young machinery | No concrete H¹ or Ḣ¹ᐟ² local Picard instantiation found among these roots. Carrier definitions and an H² convolution estimate do not supply it |
| A01 | `HorizonUniform.lean:82–138`, `LocalTheoryBundle.lean:167–230`: `SobolevSpace 1 7` solution, order-6 rough/source space, ordinary angle-invariant cylinder route; force cap and H⁷ ball select horizon | H¹ control cannot bound that H⁷ radius. The numeral 1 in `SobolevSpace 1 7` is not the Sobolev order |
| A01 smooth assembly | `CommonHorizon`, `MildUniqueness`, `TameAssembly`, `CylinderWiring`, `DatumPathSmooth`, `JointRepresentative`, `ConstructorAssembly`, `ManuscriptRegularity` | Existing higher-order compatibility, physical realization, divergence, pressure and time regularity are substantial reuse, but start on the existing high-order mild spine; no automatic H¹-to-spine bridge |
| T11 quantitative local theory | `LocalExistence.lean:87–98,238–338`; `ExistenceInputH3.lean:15–44,266–338`: `C([0,T], PeriodicSobolev 3)`, rough H², integrable one-derivative heat kernel | Lowering the datum norm in the theorem without changing the construction is invalid; radius contains K at order 3 and the L¹H³ force bound M 3 |
| T11 smoothing ladder | `DuhamelHalfStep.lean:265–272`: H^(r+1/2) / H^(r−1), kernel `(ντ)^(-3/4)`, **r≥3**; `Persistence.lean:173–221` supplies ladder interface | Half-step means a gain above an already high base, not H¹ᐟ² endpoint local theory |
| T11 physical equation | `MildMomentum` derives coefficient evolution and classical momentum; `MildClassical` assembles classical solution from the mild path and persistence; `ClassicalRegularity.lean:1125–1200` proves slab/Sobolev regularity and transformations | Adapt input from a genuinely low-order solution, prove same-interval regularity before classical assembly |
| Restart and continuation | A04 `RestartFixedForce.lean:41`, `ShiftedExtension.lean:247`; T11 `Restart`, `RestartBeyond`, `ExtendsBeyond`, and unconditional H³ versions `ExistenceInputH3.lean:350,406,456,484` | Mostly reusable gluing/quantifier plumbing once a uniform low-order supplier exists; conditional `PeriodicQuantitativeLocalInput'` wrappers are not proofs of that supplier |

A01's `HighContinuation`/`HighContinuationIntegral` and high-order Grönwall prove the squared-H² criterion on existing smooth solutions. They do not directly provide a small uniform H¹ existence time. Nor do the tree's critical small-force results (T20/R43/R44) prove large-data H¹ local theory: they have different smallness hypotheses and rely on the high-order continuation routes.

## 3. Feasible work split, estimates, and risks

These are planning estimates, not measured throughput or promises. One focused implementation/review unit: S ≈ half a working day, M ≈ 1–2 days, L ≈ 3–5 days, XL ≈ 6–10+ days. Model recommendation means a future lane assignment, **not agents launched in this assessment**: GPT-6-astra for analytic design and review; GPT-5.6-sol for bounded adapters after the interfaces are settled. Estimates include meaningful compilation and review, not a full repository rebuild per lemma.

### Route A: faithful Tao mixed-space construction on both domains

| Unit | Concrete exit condition | Size / model | Dependencies |
|---|---|---|---|
| A0 | Elaborated target statements, fixed-force versus cross-force choice, new horizon selection policy | S / sol | none |
| A1 | Complete mixed path carrier, H¹ traces, restriction, norm and measurability bridges | L / astra | A0 |
| A2 | R³ heat maximal estimate from H¹ data, L¹H¹ force and L²L² source to X¹ | L / astra | A1; reuse Fourier/Leray operators |
| A3 | Periodic counterpart with zero mode, force and viscosity constants | M–L / astra | A1, A2 design |
| A4 | Bilinear X¹ estimate with T^(1/4), difference estimate, concrete product realization on both domains | XL / astra | A1–A3 |
| A5 | Affine forced contraction, quantitative time, uniqueness by subdivision | M / sol with astra review | A2–A4 |
| A6 | H¹→X²→all-order persistence on the same interval, including the initial trace | XL / astra | A5 |
| A7 | Physical smooth solution, pressure and common-interval time derivatives, reuse existing assembly | L / sol with astra review | A6 |
| A8 | Fixed compact-window shifted-force bound, uniform restart and endpoint gluing on both domains | M / sol | A7 |
| A9 | New contract/binding/tests, axiom audit and reader-scope update | M / sol | A8 |

**Total: XL programme, approximately 27–45 focused working days**, with overlap possible only after interface design. A4/A6 dominate; allow roughly another quarter if path carriers or physical realization must be redesigned. This is substantially more than a single L lane. A critical Ḣ¹ᐟ² large-data theory is not included.

A spatial-only alternative could try `X=H¹`, `Y=H^(-1/2−ε)`, with a product estimate into Y and a heat kernel of order `t^(-3/4−ε/2)` for `0<ε<1/2`. This would fit the abstract integrable-kernel Picard shape. It still needs negative/fractional-order products, realization and persistence; no concrete instantiation was located. Avoid asserting the borderline product estimate solely from a heuristic Sobolev index calculation.

### Route B: smooth-data H¹ restart via enstrophy and existing continuation

For **the exact smooth-data, fixed-force existential targets above**, a new rough-data mild construction is not logically necessary. Start with the already proved high-order local solution and maximal development. Prove, on each shorter classical interval, with `Y=‖u‖H¹²` and `Z=‖u‖H²²`, an estimate of the shape

`Y' + cν Z ≤ Cν (1 + Y)^3 + Cν ‖f‖L²²`.

A standard 3D interpolation route bounds the convection pairing by
`C ‖u‖H¹^(3/2) ‖u‖H²^(3/2)`, then Young absorbs H² dissipation. Lower-order energy terms and the torus mean must be retained. For all shifts in `[0,S]`, smoothness of the fixed force bounds its L² norm on `[0,S+1]`. An ODE barrier gives one time d>0 and a uniform Y bound depending only on ν, K and that force bound, and integrating the same inequality bounds `∫Z` before d.

If the maximal time were ≤d, monotone passage through shorter intervals would give finite squared-H² integral at that endpoint. The already unconditional H⁷/H³ continuation theorem contradicts maximality. Hence the classical solution exists through a common smaller δ and retains its already constructed smoothness. This argument is **not circular**: it uses existing continuation from the squared-H² integral, whose proof does not assume H¹ restart. It proves neither a lower bound for the old selected horizon nor Tao's arbitrary rough-data existence theorem.

| Unit | Concrete exit condition | Size / model |
|---|---|---|
| B0 | Reconcile H¹/H² Fourier norms with derivative energy and state shifted-force cap | M / sol |
| B1 | General (no critical smallness) enstrophy interpolation/Young inequality on R³ | L / astra |
| B2 | Periodic version including mean and ordinary L² energy | L / astra |
| B3 | Uniform ODE barrier, integrated dissipation, endpoint monotone limit | M–L / astra |
| B4 | Maximal-lifespan contradiction, smooth common-interval restriction, regularity and pressure adapters | M / sol |
| B5 | Uniform restartBeyond and registration/audits | M / sol |

**Total: L–XL, approximately 12–21 focused days for both domains**, conditional on reusing the existing derivative/Fourier bridges. This is the preferred feasibility experiment if P6 is commissioned. First fund B0/B1 as a bounded proof-of-concept; do not precommit to the optimistic total.

Evidence for reuse: `F/Section4/C01/EnstrophyIdentityRaw.lean:8–24` supplies the raw differentiated energy identity; `F/Section3/T20/H1Energy.lean:5–15` supplies periodic energy infrastructure but its displayed absorbed estimate assumes critical smallness. That smallness cannot be silently dropped. Some module docstrings refer to historical residuals, so the future lane must inspect current bridge declarations rather than accept an old “still open” comment as definitive. The needed **general** cubic inequality and uniform ODE-to-lifespan theorem have not been established by this assessment. This route uses a fixed-force L² compact-window cap; it does not establish cross-force uniformity controlled only by L¹H¹.

An H²-uniform variant may reduce product-estimate difficulty (H² is an algebra in 3D and H²→L∞ tools exist), but still needs a concrete local construction or energy-to-continuation bridge and smooth assembly. It cannot close the named H¹ obligation. For the current proposition's continuation conclusion, it adds no necessary coverage beyond H⁷/H³. Do not spend a separate phase on it solely to recolor P6.

### Principal risks and acceptance conditions

- Do not replace a selected high-order horizon by a low-order number without constructing the solution on that number. An existential maximal-lifespan argument avoids this trap.
- A bound on each H¹ datum separately is not uniformity on a ball. δ must precede the datum and restart time; force smoothness bounds must be on a common compact window.
- H¹ does not embed into H³/H⁷. Smooth oscillatory divergence-free data can have bounded H¹ norm and arbitrarily large high norms. Sobolev monotonicity goes in the wrong direction for that shortcut.
- Smooth propagation must not take the infimum of independently selected high-order times, which may be zero. Either prove persistence on the H¹ interval or use the existing smooth maximal solution with the enstrophy contradiction.
- Inhomogeneous H² includes the low mode and L² norm; Laplacian dissipation alone is insufficient, especially on the torus.
- Endpoint integrability requires uniform bounds before the maximal time and a monotone-limit argument, not merely finiteness on every strict compact subinterval.
- R³ angular Fourier data, physical fields, and the ordinary cylinder are distinct carriers. Reuse requires proved bridges. Torus force shifts are not generally in the original force class.
- No claim of “missing from Mathlib” is made. This assessment locates missing assembled estimates in this project's closure; it is not a library impossibility claim.

## 4. Recommendation and downstream audit

**Choose (iii) for this phase: leave P6 Partial and retain the documented distinction.** The benefit of H¹ uniformity is a stronger local-theory library result, not repair of a current downstream theorem. If that independent result is desired, commission Route B first for the exact smooth-data fixed-force target; choose Route A only if rough-data mild well-posedness or the L¹H¹ cross-force strengthening is itself an intended deliverable.

Concrete downstream article uses located by searching `prop:local`, `lem:Rlocal`, and the criterion labels:

- `paper/revised/sections/03-torus.tex:249`: “Uniqueness in Proposition ... identifies the constructed velocity with the maximal solution ...”. This consumes uniqueness/maximality, not an H¹ ball.
- `paper/revised/sections/04-whole-space.tex:53`: “Proposition ... identifies the solution with the unique maximal solution”; extension is excluded using C_tH² boundedness and blowup. Again no uniform H¹ lifespan bound.
- `paper/revised/sections/03-torus.tex:313–315`: “Smooth data retain their higher regularity by the local theory cited in Proposition ...”. This is persistence, not an H¹-ball duration claim.
- `paper/revised/sections/04-whole-space.tex:96–98`: “persistence of regularity for the smooth data in our classes identifies it with the maximal classical solution ...”. Same distinction.
- The continuation proof itself (`02-preliminaries.tex:178–182`, quoted above) has bounds at **every** high order before restart; it therefore needs only one high-order uniform route.

Code/closure corroboration: `formalization/blueprint/CLOSURE_AUDIT.md:42,49–50,57–62` records T20, R43 and R44 using constructed high-order continuation and states explicitly that missing H¹ restart is not assumed by Closed downstream statements. `research/T11/H1_GAP.md:119` resolves the historical T20 concern: its copied H¹ vocabulary is not a consumed field; the criterion route uses order 3 and the ball-free extension conclusion. `verification/Bindings/TorusLocalTheory.lean:355–415,483–486` constructs the local and H³ continuation APIs; the final record does not take H¹ restart as an argument. Whole-space binding `verification/Bindings/LocalTheoryV2.lean:87–101` selects the proved A01 construction. `L21_H1` has no proved dependency role in `proof_graph.json:78–91`; reader inventory references to that node do not turn it into a theorem premise.

Historical record handling: the requested `research/A01/RECONCILIATION.md` and `research/A01/SPEC_ISSUES.md` do not exist in this checkout (confirmed by pathname search). Used instead: `A01/V2_DECISION.md`, `A01/REPORT_212.md`, `A01/REVIEW_H1_REFACTOR_169.md`, and the present contracts/bindings. `research/T11/RECONCILIATION.md:10,16,33,73–75` and `H1_GAP.md` preserve the ball/force/quantifier decisions. Old historical claims were checked against current declarations and the current revised article. No coverage markers, contracts, or Lean files were changed.
