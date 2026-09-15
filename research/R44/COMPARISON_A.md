# R44 — Proposition 4.4 (`prop:Rcritical2`) — draft A comparison

Statement `paper/sections/04-whole-space.tex:136-143`; proof `:145-174`.
Ledger `research/section4/STATEMENTS.md` §4 (`:556-660`); R41's consumption
`:133-140`; use in Theorem 4.1 at `04-whole-space.tex:179` (`S = T`).

Output: `research/R44/DraftA.lean`,
`BlowupDensity.R44.DraftA.RCritical2API` — 9 fields (2 universal constants +
2 positivity + `radius` + `radiusFormula` + `radiusPos` + `main` +
`nonDensityBallZero`), 0 local `def`s.  Typechecks (see §5).

R44 is the `q = 2` twin of Proposition 4.3.  This draft reuses the reconciled
R43 shape (`research/R43/Spec.lean`) deliberately: constants-as-fields before
`ν/S/f`, `ℝ≥0∞` fail-safe norms, a strict lifespan-inequality conclusion, and
the `Data`-level force norm.  **Two structural differences from R43**, both
forced by the paper:

1. **Datum is exactly zero** (`:139`), so there is *no spatial homogeneous norm*
   and *no local `dotHomogeneousENorm` `def`* (R43 needed both).  The datum is
   spelled `(fun _ => 0)`, as `Data.breakdownSetRZero` unfolds it.
2. **The force norm is inhomogeneous `H^{-1/2}` over `(0,∞)`, not homogeneous**
   (`:140`, with `:173` "The inhomogeneous norm is essential here …").  So the
   norm is `forceSobolevENormL2 (-1/2)`, **not** `forceHomogeneousENorm 2 (-1/2)`.
   This inverts the R43-gap-G3 warning: the paper's own remedy for the
   uncontrolled homogeneous negative norm *is* the inhomogeneous norm.

> Note on the task brief: the brief anticipated `L²(0,S; Ḣ^{-1/2})` (homogeneous,
> over `[0,S]`).  The paper actually states `L²(0,∞; H^{-1/2})` — **inhomogeneous**,
> over the whole half-line `(0,∞)` — and the Grönwall bound at `:167` uses the
> `(0,∞)` norm as the majorant of the `[0,S]` norm.  Draft A follows the paper.
> `forceSobolevENormL2 (-1/2)` (`Data.lean:235`) is the correct object; using
> `forceHomogeneousENorm 2 (-1/2)` would make the statement false as proved.

---

## 1. Field-by-field table

Legend: **consumed from** = the sibling-spec field or `Data.lean` definition the
field is stated in terms of.  **existing source Lean** = anything in
`formalization/NSFormalization/{Source,Paper1,Paper3}` or
`vendor/NavierStokesAndEuler/NavierStokes` that already states this (grepped for
`Rcritical2`, `prescribed`, `finite interval`, `negative Sobolev`, `Hminus`,
`H^{-1/2}`).

| field | paper line | consumed from | existing source Lean | gap |
|---|---|---|---|---|
| `c : ℝ`, `C : ℝ` | `:143` "universal positive constants `c, C`" | — (fields, bound before `ν/S/f`) | none | none — quantifier order is a statement choice |
| `hc : 0 < c`, `hC : 0 < C` | `:143` | — | none | none |
| `radius : ℝ → ℝ → ℝ` | `:137` `r_{ν,S}` | — (a named function, as `STATEMENTS.md:585` wants) | none | none |
| `radiusFormula` | `:143` `r_{ν,S}=cν^{3/2}e^{−CνS}` | `Real.rpow`, `Real.exp` (Mathlib) | none | none — exact `ν,S`-dependence pinned |
| `radiusPos` | `:137` `r_{ν,S}>0` | `radiusFormula`, `hc` | none | none |
| `main` | `:137-143` | `MemForceR` (`Data.lean:544`), `forceSobolevENormL2 (-1/2)` (`:235`), `maximalLifespanR` (`:657`) | **none** — no Prop 4.4 anywhere | statement OK; **proof** needs D01/C01/A04/A05 (§3) |
| `nonDensityBallZero` | `:179` (`S=T`), `STATEMENTS.md:133-140` | `breakdownSetRZero` (`Data.lean:686`) = `B^ℝ_{ν,0,T}` | **none** | statement OK; derivable from `main` at `S:=T` |

**Existing source Lean, overall.** `grep -rniI` over
`formalization/NSFormalization/{Source,Paper1,Paper3}` and
`vendor/NavierStokesAndEuler/NavierStokes` for `Rcritical2` / `prescribed
finite interval` / `negative Sobolev` / `Hminus` / `H^{-1/2}` returns **no
declaration** of Proposition 4.4 or of an `L²_t H^{-1/2}` regularity threshold.
`formalization/NSFormalization/Section4/I02/Prescribed.lean` matches
"prescribed" but is the torus insertion cutoff (Section 3), unrelated.
`Source/FourierConvention.lean:23` `angularFourier` is the only negative-order
Fourier machinery, and it is a pointwise Bochner transform (junk `0` off `L¹`),
not a norm-finiteness lemma.  **All reuse is at the `Contracts.V1.Data` layer.**

Data.lean objects reused, all present: `MemForceR` (`:544`), `initialClassR`
(`:509`, unused here since `a = 0`), `forceSobolevENorm`/`…L2` (`:225,235`),
`maximalLifespanR` (`:657`), `RegularThrough` (`:664`, mentioned for the
equivalence), `breakdownSetRZero` (`:686`), `SpaceTimeField`/`SpatialField`
(`:104,99`).

---

## 2. Why `main` and `nonDensityBallZero` are both fields

`nonDensityBallZero` is `main` at `S := T` composed with unfolding
`breakdownSetRZero ν T = {f | MemForceR f ∧ maximalLifespanR ν (fun _=>0) f ≤
ENNReal.ofReal T}`: from `ENNReal.ofReal T < maximalLifespanR …` and
`maximalLifespanR … ≤ ENNReal.ofReal T` (were `f ∈ B^ℝ`) one derives `False`.
It is kept as its own field for the reason R43 keeps `inhomogeneousAtZero`
(`STATEMENTS.md:522`, R43 `COMPARISON.md` §1 row 10): the consumer `R41` should
not redo the reduction.  The task brief asks for "the R41 consequence field at
`S = T` … as one field"; this is it, phrased as disjointness from `B^ℝ_{ν,0,T}`
to match the ledger's "contains no element of `B^ℝ_{ν,0,T}`"
(`STATEMENTS.md:135-137`).

Conclusion form: `ENNReal.ofReal S < maximalLifespanR ν (fun _=>0) f`, the
paper's literal `T^ν_{max,ℝ}(0,f) > S` (`:141`), chosen over
`RegularThrough ν (fun _=>0) f S` (`Data.lean:664`) because it is what the paper
writes *and* what A04's `extendsBeyond` (`research/A04/Spec.lean:613`) produces.
The two are provably equivalent: `ofReal S < ⨆_{S'}⨆_{Nonempty(Sol S')} ofReal S'`
holds iff some horizon `S' > S` carries a solution, i.e. iff `∃ δ>0` with a
solution on `[0,S+δ)`.

---

## 3. Clauses R44 needs that the sibling specs do **not** currently provide

Nothing blocks *stating* R44: the structure typechecks against `Data.lean`
alone.  These are *proof* inputs.  IDs continue R43's `COMPARISON.md` §4
scheme; "R43?" marks whether R43 already recorded the same or the homogeneous
twin.

| id | owner | exact Lean shape needed | R43? | why R44 needs it |
|---|---|---|---|---|
| **G3′** | **D01** (`DatumLemmas`) | `∀ f, MemForceR f → forceSobolevENormL2 (-1/2) f ≠ ⊤`, via the `m=0` integer path of `MemForceR` (`H⁰=L²`, `MemLp G 2 forceTimeMeasure`) and the datum-path index monotonicity `forceSobolevENorm 2 (-1/2) f ≤ forceSobolevENorm 2 0 f` (a Bochner-path lift of `‖·‖_{H^{-1/2}} ≤ ‖·‖_{H⁰}`). | new (R43 had the `+1/2` twin, `⊤` risk) | so `𝓕_ℝ` sits inside `L²(0,∞;H^{-1/2})` (`:8` "relative … topology on `𝓕_ℝ`") and the Grönwall RHS `‖f‖²_{L²_tH^{-1/2}}` is finite. **Easier than R43's G3**: `-1/2<0`, so the `m=0` path suffices — no interpolation. Not a field of the statement (fail-safe covers well-formedness). |
| **GJ** | **D01** | the operator `J=(I−Δ)^{1/2}` (symbol `(1+|ξ|²)^{1/2}`, `02-preliminaries.tex:51`) and the **exact** weight identity `‖u‖²_{H^{3/2}} = ‖u‖²_{H^{1/2}} + ‖∇u‖²_{H^{1/2}}` (`STATEMENTS.md:585-588`; it is `(1+|ξ|²)^{3/2}=(1+|ξ|²)^{1/2}+|ξ|²(1+|ξ|²)^{1/2}`, exact not up-to-constant), plus the duality `|⟨f,Ju⟩| ≤ ‖f‖_{H^{-1/2}}‖u‖_{H^{3/2}}`. | new | R44's own energy step tests against `Ju`; no lane owns `J` or this identity. |
| **G4′** | **C01** (mirror of `forceTimeRegularity`) or D01 | slicewise `B(t)=‖f(t)‖_{H^{-1/2}}` as a real function, interval-integrable on `[0,t]`, with `∫₀ᵗ B(s)² ds = ‖f‖²_{L²(0,t;H^{-1/2})}`. C01's `forceTimeRegularity` (`research/C01/Spec.lean:326`) gives this only for the **`L²` (order-0)** slice norm. | R43 had G4 at `L¹_t Ḣ^{1/2}` | the Grönwall integrates `C₃ν⁻¹B²` in time; the RHS must be the `L²_tH^{-1/2}` force norm of the hypothesis. |
| **GC2** | **R44's own lane** (no sibling; C01 declares it out of scope, `C01/Spec.lean:50`) | **eq:Rcritical2** (`:161-164`): energy identity against `Ju` with dissipation `νZ²`, the trilinear/force bounds (via A05, see below) and Young → `(Y²)'+νZ² ≤ C₂νY²+C₃ν⁻¹B²` while `Y ≤ θν`; then Grönwall from `Y(0)=0` (`:166-167`), the choice `r_{ν,S}<θ²ν²/4`, and the **first-exit-time** argument (`:169`) on `[0,min(S,T_max))`. Needs a differentiable inhomogeneous critical path (`Y,Z` as `HasDerivAt`-carrying reals), the analogue of R43-G7 / A04's `HasSmoothSobolevPath` at the critical order — **no lane exports one**. | R43-G7 (homogeneous twin) | the substance R44 owns. |
| **G6** | **A04 ↔ C01** spelling pin | `research/A04/Spec.lean:202` `squaredHTwoIntegral` uses `sobolevENorm 2 _ ^ (2:ℕ)`; `research/C01/Spec.lean:602` `h2TimeIntegralZeroDatum` gives `sobolevENorm 2 _ ^ (2:ℝ)`. One `ℝ≥0∞` identity `x^(2:ℕ)=x^(2:ℝ)` bridges them. | R43-G6, identical | R44 feeds C01's `∫₀^S‖u‖²_{H²}` into A04's `squaredHTwoIntegral … ≠ ⊤`. |
| **GG** | **R44's own lane** (gluing; a C01 endpoint corollary would ease it) | build `SolvesBelow ν (fun _=>0) f S u p` (`A04/Spec.lean:223`) from the maximal family (A02) restricted below `S`, discharge C01's absorption gate `∀ t∈Ico 0 S, C₁·criticalL3(u t) ≤ ν/4` from `‖u‖₃ ≤ Cθν` (choosing `θ` so `C₁·Cθν ≤ ν/4`), then apply `h2TimeIntegralZeroDatum` (`:599`) + `extendsBeyond` (`:613`). | R43-G5 (analogous, at `S=T_max`; here `S` is a *prescribed* finite horizon) | turns the finite `H²` integral into `ofReal S < maximalLifespanR`. |

**Already satisfied (recorded so the check shows):**

* **A05 embeddings** — `velocityCriticalL3` (`:366`, `‖u‖₃ ≤ C(1/2)‖u‖_{Ḣ^{1/2}}`),
  `derivativeCriticalL3` (`:384`, `‖∇u‖₃+‖Λu‖₃ ≤ C‖u‖_{Ḣ^{3/2}}` — gives `‖Ju‖₃`),
  `gradientLSix` (`:396`, `‖∇u‖₆ ≤ C‖Δu‖₂` for reused eq:RH1), and crucially
  `homogeneousLeSobolev` (`:268`, `‖z‖_{Ḣ^a} ≤ ‖z‖_{H^a}` for `0≤a<3/2`) which
  bridges A05's homogeneous outputs to R44's **inhomogeneous** `Y=‖u‖_{H^{1/2}}`,
  `Z=‖∇u‖_{H^{1/2}}`. `STATEMENTS.md:602` asked for exactly `a∈{1/2,1}`; A05's
  general-`a` clause covers both. **A05 is complete for R44's embeddings.**
* **C01 ordinary-energy / H² route at `a=0`** — `l2Bound` (eq:RL2, `:383`),
  `enstrophyDifferentialBound`/`enstrophyIntegralBound` (eq:RH1, `:510,532`),
  `h2TimeIntegralZeroDatum` (`:599`, the `a=0` `∫₀^S‖u‖²_{H²}` assembly with
  `K(S)=∫₀^S‖f‖₂`, `‖∇a‖₂=0`). All present.
* **A04 continuation** — `extendsBeyond` (`:613`) is *documented as the field
  R44 uses* (`A04/Spec.lean:308,593`); it delivers `ofReal S < maximalLifespanR`.
* **A02** — the maximal-solution family behind `maximalLifespanR`; no new clause.

---

## 4. Unit split (≤ 8 units)

Bounded plan to *prove* R44 once the statement is registered.  S/M/L = effort.

| unit | S/M/L | what | depends on |
|---|---|---|---|
| **U1** | S | Register `RCritical2API` (this draft, after A/B reconciliation) as the Section-4 contract; wire the two consumer fields. | — |
| **U2** | M | **G3′**: `forceSobolevENormL2 (-1/2) f ≠ ⊤` on `𝓕_ℝ` (D01: `m=0` path + index monotonicity). | `MemForceR` |
| **U3** | M | **GJ**: `J=(I−Δ)^{1/2}`, the `H^{3/2}=H^{1/2}⊕(∇)H^{1/2}` weight identity, the `⟨f,Ju⟩` duality (D01). | Fourier weights |
| **U4** | L | **GC2 core**: eq:Rcritical2 — energy identity against `Ju`, dissipation `νZ²`, trilinear+force bounds via A05, Young ⇒ `(Y²)'+νZ² ≤ C₂νY²+C₃ν⁻¹B²` under `Y≤θν`. | U3, A05 |
| **U5** | M | Grönwall from `Y(0)=0` ⇒ `Y(t)² ≤ C₃ν⁻¹e^{C₂νS}‖f‖²_{L²_tH^{-1/2}}`; choose `r_{ν,S}<θ²ν²/4`; first-exit-time bound to `min(S,T_max)`. Produces `c,C`. | U4, G4′ |
| **U6** | M | Continuation half: `‖u‖₃ ≤ Cθν` discharges C01's absorption gate; assemble `∫₀^S‖u‖²_{H²}<∞` (`h2TimeIntegralZeroDatum`), glue `SolvesBelow`, apply A04 `extendsBeyond` ⇒ `main`. | U5, C01, A04, GG, G6 |
| **U7** | S | Derive `nonDensityBallZero` from `main` at `S:=T` + `breakdownSetRZero` unfold. | U6 |
| **U8** | S | Spelling-pin bridge **G6** (`x^(2:ℕ)=x^(2:ℝ)` in `ℝ≥0∞`) between A04 and C01. | — |

---

## 5. Commands and results

```
cd WT && bash scripts/lean-install.sh            # exit 0 (toolchain + cache ready)
. scripts/lean-env.sh ; export LEAN_NUM_THREADS=6
cd verification && lake env lean ../research/R44/DraftA.lean   # exit 0, no output
grep -nE 'sorry|admit|native_decide|axiom ' DraftA.lean        # only in docstring prose
```

`DraftA.lean` typechecks with no errors and no warnings; it contains one
`structure`, no `def`, no proof term, no `sorry`/`axiom`/`native_decide`, and no
abstract `Prop` placeholder field.
