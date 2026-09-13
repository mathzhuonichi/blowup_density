# Section 4 statement ledger (task 006-SPEC)

Top-down, BFS order: Theorem 4.1 → Theorem 4.2 → Proposition 4.3 → Proposition 4.4 →
Corollary 4.5 → Proposition 4.6 → Theorem 4.7. Authoritative source is
`paper/sections/04-whole-space.tex` at the tree state of commit `4ba9f2b`; supporting
definitions from `paper/sections/01-introduction.tex`, `paper/sections/02-preliminaries.tex`,
`paper/sections/appendix-a-local-theory.tex`, `paper/sections/appendix-b-embeddings.tex`,
and the reused Euclidean content of `paper/sections/03-torus.tex`
(Prop. 3.3 `prop:scaling`, Lem. 3.4 `lem:potential`, Lem. 3.5 `lem:correction`,
eqs. `eq:scaling`, `eq:packetEscale`, `eq:packetFscale`).

This is a specification record, not a proof record. Nothing here is certified;
`⟪X:name⟫` marks an object that task `X` must define before the contract can be typed.
Most are `⟪D01:…⟫`; a few belong to `I01` (packet constants) or `G01` (grids) and are
marked accordingly. Every field listed in a skeleton is consumed by at least one
downstream proof in Section 4 — the lists are intended to be complete and minimal.

## 0. Global conventions that all seven results share

| Convention | Where fixed | Content |
|---|---|---|
| Equation | `01-introduction.tex:4` `eq:NS` | `∂_t u + (u·∇)u − νΔu + ∇p = f`, `∇·u = 0`, `u(·,0) = a` on `D = R³` |
| Fourier | `01-introduction.tex:82–98` | `ẑ(ξ) = (2π)^{-3/2}∫ e^{-ix·ξ} z(x) dx`; `‖z‖²_{H^s(R³)} = ∫ (1+|ξ|²)^s |ẑ|²` |
| Homogeneous | `01-introduction.tex:105–117`, `02-preliminaries.tex:52–74`, App. B | three distinct realizations — see §8.4 |
| Time norms | `01-introduction.tex:125` `eq:time-norms` | `L^q_t X_x = L^q(0,∞;X)` for **forces**; velocity norms use `(0,T)` |
| Velocity metric | `01-introduction.tex:143` `eq:Enorm` | `‖z‖_{E_T} = ‖z‖_{L^∞(0,T;L²)} + ‖∇z‖_{L²(0,T;L²)}` |
| Packet | `01-introduction.tex:15` `thm:packet`, line 64 | one solution of Thm 1.1 is fixed once and renamed `(U,P,F)` |
| Packet constants | `02-preliminaries.tex:127` `lem:packetenergy` | `M = sup_{0≤t<1}‖U(t)‖₂`, `D = ‖∇U‖_{L²((0,1)×R³)}`, both finite; `U,P` vanish on an initial interval |
| Data classes | `02-preliminaries.tex:13,17` | `X_R = H^∞(R³;R³) ∩ L²_σ(R³)`, `F_R` as in `eq:Rclasses` |
| Singular set | `02-preliminaries.tex:44` `eq:Rsingularforces` | `B^R_{ν,a,T} = {f ∈ F_R : T^ν_{max,R}(a,f) ≤ T}` |
| Pressure | `02-preliminaries.tex:90` `eq:Rpressure` | `∇p = (I−P)(f − ∇·(u⊗u))`; scalar `p` determined up to a function of time; **no** `p ∈ L²` requirement |
| Local theory | `02-preliminaries.tex:105` `prop:local` | existence, uniqueness, maximal lifespan `T^ν_{max,R}(a,f)`, continuation under `∫₀^S ‖u‖²_{H²} < ∞` |
| "Regular through T" | `02-preliminaries.tex:34–36` | the solution extends smoothly to `[0,T+δ]` for some `δ > 0` |
| Topology on force classes | `01-introduction.tex:137–141` | each smooth force class carries the **relative** topology of the stated norm, *not* the test-function topology |

Exponent arithmetic used everywhere: `s_q = 2/q − 3/2`, `β(q,s) = 2/q − 3/2 − s = s_q − s`,
`α(p,q) = −3 + 3/p + 2/q`. `s_1 = 1/2`, `s_2 = −1/2`. This arithmetic is already frozen in
`verification/Contracts/V1/Thresholds.lean` as `ThresholdAPI.exponent`; every skeleton below
must reuse that field rather than re-deriving the formula.

---

## 1. Theorem 4.1 — `thm:Rmain` (Two whole-space Sobolev thresholds), task **R41**

`04-whole-space.tex:7–14`. Merged number: Theorem 4.1.

### 1(i). Statement

Fix `ν > 0` and `T > 0`. Let `q ∈ {1,2}` and set `s_q = 2/q − 3/2`. Let `s ∈ R` be arbitrary,
and give `F_R` the relative topology of the norm `‖·‖_{L^q(0,∞;H^s(R³))}`. Then:

1. **(subcritical density, every fixed `a`)** For every fixed `a ∈ X_R`, if `s < s_q` then
   `B^R_{ν,a,T}` is dense in `F_R` for that topology. Unwound: for every `a ∈ X_R`, every
   `s < s_q`, every `g ∈ F_R` and every `ρ > 0`, there exists `f ∈ F_R` with
   `T^ν_{max,R}(a,f) ≤ T` and `‖f − g‖_{L^q(0,∞;H^s)} < ρ`. Quantifier order in the paper:
   `∀ ν,T > 0 ∀ q ∀ s ∀ a ∀ g ∀ ρ ∃ f`.
2. **(sharp characterisation, `a = 0` only)** For `a = 0`, `B^R_{ν,0,T}` is dense in `F_R`
   in that topology **if and only if** `s < s_q`.

So the thresholds are `1/2` for `L¹_t H^s_x` and `−1/2` for `L²_t H^s_x`. The trailing sentence of
the theorem adds a rider on the approximant produced in the density direction: around every
reference that is regular through `T`, the approximating solution can be chosen to have
(a) the same initial velocity `a`, (b) the same earlier history, (c) singularity exactly at `T`
(not merely by `T`), and (d) velocity difference tending to zero in `E_T`.

Quantifier/typing notes that a Lean statement must not lose:
* `a` is **fixed and universally quantified** in (i); (ii) is asserted **only at `a = 0`**. There
  is no claim that the converse holds for general `a`.
* Time domain of the force norm is `(0,∞)` (all of positive time, including after `T`); the
  velocity domain is `[0,T)`.
* The topology is relative on `F_R`, i.e. density inside the smooth class, not in a completion
  (contrast Proposition 4.6). Clarification **C4** is exactly about not conflating the two.
* `T^ν_{max,R}(a,f) ≤ T` is breakdown **by** `T`, not at `T` (see optional wording change **O1**).
* Non-density direction means: there exist `f₀ ∈ F_R` and `ρ > 0` with
  `‖f' − f₀‖_{L^q_tH^s} ≥ ρ` for every `f' ∈ B^R_{ν,0,T}`; the proof takes `f₀ = 0`.
* Context sentence after the theorem (`04-whole-space.tex:16`): "For `q = 2`, the converse uses a
  regular neighborhood whose radius depends on `T`" — i.e. the `q=2` obstruction radius is
  `r_{ν,T}` from Proposition 4.4 and is *not* uniform in `T`.

### 1(ii). D01 needs

* `⟪D01:X_R⟫` = `H^∞(R³;R³) ∩ L²_σ(R³)` — `02-preliminaries.tex:13`; `H^∞ = ⋂_m H^m` with its
  Fréchet topology (only the *set* is used in Section 4, not its topology).
* `⟪D01:F_R⟫` — `02-preliminaries.tex:17` `eq:Rclasses`:
  `f ∈ C^∞([0,∞);H^∞)` (smooth into each `H^m`, one-sided time derivatives at `0`) with
  `‖f‖_{L^1_tH^m} + ‖f‖_{L^2_tH^m} < ∞` for every integer `m ≥ 0`. Needed corollaries:
  `0 ∈ F_R`; `F_R` is a real vector space; `‖f‖_{L^q_tH^s} < ∞` for **every real `s`** and
  `q ∈ {1,2}` (take integer `m ≥ max(s,0)` and use monotonicity), so the relative topology is
  well defined at every `s` in the theorem.
* `⟪D01:normLqHs q s⟫` = `‖·‖_{L^q(0,∞;H^s(R³))}` — `01-introduction.tex:125`.
* `⟪D01:Hs s⟫` for all real `s`, real-vector-valued, with monotonicity
  `‖z‖_{H^s} ≤ ‖z‖_{H^r}` for `s ≤ r` **with constant one** (used twice in the converse:
  `H^s ↪ H^{1/2}` for `s ≥ 1/2`, `H^s ↪ H^{-1/2}` for `s ≥ −1/2`).
* `⟪D01:Tmax ν a f⟫` = `T^ν_{max,R}(a,f) ∈ (0,∞]` — `02-preliminaries.tex:30–36`, well defined by
  `prop:local`; `⟪D01:B_R ν a T⟫` — `eq:Rsingularforces`.
* `⟪D01:RegularThrough ν a g T⟫` — `02-preliminaries.tex:34–36` (used only by the rider).
* `⟪D01:normET T⟫` — `eq:Enorm` (rider (d)).
* `⟪D01:DenseRel⟫` — relative density of a subset of a normed class.
* Threshold arithmetic: `ThresholdAPI.exponent`, `positive`, `l1`, `l2`
  (`verification/Contracts/V1/Thresholds.lean`).

### 1(iii). DAG children and the exact shape consumed

`R41 ← R41D, R43, R44` (`DEPENDENCY_GRAPH.md`).

* **From R41D (subcritical density branch, itself `← R42`)** the proof consumes the two-case
  split at `04-whole-space.tex:176–180`: for fixed `a ∈ X_R`, `g ∈ F_R`, `ρ > 0`, `s < s_q`,
  either `T^ν_{max,R}(a,g) ≤ T`, in which case `f := g` already lies in `B^R_{ν,a,T}` and the
  distance is `0`; or `T^ν_{max,R}(a,g) > T`, in which case there is `δ > 0` with the reference
  regular through `T+δ` and Theorem 4.2 supplies `ε₀ > 0` such that for all `0 < ε < ε₀`,
  `f := g_ε` satisfies `g_ε ∈ F_R`, `T^ν_{max,R}(a,g_ε) = T`, and
  `‖g_ε − g‖_{L^q_tH^s} < ρ`.
* **From R43 (Prop. 4.3)** exactly one consequence: there is a universal `c > 0` such that
  `{f ∈ F_R : ‖f‖_{L^1_tH^{1/2}} < cν}` contains no element of `B^R_{ν,0,T}`
  (because each such `f` has `T^ν_{max,R}(0,f) = ∞ > T`). Combined with
  `‖·‖_{H^{1/2}} ≤ ‖·‖_{H^s}` for `s ≥ 1/2`, this gives, for every `s ≥ 1/2`, a ball of radius
  `cν` about `0` in the `L^1_tH^s` metric that misses `B^R_{ν,0,T}`.
* **From R44 (Prop. 4.4)** exactly one consequence, applied at `S = T`: there is
  `r_{ν,T} > 0` such that `{f ∈ F_R : ‖f‖_{L^2_tH^{-1/2}} < r_{ν,T}}` contains no element of
  `B^R_{ν,0,T}` (each such `f` has `T^ν_{max,R}(0,f) > T`). With
  `‖·‖_{H^{-1/2}} ≤ ‖·‖_{H^s}` for `s ≥ −1/2`, same conclusion in `L^2_tH^s` for every `s ≥ −1/2`.
* The rider sentence is *not* proved in `R41`; the paper says "The energy and earlier-history
  assertions are part of the insertion theorem", so it is a re-export of R42 fields.

### 1(iv). Proposed contract skeleton

```lean
structure RMainAPI where
  ν T : ℝ
  hν : 0 < ν
  hT : 0 < T
  q : ℝ
  hq : q = 1 ∨ q = 2
  thresholds : ThresholdAPI                       -- V1 contract, supplies s_q = exponent q 0
  -- (i) density for every fixed initial velocity, strictly below the threshold
  densityFixedInitial :
    ∀ a, a ∈ ⟪D01:X_R⟫ → ∀ s : ℝ, s < thresholds.exponent q 0 →
      ∀ g, g ∈ ⟪D01:F_R⟫ → ∀ ρ : ℝ, 0 < ρ →
        ∃ f, f ∈ ⟪D01:B_R⟫ ν a T ∧ ⟪D01:normLqHs⟫ q s (f - g) < ρ
  -- (ii) at zero initial velocity the subcritical range is exactly characterised
  densityZero :
    ∀ s : ℝ, s < thresholds.exponent q 0 →
      ∀ g, g ∈ ⟪D01:F_R⟫ → ∀ ρ : ℝ, 0 < ρ →
        ∃ f, f ∈ ⟪D01:B_R⟫ ν 0 T ∧ ⟪D01:normLqHs⟫ q s (f - g) < ρ
  nonDensityZero :
    ∀ s : ℝ, thresholds.exponent q 0 ≤ s →
      ∃ g ρ, g ∈ ⟪D01:F_R⟫ ∧ 0 < ρ ∧
        ∀ f, f ∈ ⟪D01:B_R⟫ ν 0 T → ρ ≤ ⟪D01:normLqHs⟫ q s (f - g)
  -- trailing rider: the approximant around a regular reference is the inserted family
  regularReferenceRider :
    ∀ a g, a ∈ ⟪D01:X_R⟫ → g ∈ ⟪D01:F_R⟫ → ⟪D01:RegularThrough⟫ ν a g T →
      ∀ s : ℝ, s < thresholds.exponent q 0 → ∀ ρ : ℝ, 0 < ρ →
        ∃ f u, f ∈ ⟪D01:F_R⟫ ∧
          ⟪D01:Tmax⟫ ν a f = T ∧                                 -- singular exactly at T
          ⟪D01:IsMaximalSolution⟫ ν a f u ∧
          (∀ t, 0 ≤ t → t ≤ T - ρ → u t = ⟪D01:refVelocity⟫ ν a g t) ∧  -- same earlier history
          ⟪D01:normET⟫ T (u - ⟪D01:refVelocity⟫ ν a g) < ρ ∧
          ⟪D01:normLqHs⟫ q s (f - g) < ρ
```

`densityZero` is the `a = 0` instance of `densityFixedInitial`; keep it as a separate field only
if the reviewer wants the "iff" readable as one pair of fields, otherwise derive it.

### 1(v). Risk notes

* **Relative vs completed topology.** (C4) The theorem is relative density inside `F_R`.
  Proposition 4.6 is density in the *completion*. A single Lean `Dense` predicate on a
  `Metric.Space` structure will silently pick one; the contract must name the ambient set.
* **`a` quantification.** The single most likely formalisation error is stating (ii) for general
  `a`. The paper proves the converse only at `a = 0`, and the proof genuinely needs `Y(0)=0`
  in Prop. 4.4 and `‖a‖_{Ḣ^{1/2}} = 0` to reach the clean `cν` ball in Prop. 4.3.
* **Endpoint inclusion.** Non-density is asserted at `s = s_q` itself (the embedding steps use
  `s ≥ 1/2` and `s ≥ −1/2`). Do not write `s > s_q`.
* **Norm-one embedding.** The proof relies on `H^s ↪ H^{1/2}` "with norm at most one". With the
  paper's weight `(1+|ξ|²)^s` this is exact, but it is false for the periodic
  `(1+4π²|k|²)^s` vs `(1+|k|²)^s` normalisations mentioned in the intro footnote. D01 must pin
  the Euclidean weight.
* **Deferred detail.** The proof says "choose `δ > 0` so that the reference exists through
  `T+δ`" without constructing `δ`; the construction is
  `δ := (min(T^ν_{max,R}(a,g), T+1) − T)/2`, which needs `T_max > T` and the fact that the
  solution is smooth on every compact subinterval of `[0,T_max)`.
* **Well-definedness of the topology at every real `s`.** Not stated in the paper; needed so that
  the phrase "relative `L^q_tH^s` topology on `F_R`" makes sense at, e.g., `s = −7`.
* Clarifications affecting this result: **C4** (naming of the completed spaces, indirectly),
  **O1** ("by" vs "before" `T`). C1/C2 reach it through Theorem 4.2.

---

## 2. Theorem 4.2 — `thm:Rinsert` (Whole-space local insertion), task **R42**

`04-whole-space.tex:31–43`. Merged number: Theorem 4.2. This is the engine of the whole section.

### 2(i). Statement

Let `ν, T > 0`. Let `a ∈ X_R` and `g ∈ F_R`, and let `(v,π,g)` be *the* (unique maximal)
solution with that data, assumed **regular through `T+δ` for some `δ > 0`** — i.e. `v` extends
smoothly to `[0, T+δ+δ']` for some `δ' > 0`; see risk note on **O2**. Fix any nonempty open ball
`B ⊂ R³`. Then there is `ε₀ > 0` such that for every `0 < ε < ε₀` there exist `g_ε ∈ F_R` and a
solution `u_ε` (the maximal solution for the data `(a, g_ε)`) with:

1. `T^ν_{max,R}(a,g_ε) = T` — the lifespan is **exactly** `T`;
2. `limsup_{t↑T} ‖u_ε(t)‖_{L^∞(R³)} = ∞`;
3. `u_ε(t) = v(t)` for all `0 ≤ t ≤ T − 2ε²` (same initial velocity `a`, same earlier history);
4. for every `t < T`, `supp(u_ε(t) − v(t)) ⊂ B`;
5. `g_ε − g ∈ C_c^∞(B × (0,∞))` — spatially supported in `B`, temporally compact in `(0,∞)`;
6. `‖u_ε − v‖_{E_T} ≤ (M + D) ε^{1/2} + C ε^{3/2}` (eq. `eq:REclose`), with `M, D` the packet
   constants of Lemma 2.2 and `C = C(v, B, T, δ, ν, θ, η)` independent of `ε`;
7. for `q ∈ {1,2}` and every `s < 2/q − 3/2`, `‖g_ε − g‖_{L^q(0,∞;H^s)} → 0` as `ε ↓ 0`;
8. **all of 1–7 hold for one and the same family** `{(u_ε, p_ε, g_ε)}_{0<ε<ε₀}`.

Quantitative content of 7 extracted from the proof (`04-whole-space.tex:55–78`), with
`β(q,s) = 2/q − 3/2 − s` and `g_ε − g = H_ε + F_ε`:
* `0 ≤ s ≤ 1` (eq. `eq:RpositiveScale`):
  `‖F_ε‖_{L^q_tH^s} ≤ C_{q,s}(ε^{2/q−3/2} + ε^{β(q,s)})`,
  `‖H_ε‖_{L^q_tH^s} ≤ C_{q,s}(ε^{2/q−1/2} + ε^{β(q,s)+1})`;
* `−3/2 < s < 0` (eq. `eq:RnegativeScale`):
  `‖F_ε‖_{L^q_tH^s} ≤ C_{q,s} ε^{β(q,s)}`, `‖H_ε‖_{L^q_tH^s} ≤ C_{q,s} ε^{β(q,s)+1}`;
* `q = 1`: convergence for `0 ≤ s < 1/2` from the first bullet, and for all `s < 0` from
  `‖z‖_{H^s} ≤ ‖z‖_2` plus the `s = 0` case;
* `q = 2`: convergence for `−3/2 < s < −1/2` from the second bullet, and for `s ≤ −3/2` by
  picking `r ∈ (−3/2,−1/2)` with `r > s` and using `‖z‖_{H^s} ≤ ‖z‖_{H^r}`.

Objects built in the proof that the statement does **not** expose but downstream results use:
`u_ε = v + w_ε + U_ε`, `p_ε = π + P_ε`, `g_ε = g + H_ε + F_ε`, where `U_ε,P_ε,F_ε` are the
parabolic rescalings `eq:scaling` of the packet placed at `x₀ ∈ B`, `t_ε = T − ε²`, `w_ε` is the
divergence-free cutoff of Lemma 3.4, and `H_ε` is the correction force of Lemma 3.5.

### 2(ii). D01 needs

* `⟪D01:X_R⟫`, `⟪D01:F_R⟫`, `⟪D01:Tmax⟫`, `⟪D01:RegularThrough⟫`, `⟪D01:normLqHs q s⟫`,
  `⟪D01:normET T⟫` — as in §1(ii).
* `⟪D01:IsClassicalSolution ν a f u p⟫` on an interval — `02-preliminaries.tex:28–36`:
  `u ∈ C([0,S];H^m)` for every integer `m ≥ 0` on each compact subinterval, `∇·u = 0`,
  momentum equation `eq:NS`, pressure gradient given by `eq:Rpressure`; scalar `p` free up to a
  function of time. **No** `p ∈ L²(R³)` requirement, and no compact support of `v`.
* `⟪D01:IsMaximalSolution⟫` and its lifespan (`prop:local` via A01/A02).
* `⟪D01:Leray⟫` (symbol `I − ξ⊗ξ/|ξ|²`, `02-preliminaries.tex:76–79`) and the pressure recovery
  `eq:Rpressure`, including the potential formula `p(x,t) = ∫₀¹ G(rx,t)·x dr` and the freedom to
  replace it by any gauge differing by a function of time.
* `⟪D01:normLinfty⟫` = `‖·‖_{L^∞(R³)}` and the embedding `‖z‖_∞ ≤ C‖z‖_{H²}` (`eq:Rproduct`,
  App. A — this is **A03**, see risk note).
* `⟪D01:normHs s⟫` with `‖z‖_{H^s} ≤ ‖z‖_2` for `s ≤ 0` and `‖z‖_{H^s} ≤ ‖z‖_{H^r}` for `s ≤ r`.
* `⟪D01:dotHsFinite s⟫` — the *plain Fourier-integral* homogeneous norm
  `(∫ |ξ|^{2s}|ẑ|²)^{1/2}` for smooth compactly supported `z` and `−3/2 < s < 0`, together with
  the two facts used at `04-whole-space.tex:70–72`: finiteness (split at `|ξ|=1`, using
  `|ẑ| ≤ C‖z‖₁` on `|ξ|<1` and `∫_{|ξ|<1}|ξ|^{2s} < ∞`), and `(1+|ξ|²)^s ≤ |ξ|^{2s}` for `s<0`,
  giving `‖z‖_{H^s} ≤ ‖z‖_{Ḣ^s}`. Uniformity over the rescaled profile family is required.
* `⟪D01:Cc_infty⟫` on `R³ × (0,∞)` and the fact that `F_R + C_c^∞(R³×(0,∞)) ⊆ F_R`.
* `⟪I01:packetU⟫`, `⟪I01:packetP⟫`, `⟪I01:packetF⟫`, `⟪I01:packetM⟫ = M`, `⟪I01:packetD⟫ = D`,
  the compact support set `K`, and the zero extension of `U,P,F` to nonpositive source times
  (**C1**).
* Ball geometry: `⟪D01:openBall x r⟫`, `x₀ ∈ B`, `R_* = sup_{y∈K_*}|y|`, and the smallness
  requirements `2ε² < min(T,δ)`, `ε R_* < dist(x₀, ∂B)` (**C2**).

### 2(iii). DAG children and the exact shape consumed

`R42 ← I03, A02`.

* **From I03 (same-family scaling and negative norms; itself `← I02 ← I01, D01`)**:
  1. the scaled fields `eq:scaling`
     `U_ε(x,t) = ε^{-1}U((x−x₀)/ε,(t−t_ε)/ε²)`, `P_ε = ε^{-2}P(…)`, `F_ε = ε^{-3}F(…)`
     solve the momentum equation at the same viscosity `ν` on `R³`, are divergence free, vanish
     for `t ≤ t_ε` in a neighbourhood of the initial time, and satisfy
     `‖U_ε(t)‖_∞ = ε^{-1}‖U((t−t_ε)/ε²)‖_∞ → ∞` as `t ↑ T`;
  2. `eq:packetEscale`: `‖U_ε‖_{L^∞(0,T;L²)} = ε^{1/2}M`, `‖∇U_ε‖_{L²(0,T;L²)} = ε^{1/2}D`;
  3. `eq:packetFscale`: `‖F_ε‖_{L^q_tL^p_x} = ε^{α(p,q)}‖F‖_{L^q_tL^p_x}`,
     `α(p,q) = −3 + 3/p + 2/q`;
  4. the Sobolev scaling bounds `eq:RpositiveScale`/`eq:RnegativeScale` above, uniform over the
     rescaled profile family, **for one common `ε`-family**;
  5. from I02 (Lem. 3.4/3.5, Euclidean content only, no periodization): `w_ε` smooth,
     divergence free, supported in `B` and in `(T−2ε², T+2ε²)`; `v + w_ε = 0` on an open
     neighbourhood of `supp U_ε(t)` during the active interval (`eq:bgzero`); `H_ε` as in
     `eq:H`, smooth across `T`, spacetime compact, `|∂_x^β H_ε| ≤ C_β ε^{-2-|β|}`,
     `‖w_ε‖_{E_T} ≤ Cε^{3/2}`, `‖H_ε‖_{L^q_tL^p_x} ≤ C_{p,q}ε^{α(p,q)+1}`.
* **From A02 (uniqueness and maximal solution identification; `← A01`)**:
  1. the constructed `u_ε` coincides with the unique maximal solution for `(a,g_ε)` on every
     `[0,T']`, `T' < T` — so the lifespan is `≥ T`;
  2. a smooth extension past `T` would be bounded in `C_t H²` near `T`; with
     `‖·‖_∞ ≤ C‖·‖_{H²}` (**A03**, missing DAG edge) this contradicts 2 above, so the lifespan
     is `≤ T`. Combined: `T^ν_{max,R}(a,g_ε) = T`.

### 2(iv). Proposed contract skeleton

```lean
structure RInsertAPI where
  ν T δ : ℝ
  hν : 0 < ν
  hT : 0 < T
  hδ : 0 < δ
  a : ⟪D01:VectorField⟫
  g : ⟪D01:ForceField⟫
  ha : a ∈ ⟪D01:X_R⟫
  hg : g ∈ ⟪D01:F_R⟫
  v : ℝ → ⟪D01:VectorField⟫
  π : ℝ → ⟪D01:Scalar⟫
  reference : ⟪D01:IsClassicalSolution⟫ ν a g v π (Set.Icc 0 (T + δ))
  B : ⟪D01:Ball⟫
  hB : ⟪D01:Nonempty⟫ B
  -- the single ε-family
  ε₀ : ℝ
  hε₀ : 0 < ε₀
  gPert : ℝ → ⟪D01:ForceField⟫                    -- ε ↦ g_ε
  uPert : ℝ → ℝ → ⟪D01:VectorField⟫               -- ε ↦ t ↦ u_ε(t)
  pPert : ℝ → ℝ → ⟪D01:Scalar⟫                    -- ε ↦ t ↦ p_ε(t)
  -- conclusions, all for the same family
  memF   : ∀ ε, 0 < ε → ε < ε₀ → gPert ε ∈ ⟪D01:F_R⟫
  isSol  : ∀ ε, 0 < ε → ε < ε₀ →
             ⟪D01:IsMaximalSolution⟫ ν a (gPert ε) (uPert ε) (pPert ε)
  lifespan : ∀ ε, 0 < ε → ε < ε₀ → ⟪D01:Tmax⟫ ν a (gPert ε) = T
  blowup : ∀ ε, 0 < ε → ε < ε₀ →
             ¬ ⟪D01:BoundedNear⟫ (fun t => ⟪D01:normLinfty⟫ (uPert ε t)) T
  history : ∀ ε, 0 < ε → ε < ε₀ → ∀ t, 0 ≤ t → t ≤ T - 2*ε^2 → uPert ε t = v t
  velSupport : ∀ ε, 0 < ε → ε < ε₀ → ∀ t, t < T →
             ⟪D01:support⟫ (uPert ε t - v t) ⊆ B
  velDivFree : ∀ ε, 0 < ε → ε < ε₀ → ∀ t, t < T →
             ⟪D01:divFree⟫ (uPert ε t - v t)                 -- used by R47
  forceDiff : ∀ ε, 0 < ε → ε < ε₀ →
             gPert ε - g ∈ ⟪D01:Cc_infty⟫ B (Set.Ioi 0)
  pressureCompact : ∀ ε, 0 < ε → ε < ε₀ → ∀ t, t < T →
             ⟪D01:support⟫ (pPert ε t - π t) ⊆ B             -- used by R47
  energyRate : ∀ ε, 0 < ε → ε < ε₀ →
             ⟪D01:normET⟫ T (uPert ε - v)
               ≤ (⟪I01:packetM⟫ + ⟪I01:packetD⟫) * ε^(1/2 : ℝ) + Cconst * ε^(3/2 : ℝ)
  Cconst : ℝ
  forceConvergence : ∀ q, (q = 1 ∨ q = 2) → ∀ s : ℝ, s < 2/q - 3/2 →
             ⟪D01:TendsToZero⟫ (fun ε => ⟪D01:normLqHs⟫ q s (gPert ε - g))
```

`velDivFree` and `pressureCompact` are not displayed in the paper's Theorem 4.2 but are proved
inside its proof and are consumed by Theorem 4.7; exposing them here avoids a re-proof.

### 2(v). Risk notes

* **"regular through `T+δ` for some `δ>0`" (O2).** `RegularThrough ν a g T` already means
  "extends smoothly to `[0,T+δ]` for some `δ>0`". The theorem's phrasing therefore nests the
  margin. It is harmless (shrink `δ`) but a literal Lean transcription would demand a solution on
  `[0, T + δ + δ']`. Recommendation: state the hypothesis as
  `∃ δ > 0, IsClassicalSolution … (Icc 0 (T+δ))` and record the deviation.
* **"the solution for `a` and `g`".** The definite article presupposes uniqueness (A02) and that
  `T^ν_{max,R}(a,g) > T + δ`. Both should be explicit hypotheses.
* **C1 (source-force zero extension).** `F_ε(x,t)` evaluates `F` at negative source times for
  `0 < t < t_ε`. The repair (zero extension, smooth because `supp_t F ⋐ (0,∞)`) is already in the
  torus text at `03-torus.tex:108–111` and must be part of `⟪I01:packetF⟫`.
* **C2 (choice of scaling center).** `x₀` must be chosen **inside `B`** and `ε R_* < dist(x₀,∂B)`;
  an arbitrary center does not give `x₀ + εK_* ⊂ B`.
* **Force support after `T`.** The proof states explicitly "Each rescaled force has time support
  of length `O(ε²)`, including any part after `T`." So `g_ε ≠ g` on a small interval **after**
  `T`, even though `u_ε` only exists on `[0,T)`. This is the technical root of **C3** and must not
  be quietly dropped.
* **Missing DAG edge to A03.** The lifespan-`≤ T` argument uses `‖z‖_∞ ≤ C‖z‖_{H²}` from
  Lemma A.1, whose task is **A03** (`← D01, U04, A05`). `A03` is not an ancestor of `R42` in
  `DEPENDENCY_GRAPH.md` (`R42 ← I03, A02`). Either add `A03 → R42`, or have `A02` export a
  ready-made `L^∞`-blowup continuation criterion.
* **Pressure gauge.** The proof chooses the *compact* representative `P_ε`, which is generally
  **not** the gauge produced by the potential formula `p = ∫₀¹ G(rx)·x dr`. The contract must
  carry the gauge choice explicitly; Theorem 4.7 depends on it.
* **Constant bookkeeping.** `M, D` are packet constants (universal once `(U,P,F)` is fixed);
  `C` in `eq:REclose` depends on `v` near `(x₀, T)`, on `B`, on the cutoffs `θ, η`, and on `ν`,
  but not on `ε`. Conflating them would make the estimate false as `B` shrinks.
* **`ε₀` is not explicit.** The paper says "for all sufficiently small `ε`". The constraints
  visible in the sources are `2ε² < min(T,δ)`, `x₀ + εK_* ⊂ B`, `εR_* < dist(x₀,∂B)`, the scaled
  `supp θ` strictly inside the coordinate ball, and `ε ≤ 1` (used to absorb lower-order terms).
  A Lean statement should either produce `ε₀` or take these as explicit side conditions.
* **`E_T` is a norm on `(0,T)` only**; `u_ε` is undefined at `t = T`. `eq:Enorm` "imposes no
  endpoint value at `T`" (`01-introduction.tex:151`).
* Clarifications affecting this result: **C1**, **C2**, **O2**; **C3** originates here.

---

## 3. Proposition 4.3 — `prop:Rcritical1` (Global regularity for small critical data and `L¹` force), task **R43**

`04-whole-space.tex:82–89`. Merged number: Proposition 4.3.

### 3(i). Statement

There is a **universal** constant `c > 0` (independent of `ν`, `a`, `f`) such that for every
`ν > 0`, every `a ∈ X_R` and every `f ∈ F_R`,

    ‖a‖_{Ḣ^{1/2}(R³)} + ‖f‖_{L^1(0,∞;Ḣ^{1/2}(R³))} < c ν   ⟹   T^ν_{max,R}(a,f) = ∞.

In particular, for `a = 0`, every `f ∈ F_R` with `‖f‖_{L^1(0,∞;H^{1/2})} < cν` is a globally
regular input (using `‖f‖_{Ḣ^{1/2}} ≤ ‖f‖_{H^{1/2}}`).

Quantifier order in the paper: `∃ c > 0 ∀ ν > 0 ∀ a ∈ X_R ∀ f ∈ F_R (smallness ⟹ T_max = ∞)`.
`a` is quantified (not fixed, not zero). Time domain of the force norm is `(0,∞)`. Conclusion is
**global** regularity, not regularity up to a horizon.

Proof quantities (needed if the statement is decomposed): `Λ = (−Δ)^{1/2}`,
`y(t) = ‖Λ^{1/2}u(t)‖₂`, `z(t) = ‖Λ^{3/2}u(t)‖₂`, `b(t) = ‖f(t)‖_{Ḣ^{1/2}}`, and

* `eq:Rcritical1`: `½(y²)' + (ν − C₀y) z² ≤ b y`;
* on `{y ≤ ν/(2C₀)}`, regularising by `(y²+ζ²)^{1/2}` and `ζ↓0` gives `y(t) ≤ y(0) + ∫₀^t b`;
* `c < 1/(4C₀)` makes the bound propagate through the whole lifespan by continuity, including at
  times where `y = 0`;
* `eq:RH1`: after decreasing `c` so that `C₁ y ≤ ν/4`,
  `(‖∇u‖₂²)' + ν‖Δu‖₂² ≤ Cν^{-1}‖f‖₂²`;
* `eq:RL2`: `‖u(t)‖₂ ≤ ‖a‖₂ + ∫₀^t ‖f(s)‖₂ ds =: K(t)`;
* combining, for every finite `S ≤ T_max`,
  `∫₀^S ‖u‖²_{H²} ≤ C S K(S)² + Cν^{-1}‖∇a‖₂² + Cν^{-2}∫₀^S‖f‖₂² < ∞`, and `prop:local`
  excludes a finite maximal lifespan.

### 3(ii). D01 needs

* `⟪D01:X_R⟫`, `⟪D01:F_R⟫`, `⟪D01:Tmax⟫` as above.
* `⟪D01:dotHs (1/2)⟫` and `⟪D01:dotHs (3/2)⟫` — the **Appendix B Euclidean homogeneous
  realization** (`appendix-b-embeddings.tex:41–72`): completion of
  `{v : v̂ ∈ C_c^∞(R³∖{0})}` in `‖Λ^a v‖₂`, realized by `v̂ = |ξ|^{-a}G`, `G ∈ L²`, valid for
  `0 < a < 3/2`. Applied only to smooth `H^∞` fields, for which the norm is the plain Fourier
  integral. `‖a‖_{Ḣ^{1/2}} ≤ ‖a‖_{H^{1/2}} < ∞` for `a ∈ X_R`.
* `⟪D01:Lambda⟫ = (−Δ)^{1/2}`, symbol `|ξ|` (`02-preliminaries.tex:51`, App. B header).
* `⟪D01:normLqDotHs 1 (1/2)⟫` = `‖·‖_{L^1(0,∞;Ḣ^{1/2})}`, and the inhomogeneous
  `‖·‖_{L^1(0,∞;H^{1/2})}` with `‖z‖_{Ḣ^{1/2}} ≤ ‖z‖_{H^{1/2}}`.
* `⟪D01:normLp p⟫` for `p ∈ {2,3,6}`; `⟪D01:normHs 2⟫`; the Fourier inequality
  `‖u‖²_{H²} ≤ C(‖u‖²₂ + ‖Δu‖²₂)` and Plancherel `‖D²u‖₂ = ‖Δu‖₂`.
* `⟪D01:Leray⟫` and the projected equation `eq:projected` (the estimates test the *projected*
  equation against `Λu` and `−Δu`).
* `⟪D01:pairing⟫` `⟨·,·⟩` on `L²(R³;R³)`.
* Universal-constant discipline: `c`, `C₀`, `C₁` must be `ν`-free; the smallness threshold is
  `cν`, so a Lean `c : ℝ` outside the `∀ ν` binder.

### 3(iii). DAG children and the exact shape consumed

`R43 ← A04, A05, C01`.

* **From A05 (critical embeddings for the actual whole-space fields)**, exactly Lemma B.1's
  derived clauses `eq:critical-derived` applied to the real vector field `u(t) ∈ H^∞`:
  `‖u‖₃ ≤ C‖u‖_{Ḣ^{1/2}} = C y`, `‖∇u‖₃ + ‖Λu‖₃ ≤ C‖u‖_{Ḣ^{3/2}} = C z`,
  and `‖∇u‖₆ ≤ C‖Δu‖₂`. All three with constants independent of the field and of `ν`.
* **From C01 (ordinary energy and `H¹` absorption)**:
  1. the `L²` estimate `eq:RL2` with regularised norm division;
  2. the `H¹` absorption `eq:RH1` valid once `C₁‖u‖₃ ≤ ν/4`;
  3. the assembly `∫₀^S ‖u‖²_{H²} < ∞` from 1, 2 and the `H²` Fourier inequality.
* **From A04 (squared-`H²` continuation adapter)**: given `∫₀^S ‖u‖²_{H²} dt < ∞` at a finite
  candidate endpoint `S`, the solution extends smoothly beyond `S`; hence no finite maximal
  lifespan. This is exactly `prop:local`'s continuation clause `eq:criterion`.

### 3(iv). Proposed contract skeleton

```lean
structure RCritical1API where
  c : ℝ
  hc : 0 < c
  universal :                                        -- c is quantified outside ν, a, f
    ∀ ν : ℝ, 0 < ν →
      ∀ a, a ∈ ⟪D01:X_R⟫ →
      ∀ f, f ∈ ⟪D01:F_R⟫ →
        ⟪D01:normDotHs⟫ (1/2) a
          + ⟪D01:normLqDotHs⟫ 1 (1/2) f < c * ν →
        ⟪D01:Tmax⟫ ν a f = ⊤
  inhomogeneousAtZero :                              -- the "in particular" clause
    ∀ ν : ℝ, 0 < ν →
      ∀ f, f ∈ ⟪D01:F_R⟫ →
        ⟪D01:normLqHs⟫ 1 (1/2) f < c * ν →
        ⟪D01:Tmax⟫ ν 0 f = ⊤
```

`inhomogeneousAtZero` must use the **same** `c`; it is the field consumed by `RMainAPI.nonDensityZero`
at `q = 1`.

### 3(v). Risk notes

* **Which homogeneous realization.** `Ḣ^{1/2}` and `Ḣ^{3/2}` here are the Appendix B completion,
  a *different* object from the `Ḣ^{-1}` of `eq:homogeneous-realization` used in Prop. 4.6, and
  from the "finite Fourier integral" usage at negative orders in Thm 4.2's proof. Three
  realizations coexist in Section 4 — see §8.4. `Ḣ^{3/2}` sits at the endpoint `a = 3/2` of the
  Appendix B range and appears only as the *quantity* `‖Λ^{3/2}u‖₂` for smooth fields, never as a
  completion; do not build a `Ḣ^{3/2}` space.
* **Universality of `c`.** Two separate shrinkings occur (`c < 1/(4C₀)`, then `C₁y ≤ ν/4`). Both
  are `ν`-free because `y ≤ cν`. A formalisation that lets `c` depend on `ν` still yields a true
  statement but breaks the `cν`-ball scaling used in Theorem 4.1's converse.
* **Regularised norm division.** The paper's `(y²+ζ²)^{1/2}, ζ↓0` device appears three times
  (`lem:packetenergy`, `eq:RL2`, and here) and again in Appendix A `eq:highcontinuation`. It
  should be one reusable lemma, not four ad hoc arguments. It is what licenses differentiating
  at times where `y = 0` — the paper flags this explicitly.
* **Continuity bootstrap.** "Choosing `c < 1/(4C₀)` gives the bound throughout the lifespan by
  continuity" is a deferred open/closed argument on `{t : y(t) ≤ ν/(2C₀)}`; the paper does not
  spell it out. Lean will need the standard "first exit time" lemma.
* **`a` general, not zero.** Unlike 4.4, this proposition allows a nonzero small critical initial
  velocity. Theorem 4.1 only uses `a = 0`, but the general statement is what the contract must
  carry.
* **`prop:local` is invoked at every finite `S`**, including `S` "within or at the maximal
  lifespan"; the phrase "at the maximal lifespan" only makes sense when `T_max < ∞`, which is the
  case being excluded. Make the contrapositive structure explicit.
* Clarifications affecting this result: none of C1–C6 directly. (C4 touches its use inside 4.6.)

---

## 4. Proposition 4.4 — `prop:Rcritical2` (Regularity on a prescribed finite interval), task **R44**

`04-whole-space.tex:136–144`. Merged number: Proposition 4.4.

### 4(i). Statement

For each `ν > 0` and each `S > 0` there is `r_{ν,S} > 0` such that

    f ∈ F_R,   ‖f‖_{L²(0,∞;H^{-1/2}(R³))} < r_{ν,S}   ⟹   T^ν_{max,R}(0,f) > S.

One may take `r_{ν,S} = c ν^{3/2} e^{−C ν S}` for suitable **universal** positive constants
`c, C`.

Quantifier order: `∃ c,C > 0 ∀ ν,S > 0 ∀ f ∈ F_R (‖f‖ < cν^{3/2}e^{−CνS} ⟹ T_max(0,f) > S)`.
Initial velocity is **exactly zero**. The norm is **inhomogeneous** `H^{-1/2}`; the paper states
explicitly why: "smallness in `H^{-1/2}` does not control the homogeneous negative norm at low
frequencies". Conclusion is a strict inequality `> S`, over the horizon `S`, not global.

Proof quantities: `J = (I−Δ)^{1/2}`, `Y = ‖u‖_{H^{1/2}}`, `Z = ‖∇u‖_{H^{1/2}}`,
`B = ‖f‖_{H^{-1/2}}`, the Fourier identity `‖u‖²_{H^{3/2}} = Y² + Z²`, and
`eq:Rcritical2`: while `Y ≤ θν` for a universal `θ > 0`,
`(Y²)' + νZ² ≤ C₂νY² + C₃ν^{-1}B²`, whence by Grönwall from `Y(0) = 0`,
`Y(t)² ≤ C₃ν^{-1}e^{C₂νS}‖f‖²_{L²_tH^{-1/2}}` for `t ≤ S` while `Y ≤ θν`; choose `r_{ν,S}` so
that this is `< θ²ν²/4`, and a first crossing `Y = θν` is contradicted.
The continuation half then reuses `eq:RH1` (via `‖u‖₃ ≤ CY ≤ Cθν`), `eq:RL2`, and the closing
calculation of Prop. 4.3, using that `f ∈ F_R` has **finite** (not small) `L^1_tL²_x` and
`L²_tL²_x` norms.

### 4(ii). D01 needs

* `⟪D01:F_R⟫`, `⟪D01:Tmax⟫`, `⟪D01:normLqHs 2 (−1/2)⟫`.
* `⟪D01:J⟫ = (I−Δ)^{1/2}`, symbol `(1+|ξ|²)^{1/2}` (`02-preliminaries.tex:51`).
* `⟪D01:normHs s⟫` at `s ∈ {−1/2, 1/2, 3/2}` and the exact Fourier identity
  `‖u‖²_{H^{3/2}} = ‖u‖²_{H^{1/2}} + ‖∇u‖²_{H^{1/2}}` (this is a weight identity
  `(1+|ξ|²)^{3/2} = (1+|ξ|²)^{1/2} + |ξ|²(1+|ξ|²)^{1/2}`; it is exact, not up to constants).
* Duality/Fourier Cauchy–Schwarz: `|⟨f, Ju⟩| ≤ ‖f‖_{H^{-1/2}} ‖u‖_{H^{3/2}}`.
* `⟪D01:normLp 3⟫`, the `L²` and `L^1` in-time norms of `f`, and `⟪D01:normHs 2⟫`.
* `⟪D01:Leray⟫`, projected equation, `⟪D01:pairing⟫`.
* Universal constants `θ, C₀, C₂, C₃, c, C` all `ν`- and `S`-free.

### 4(iii). DAG children and the exact shape consumed

`R44 ← A04, A05, C01`. Same three children as R43, different instantiation.

* **From A05**: `‖u‖₃ ≤ C‖u‖_{Ḣ^{1/2}} ≤ C‖u‖_{H^{1/2}} = CY` and
  `‖∇u‖₃ ≤ C‖∇u‖_{Ḣ^{1/2}} ≤ CZ`, and `‖Ju‖₃ ≤ C(Y²+Z²)^{1/2}`; also `‖∇u‖₆ ≤ C‖Δu‖₂` for the
  reused `eq:RH1`. Note these are used with the **inhomogeneous** `Y,Z`, so A05 must also supply
  the homogeneous-to-inhomogeneous comparison `‖z‖_{Ḣ^{a}} ≤ ‖z‖_{H^{a}}` at `a ∈ {1/2, 1}`.
* **From C01**: `eq:RH1` (`H¹` absorption once `‖u‖₃ ≤ ν/(4C₁)`), `eq:RL2` (`L²` bound), and the
  `∫₀^S ‖u‖²_{H²} < ∞` assembly — here with `a = 0`, so `K(S) = ∫₀^S ‖f‖₂` and `‖∇a‖₂ = 0`.
* **From A04**: the same continuation adapter, used to exclude a maximal lifespan **at or before
  `S`** (not to prove globality).

### 4(iv). Proposed contract skeleton

```lean
structure RCritical2API where
  c C : ℝ
  hc : 0 < c
  hC : 0 < C
  radius : ℝ → ℝ → ℝ
  radiusFormula : ∀ ν S : ℝ, radius ν S = c * ν^(3/2 : ℝ) * Real.exp (-(C * ν * S))
  radiusPos : ∀ ν S : ℝ, 0 < ν → 0 < S → 0 < radius ν S
  main :
    ∀ ν S : ℝ, 0 < ν → 0 < S →
      ∀ f, f ∈ ⟪D01:F_R⟫ →
        ⟪D01:normLqHs⟫ 2 (-1/2) f < radius ν S →
        S < ⟪D01:Tmax⟫ ν 0 f
```

Keeping `radius` as a field (rather than inlining the formula) lets `RMainAPI.nonDensityZero`
consume `radius ν T` without re-deriving `c, C`.

### 4(v). Risk notes

* **`a = 0` is essential.** Grönwall starts from `Y(0) = 0`. A general `a` version would carry a
  `Y(0)²e^{C₂νS}` term and the radius would depend on `a`. Do not generalise.
* **`f ∈ F_R` is load-bearing beyond the smallness.** The continuation step uses that
  `‖f‖_{L^1_tL²_x}` and `‖f‖_{L²_tL²_x}` are finite ("even though they are not required to be
  small"). So the conclusion is **not** uniform over the `H^{-1/2}` ball of an abstract space: it
  is a statement about the smooth class only. This is exactly why Theorem 4.1's converse gives a
  *relative* open ball, and it is a place where a careless "open ball in `L²_tH^{-1/2}`"
  formalisation would be wrong.
* **Inhomogeneous vs homogeneous at `−1/2`.** The paper flags that the inhomogeneous norm is
  essential. Formalising the hypothesis with `Ḣ^{-1/2}` would make the statement false as proved.
* **Radius is not monotone-free in `T`.** `r_{ν,S}` decreases exponentially in `νS`; the
  non-density ball in Theorem 4.1 therefore shrinks as `T` grows. The paper's sentence at
  `04-whole-space.tex:16` records this. It does **not** damage the "iff", since `T` is fixed
  first.
* **Deferred detail.** "For instance absorb the `C₀YZ²` and `BZ` terms into dissipation, use
  `C₀Y³ ≤ C₀θνY²`, and bound `BY` by a multiple of `νY² + ν^{-1}B²`" is an outline, not a
  derivation; the exact `C₂, C₃` are not pinned. Also "Take `θ` smaller if necessary" happens
  twice (once for `eq:Rcritical2`, once for the `H¹` absorption) — one final `θ` must serve both.
* **First-crossing argument.** "The first possible time with `Y = θν` would contradict this
  bound" is again an implicit continuity/first-exit-time argument on `[0, min(S, T_max))`.
* Clarifications affecting this result: none of C1–C6 directly.

---

## 5. Corollary 4.5 — `cor:Rclasses` (Same thresholds for compact and rapidly decaying forces), task **R45**

`04-whole-space.tex:194–196`, with the two subclasses defined at `04-whole-space.tex:182–192`.
Merged number: Corollary 4.5.

### 5(i). Statement

Define

    F_c  = C_c^∞(R³ × (0,∞); R³),
    F_rd = { f ∈ C^∞(R³ × [0,∞); R³) :
               sup_{x∈R³, t≥0} (1+|x|+t)^N |∂_x^α ∂_t^j f(x,t)| < ∞  for all N, α, j },
    S_σ  = S(R³;R³) ∩ L²_σ.

Then Theorem 4.1 remains valid verbatim with `F_R` replaced by `F_c`, and with `F_R` replaced by
`F_rd`. That is, for `ν,T > 0`, `q ∈ {1,2}`, `s_q = 2/q − 3/2`, and `Y ∈ {F_c, F_rd}` with the
relative `L^q(0,∞;H^s)` topology on `Y`:
(i) for every fixed `a ∈ X_R`, `{f ∈ Y : T^ν_{max,R}(a,f) ≤ T}` is dense in `Y` when `s < s_q`;
(ii) at `a = 0`, that set is dense in `Y` if and only if `s < s_q`.
In particular the statement holds for every fixed `a ∈ S_σ` in the rapid-decay formulation, with
the complete "if and only if" classification at `a = 0`.

The paper adds explicitly: no uniform common numerical bound on the `F_rd` seminorms is imposed,
and nothing requires the reference velocity or its pressure to be spatially compact.

### 5(ii). D01 needs

* `⟪D01:F_c⟫`, `⟪D01:F_rd⟫`, `⟪D01:S_sigma⟫` as displayed above, with the inclusions
  `F_c ⊆ F_rd ⊆ F_R` and `S_σ ⊆ X_R`. The middle inclusion is asserted, not proved, in the paper:
  it needs (a) polynomial decay `⟹ ‖f(t)‖_{H^m} ≤ C_{m,N}(1+t)^{-N}`, hence finite `L^1_t` and
  `L^2_t` norms, and (b) `f ∈ C^∞([0,∞);H^m)` — i.e. that the pointwise mixed-derivative decay
  upgrades to time-smoothness *into each* `H^m`, with one-sided derivatives at `t=0`.
* Closure properties: `F_c + C_c^∞(R³×(0,∞)) ⊆ F_c` and `F_rd + C_c^∞(R³×(0,∞)) ⊆ F_rd`
  (the latter needs every rapid-decay seminorm to stay finite after adding a compact function).
* `0 ∈ F_c`, `0 ∈ F_rd` (nonemptiness of the relative critical balls).
* Everything from §1(ii).

### 5(iii). DAG children and the exact shape consumed

`R45 ← R41` per `DEPENDENCY_GRAPH.md`. The proof at `04-whole-space.tex:197–199` in fact consumes
four separate things:

* **From R41D / R42 (density half)**: the *approximant produced by the insertion is
  `g + (H_ε + F_ε)` with `H_ε + F_ε ∈ C_c^∞(B×(0,∞))`*, so if `g ∈ Y` then `g_ε ∈ Y`. This is
  Theorem 4.2 conclusion 5, **not** visible in Theorem 4.1's statement. See risk note.
* **From R41D (case split)**: the two-case argument, applied with the reference `g` ranging over
  `Y` rather than `F_R`; case 1 (`T_max(a,g) ≤ T`) returns `g ∈ Y` unchanged.
* **From R43, R44 via R41 (converse half)**: the critical balls
  `{‖f‖_{L^1_tH^{1/2}} < cν}` and `{‖f‖_{L^2_tH^{-1/2}} < r_{ν,T}}`, intersected with `Y`, are
  nonempty relative open balls (they contain `0 ∈ Y`) consisting of inputs with
  `T^ν_{max,R}(0,f) > T`.
* **From D01 / A01**: the local framework only requires `a ∈ X_R`, so it applies to `a ∈ S_σ`.

### 5(iv). Proposed contract skeleton

```lean
structure RClassesAPI where
  base : RMainAPI
  subclassInclusion : ⟪D01:F_c⟫ ⊆ ⟪D01:F_rd⟫ ∧ ⟪D01:F_rd⟫ ⊆ ⟪D01:F_R⟫
  compactPerturbationStable :
    ∀ Y, (Y = ⟪D01:F_c⟫ ∨ Y = ⟪D01:F_rd⟫) →
      ∀ f h, f ∈ Y → h ∈ ⟪D01:Cc_infty_all⟫ → f + h ∈ Y
  zeroMem : ∀ Y, (Y = ⟪D01:F_c⟫ ∨ Y = ⟪D01:F_rd⟫) → (0 : ⟪D01:ForceField⟫) ∈ Y
  densityFixedInitial :
    ∀ Y, (Y = ⟪D01:F_c⟫ ∨ Y = ⟪D01:F_rd⟫) →
      ∀ a, a ∈ ⟪D01:X_R⟫ → ∀ s : ℝ, s < base.thresholds.exponent base.q 0 →
        ∀ g, g ∈ Y → ∀ ρ : ℝ, 0 < ρ →
          ∃ f, f ∈ Y ∧ ⟪D01:Tmax⟫ base.ν a f ≤ base.T ∧
               ⟪D01:normLqHs⟫ base.q s (f - g) < ρ
  nonDensityZero :
    ∀ Y, (Y = ⟪D01:F_c⟫ ∨ Y = ⟪D01:F_rd⟫) →
      ∀ s : ℝ, base.thresholds.exponent base.q 0 ≤ s →
        ∃ ρ : ℝ, 0 < ρ ∧
          ∀ f, f ∈ Y → ⟪D01:Tmax⟫ base.ν 0 f ≤ base.T →
            ρ ≤ ⟪D01:normLqHs⟫ base.q s f          -- the excluded ball is centred at 0 ∈ Y
  schwartzInitial : ⟪D01:S_sigma⟫ ⊆ ⟪D01:X_R⟫
```

### 5(v). Risk notes

* **Missing DAG edge `R42 → R45`.** The corollary's density half needs the *compact support of
  the force difference*, a Theorem 4.2 conclusion that Theorem 4.1's statement does not carry.
  With `R45 ← R41` alone, the contract cannot be discharged. Either add `R42 → R45`, or make
  `R41D` export a "class-preserving" density statement parameterised by the admissible subclass.
* **`F_rd ⊆ F_R` is an unproved assertion.** The paper never checks that rapid-decay forces are
  `C^∞([0,∞);H^∞)` with finite `L^1_t`/`L^2_t` `H^m` norms; it is routine but must be in D01's
  obligations. Note `F_rd` allows `f(·,0) ≠ 0` (unlike the periodic class).
* **`F_c ⊆ F_rd` needs the zero extension to `t = 0`.** An `f ∈ C_c^∞(R³×(0,∞))` extends smoothly
  by zero to `t = 0` precisely because its time support is compact in the *open* half-line.
* **Ambiguity: "Theorem 4.1 remains valid".** The relative topology changes with the ambient
  class. Formalise as a statement about each `Y` separately with its own relative topology, not
  as a statement about the same topology restricted.
* **`a ∈ S_σ` is a further restriction on `a`, independent of the force class.** The "in
  particular" sentence pairs `F_rd` with `S_σ`, but the corollary does not require `a ∈ S_σ` for
  the `F_rd` case; `a ∈ X_R` suffices. Do not fuse the two restrictions.
* **Deferred detail: "Each critical regular ball contains zero and remains a nonempty relative
  open ball in that subclass."** Nonemptiness is by `0`; relative openness is by definition of the
  subspace topology. Both trivial but must be stated.
* Clarifications affecting this result: **C4** (relative vs completed, since 4.6 immediately
  follows and uses `F_c` in a *completed* sense).

---

## 6. Proposition 4.6 — `prop:Renergy` (Density in completed force spaces and strong trajectory closure), task **R46**

`04-whole-space.tex:218–229`, with the preparatory paragraph at `04-whole-space.tex:201–216`.
Merged number: Proposition 4.6.

### 6(i). Statement

Fix `a ∈ X_R` and `ν, T > 0`. Two assertions.

**(A) Density in complete spaces.** The set
`Sing_c(a) := { f ∈ F_c : T^ν_{max,R}(a,f) ≤ T }` of smooth compact forces producing breakdown by
`T` is dense in each **full Bochner space** `L^q(0,∞;H^s(R³))` for `q ∈ {1,2}` and `s < s_q`, and
also dense in `L²(0,∞; Ḣ^{-1}(R³))`. Here the ambient space is the complete space itself, not a
relative topology on a smooth class; `Sing_c(a)` is a subset of each of these spaces.

**(B) Strong trajectory closure, same family.** For every reference `(v,π,g)` as in Theorem 4.2
(i.e. `a ∈ X_R`, `g ∈ F_R`, regular through `T+δ`, any nonempty open ball `B`), the inserted
family of Theorem 4.2 can be chosen so that **simultaneously**, as `ε ↓ 0`,

    ‖u_ε − v‖_{E_T} → 0,
    ‖g_ε − g‖_{L^1(0,∞;L²)} + ‖g_ε − g‖_{L²(0,∞;H^{-1})} + ‖g_ε − g‖_{L²(0,∞;Ḣ^{-1})} → 0.

The homogeneous norm is a norm of the **compact difference** only; `g` itself need not lie in
`L²(0,∞;Ḣ^{-1})`.

Rates recoverable from the proof: `‖F_ε‖_{L²_tḢ^{-1}} ≤ Cε^{1/2}`,
`‖H_ε‖_{L²_tḢ^{-1}} ≤ Cε^{3/2}`; and by `β(1,0) = 1/2`, `β(2,−1) = 1/2` the two inhomogeneous
rates are also `ε^{1/2}` and `ε^{3/2}`. (These are exactly `ThresholdAPI.energy`:
`exponent 1 0 = 1/2 ∧ exponent 2 (-1) = 1/2`.)

Context that constrains the formalisation (`04-whole-space.tex:201–216`): with
`V = H¹(R³;R³) ∩ L²_σ`, a finite-energy velocity lies in `L^∞_tL²_σ ∩ L²_tV`; a full `H^{-1}`
distribution restricts to an element of `V'`, recording only its action on divergence-free tests;
the chosen `Ḣ^{-1}` realization gives `|⟨h,z⟩| ≤ ‖h‖_{Ḣ^{-1}}‖∇z‖₂` and
`|∫₀^T ⟨f,u⟩ dt| ≤ ‖f‖_{L²_tḢ^{-1}}‖∇u‖_{L²_{t,x}}`, first for Schwartz functions and then by
completion. Inhomogeneous `H^{-1}` pairs with `H¹`; `L^1_tL²_x` pairs with `L^∞_tL²_x`.

### 6(ii). D01 needs

* `⟪D01:F_c⟫`, `⟪D01:X_R⟫`, `⟪D01:Tmax⟫`, `⟪D01:normET T⟫`.
* `⟪D01:Hs s⟫` for arbitrary real `s`, as a **separable Hilbert space**, with the isometry
  `h ↦ ⟨ξ⟩^s ĥ` onto `L²` (`02-preliminaries.tex:70–74`), and the real-vector subspace
  characterised by `F(−ξ) = conj F(ξ)` (`02-preliminaries.tex:74`).
* `⟪D01:dotHminus1⟫` — the realization `eq:homogeneous-realization`
  (`02-preliminaries.tex:58`): `{h ∈ S' : ĥ = F` measurable, `|ξ|^{-1}F ∈ L²}`, with
  `h ↦ |ξ|^{-1}ĥ` an isometric bijection onto `L²`, separable Hilbert, no polynomial ambiguity.
* `⟪D01:lowHighSplit⟫` — `eq:Rnegative-cutoff`: for `k ∈ L¹ ∩ L²`,
  `‖k‖²_{Ḣ^{-1}} ≤ C‖k‖₁² + ‖k‖₂²` (finiteness of `∫_{|ξ|<1}|ξ|^{-2}` in dimension three).
* `⟪D01:BochnerLq q X⟫` for `1 ≤ q < ∞` and separable Hilbert `X`, over `(0,∞)`, with strong
  measurability, a.e. identification, simple-function approximation, and the norm `eq:time-norms`.
* `⟪D01:normLqLp 1 2⟫`, `⟪D01:normLqHs 2 (−1)⟫`, `⟪D01:normLqDotHminus1 2⟫`.
* `⟪D01:pairingDotHminus1⟫`: `|⟨h,z⟩| ≤ ‖h‖_{Ḣ^{-1}}‖∇z‖₂` and its time-integrated form.
* `⟪D01:V⟫ = H¹(R³;R³) ∩ L²_σ` and `V'` (used only in the framing paragraph, but the paragraph is
  what tells us the intended pairing; keep it as documentation, not a contract field).
* Cutoffs: a fixed `χ ∈ C_c^∞` with `χ = 1` on the unit ball, `0` outside radius `2`,
  `0 ≤ χ ≤ 1`, and `χ_R(x) = χ(x/R)`.
* `⟪I01:packetF⟫` amplitude `ε^{-3}`, correction amplitude `ε^{-2}`, and the scaling identity
  `\widehat{ε^{-α}h(·/ε)}(ξ) = ε^{3−α}ĥ(εξ)` used at `04-whole-space.tex:264–270`.

### 6(iii). DAG children and the exact shape consumed

`R46 ← R41D, B01, B02, I03`.

* **From B01 (real positive-time Bochner approximation)**, exactly: for every real `s`, every
  `q ∈ [1,∞)`, and every `b ∈ L^q((0,∞);H^s(R³;R³))`, there are finite sums
  `Σ_{j≤J} φ_j(t) h_j(x)` with `φ_j ∈ C_c^∞((0,∞))`, `h_j ∈ C_c^∞(R³;R³)` real-valued,
  converging to `b` in `L^q((0,∞);H^s)`; the resulting function is jointly smooth with compact
  support strictly inside `R³ × (0,∞)`, i.e. lies in `F_c`. The paper's chain is: Fourier
  truncation/mollification `⟹` Schwartz `h_n → h` in `H^s`; spatial cutoff
  `‖(1−χ_R)h_n‖_{H^m} → 0` with `m ≥ max(s,0)`; real parts (conjugation is an isometry for these
  even real weights); time restriction to `[1/N,N]`; simple functions; measurable sets
  approximated by finite unions of intervals; smoothed indicators.
* **From B02 (homogeneous `H^{-1}` approximation)**, exactly the same conclusion for
  `X = Ḣ^{-1}(R³;R³)`, via: annular approximation `G_n ∈ C_c^∞(R³∖{0})` of `G = |ξ|^{-1}ĥ` in
  `L²`, `ĥ_n = |ξ|G_n` Schwartz; then `χ_R h_n → h_n` in `Ḣ^{-1}` by `eq:Rnegative-cutoff` since
  `(1−χ_R)h_n → 0` in both `L¹` and `L²`; then diagonal choice; then the same Bochner step.
* **From R41D (restricted to `F_c`) — in the manuscript this is cited as Corollary 4.5**: for a
  smooth compact reference force `f₀ ∈ F_c` and any `ρ > 0`, there is `f₁ ∈ F_c` with
  `T^ν_{max,R}(a,f₁) ≤ T` and `‖f₁ − f₀‖_X < ρ` for `X` the relevant norm. Two-radius assembly:
  approximate the target `b` by `f₀ ∈ F_c` within `ρ/2` (B01/B02), then `f₀` by a singular
  `f₁ ∈ F_c` within `ρ/2`.
* **From I03 (same-family scaling)**: the `s = −1` Fourier scaling calculation
  (amplitude `ε^{-α}` gives spatial `Ḣ^{-1}` factor `ε^{5/2−α}`; time `L²` factor `ε`), giving
  `‖F_ε‖_{L²_tḢ^{-1}} ≤ Cε^{1/2}` (`α = 3`) and `‖H_ε‖_{L²_tḢ^{-1}} ≤ Cε^{3/2}` (`α = 2`), with
  uniformly finite `Ḣ^{-1}` norms of the rescaled profiles by `eq:Rnegative-cutoff`; plus
  `eq:REclose` and the `q=1,s=0` / `q=2,s=−1` insertion estimates, **all for the one family**.

### 6(iv). Proposed contract skeleton

```lean
structure REnergyAPI where
  ν T : ℝ
  hν : 0 < ν
  hT : 0 < T
  a : ⟪D01:VectorField⟫
  ha : a ∈ ⟪D01:X_R⟫
  thresholds : ThresholdAPI
  -- (A) density of the smooth compact singular set in the complete spaces
  densityInhomogeneous :
    ∀ q, (q = 1 ∨ q = 2) → ∀ s : ℝ, s < thresholds.exponent q 0 →
      ∀ b, b ∈ ⟪D01:BochnerLq⟫ q (⟪D01:Hs⟫ s) → ∀ ρ : ℝ, 0 < ρ →
        ∃ f, f ∈ ⟪D01:F_c⟫ ∧ ⟪D01:Tmax⟫ ν a f ≤ T ∧ ⟪D01:normLqHs⟫ q s (f - b) < ρ
  densityHomogeneous :
    ∀ b, b ∈ ⟪D01:BochnerLq⟫ 2 ⟪D01:dotHminus1⟫ → ∀ ρ : ℝ, 0 < ρ →
      ∃ f, f ∈ ⟪D01:F_c⟫ ∧ ⟪D01:Tmax⟫ ν a f ≤ T ∧ ⟪D01:normLqDotHminus1⟫ 2 (f - b) < ρ
  -- (B) simultaneous convergence for the SAME family as Theorem 4.2
  simultaneous :
    ∀ ins : RInsertAPI, ins.ν = ν → ins.T = T → ins.a = a →
      ⟪D01:TendsToZero⟫ (fun ε => ⟪D01:normET⟫ T (ins.uPert ε - ins.v)) ∧
      ⟪D01:TendsToZero⟫ (fun ε => ⟪D01:normLqLp⟫ 1 2 (ins.gPert ε - ins.g)) ∧
      ⟪D01:TendsToZero⟫ (fun ε => ⟪D01:normLqHs⟫ 2 (-1) (ins.gPert ε - ins.g)) ∧
      ⟪D01:TendsToZero⟫ (fun ε => ⟪D01:normLqDotHminus1⟫ 2 (ins.gPert ε - ins.g))
  -- the homogeneous norm is only ever applied to the compact difference
  differenceOnly :
    ∀ ins : RInsertAPI, ∀ ε, 0 < ε → ε < ins.ε₀ →
      ins.gPert ε - ins.g ∈ ⟪D01:BochnerLq⟫ 2 ⟪D01:dotHminus1⟫
```

`simultaneous` is deliberately phrased as a property of an `RInsertAPI` value, so that the family
cannot silently differ from Theorem 4.2's. `differenceOnly` records that no membership claim is
made about `g` or `g_ε` individually.

### 6(v). Risk notes

* **C4 directly.** "Completed force spaces" is the term; there is no space called "completed
  energy-force space". Two distinct claims live here (density in a completion; trajectory
  closure) and they must not be fused into "density in a force/trajectory product space".
  Explicitly: no classical trajectory is assigned to a rough force in the completion.
* **Ambient space switch.** (A) is density in the *complete* space; §1 was relative density in
  `F_R`. Using the same Lean `Dense` idiom for both will lose the distinction.
* **"Smooth compact forces" = `F_c`.** The paper's phrase is resolved by its own proof
  ("Given a compact smooth reference force …"). Worth pinning: it is `F_c`, not "smooth forces
  with compact spatial support", and not `F_R`.
* **Which homogeneous realization.** `Ḣ^{-1}` here is `eq:homogeneous-realization`
  (`02-preliminaries.tex:58`), which is *not* the Appendix B `Λ^a`-completion used in Prop. 4.3.
  A single "homogeneous Sobolev space" typeclass covering both would need care at `s < 0`.
* **`R46 ← R41D` vs the proof's citation of Corollary 4.5.** The manuscript proof says
  "Corollary 4.5 supplies a singular smooth compact force within the other half". The DAG has
  `R46 ← R41D` and `R45 ← R41`, so the graph and the text disagree about which node carries the
  `F_c`-valued density. Resolution options: (a) add `R45 → R46`, which introduces no cycle but
  drags `R43/R44` in unnecessarily; (b) make `R41D` class-parametric (`F_R`, `F_c`, `F_rd`) so
  `R46` and `R45` both consume the same `F_c` instance. (b) is the cleaner interface, and matches
  the fact that only the *density* half of Cor. 4.5 is needed.
* **Separability and real-valuedness.** The Bochner approximation needs `H^s` and `Ḣ^{-1}` to be
  separable and the approximants to be **real** vector fields. The paper argues real parts are a
  contraction because the Fourier weights are real and even. Complex-scalar Lean Sobolev spaces
  would need this bridge explicitly.
* **`L²(0,∞;Ḣ^{-1})` and `s_q`.** `Ḣ^{-1}` corresponds to `s = −1 < −1/2 = s_2`, consistent with
  the inhomogeneous range, but the density claim there is a separate proof (the `Ḣ^{-1}`
  realization is not `H^{-1}`).
* **Deferred detail.** The Bochner step is written for "any of the preceding separable Hilbert
  spaces `X`" — i.e. it is a general lemma applied twice; formalise it once (B01/B02 share it).
* **Interaction with `ε₀`.** (B) requires one family valid for all four convergences; if any of
  the four estimates needs a smaller `ε₀`, the minimum must be taken **before** the family is
  produced, not after.

---

## 7. Theorem 4.7 — `thm:Rgrid` (Identical whole-space cell observations), task **R47**

`04-whole-space.tex:297–304`, with the grid definitions at `04-whole-space.tex:288–296`.
Merged number: Theorem 4.7.

### 7(i). Statement

Setup (`04-whole-space.tex:288–296`): let `T_h` be a **complete uniform Cartesian grid of `R³`
with positive mesh widths** — a partition of `R³` into congruent axis-parallel boxes; each grid
has infinitely many cells. Define the cell-observation map with sequence codomain

    A_h : L¹_loc(R³;R³) → (R³)^{T_h},   (A_h z)_C = (1/|C|) ∫_C z(x) dx,

and use only coordinatewise equality in the codomain. (Recorded but not used in the theorem:
for `z ∈ L²`, `Σ_{C∈T_h} |C| |(A_h z)_C|² ≤ ‖z‖₂²`.)

**Theorem.** Under the regular-reference hypotheses of Theorem 4.2 (`ν,T > 0`, `a ∈ X_R`,
`g ∈ F_R`, reference `(v,π,g)` regular through `T+δ`), fix a **finite** family
`{T_{h_1},…,T_{h_K}}` of complete uniform Cartesian grids. Then the inserted solutions may be
chosen so that, for every grid `T_{h_i}` in that family,

    A_{h_i} u_ε(t) = A_{h_i} v(t)   and   A_{h_i} g_ε(t) = A_{h_i} g(t)    for all 0 ≤ t < T,

while `T^ν_{max,R}(a,g_ε) = T` and the energy and force convergences of Proposition 4.6 hold.
All differences are supported inside a ball contained in one cell of every grid, **except for an
optional spatially constant pressure gauge**.

Proof mechanism (`04-whole-space.tex:306–320`): the union of faces of the finite family is a
closed measure-zero set; pick a point outside it and a ball with closure inside one cell of each
grid; apply Theorem 4.2 in that ball with the compact pressure representative. With
`δu = u_ε − v`, `δp = p_ε − π = P_ε`, `δg = g_ε − g`, and a containing cell `C`:
`δu_j = ∇·(x_j δu)` so `∫_C δu_j = ∮_{∂C} x_j δu·n dS = 0`; subtracting the two momentum
equations and integrating gives `eq:gridforce`
`∫_C δg = (d/dt)∫_C δu + ∮_{∂C}(u_ε⊗u_ε − v⊗v + δp I − ν∇δu) n dS`, whose first term is zero by
the previous identity and whose surface term vanishes because all differences vanish near `∂C`;
a spatially constant pressure gauge adds a multiple of `∮_{∂C} n dS = 0`. Other cells agree by
support.

### 7(ii). D01 / G01 needs

* `⟪G01:UniformCartesianGrid⟫` — mesh widths `h = (h₁,h₂,h₃) ∈ (0,∞)³` and an origin offset
  `o ∈ R³`; cells `C_{n} = ∏_i [o_i + n_i h_i, o_i + (n_i+1)h_i)`, `n ∈ Z³`; the family is a
  partition of `R³`; `|C| = h₁h₂h₃ > 0`. **The offset is not stated in the paper** and must be
  decided — see risk note.
* `⟪G01:cellAverage⟫` `A_h : L¹_loc(R³;R³) → (R³)^{T_h}`.
* `⟪G01:faceSet⟫` — the union of cell boundaries; closed, locally finite union of planes, measure
  zero; finite unions of such sets are closed of measure zero, so the complement is nonempty
  (indeed dense open).
* `⟪D01:L1loc⟫`, `⟪D01:divergenceTheorem⟫` on a box for smooth compactly supported fields.
* Everything in §2(ii), plus the two Theorem 4.2 conclusions not displayed in its statement:
  `δu(t)` divergence free and compactly supported in the interior of `C` for every `t < T`; and
  `δp = P_ε` a compactly supported scalar.
* `⟪D01:pressureGaugeFreedom⟫` — the equivalence class `p ∼ p + c(t)` from
  `02-preliminaries.tex:30–36` and `eq:Rpressure`.
* Everything in §6(ii) for the re-exported convergences.

### 7(iii). DAG children and the exact shape consumed

`R47 ← R42, R46, G01`.

* **From R42**: the entire family, instantiated with `B` = the ball produced by G01. Specifically
  needed: `T^ν_{max,R}(a,g_ε) = T`; `supp(u_ε(t) − v(t)) ⊂ B` for `t < T`;
  `u_ε(t) − v(t)` divergence free; `g_ε − g ∈ C_c^∞(B×(0,∞))`; `p_ε − π = P_ε` compactly
  supported in `B`; and that `u_ε, v` are classical solutions on `[0,T)` so the two momentum
  equations may be subtracted and integrated over `C`.
* **From R46**: the four simultaneous convergences of §6(B), for the same family.
* **From G01 (actual finite-grid observations; itself `← I02`)**:
  1. given finitely many grids, there is a point `x₀` and radius `r > 0` with
     `closure(B(x₀,r))` contained in the interior of one cell of **every** grid;
  2. for a smooth, divergence-free, compactly-supported-in-`int C` field `w`,
     `∫_C w_j dx = 0` for each component `j` (via `w_j = ∇·(x_j w)` and the divergence theorem);
  3. the integrated momentum-difference identity `eq:gridforce`, and the vanishing of its
     boundary flux and of `∮_{∂C} n dS`;
  4. the conclusion that `∫_C δg(t) dx = 0` for every cell of every grid and every `t < T`
     — **derived from the PDE**, not from the support of `δg` alone.

### 7(iv). Proposed contract skeleton

```lean
structure RGridAPI where
  ν T δ : ℝ
  hν : 0 < ν
  hT : 0 < T
  hδ : 0 < δ
  a : ⟪D01:VectorField⟫
  g : ⟪D01:ForceField⟫
  v : ℝ → ⟪D01:VectorField⟫
  π : ℝ → ⟪D01:Scalar⟫
  ha : a ∈ ⟪D01:X_R⟫
  hg : g ∈ ⟪D01:F_R⟫
  reference : ⟪D01:IsClassicalSolution⟫ ν a g v π (Set.Icc 0 (T + δ))
  grids : Finset ⟪G01:UniformCartesianGrid⟫
  -- one common ball inside a cell of every grid
  ball : ⟪D01:Ball⟫
  ballInCell : ∀ G ∈ grids, ∃ C ∈ ⟪G01:cells⟫ G, ⟪D01:closure⟫ ball ⊆ ⟪D01:interior⟫ C
  -- the inserted family, produced by R42 in that ball
  insertion : RInsertAPI
  insertionBall : insertion.B = ball
  insertionData : insertion.ν = ν ∧ insertion.T = T ∧ insertion.a = a ∧ insertion.g = g
  -- conclusions
  velocityAverages :
    ∀ G ∈ grids, ∀ ε, 0 < ε → ε < insertion.ε₀ → ∀ t, 0 ≤ t → t < T →
      ⟪G01:cellAverage⟫ G (insertion.uPert ε t) = ⟪G01:cellAverage⟫ G (v t)
  forceAverages :
    ∀ G ∈ grids, ∀ ε, 0 < ε → ε < insertion.ε₀ → ∀ t, 0 ≤ t → t < T →
      ⟪G01:cellAverage⟫ G (insertion.gPert ε t) = ⟪G01:cellAverage⟫ G (g t)
  lifespan : ∀ ε, 0 < ε → ε < insertion.ε₀ → ⟪D01:Tmax⟫ ν a (insertion.gPert ε) = T
  convergences : REnergyAPI                       -- re-export of §6(B) for this same family
  differenceSupport :
    ∀ ε, 0 < ε → ε < insertion.ε₀ → ∀ t, t < T →
      ⟪D01:support⟫ (insertion.uPert ε t - v t) ⊆ ball ∧
      ⟪D01:support⟫ (insertion.gPert ε t - g t) ⊆ ball ∧
      ∃ κ : ℝ, ⟪D01:support⟫ (insertion.pPert ε t - π t - fun _ => κ) ⊆ ball
```

### 7(v). Risk notes

* **C3, the highest-priority editorial clarification in the audit, lives here.** The equality is
  asserted **only for `0 ≤ t < T`** and only on `R³`. The forces `g_ε, g` are defined for all
  positive time and `g_ε − g` is generally **nonzero after `T`** (Theorem 4.2's rescaled force has
  time support of length `O(ε²)` "including any part after `T`"). The audit gives an explicit
  counterexample family `F^♯ = F + χ(σ)ψ(x)e` showing post-`T` equality is *not* implied by the
  packet hypotheses. Any Lean statement that quantifies `∀ t ≥ 0` is false.
* **Grid definition is under-specified in the paper.** "Complete uniform Cartesian grid with
  positive mesh widths" does not say whether an offset `o` is allowed, nor whether cells are
  half-open. Both matter: with no offset, `0` is always a vertex and the "point outside the union
  of faces" argument still works, but the statement is weaker than intended. Recommendation:
  allow arbitrary `o ∈ R³` and per-axis widths, cells half-open, since the proof only uses
  "closed locally finite union of planes" and "finitely many grids".
* **Pressure gauge.** Two separate gauge facts are needed: (a) `δp = P_ε` must be the *compact*
  representative (Theorem 4.2's proof chooses it; its statement does not say so); (b) the theorem
  permits an additional **spatially constant** `κ(t)`, harmless because `∮_{∂C} n dS = 0`. A
  gauge that is not spatially constant (e.g. the potential-formula gauge `∫₀¹ G(rx)·x dr` applied
  to a non-compact `G`) would break the surface-term cancellation.
* **Force equality is a PDE consequence, not a support consequence.** `∫_C δg = 0` does not follow
  from `supp δg ⊂ C`; it follows from `eq:gridforce`. `G01`'s contract already says this; the
  contract field `forceAverages` must be derived, never assumed.
* **`∫_C δu_j = 0` needs `δu` compactly supported in the *interior*** of the cell, not merely in
  the closed cell — otherwise the surface integral need not vanish. Hence `closure(ball) ⊆
  interior(C)` in `ballInCell`.
* **`(d/dt)∫_C δu = 0` requires the identity at every `t < T`, plus differentiation under the
  integral sign** on a fixed compact set; routine but must be justified for `t` up to `T`.
* **Interpretation limits (paper's own closing paragraph, `04-whole-space.tex:323–329`).** The
  perturbation depends on the fixed grid family and its amplitude grows as its support shrinks;
  the result is about the information in the prescribed averages, not about convergence under
  refinement. Point values and pressure may distinguish the two solutions. Do not let a Lean
  statement's name suggest otherwise.
* **Bounded-domain framing paragraph** (`04-whole-space.tex:277–286`, Guermond–Minev–Shen) is
  context only: "These bounded-domain conventions do not impose boundary conditions at infinity in
  the whole-space result below." Nothing in Theorem 4.7 depends on it.
* Clarifications affecting this result: **C3** (primary), plus C1/C2/O2 inherited via Theorem 4.2.

---

## 8. Consolidated D01 requirements

Deduplicated list of everything D01 (and the two objects that belong to I01 and G01) must define,
with the exact properties Section 4 consumes. Consumers in brackets.

### 8.1 Base setting and Fourier normalisation
* `⟪D01:R3⟫`, real vector fields `R³ → R³`, tensors by componentwise squared sums.
  `ẑ(ξ) = (2π)^{-3/2}∫ e^{-ix·ξ}z(x) dx`; Plancherel with this normalisation.
  [everything; the `H^s ↪ H^{r}` norm-one embeddings depend on the exact weight]
* Real subspace of a Fourier space: `F(−ξ) = conj F(ξ)`; conjugation is an isometry for every
  weight used (real, even), so taking real parts is a contraction. [4.6/B01/B02]

### 8.2 Inhomogeneous Sobolev scale
* `⟪D01:Hs s⟫`, all real `s`, norm `‖z‖²_{H^s} = ∫(1+|ξ|²)^s|ẑ|²`; separable Hilbert; isometry
  `h ↦ ⟨ξ⟩^s ĥ` onto `L²`. [4.1, 4.2, 4.4, 4.6]
* Monotonicity with constant one: `‖z‖_{H^s} ≤ ‖z‖_{H^r}` for `s ≤ r`; in particular
  `‖z‖_{H^s} ≤ ‖z‖_2` for `s ≤ 0`. [4.1 converse; 4.2 negative orders]
* `‖z‖²_{H^{3/2}} = ‖z‖²_{H^{1/2}} + ‖∇z‖²_{H^{1/2}}` (exact weight identity). [4.4]
* `‖z‖²_{H²} ≤ C(‖z‖²₂ + ‖Δz‖²₂)`; `‖D²z‖₂ = ‖Δz‖₂`. [4.3, 4.4]
* `H^∞ = ⋂_m H^m` with its Fréchet topology (set only). [X_R]

### 8.3 Multiplication / embedding facts imported from Appendix A (task A03)
* `‖z‖_∞ ≤ C‖z‖_{H²}` (`eq:Rproduct`). [4.2 lifespan `≤ T`]
* `‖vw‖_{H^m} ≤ C_m(‖v‖_{H²}‖w‖_{H^m} + ‖w‖_{H²}‖v‖_{H^m})`, `m ≥ 2`. [via `prop:local`/A04]

### 8.4 Homogeneous realizations — **three distinct objects**
1. `⟪D01:dotHs a⟫` for `0 < a < 3/2`: Appendix B completion of `{v : v̂ ∈ C_c^∞(R³∖{0})}` under
   `‖Λ^a v‖₂`, realized by `v̂ = |ξ|^{-a}G`, `G ∈ L²`, with a unique `L^{p_a}` representative,
   `p_a = 6/(3−2a)`. Contains all Schwartz and all `H^∞` fields of finite norm. [4.3, 4.4 via A05]
   Note `Ḣ^{3/2}` is used only as the *quantity* `‖Λ^{3/2}u‖₂` on smooth fields; no space.
2. `⟪D01:dotHsFinite s⟫` for `−3/2 < s < 0`: the plain Fourier integral
   `(∫|ξ|^{2s}|ẑ|²)^{1/2}` for smooth compactly supported `z`, finite by splitting at `|ξ|=1`;
   plus `(1+|ξ|²)^s ≤ |ξ|^{2s}` for `s<0`, so `‖z‖_{H^s} ≤ ‖z‖_{Ḣ^s}`; uniform over the rescaled
   profile family (common compact support, uniform derivatives). [4.2 negative orders]
3. `⟪D01:dotHminus1⟫`: `eq:homogeneous-realization`, `{h ∈ S' : ĥ = F` measurable,
   `|ξ|^{-1}F ∈ L²}`, `h ↦ |ξ|^{-1}ĥ` an isometric bijection onto `L²`; separable Hilbert; no
   polynomial ambiguity; `|⟨h,z⟩| ≤ ‖h‖_{Ḣ^{-1}}‖∇z‖₂`; `‖k‖²_{Ḣ^{-1}} ≤ C‖k‖₁² + ‖k‖₂²`
   (`eq:Rnegative-cutoff`). [4.6, 4.7]
* `⟪D01:Lambda⟫ = (−Δ)^{1/2}` (symbol `|ξ|`), `⟪D01:J⟫ = (I−Δ)^{1/2}`. [4.3, 4.4]

### 8.5 Bochner spaces and mixed norms
* `⟪D01:BochnerLq q X⟫` on `I = (0,∞)`, `1 ≤ q < ∞`, strongly measurable, a.e. identification,
  norm `eq:time-norms`; simple-function density; separability of the target. [all]
* `⟪D01:normLqHs q s⟫`, `⟪D01:normLqLp q p⟫`, `⟪D01:normLqDotHs q s⟫`,
  `⟪D01:normLqDotHminus1 2⟫`. [all]
* `⟪D01:normET T⟫ = ‖·‖_{L^∞(0,T;L²)} + ‖∇·‖_{L²(0,T;L²)}` (`eq:Enorm`), no endpoint value at `T`.
  [4.1 rider, 4.2, 4.6, 4.7]
* `⟪D01:normLinfty⟫`, `⟪D01:normLp p⟫` for `p ∈ {1,2,3,6}`. [4.2, 4.3, 4.4, 4.6]

### 8.6 Data and force classes
* `⟪D01:L2sigma⟫`, `⟪D01:X_R⟫ = H^∞ ∩ L²_σ`. [all]
* `⟪D01:F_R⟫` (`eq:Rclasses`): `C^∞([0,∞);H^∞)` with one-sided derivatives at `0`, and
  `‖f‖_{L^1_tH^m} + ‖f‖_{L^2_tH^m} < ∞` for every integer `m ≥ 0`. Derived facts needed:
  real vector space; `0 ∈ F_R`; `‖f‖_{L^q_tH^s} < ∞` for every real `s`, `q ∈ {1,2}`;
  `F_R + C_c^∞(R³×(0,∞)) ⊆ F_R`; forces may be nonzero at `t = 0` and need not have compact
  support; forces are defined **through and past** any singular time of the velocity. [all]
* `⟪D01:F_c⟫ = C_c^∞(R³×(0,∞);R³)`; `⟪D01:F_rd⟫` (rapid decay, all `N, α, j`, no common bound);
  `⟪D01:S_sigma⟫ = S(R³;R³) ∩ L²_σ`. Inclusions `F_c ⊆ F_rd ⊆ F_R`, `S_σ ⊆ X_R`; both subclasses
  stable under adding `C_c^∞(R³×(0,∞))`; both contain `0`. [4.5, 4.6]
* `⟪D01:V⟫ = H¹(R³;R³) ∩ L²_σ` and `V'` — documentation of the intended pairing only. [4.6]

### 8.7 Equation, projection, pressure, solutions
* `⟪D01:Leray⟫` with symbol `I − ξ⊗ξ/|ξ|²`, bounded on every `H^s`, commuting with derivatives
  and the heat semigroup; projected equation `eq:projected`. [4.2, 4.3, 4.4]
* `⟪D01:gradPressure⟫`: `∇p = (I−P)(f − ∇·(u⊗u))` (`eq:Rpressure`); potential formula
  `p(x,t) = ∫₀¹ G(rx,t)·x dr`; scalar `p` determined up to a function of time; `∇p ∈ L²`, so no
  nonzero constant pressure gradient; **no** `p ∈ L²(R³)` requirement.
  `⟪D01:pressureGaugeFreedom⟫`: `p ∼ p + κ(t)`. [4.2, 4.7]
* `⟪D01:IsClassicalSolution ν a f u p I⟫`: `u ∈ C(I;H^m)` for every integer `m ≥ 0` on each
  compact subinterval, `∇·u = 0`, `u(0)=a`, `eq:NS` with the pressure convention. [all]
* `⟪D01:IsMaximalSolution⟫`, `⟪D01:Tmax ν a f⟫ ∈ (0,∞]`, uniqueness, mild formulation `eq:mild`,
  continuation criterion `∫₀^S ‖u‖²_{H²} < ∞ ⟹` extension (`eq:criterion`). [all]
* `⟪D01:RegularThrough ν a f T⟫` = extends smoothly to `[0,T+δ]` for some `δ > 0`. [4.1, 4.2, 4.7]
* `⟪D01:B_R ν a T⟫ = {f ∈ F_R : Tmax ν a f ≤ T}` (`eq:Rsingularforces`). [4.1, 4.5]
* `⟪D01:DenseRel S Y ‖·‖⟫` — relative density of `S ⊆ Y` in the norm topology; and ordinary
  density in a complete space. Must be two distinguishable predicates. [4.1/4.5 vs 4.6]

### 8.8 Packet data (task I01) and geometry
* `⟪I01:packetU⟫, ⟪I01:packetP⟫, ⟪I01:packetF⟫` — one fixed solution of Theorem 1.1, renamed
  `(U,P,F)` at `01-introduction.tex:64`; compact set `K`; `F ∈ C_c^∞(R³×(0,∞))`;
  `sup_{t<1}‖U(t)‖₂ < ∞`; `limsup_{t↑1}‖U(t)‖_∞ = ∞`.
* `⟪I01:packetM⟫ = M`, `⟪I01:packetD⟫ = D` (`lem:packetenergy`), both finite;
  `U, P` vanish on an initial interval, hence extend smoothly by zero to negative times;
  **`F` likewise extends by zero to nonpositive source times (C1)**.
* `K_*` = a compact set containing `K` and the spatial projection of `supp F`;
  `R_* = sup_{y ∈ K_*}|y|`; scaling center `x₀ ∈ B` (**C2**); `t_ε = T − ε²`.
* Cutoffs: `θ ∈ C_c^∞(R³)` equal to one near `K_*`; `η ∈ C_c^∞((−2,2))` equal to one on `[−1,1]`;
  `θ_ε(x) = θ((x−x₀)/ε)`, `η_ε(t) = η((t−T)/ε²)`; smooth-Urysohn construction.
* `χ ∈ C_c^∞`, `χ = 1` on the unit ball, `0` outside radius `2`, `χ_R(x) = χ(x/R)`. [4.6]

### 8.9 Grids (task G01)
* `⟪G01:UniformCartesianGrid⟫` (mesh widths, offset, half-open cells, partition of `R³`,
  infinitely many cells, `|C| > 0`); `⟪G01:cells⟫`; `⟪G01:faceSet⟫` closed, locally finite union
  of planes, measure zero; `⟪G01:cellAverage⟫ A_h` on `L¹_loc`, codomain `(R³)^{T_h}` with
  coordinatewise equality; the recorded inequality `Σ_C |C||(A_h z)_C|² ≤ ‖z‖₂²`.

### 8.10 Exponent arithmetic (already frozen)
* `ThresholdAPI.exponent q s = 2/q − 3/2 − s`, `positive`, `l1`, `l2`, `negativeIndex`,
  `energy : exponent 1 0 = 1/2 ∧ exponent 2 (-1) = 1/2`
  (`verification/Contracts/V1/Thresholds.lean`). Also `α(p,q) = −3 + 3/p + 2/q` and the relation
  `‖H_ε‖`-exponent `= ‖F_ε‖`-exponent `+ 1`.

---

## 9. Cross-result consistency checks

Items that must be the *same object* (not merely equal-looking) across the seven results. Each is
a place where independent formalisation of two results would silently diverge.

1. **One packet `(U,P,F)`, one `(M,D)`.** Fixed once at `01-introduction.tex:64` and
   `02-preliminaries.tex:127`. `M+D` appears in `eq:REclose` (4.2) and, through it, in 4.1's
   rider, 4.6(B) and 4.7. The torus `eq:Eclose` uses the same constants — one global instance.
2. **One `ε`-family.** Theorem 4.2 ends "All of these conclusions hold for the same family of
   inserted solutions"; Proposition 4.6(B) says "For every reference in Theorem 4.2, one may
   *simultaneously* arrange …"; Theorem 4.7 says "the inserted solutions may be chosen so that …
   *and* the energy and force convergences in Proposition 4.6 hold". In Lean this must be one
   value (`RInsertAPI`) threaded through R42 → R46 → R47, not three independently existentially
   quantified families. `I03`'s contract already states "Preserve one epsilon family for all
   required convergences".
3. **`ε₀` is a single threshold.** All constraints (`2ε² < min(T,δ)`, `x₀+εK_* ⊂ B`,
   `εR_* < dist(x₀,∂B)`, scaled `supp θ` inside the ball, `ε ≤ 1`, plus whatever 4.6's four
   convergences need, plus 4.7's "fixed upper bound on `ε`") must be minimised **before** the
   family is produced. 4.7's proof says explicitly "the convergence estimates are unaffected by
   this fixed upper bound on `ε`".
4. **The ball `B`.** Theorem 4.2 takes an arbitrary nonempty open ball; Theorem 4.7 instantiates it
   with a ball inside a common cell of every grid. `B` must therefore be a *parameter* of R42, not
   an existential inside it. Corollary 4.5 and Proposition 4.6 do not constrain `B`.
5. **`x₀ ∈ B`, and one center for everything.** `U_ε, P_ε, F_ε` (via `eq:scaling`), `θ_ε`, the
   vector potential `A` (centered at `x₀`), `w_ε` and `H_ε` all use the same `x₀` (**C2**).
   Section 4 drops the torus localization lemma, so `B` is genuinely arbitrary here, but the
   center must still lie inside it.
6. **Two time centers.** The packet is centered at `t_ε = T − ε²` while the time cutoff `η_ε` is
   centered at `T`. Both supports lie in `(T−2ε², T+2ε²)`, and `U_ε ≡ 0` before `t_ε`. Do not
   unify them.
7. **`s_q` and `β`.** `s_q = 2/q − 3/2` in 4.1, 4.2, 4.6; `β(q,s) = s_q − s` in 4.2's proof;
   `α(p,q) + 1` for the correction. All must route through `ThresholdAPI.exponent`. The two rates
   used in 4.6(B) are exactly `ThresholdAPI.energy`.
8. **The constant `c` of Proposition 4.3.** One universal `c` serves (a) the homogeneous
   hypothesis `‖a‖_{Ḣ^{1/2}} + ‖f‖_{L^1_tḢ^{1/2}} < cν`, (b) the `a=0` inhomogeneous corollary
   `‖f‖_{L^1_tH^{1/2}} < cν`, and (c) the radius of the `q=1` non-density ball in Theorem 4.1(ii)
   and Corollary 4.5. It must not depend on `ν`, `T`, `a` or `f`.
9. **The radius `r_{ν,S}` of Proposition 4.4 at `S = T`.** This same number is the radius of the
   `q=2` non-density ball in Theorem 4.1(ii) and Corollary 4.5, and is what the sentence at
   `04-whole-space.tex:16` means by "a regular neighborhood whose radius depends on `T`". `c, C`
   in `r_{ν,S} = cν^{3/2}e^{−CνS}` are universal and distinct from item 8's `c`.
10. **The pressure representative.** Theorem 4.2's proof chooses the compact `P_ε`; Theorem 4.7
    requires exactly that choice (`δp = P_ε`) plus an optional **spatially constant** gauge. A
    different scalar gauge invalidates the boundary-flux cancellation in `eq:gridforce`.
11. **Relative vs complete ambient space.** 4.1 and 4.5 are relative density in
    `F_R` / `F_c` / `F_rd`; 4.6(A) is density in the complete Bochner spaces. `F_c` appears on
    both sides (as an ambient class in 4.5, as a dense subset in 4.6) — the two roles must be
    distinguishable (**C4**).
12. **Which class the singular set lives in.** `B^R_{ν,a,T} ⊆ F_R` (4.1);
    `{f ∈ F_c : Tmax ≤ T}` (4.6); `{f ∈ Y : Tmax ≤ T}` for `Y ∈ {F_c, F_rd}` (4.5). The lifespan
    function `Tmax ν a ·` is the same in all three.
13. **`a` discipline.** `a` is fixed and arbitrary in 4.1(i), 4.2, 4.5, 4.6, 4.7 — and it is the
    *same* `a` inside each of those results (the insertion preserves the initial velocity
    exactly). `a = 0` in 4.1(ii) and 4.4. `a` is general in 4.3.
14. **Time range of the force equality.** 4.7 claims equality only for `0 ≤ t < T`, while
    `g_ε − g` is generally nonzero on a short interval after `T` (4.2). 4.1's density is measured
    by a force norm over all of `(0,∞)`, which *includes* that post-`T` piece. These are
    consistent only because the post-`T` piece is `O(ε²)` in duration; do not "simplify" either
    statement into the other's time range (**C3**).
15. **`E_T` interval.** Always `(0,T)` with no endpoint value at `T`; the velocity is undefined at
    `T`. Force norms are always over `(0,∞)` unless an interval is displayed
    (`01-introduction.tex:140`).
16. **`prop:local` is one proposition serving both domains** (`prop:local` = `lem:Rlocal` =
    merged Proposition 2.1, task A04). Its whole-space instance is the only one Section 4 uses;
    the periodic mean reduction in Appendix A is irrelevant here.
17. **Missing DAG edges found while reading** (all recorded above): `A03 → R42` (the
    `H² ↪ L^∞` step in the lifespan argument); `R42 → R45` (compact force difference, needed to
    stay inside `F_c` / `F_rd`); and the `R46 ← R41D` vs "Corollary 4.5" discrepancy — the cleanest
    fix is to make `R41D` parametric in the admissible force class so that `R45` and `R46` share
    one instance.
