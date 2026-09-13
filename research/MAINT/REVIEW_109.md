# 审稿 · lane 109-MAINT-promotions — 把 reviewer 标记的 Paper3 / A03 级事实上提到规范位置

审稿人跑通 Lean。被审提交：`a46a449`（rebase 到 `36b4261` 之上），11 个 `.lean` + `research/MAINT/ATTEMPTS_109.md`。

## 结论

**ACCEPT-WITH-NOTES**

8 条被搬的定理**陈述和证明体逐字节一致**（不只是陈述），老位置各留恰好一条同名空间 `alias`，
树里所有裸名引用仍然解析，两条 corollary 改写只动证明不动陈述，`Source/RealSobolev.lean` 净变更为零，
没有引入 import 环、没有重复定义。全部门禁绿。**lane 108 的 `OrderZeroCurl.lean` 在本分支上直接
elaborate 通过（517 行，exit 0，无输出）**——这是本次最关键的兼容性问题，已用真编译器证实，不是推断。

所有 findings 都是文档准确性与将来风险，没有正确性缺陷，不阻塞合入。**但 finding 1 必须改**：
ATTEMPTS 里把一条**假的**技术事实写成了偏离理由，且同一份文档里自相矛盾，留着会污染后续车道。

---

## 1. 门禁（命令 + 结果）

| 命令 | 结果 |
|---|---|
| `lake build` 11 个改动模块 + 7 个下游消费者 | `Build completed successfully (9954 jobs).` |
| `lake env lean` × 11 个改动模块 | 全部 **SILENT**（exit 0，零输出） |
| `lake env lean` lane 108 的 `OrderZeroCurl.lean`（只读，跨 worktree） | **exit 0，零输出**（7.4s / 517 行） |
| `research/D01/axioms_transverse.lean` | `…D01.angularFrequencyDilation_coeFn` → `[propext, Classical.choice, Quot.sound]` |
| `research/D01/axioms_order_zero.lean` | `…D01.transverse_of_transverse_symm` → 同上（21 条全绿） |
| `research/A04/axioms_sl2.lean` | `…A04.{isSobolevDatum_smul, isScalarSobolevDatum_smul, isSobolevDatum_neg, isScalarSobolevDatum_neg}` → 同上 |
| `research/A04/axioms_sl5_columns.lean` | `…A04.columnsSobolevENorm_toReal_sq_eq_sum` → 同上 |
| `research/A04/axioms_sl3.lean` | `…A04.gradientSobolevENorm_toReal_sq_eq_sum` → 同上 |
| `research/B02/axioms_u2_sl3.lean` | `…B02.angularFourier_conj` **和** `…Paper3.angularFourier_conj` → 同上（见 finding 3） |
| `make check` | `Ran 13 tests … OK`；`30 work items: ownership, contract registration and task cards consistent.` exit 0 |
| `make test` | exit 0，**18/18** `checked; standard logical axioms only` |

下游消费者实际编译的集合：`D01.Longitudinal`、`D01.LerayLowering`、`A04.LaplacianAssembly`、
`A04.NonlinearDatum`、`A04.NonlinearBound`、`B02.SeparatedAssembly`、`B02.Remaining`。
**`D01.OrderZeroCurl` 本分支上不存在**（lane 108 未合），改用跨 worktree 只读 elaborate 代替，见上表第 3 行。

审稿人另做了一次**探针可信度自检**（防止"7.4 秒 = 其实没编译"的误判）：
同样的 `lake env lean` 调用对一个故意写错的文件报
`error(lean.unknownIdentifier): Unknown identifier 'this_name_does_not_exist'`，exit 1。
所以上面的"零输出 exit 0"是真的编过了。

构建日志里 50 条 warning **无一条落在 11 个改动模块**；ATTEMPTS 提到的 `ring` trace 定位到
`NSFormalization/Source/PhysicalBesselSobolev.lean:134`，与本车道无关，属既有噪声，核实属实。

## 2. 逐字节比对（8 条搬迁 + 2 条 corollary）

按名字抽出老文件（`git show 36b4261:<old path>`）与新家的完整 `theorem` 块做 diff：

| # | 定理 | 老位置 | 新家 | 结果 |
|---|---|---|---|---|
| 1a | `angularFrequencyDilation_coeFn` | `D01/Transverse.lean:66` | `Paper3/AngularFourierDilation.lean:248` | **陈述+证明体逐字节一致** |
| 1b | `transverse_of_transverse_symm` | `D01/OrderZeroSymbol.lean:491` | `Paper3/…:297` | 同上 |
| 3 | `angularFourier_conj` | `B02/AnnularReal.lean:54` | `Paper3/…:339` | 同上 |
| 4a | `isScalarSobolevDatum_smul` | `A04/MomentumDatum.lean:116` | `A03/ScalarTameProduct.lean:226` | 同上 |
| 4b | `isScalarSobolevDatum_neg` | `A04/MomentumDatum.lean:140` | `A03/ScalarTameProduct.lean:241` | 同上 |
| 4c | `isSobolevDatum_smul` | `A04/MomentumDatum.lean:132` | `A03/VectorTameProduct.lean:197` | 同上 |
| 4d | `isSobolevDatum_neg` | `A04/MomentumDatum.lean:146` | `A03/VectorTameProduct.lean:205` | 同上 |
| 5a | `columnsSobolevENorm_toReal_sq_eq_sum` | `A04/NonlinearColumns.lean:137` | `A03/OuterTameProduct.lean:97` | 同上 |

两条 corollary 改写（只允许动证明）：

- `D01/HomogeneousWitness.lean:190 angularFourier_conj_neg` — 陈述 diff 为空，**逐字节一致**。
- `A04/LaplacianDatum.lean:96 gradientSobolevENorm_toReal_sq_eq_sum` — 四行陈述用 `cat -A` 逐字节比过，
  唯一差别是行尾 ` := by` → ` :=`（证明模式切换，不是陈述）。

## 3. 结构

- **无 import 环**：`Paper3/AngularFourierDilation` 闭包 58 个模块，**Section4 出现 0 次**；
  `A03/{Outer,Scalar,Vector}TameProduct` 闭包 138/129/134，**A04 出现 0 次**。
- **无重复定义**：8 个名字各自恰好一个 `theorem` + 恰好一个 `alias`（本车道新增 `alias` 语句正好 8 条）。
- **alias 命名空间正确**：`D01/Transverse.lean:59`、`D01/OrderZeroSymbol.lean:483` 在
  `NSFormalization.Section4.D01`；`B02/AnnularReal.lean:51` 在 `…B02`；
  `A04/MomentumDatum.lean:116-119`、`A04/NonlinearColumns.lean:135` 在 `…A04`。全部对得上。
- **Paper3 文件只增不减**：新增恰好 3 条 `theorem`，`-theorem/-def/…` 为空。新加的两个 `open`
  （`Source.RealSobolev (FourierData fourier_conjugate)` 和 scoped `ComplexConjugate`）不会改写既有代码的含义——
  该文件改动前 `conj` / `FourierData` 出现次数为 **0**。
- **`Source/RealSobolev.lean` 净变更为零**：`git diff 36b4261 -- formalization/NSFormalization/Source/` 输出为空。
- `verification/contracts.json` 未被触碰（MAINT 车道本就不该动），HEAD~1 与 `origin/erenup/integration` 都是 18 条。

## 4. Findings

### Finding 1 —（低，文档，**要求改**）ATTEMPTS 里 item 3 的偏离理由是假的，且自相矛盾
位置：`research/MAINT/ATTEMPTS_109.md` §"Skipped / deviated" item 3，第一个 bullet。

原文声称：`Source/FourierConvention.lean`（原定目标）**circular**，理由是
"`fourier_conjugate` lives in `Source/RealSobolev.lean`, and `RealSobolev` imports `FourierConvention`"。

审稿人独立核实（含 vendor 的完整 import 闭包）：

```
FourierConvention in closure(RealSobolev)?  False
RealSobolev in closure(FourierConvention)?  False
=> 给 FourierConvention 加 'import RealSobolev' 会成环吗？ False
```

两者是**互不相干的兄弟模块**（`RealSobolev` 只 import `Paper3.SobolevDensity`；
`FourierConvention` 只 import `Source.FourierTranslation`）。所以"circular"是假的——
把定理放进 `FourierConvention.lean` 并加一条 `import NSFormalization.Source.RealSobolev`
**不会成环**。而且同一份文档的第二个 bullet 自己写了正确事实
（"`RealSobolev` does not import `Source/FourierConvention` (verified: …)"），前后直接打架。

**但结论仍然正确，审稿人支持这个偏离**——只是理由该换成真的那条：加这条 import 会让
`Source/FourierConvention` 的闭包从 **30 → 73** 个模块，并把 **11 个 `Paper3.*` 模块**
（现在只有 1 个 `Paper3.SobolevWeights`）拖进一个 `Source` 层模块，属于层级倒挂；
`FourierConvention` 有 6 个直接 importer（含 `Paper3.AngularSobolevCoordinates`），
这条倒挂边一旦立起来，将来任何人给那几个 Paper3 模块加一条 `FourierConvention` 的 import 就变成真环。
`Paper3/AngularFourierDilation.lean` 是正确的家。

**修法**：把 item 3 第一个 bullet 的 "circular / RealSobolev imports FourierConvention"
换成上面这条闭包成本 + 层级倒挂的真理由（30→73、1→11 个 Paper3、6 个 importer）。不必动 Lean。

### Finding 2 —（低，文档）ATTEMPTS 里 "A03 只 import A03/A05/Paper3/Source/Mathlib" 不准确
位置：`research/MAINT/ATTEMPTS_109.md` 移动表下方那句括号 "(checked: `A03` modules import only …)"。

实际 `A03/*.lean` 还 import 了：`Euler.EulerProof`（`BoundedRepresentative.lean:1`）、
`NSFormalization.Section4.D01.SmoothDatum`（`RealAngularProduct.lean:2`）、
`NavierStokes.ProblemStatement`（`SmoothJets.lean:5`）。

**结论本身（A03 不 import A04、没成环）是对的**，审稿人已用闭包独立复核（A04 在三个 A03 模块闭包里出现 0 次）。
只是取证描述写松了。**修法**：改那句括号。不必动 Lean。

### Finding 3 —（低，将来风险）alias 策略引入了一个真实的裸名歧义，当前无人踩到
"老位置留 alias" 必然让同一个裸名在两个命名空间里各有一份。审稿人构造探针复现了：

```
error: Ambiguous term
  angularFourier_conj
Possible interpretations:
  NSFormalization.Paper3.angularFourier_conj f xi : …
  NSFormalization.Section4.B02.angularFourier_conj f xi : …
```

触发条件：某模块**同时 top-level `open` 新旧两个命名空间、且自己不在其中任何一个里**，再用裸名。

- **当前树里无人触发**（全量 build 绿）。既有消费者都在老命名空间**内部**，
  Lean 的"外层命名空间优先于 open"规则让它们稳稳解析到 alias。
- **lane 108 安全**：`OrderZeroCurl.lean:457` 的裸名 `angularFrequencyDilation_coeFn` 虽然处在
  `open NSFormalization.Paper3`（:323）之下，但它同时在 `namespace NSFormalization.Section4.D01`（:318）**之内**，
  外层命名空间优先。已用真编译器验证（见 §1 第 3 行）。
- **已经有一个"擦边"文件**：`research/B02/axioms_u2_sl3.lean` 同时 open 了 `Section4.B02` 和 `Paper3`，
  它没炸只是因为 `#print axioms` 对歧义名的处理是**把所有解释都打印一遍**（输出里确实两条都在），
  换成 term 位置（`exact` / `:=`）就会报上面的 Ambiguous term。

**修法（建议写进 `logs/LESSONS.md`，不阻塞本车道）**：以后新模块引用被上提过的名字，
要么待在老命名空间内，要么写全限定名；不要在模块顶层同时 open 新旧两个命名空间。

### Finding 4 —（信息）合同数是 18 不是 19
审稿单写的"19 contracts on the rebased branch"是过期预期。`verification/contracts.json` 在
HEAD~1、`origin/erenup/integration`、本车道 HEAD 上**都是 18 条**，本车道也没碰这个文件（MAINT 车道正确行为）。
`make test` 18/18 全绿，不是回归。

## 5. 三个偏离的判断

**(a) item 3 的家用 `Paper3/AngularFourierDilation.lean` 而非 `Source/FourierConvention.lean` —— 可接受，审稿人支持。**
这是正确的落点：它是 angular-Fourier 的自然归属、已经承载本车道 item 1 的两条上提、
`B02/AnnularReal` 与 `D01/HomogeneousWitness` 都传递 import 它（alias 和 corollary 都解析得到），
陈述证明逐字节不变，只靠两条 header `open` 就落地。**注意理由要改**，见 finding 1——
真正的障碍不是环，是层级倒挂和闭包成本。

**(b) item 2（`angular_plancherel`）跳过 —— 可接受，理由核实属实；建议后续做"整簇搬"而不是单条搬。**
审稿人逐条核对了 ATTEMPTS 的说法，全部属实：`angular_plancherel` 在
`B02/LowHigh.lean:186`，它依赖的 8 个 helper（`angular_lintegral_eq_cycles:154`、`sq_eLpNorm_two:134`、
`eLpNorm_fourierIntegral_eq:121`、`coeFn_l2Fourier_ae:86`、`l2_fourier_pairing:72`、
`fourier_mul_formula:56`、`lintegral_comp_const_smul:146`、`finrank_space_eq_three:142`）
**全部在同一个文件里**，而该文件确实 import 了 `NavierStokes.R3.CompactSchwartz`、
`Mathlib.Analysis.Fourier.LpSpace`、`Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff`，
这些都不在 Paper3 的 import 面上。单条搬会破坏"逐字节搬"的前提，跳过是对的。

**后续建议**：如果要做，应该开一个专门的新模块（例如 `Paper3/AngularPlancherel.lean`）
把整簇 9 条一起搬过去，而不是硬塞进已有的 Paper3 文件。**优先级低**：目前 `angular_plancherel`
在 B02 之外没有消费者，没有真实收益，等到有第二个消费者再做。

**(c) item 6（`contDiff_slice_pressure` 留在原地，`+1063 modules`）—— 可接受，数字审稿人完全复现。**
独立计算（口径：`NSFormalization.*` + vendor `Euler.*` / `NavierStokes.*`，排除 Mathlib）：

```
PressureGradient project closure: 52
D01.DatumToJets project closure: 1113
extra modules if imported:       1063
```

与 ATTEMPTS 的 52 / 1113 / 1063 **一字不差**。`R42/PressureGradient.lean:69` 的
`contDiff_slice_pressure` 与 `D01/DatumToJets.lean:378` 的 `contDiff_slice_scalar` 确实是同一事实的两份，
但为省 1063 个模块的 import 面留一份副本是划算的。**这一条已经量化闭环，后续车道不要再翻。**

## 6. ATTEMPTS_109.md 诚实度

抽查远超要求的 3 行：**移动表 8 行的老位置行号逐个回老文件核对，全部精确命中对应的 `theorem` 行**
（1a `Transverse.lean:66`、1b `OrderZeroSymbol.lean:491`、3 `AnnularReal.lean:54`、
4a/4c/4b/4d `MomentumDatum.lean:116/132/140/146`、5a `NonlinearColumns.lean:137`、5b `LaplacianDatum.lean:96`）。
item 6 的三个数字完全复现；item 2 的 helper 清单与 import 清单完全属实；
"`RealSobolev` 无净变更"属实；`ring` trace 的定位属实。

**结论：记账整体可信，正负例都记了**。两处文档不准（finding 1 的假理由 + finding 2 的取证描述），
其中 finding 1 是把一条**错误的技术事实**写成了负例，按 CLAUDE.md 规矩 4 必须纠正后再合入。

## 7. 剩余 MAINT 清单

1. **`angular_plancherel` + 8 个 B02-local helper 整簇上提**到新模块（如 `Paper3/AngularPlancherel.lean`）。
   低优先级，等 B02 之外出现第二个消费者再做。（本车道 item 2 跳过，理由已核实）
2. **lane 108 的 `longitudinal_of_longitudinal_symm`**（`OrderZeroCurl.lean:439` 自带 `TODO (SIMP lane)`）——
   `transverse_of_transverse_symm` 的 pairwise/longitudinal 对应物，等 108 合入后与本次一样上提到
   `Paper3/AngularFourierDilation.lean`。
3. **`OrderZeroDatum` / `HalfOrder` 各处小副本**去重（`NEXT_SESSION.md` 原清单，未动）。
4. **B02 数据链副本**去重（`NEXT_SESSION.md` 原清单，未动）。
5. **074 三条交换引理与 vendor 重复**（`NEXT_SESSION.md` 原清单，未动）。
6. ~~`contDiff_slice_pressure` 去重~~ —— **已量化闭环，决定保留副本，不要再开**（见 §5(c)）。
7. 新增（finding 3 衍生）：给 `logs/LESSONS.md` 加一行"上提 + alias 之后，新模块别在顶层同时 open 新旧命名空间"。

## 8. 建议

合入前只需要改 `research/MAINT/ATTEMPTS_109.md` 的两处文字（finding 1、finding 2），**Lean 一行都不用动**。
审稿人不改代码。
