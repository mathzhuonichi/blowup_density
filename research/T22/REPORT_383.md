# Lane 383 report — T22 U-B1 restriction bridge

## 1. 证了哪个定理

完成了 `restrictDatum_eq_restrictField`：任何表示
`zeroExtension Ω z` 的全空间 `IsSobolevDatum`，在支撑包含于 `Ω` 的
Schwartz 测试上都恰好限制为 `restrictField Ω z`。随后由两个下确界的
定义证明了 `domainSobolevENorm_le_sobolevENorm`，即
`zeroExtension Ω z` 给出域商范数的一个可容许延拓。

关键点是没有偷偷增加 `MeasurableSet Ω`：测试函数在 `Ωᶜ` 上逐点为零，
所以可用 `setIntegral_eq_integral_of_forall_compl_eq_zero` 把域积分化为全空间
积分，再按 `Ω.indicator` 的两个分支逐点比较。

## 2. Lean 里现在有什么

- `Section3/T22/Domain.lean`：从 canonical Section 4 D01 导入
  `IsSobolevDatum`/`sobolevENorm`，逐字重述 T22 的六个定义与三字段
  `BoundedDomainNormAPI`。
- `Section3/T22/RestrictBridge.lean`：上述 restriction bridge 和左侧范数不等式。
- `probes/api_on_canonical.lean`：Spec 六个定义到 canonical module 的 `rfl`
  检查，以及结构体的逐字段双向转换和往返检查；没有构造 API inhabitant。
- `probes/restrict_bridge_closes.lean`：半径 `1/2` 的非零光滑向量 bump，证明其
  紧支撑包含在 `ball 0 1`，并在该具体字段上实例化左侧不等式。
- `axioms_ub1.lean`：所有 canonical T22 声明和两个 U-B1 定理的公理审计；
  每项均恰为 `[propext, Classical.choice, Quot.sound]`。

## 3. 缺口是什么

U-B1 本身没有剩余缺口，也没有 named input、占位声明或额外假设。完整
`zeroExtensionComparison` 的右侧不等式仍按拆分计划依赖 U-A3 的 cutoff
multiplier、U-B2 的零延拓正则性与 U-B3 的 cutoff datum identity；`orderZero`
仍依赖 U-A4/U-A5。这些都在本 lane 范围外。

## 4. 跑了什么命令、什么结果

- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T22.RestrictBridge`：成功，0 errors。
- `lake env lean` 分别检查 `Domain.lean`、`RestrictBridge.lean`、两个 probe 和
  `axioms_ub1.lean`：全部成功，0 errors。
- `make check`：成功（exit 0）；合同政策 13 tests `OK`，work queue 检查通过。
- 禁止项扫描：新增 Lean 文件无 `sorry`、`admit`、`axiom`、`native_decide`
  或 `set_option maxHeartbeats`。
