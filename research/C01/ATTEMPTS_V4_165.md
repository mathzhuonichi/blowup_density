# C01 V4 组装尝试（lane 165）

## 已完成

独立盲稿与原 Spec 已协调为 V4 六字段，B 的 REVIEW_SPEC_165 为 ACCEPT，root 核对字段源文本一致。Root 转述 Luna 的两盲稿 typecheck 均为 0。A 首次失败因 `ν⁻²` 不是 Lean 记号，仅改成 `(ν⁻¹) ^ 2` 后重验通过；此修复没有改变数学内容或独立盲稿过程。

新 `Bindings/EnergyAbsorptionV4.lean` 用 frozen V3 witness 扩展，CRH1=2、CH2=16、Cassembly=32。六结果分别直连 C01 的同名实现定理；复用 `uniqueness_toA02` 和既有 `energyAbsorptionPartialV2_gradientSq_eq`。没有新规范定义镜像、没有改四个源模块。父投影 `energyAbsorptionPartialV3_of_v4` 用 rfl 保留 V3 原 witness。

新 `Tests/EnergyAbsorptionV4.lean` 包含 checked record、公理审计、父投影消费、六个逐字字段形状，以及 S=T 的 H² 下积分有限性消费者及其公理审计。旧 Tests 与 Contracts 不改。contracts.json 只新增 C01.energy_absorption_v4 条目，未重写原条目内容；JSON 解析成功。新 Lean 文件 LF 单末换行。

## 负向消费检查

未跟踪临时文件 `tmp/no_smallness_165.lean` 删除 terminal finiteness 消费者的 hsmall 参数，然后尝试同一 exact 应用。预期 typecheck exit 1，失败点应为缺失吸收前件造成的函数类型与目标不匹配。它验证此消费确实需要 hsmall，不声称无小量结论在数学上必假。该故意失败文件不进入 tracked proof/test。

结果：待 Luna high 验证；本代理未执行 Lean/lake。

## 待编译验证与语义桥

Bindings、Tests 和负向探针已就绪，交 Luna 编译。编译前不声称通过或标准公理闭包已确认。

B 的任意 datum 路径实积分表述与规范下积分的数学协调见 COMPARISON_165。当前 H2TimeIntegral 文件只直接输出下积分界，没有一个可直接短接的任意 datum 实积分消费者；未为此扩大公有 API。若后续需要研究消费者，须以 datum 唯一性、已有连续路径及真实范数桥推出可测性与积分转换，不增加额外路径正则性前件。

未 commit/push，未改 PLAN/NEXT_SESSION/CSV/work_items 或生成卡片。

## Lead verification update

Luna build of the new Tests module succeeded, including the full record,
parent projection and terminal consumer standard-axiom audits. Full lake test
completed all 27 registered contracts; the no-smallness probe failed exactly
for the missing absorption hypothesis; the mutation suite passed. Five original
Python checks and the regenerated in-review queue check passed. No author ran Lean.
