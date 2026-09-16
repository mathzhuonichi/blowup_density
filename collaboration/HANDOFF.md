# HANDOFF.md — 第 3 节工作包

当前 **S3-0**；[实时状态](../NEXT_SESSION.md)、[编号表](../PLAN.md#8-进度表)、[详细 DAG 与阶段](SECTION3_PLAN.md)。
所有新 lane 从 `erenup/integration-section3` 开 worktree，PR 以它为 base；按 [CLAUDE.md](../CLAUDE.md) 的陈述、审稿与门禁规则交付。

| 阶段 | 节点 | 工作包 | 可领取条件（claimable after） |
|---|---|---|---|
| S3-1 | T13 | 局部化、Gagliardo 核与一致常数 | T10 数据合同注册、T13 reconciliation/spec 定稿；双盲稿已完成 |
| S3-1 | T16 | 径向向量势、截断与背景消去 | T10 数据合同注册，T16 陈述审定 |
| S3-1 | T12 | 均值零微积分、谱隙、一致临界嵌入 | T10 数据合同注册，T12 陈述审定；不得用有限模常数替代 |
| S3-1 | T14 | 包导入、能量与零延拓 | T10 数据合同注册，T14 陈述审定；复用 I01.packet |
| S3-1 | T22 | 有界区域限制与零延拓范数 | T10 数据合同注册，T22 陈述审定 |
| S3-2 | T11 | 周期局部理论、Galilean 均值消去、唯一性/重启/延拓 | T10 注册、局部理论接口审定，由 lead 拆分主线 |
| S3-2 | T20 | 临界能量、bootstrap、H¹ 吸收与延拓 | T10/T11/T12 依赖已交付、接口审定，由 lead 拆分主线 |

S3-1 五个包在满足条件后互不依赖；T11/T20 的次序仍服从 DAG。提前做陈述准备不等于证明包已可领取。

外部协作预留 **300–399**，纯分析优先 T13/T12/T22，后续 T24a/b/c 按 DAG 分配。
lane 号全局唯一，由 lead 在 PLAN §8 登记后领取；当前下一号 **268**，不能自行占用外部预留号。

第 4 节 P1–P11 与历史交接见 [归档 HANDOFF](../archive/section4/HANDOFF_SECTION4.md)；
[归档索引](../archive/section4/README.md) 保留原计划、完整时间线和简报。交付分支 `erenup/integration` 冻结，PR #259 待 owner。
