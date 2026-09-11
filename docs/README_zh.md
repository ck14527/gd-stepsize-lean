# 中文使用说明

本仓库是论文 **[Optimal Recursive Composition and Dyadic Phase Laws for Gradient Descent with Predetermined Stepsizes](https://arxiv.org/abs/2609.11788)** 的 Lean 形式化代码。

**论文链接：**[arXiv:2609.11788](https://arxiv.org/abs/2609.11788) · [PDF 全文](https://arxiv.org/pdf/2609.11788)。形式化针对该论文的标量与组合结论，具体覆盖范围见[验证说明](VERIFICATION.md)。

已核验 **36/36 项编号标量／组合结论、569 个源码定理**，覆盖组合核、最优树、递推、相位律、正则性和精确有限网格证书。

工具链固定为 Lean 4.19.0，依赖版本由 `lake-manifest.json` 固定。验证范围从论文的标量递推和组合模型开始；外部光滑凸梯度下降证书接口不属于本形式化。

- [全部 36 项结论](THEOREMS.md)：逐项列出定理入口、源码和精确范围。
- [验证范围与复现说明](VERIFICATION.md)：公理检查、来源校验与数学对应关系。
- 数学依赖图和实际代码图：[DEPENDENCIES.md](DEPENDENCIES.md)。

复现命令见 [README](../README.md#reproduce-the-verification)。请查看所用 commit 在 Actions 中 `Lean proofs and audit` 的实际结果；每次运行的日志和审计附件随工作流保存。
