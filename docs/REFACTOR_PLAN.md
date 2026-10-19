# FalseTateExtension 重构方案（v1，全部定稿 2026-10-19）

> 状态：A–F 全部与作者逐项讨论定稿（2026-10-19）。执行按 §F 分阶段进行，每阶段一个分支，阶段内直接提交。
>
> 范围 = instruction.pdf §2 的六个目标。对应代码位置：
> (1) `K_{m,n}`, `K_FT`, `K_Kum`, `K_cyc` 的定义 → `Layers.lean`
> (2) 三者 strict APF → `StrictAPF.lean:640/661`，`Padic/CyclotomicAPF.lean:225/363`，`KummerProfile.lean:1033`
> (3) Liu Lemma 5.1.2 → `GaloisStructure.lean:883`（`K_Kum ∩ K_cyc = K`）、`:894`（半直积）、`:1112`（`Gal(K_FT/K_cyc) ≅ ℤ_p`）
> (4) 拓扑生成元 τ → `GaloisStructure.lean:767 tau`，刻画 `tau_extensionRadical :779`
> (5) `K = ℚ_p` 时 `K_FT` 完全分歧 → `Padic/FiniteGaloisStructure.lean:774/807`
> (6) Viviani Cor. 6.10 → `Padic/Viviani.lean`，**分散在 ~15 个定理里，没有单条总结语句；整数参数版本只有 ψ 表和上分歧群，缺下分歧群**
>
> 另有 `Padic/NormField{Ramification,Coordinates,Action}.lean`（1387 行）做的是 FalseTateLift Def 1.1 / Prop 2.2 / Prop 5.1 / Lemma 5.3，属于 instruction §3（FalseTateNonliftability），不在本项目范围内（见 A1）。

---

## 0. 现状数据（2026-10-19 实测）

| 指标 | 数值 |
|---|---|
| Lean 文件 | 35（34 个模块 + 根文件），全部平铺在 `FalseTateExtension/` 和 `FalseTateExtension/Padic/` 两层 |
| 总行数 | 13 836 |
| 声明数 | 878（其中 `private` 68） |
| **从未被其他文件引用的声明** | **650 / 878**（Viviani 83，GaloisStructure 57，KummerProfile 52，FiniteGaloisStructure 45，AffineIndex 30） |
| 全量干净编译（仅本项目 35 模块，20 核） | **6 min 44 s 墙钟，1115 s CPU** |
| 编译 > 40 s 的文件 | 5 个（见 C） |
| `set_option maxHeartbeats` / `synthInstance.maxHeartbeats` | 16 / 12（KummerProfile 10+10，CyclotomicUpper 3，RadicalRamification 2+2，CyclotomicAPF 1） |
| `letI` / `haveI` / `let :=` 局部实例 | 280 |
| 定理**陈述**里的 `letI := isAPF_falseTateExtension …` | 79（NormField* 三文件） |
| `let := cyclotomicBase_isCompleteDiscreteValuedField p K` 作为第一条 tactic | 45 |
| `local notation` 声明 | 50（`OK` 定义 7 次，`Qp` 3 次；`O(n)`、`G` 各有 2–3 种不同含义） |
| 显式 `(K := …)` | 885 |
| `(hπ : Irreducible π)` / `(hπ : π ≠ 0)` / `(hp₂ : p ≠ 2)` 显式参数 | 137 / 85 / 85 |
| 内联 `fun h => hπ.ne_zero (Subtype.ext h)` | 52 |
| `spectralIntegerRing K L` 手写 vs FW 记号 `𝒪[L]` | 119 / 0 |
| 文档填充词 actual / original / canonical / ordinary / intrinsic / literal | 536 / 296 / 89 / 48 / 21 / 14 |
| 引用不存在的 `blueprint` 的文件 | 21（仓库里没有 `blueprint/`；根文件还指向 `blueprint/src/content.tex`） |
| 引用 Liu / Viviani / Serre / Wintenberger 章节号 | Liu §5.1 ×11 文件；Viviani Cor 6.10 仅在 NormFieldRamification；**证明 Liu 5.1.2 和 Viviani 6.10 的两个文件本身都不引用原文** |
| `sorry` | 0 |
| 警告 | 0 |
| LICENSE / README / CLAUDE.md | **均不存在**（文件头声称 "as described in the file LICENSE"） |

---

## A. 全局设计决策（需先讨论）

### A1. 范围：NormField* 三个文件移出本项目　【已定稿 2026-10-19】

**决定**：直接删除（不进 Attic）`Padic/NormField{Ramification,Coordinates,Action}.lean`、`Padic/TameUnits.lean`、`Padic/TameGenerator.lean`（tame 部分对一般基域可能平凡，只在 `K = ℚ_p` 的 Lemma 5.3 起作用）以及 `Padic/KummerRamification.lean` 的 `section PadicLimit`（`d_k` 的 p 进极限，只有 FalseTateNonliftability 用）；**执行时修正**：`kummerTauFinite` 及其分歧数引理（`τ^{p^k}` 在 `K_{N,N}` 上的下分歧数为 `d_k`）是 `K_FT` 本身的分歧性质，按 E 节的数学判据留在本项目（归入 `FalseTate/Viviani/`）；内容在 FalseTateNonliftability（`~/FalseTateNonliftability`，其 `FieldOfNorms/` 目录）重做时按新 API 接入。该项目目前钉在本项目旧提交 `7d6876c` 和 FW 旧名（`NormLimit`），只 import 本项目 `Padic.CyclotomicRamification`、`Padic.KummerRamification`、`Padic.NormFieldAction` 三个模块，`FalseTate/TheoremA.lean` 是 NormField* 的唯一消费者。留下归位：对角层共尾性 4 条 → `Layers`；`not_finiteDimensional_falseTateExtension_padic` → `StrictAPF`；`padicUnitBallResidueEquiv` → `Padic/Basic`；`kummerRamificationBreak` → Viviani。上游 FW：`irreducible_of_normalizedValuation_eq_exp_neg_one`。FW（`~/FontaineWintenberger`）的 `Attic/` 8 个文件没有被两个下游项目引用或重复，暂不迁移；重做 FalseTateNonliftability 时再评估 `ResidueLayerComposite`、`RelativeStages`。

原始分析：

`Padic/NormFieldRamification.lean`（353）、`NormFieldCoordinates.lean`（524）、`NormFieldAction.lean`（510）证明的是 Yuan Prop 5.1 / Lemma 5.3 / Def 1.1 的内容（文件自己的 docstring 引用 "Yuan, Proposition 5.1 and Lemma 5.3"），依赖 FW 的 `FieldOfNorms`，属于 instruction §3。它们也是 79 处 "`letI` 进陈述" 的全部来源。

**建议**：整体迁到 FalseTateNonliftability 项目。留下并归位的只有：
- `not_finiteDimensional_falseTateExtension_padic` → `Layers`/`StrictAPF`
- `falseTateNormFiniteLayer` + `_mono` + `exists_le_…` + `_isGalois`（对角层的共尾性）→ `Layers`
- `padicUnitBallResidueEquiv` → `Padic/` 基础文件
- `irreducible_of_normalizedValuation_eq_exp_neg_one` → 上游 FW
- `KummerRamification.lean` 中 `kummerTauFinite`/`normalizedValuation_kummerTauFinite_displacement`：它们只被 NormField* 用，跟着走；`kummerRamificationBreak` 本身留下（Viviani 需要）。

**备选**：留在本项目但放入独立目录 `FieldOfNorms/`，并同样做 A3 的实例化。

### A2. 与 FontaineWintenberger 约定对齐　【已定稿 2026-10-19】

**决定**：
- A2.1 基域记号：`𝒪[K]`、`𝓀[K]` 全面替换手写项和 `OK`/`A`/`R`/`S`/`Zp₀`。
- A2.2 有限扩张整数环：**(b) 已试验失败，退回 (a)**（2026-10-19 F3）：Lean 4 拒绝 `[FiniteDimensional K L] → NontriviallyNormedField L` 形式的实例（"cannot find synthesization order: all remaining arguments have metavariables K"），`K` 不出现在结论里就无法作为实例。保持 `spectralIntegerRing K L`。原计划：先试 (b)，在 FW 补 scoped instance `[IsCompleteDiscreteValuedField K] [FiniteDimensional K L] → NontriviallyNormedField L`（FW 当前并无 `LocalField/Spectral/Instances.lean`，其自身 250 余处仍写 `spectralIntegerRing K E`），验证 `𝒪[L] = spectralIntegerRing K L` 为 rfl 且无 diamond 后两个项目改用 `𝒪[L]`；出问题则退回 (a) 保持 `spectralIntegerRing K L`。
- A2.3 `Padic/Basic.lean` 集中 ℚ_p 实例；有限 `K/ℚ_p` 的 `IsCompleteDiscreteValuedField` 改为 instance。
- A2.4 **保留显式 `(p : ℕ) [Fact p.Prime]`**，不用 `residueChar K`（项目始终在特征 0 的 p 进域上，`residueChar` 损害可读性）；边界上提供 `residueChar (Padic p) = p`、`residueChar K = p` simp 引理。

原始分析：

FW 的 `CLAUDE.md` 明确规定：用 `𝒪[K]`、`𝓀[K]`（scoped notation），**禁止**文件局部缩写 `OK`/`R`/`O`；`residueChar K` 代替穿参 `p`；有限扩张的整数环写 `𝒪[L]`（FW 实测与 `spectralIntegerRing K L` 为 `rfl`）；`IsAPF`/`IsStrictlyAPF` 是 class，不用 `letI`。本项目全部违反。

**建议**：
1. 全项目 `open scoped NormedField Valued NNReal FontaineWintenberger`；`Valuation.valuationSubring (NormedField.valuation (K := K))`（21 处）和 7 个 `OK` → `𝒪[K]`；`IsLocalRing.ResidueField 𝒪[K]` → `𝓀[K]`；`spectralIntegerRing K L`（119 处）→ `𝒪[L]`（需要 FW 的 `LocalField/Spectral` scoped instance，先验证 rfl）。
2. `Padic p` 的基础实例集中到一个文件 `Padic/Basic.lean`：`IsCompleteDiscreteValuedField (Padic p)`、`IsPerfectResidueLocalField (Padic p)`、`padicUnitBallEquiv : 𝒪[ℚ_p] ≃+* ℤ_[p]`、`residueChar (Padic p) = p`、`Infinite (ℤ_[p])ˣ`。目前这些散在 `CyclotomicRamification:36–56`、`CyclotomicResidueBound:36–55`、`CyclotomicInertiaCompletion:244`，而且 "`𝒪_K` 是 DVR / `K` 是完备 DVF" 有三份（`padicUnitBall_isDiscreteValuationRing`、`cyclotomicBase_unitBall_isDiscreteValuationRing`、`CyclotomicAPF:41` 的 local instance）。
3. `cyclotomicBase_isCompleteDiscreteValuedField`（对任意有限 `K/ℚ_p`，现在是 theorem 以免全局触发）改成 **instance**，消掉 45 处 `let :=` 和 13 条陈述里的 `letI`。名字去掉 "cyclotomicBase"（它跟分圆无关）。
4. `p` 是否也改成 `residueChar K`？本项目 `p` 同时是分圆层的素数，且 `K/ℚ_p` 有限时二者相等但不是定义相等。**建议保留显式 `p`**，但在 `Padic/Basic.lean` 给出 `residueChar (Padic p) = p` 的 simp 引理。—— 请确认。

### A3. 假设传递：`hπ`、`hp₂`、`IsAPF` 改为实例　【已定稿 2026-10-19】

**决定**：方案 (a)。
- 第一层（任意 `CharZero K`）：`(π : K) [NeZero π]`；`IsGalois K (falseTateLayer p π n n)`、`IsGalois K (falseTateExtension p π)` 为 instance；`finiteKummerExponent` 在 `π = 0` 取 junk value，定义不带 `hπ`。
- 第二层（`K/ℚ_p` 有限）：`(π : 𝒪[K]) [Fact (Irreducible π)]`；instance `NeZero (π : K)`（替代 52 处 `fun h => hπ.ne_zero (Subtype.ext h)`）、`IsAPF K (falseTateExtension p π)`、`IsStrictlyAPF K (falseTateExtension p π)`；同样对 `kummerExtension`、`cyclotomicExtension`。
- 奇素数：`[Fact (p ≠ 2)]`（对接 Mathlib `ZMod.isCyclic_units_of_prime_pow` 等取 `p ≠ 2` 的引理）。
- 只有 Prop-class 结论（`IsAPF`、`IsStrictlyAPF`、`IsGalois`）写成 instance。Liu 5.1.2 的同构（数据 `≃ₜ*`）、中间域等式、完全分歧（`e = finrank`、`f = 1`，Mathlib 与 FW 均无 `IsTotallyRamified` class）、Viviani 的分歧群等式都保持 `theorem`/`def`，只是假设从显式 `hπ hp₂` 变为 instance 参数 `[Fact (Irreducible π)] [Fact (p ≠ 2)]`。
- 主定理**不**另给显式假设版本；README 目标表直接引用 instance 参数版本。

原始分析：

现状：`(hπ : Irreducible π)` 137 次、`(hπ : π ≠ 0)` 85 次、`(hp₂ : p ≠ 2)` 85 次作为显式参数进入**数据定义**（`finiteKummerExponent p π n hπ g`、`affineGaloisHom p π hπ`、`tau p hp₂ hπ`、`finiteDiagonalGaloisEquiv_padic p hp₂ hπ n` …），于是每条引理陈述都要带 2–3 个证明参数；52 处手写 `fun h => hπ.ne_zero (Subtype.ext h)` 把 `Irreducible π` 降成 `π ≠ 0`。`IsAPF K K_FT` 是 theorem，于是 NormField* 里 79 条陈述以 `letI := isAPF_falseTateExtension p hπ` 开头。

**建议**（三选一，请拍板）：
- (a) **`Fact` 包装**：`[Fact (Irreducible π)]`、`[Fact (p ≠ 2)]`（或 `[Fact (Odd p)]`），同 Mathlib 的 `[Fact p.Prime]`。定义不再带证明参数；`instance [Fact (Irreducible π)] : IsAPF K (falseTateExtension p π)`、`IsStrictlyAPF` 同理；`Fact (¬ Module.Finite …)` 也做成 instance（与 FW A3 一致）。
- (b) 一个 bundled class `IsFalseTateDatum p π : Prop`（字段 `irreducible`、`ne_two`），`π` 仍是 `𝒪[K]` 的元素。
- (c) 保持显式参数，只做 `variable` 整理 + `Irreducible.coe_ne_zero` 引理。

倾向 (a)。`π ≠ 0` 层面的引理（`FiniteCoordinates`、`PadicCoordinates`、`AffineEmbedding`）给 `finiteKummerExponent` 在 `π = 0` 取 junk value，彻底去掉 `hπ`。

### A4. 仿射群只定义一次　【已定稿 2026-10-19】

**决定**：新建 `Affine/Group.lean`，`AffineGroup A H := A ⋊ H`（`H ≤ Aˣ`），四个群都是实例化。拓扑用方案 **(b)**：在 `Mathlib/` 上游层给 Mathlib 的一般 `N ⋊[φ] G` 写 `TopologicalSpace`（积拓扑）/ `IsTopologicalGroup` / `T2Space` / `CompactSpace` 实例（假设作用连续），而不是经 `≃ A × H` 转移。交换子公式、`mem_range_inl_iff`、`translationKernel` 各写一次。

原始分析：

`PadicAffineGroup`（`AffineEmbedding:37–81`）、`RestrictedPadicAffineGroup`（`GaloisStructure:542–595`，逐行拷贝）、`FiniteAffineGroup`/`FullFiniteAffineGroup`（`FiniteGaloisStructure:197/201/295`，`ZMod (p^n)` 版）是同一构造的三份；`padicAffine_commutator_inl` / `finiteAffine_commutator_inl` / `finiteAffine_commutator_two`、六份 `*_mem_translations/_mem_units` 随之重复。

**建议**：新文件 `Affine/Group.lean`：`def AffineGroup (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (H : Subgroup Aˣ) := A ⋊[…] H`，一次给出拓扑、`T2Space`、`IsTopologicalGroup`、`CompactSpace`、`continuous_inl/inr/left/right`、交换子公式、`range_inl_eq_ker_rightHom`。四个群都是实例化。`AffineCommutator.lean` + `AffineIndex.lean` 的 `PadicInt` 部分 + `Padic/ClosedAddSubgroup.lean` 组成不依赖域论的 `Affine/` 子目录。

### A5. 上游层 `FalseTateExtension/Mathlib/`　【已定稿 2026-10-19】

**决定**：
- A5.1 建 `FalseTateExtension/Mathlib/`（规则同 FW）。A1 之后清单去掉 Teichmüller（随 `TameUnits` 走）和 `PowerSeries` jet（随 `NormFieldAction` 走），增加 A4(b) 的一般半直积拓扑实例。
- A5.2 改用 Mathlib：`FiniteCharacter.lean:65–120` → `IsCyclotomicExtension.autEquivPow`（已核实 `Gal.lean:77`）+ `IsPrimitiveRoot.autToPow_eq_modularCyclotomicCharacter`（`CyclotomicCharacter.lean:243`）；`card_cyclotomicLayer_character_units`、`Padic.minpoly_primitive_root`、`Padic.finrank_adjoin_primitive_root` 删除。记入 `docs/MATHLIB_REUSE.md`。
- A5.3 应进 FW 的引理**本轮直接在 FW 改**（FW 开分支，本项目升级依赖 rev；与 A2.2 的 scoped instance 同一次升级）。

原始分析：

与 FW 相同：Mathlib 命名空间、零项目依赖、文件头注明 upstream candidate。候选（已核实 Mathlib 无对应物）：

| 内容 | 现位置 | 目标 |
|---|---|---|
| `PadicInt.continuous_of_toZModPow` | AffineEmbedding:85 | `Mathlib/NumberTheory/Padics/Continuity.lean` |
| 闭加法子群 = `⊥` 或 `(p^s)`，`relIndex` 计算 | Padic/ClosedAddSubgroup + AffineIndex:25–86 | `Mathlib/NumberTheory/Padics/ClosedAddSubgroup.lean` |
| Teichmüller 提升（Hensel 版，应说明与 `Perfection.teichmuller₀` 的关系） | Padic/TameUnits | `Mathlib/NumberTheory/Padics/Teichmuller.lean` |
| `Φ_{p^n}(X+1)` 在 `ℤ_p` 上 Eisenstein、`cyclotomic (p^n) ℚ_p` 不可约、`finrank` | Padic/Cyclotomic:35–140 | `Mathlib/NumberTheory/Padics/Cyclotomic.lean` |
| `X^m - C π` Eisenstein / 不可约 | RadicalRamification:31–85 | `Mathlib/RingTheory/Polynomial/Eisenstein/…` |
| `ZMod.unitsMap` 核的指数/基数 | CyclotomicUpper:254–285 | `Mathlib/Data/ZMod/Units.lean` |
| `cyclotomicCharacter_eq_of_intertwines`（自然性） | GeneralCharacter:35 | `Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean` |
| `range_restrictScalarsHom_eq_fixingSubgroup`、`index_range_restrictScalarsHom`、`continuous_restrictScalars_of_isAlgebraic`、`relativeGaloisFixingKrullEquiv`、四条无限 Galois 对应引理（StrictAPF:31，GaloisStructure:37/506/856） | 散落 | `Mathlib/FieldTheory/Galois/Infinite.lean` |
| `IntermediateField.restrictNormalHomOfLE` + `_commutes` + `_surjective`（替代 25 处 `RingHom.toAlgebra (Subsemiring.inclusion …)` + 27 处 `IsScalarTower.of_algebraMap_eq (congrFun rfl)`） | CoordinateTransitions / PadicCoordinates / CyclotomicImage / CyclotomicInertia / InfiniteCharacter / FiniteGaloisStructure | `Mathlib/FieldTheory/Normal/…` |
| `IntermediateField.mem_iSup_of_monotone`（三份 `coe_iSup_of_directed` 套路） | Layers | `Mathlib/FieldTheory/IntermediateField/Adjoin/…` |
| `iInf_sup_closed_normal`、`index_sup_le_index_sup_mul_relIndex` | KummerProfile:650，AffineIndex:492 | `Mathlib/GroupTheory/Index.lean` / `Topology/Algebra/Group/…` |
| `powerBasis_eigenvector_eq_smul_pow` | GaloisStructure:195 | `Mathlib/RingTheory/PowerBasis.lean` |
| `PowerSeries` 一阶 jet 引理（`section FiniteJets`） | NormFieldAction:33–152 | 随 A1 走，或 `Mathlib/RingTheory/PowerSeries/Substitution.lean` |

**直接改用 Mathlib 已有结果**（删本项目重证）：
- `FiniteCharacter.lean:65–120`（基数论证 `Gal ≅ (ZMod p^n)ˣ`）→ `IsCyclotomicExtension.autEquivPow` + `IsPrimitiveRoot.autToPow_eq_modularCyclotomicCharacter`；前提 `cyclotomicLayer_padic_isCyclotomicExtension`、`Padic.irreducible_cyclotomic_prime_pow` 已有。
- `card_cyclotomicLayer_character_units` = `ZMod.card_units_eq_totient`；`Padic.minpoly_primitive_root` = `IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible`；`Padic.finrank_adjoin_primitive_root` = `IsCyclotomicExtension.finrank`。

**上游到 FW**：`apfSubgroup_iSup_eq_iInf`、`finite_totalRam_apfSubgroup_index`（KummerProfile:688/707）、`apfSubgroup_map_eq_comap_upper_infinite`（StrictAPF:259）、`viviani_inverse_affine`（"指数常值区间上 ψ 仿射"）、`viviani_lower_parameter`、`compatibleSpectralIntegerRingEquiv`、`finite_spectralResidue_padic`/`isCyclic_rationalResidueGaloisImage`/`commutator_mem_inertia_padic`/`fixingSubgroup_sup_inertia_index_eq_residueDegree_padic`（FiniteGaloisStructure:552–592，对任意有限剩余域局部域成立）。

### A6. 命名方案　【已定稿 2026-10-19】

**决定**：下表全部采纳，其中 `radical → pPowRoot`、`rootOfUnity → zeta`、四/六个同元素名合并为 `pPowRoot*` / `zeta*` 一套、新定义 `falseTateDiagonalLayer`、`abbrev FalseTateGaloisGroup`、`tau → kummerGenerator`（并在 `FalseTate/` 命名空间下提供 `scoped notation "τ" => kummerGenerator p π`，因文献约定俗成叫 τ；`relativeTau → kummerGeneratorRel`）、两个 `*Coordinates` 先定义再谈单射、`affineIndex_comparison` 与 `inverseHerbrandFunction_falseTate_integerParameter` 拆分、`∧` 结论拆分、`kummerRamificationBreak_*` 14→5、instance 统一匿名。A1/A3 之后 `normLimit*`、`kummerTauFinite`、`hp₂` 三行不再适用。

原始分析：

通用规则：Mathlib 约定（def lowerCamelCase，定理 snake_case，类型 UpperCamelCase，结论进名字）；去掉 `actual/original/full/…`；**同一对象只有一个名字**。

| 现名 | 问题 | 建议 |
|---|---|---|
| `radical p π n` | 与 `Ideal.radical` 撞词 | `pPowRoot p π n`（或 `radicalSeq`） |
| `rootOfUnity p n` | 与 `rootsOfUnity` 撞词 | `zeta p n`（或 `primRoot`） |
| `radical` / `layerRadical` / `radicalLayerRoot` / `extensionRadical`（同一元素在 4 个域里） | 四个名字 | 统一 `pPowRoot` + 后缀标明所在域：`pPowRoot`、`pPowRootLayer`、`pPowRootExt` |
| `rootOfUnity` / `layerRootOfUnity` / `cyclotomicLayerRoot` / `cyclotomicRootOfUnity` / `extensionRootOfUnity` / `cyclotomicLayerRootOver` | 六个名字 | 同上 `zeta*` |
| `falseTateLayer p π n n`（"对角层"，~20 个名字含 diagonal） | 没有定义 | `def falseTateDiagonalLayer p π n`，并消掉 Viviani 的 `D(n)`（带 `n+1` 偏移）和 `falseTateNormFiniteLayer` |
| `falseTateExtension p π ≃ₐ[K] falseTateExtension p π`（手写 ~30 次 + `Γ` 记号） | | `abbrev FalseTateGaloisGroup p π` |
| `tau` / `relativeTau` | 无内容 | `kummerGenerator` / `cyclotomicRelativeKummerGenerator`；docstring 写出 `τ(π^{1/p^m}) = ζ_{p^m} π^{1/p^m}` |
| `hp₂ : p ≠ 2` | 读作"第二个 p 假设" | `hp2` / `hp_ne_two`，或按 A3 变成 `[Fact (p ≠ 2)]` |
| `finiteAffineTwo` | 是 `(ZMod p^n)ˣ` 里的 2 | `ZMod.unitTwo` |
| `fullKummerKernelEquiv` / `kummerKernelEquiv` / `fullKummerKernelMulEquiv` | "full" 编码的是 `affineAdditiveKernel = ⊤` | `kummerKernelEquivPadicInt` 等 |
| `falseTateAffineEquiv`（StrictAPF）vs `falseTateGaloisEquiv`（GaloisStructure） | 两条不同定理，名字几乎相同 | `falseTateGaloisEquivAffineImage` / `falseTateGaloisEquivSemidirectProduct` |
| `affineAdditiveKernel` / `affineTranslationKernel` / `affineTranslationIntersection` | 同一构造三份 | 统一 `affineTranslationKernel` |
| `affineZeroStabilizer` | 不是零的稳定子 | `affineTranslationStabilizer` |
| `cyclotomicLayerRestriction`（InfiniteCharacter）/ `cyclotomicRestrictionToLayer`（CyclotomicInertia） | 同一映射两份（前者是 `K = ℚ_p` 特例） | 删前者 |
| `cyclotomicLayerCharacter`（ℚ_p）/ `cyclotomicLayerCharacterOver`（一般 K，`_padic` 版 `rfl`） | 同一定义 | 删 ℚ_p 版，去掉 `Over` |
| `padicCyclotomicCharacter` / `cyclotomicExtensionCharacter` | 同一 body | 一个 `intermediateFieldCyclotomicCharacter L` |
| `cyclotomicBase_*` | 与分圆无关，是任意有限 `K/ℚ_p` 的性质 | `Padic.*` / 实例匿名 |
| `padicUnitBall_*` | Mathlib 词汇是 `valuationSubring` | `Padic.valuationSubring_*` |
| `normLimit*`（6 个，NormFieldRamification） | FW 已无 `normLimit` API，且 CLAUDE.md 禁用该词 | `FieldOfNorms.*` / 随 A1 迁出 |
| `kummerTauFinite` | 不描述对象 | `tauPowRestrict` |
| `kummerRamificationBreak_*` 14 条引理 | 可压到 5 条 | 见 C |
| `viviani_fraction_pos_lt_one`、`viviani_first_break` 等 `viviani_*` | 名字不含陈述 | 按内容命名；见 Viviani 拆分 |
| `*_fractional` vs `*_fractional_integer`（上/下分歧群各一对） | 一个是"在断点处的值"，一个是"区间上的值" | `_at_fractionalBreak` / `_on_Ioc_…` |
| `finiteCoordinates_injective` / `padicCoordinates_injective` | 没有 `finiteCoordinates` 这个声明 | 先定义 `finiteCoordinates : Gal → ZMod × (ZMod)ˣ` |
| `affineIndex_comparison`（两个 ∃ + 四重 ∧） | 不可用 | 拆成三条，常数给名字 |
| `inverseHerbrandFunction_falseTate_integerParameter`（`let` 进陈述 + 三重 ∧） | 不可用 | 拆成三条 |
| 实例命名 `radicalLayer_finiteDimensional`（snake）vs `padicAffineT2Space`（camel） | 不一致 | 统一匿名或 `inst…` |
| 文件名 `CyclotomicInertiaCompletion`、`CyclotomicUpper`（560/631 行是下分歧群）、`GeneralCharacter`、`TameUnits`（内容是 Teichmüller） | 名不副实 | 见 B |

### A7. `local notation` 政策　【已定稿 2026-10-19】

**决定**：
- 删除：`OK`/`A`/`R`/`S`/`Zp₀`（→ `𝒪[K]`）、`O₀ O₁ B₀ B₁ O(n)`（→ `𝒪[E]` 或 `spectralIntegerRing K E` + section 变量）、`F₀ F₁ M₀ M₁ L(n)`（→ section `variable (E F) (hEF : E ≤ F)`）、`Γ`/`G`/`G(n)`（→ `FalseTateGaloisGroup p π`、`Gal(·/·)`）、`Qp`（→ Mathlib 记号）。
- 变成定义：`eK → absoluteRamificationIdx K`、`δ → vivianiOffset p`、`D(n) → falseTateDiagonalLayer p π n`、`Ψ(n)` 内联；`FT/NX/κL/L/X` 随 A1 走。
- 保留为 section 内 `local notation`：`Cyc`、`v(n)`；并在 `CyclotomicResidueBound`/`CyclotomicInertia` 新增分圆层记号。
- **全项目改用 Mathlib 记号 `ℚ_[p]`、`ℤ_[p]`**（替换 `Padic p` 816 处、`PadicInt p` 约 250 处）。
- 规则写入 CLAUDE.md：local notation 只在 section 内、只用于证明体，不进公开陈述；scoped/全局记号（`τ`、`𝒪[K]`、`ℚ_[p]`）作为命名定义的显示形式不受此限；一文件内不重定义，跨文件同对象同名；出现在两个以上公开陈述里的项必须是 `def`/`abbrev`。

原始分析：

现状 50 条；真正帮助可读性的只有 `CyclotomicUpper`/`CyclotomicAPF` 里的 `L(n)`、`O(n)`、`v(n)`、`Cyc`、`StrictAPF` 的 `Γ`。其余问题：
- `OK`（7 次，每次 `K` 不同）、`A`、`R`、`S`、`Zp₀` → 全部换 FW 的 `𝒪[·]`。
- `F₀ F₁ O₀ O₁`（RadicalRamification 与 KummerProfile 各一份）、`M₀ M₁ B₀ B₁` → section `variable (E F : IntermediateField …) (hEF : E ≤ F)`。
- `eK`（KummerProfile）→ `def absoluteRamificationIdx K : ℕ`；它想服务的公开定理里反而把项写全了，证明记号已失效。
- `δ`、`Ψ(n)`（Viviani）出现在**公开定理的陈述**里，下游（`KummerRamification:338`）只能手工展开 → `def vivianiOffset p : ℝ := 1/(p-1)` 或内联。
- `D(n)`（Viviani，含 `n+1` 偏移）→ A6 的 `falseTateDiagonalLayer`。
- `O(n)`：CyclotomicUpper 指分圆层整数环，Viviani 指 false Tate 层整数环；`G`：三个文件三种含义；`Qp` 三份；`L`/`FT` 与 `X`/`NX`：同一对象在互相 import 的三文件里各叫一个名字。
- 两个值得**新增**记号的文件：`CyclotomicResidueBound`/`CyclotomicInertia` 把 `cyclotomicLayer (K := K) p (n + 1)` 写了 15/24 次。

**规则**：记号只允许出现在证明里，不进公开陈述；一个文件内不重定义；跨文件同对象同名，放到 `Layers.lean` 的 `scoped notation`（`Qp`、`Γ`）。

---

## B. 目录结构　【已定稿 2026-10-19，树按 A1 调整：去掉 NormField*/TameUnits/TameGenerator，`KummerRamification` 压缩为 `FalseTate/Viviani/KummerBreak.lean`，`Affine/Finite.lean` 收 Viviani:155–412】

```
FalseTateExtension/
  Mathlib/                     A5 上游候选，零项目依赖
    NumberTheory/Padics/{Continuity,ClosedAddSubgroup,Teichmuller,Cyclotomic}.lean
    RingTheory/{Eisenstein,PowerBasis}.lean
    FieldTheory/{RestrictNormal,InfiniteGalois,IntermediateFieldSup}.lean
    GroupTheory/Index.lean
    Data/ZMod/Units.lean
  Padic/
    Basic.lean                 ℚ_p 的 FW 实例、𝒪[ℚ_p] ≃ ℤ_[p]、residueChar、Infinite ℤ_pˣ   (A2.2)
    Tame.lean                  tameGenerator（Teichmüller 本身去 Mathlib/）
  Affine/                      不依赖域论                                            (A4)
    Group.lean                 AffineGroup A H + 拓扑 + 交换子
    ClosedSubgroup.lean        AffineCommutator + AffineIndex 的仿射部分
    Index.lean                 affineIndex_comparison 拆分后的三条
    FiniteNormal.lean          Viviani:155–412（ZMod 版子群动物园）
  Layers/
    Tower.lean                 通用 adjoinSeq（x (n+1)^p = x n 生成的塔）—— 现在 radical/cyclotomic 两份逐条相同
    Basic.lean                 pPowRoot/zeta/三种层/三种无限扩张/对角层/共尾性   ← Layers + GaloisLayers + CoordinateTransitions 的 6 条幂引理 + StrictAPF:104 + NormFieldRamification 的对角层引理
  Coordinates/
    Finite.lean                FiniteCoordinates（去 hπ）
    Padic.lean                 PadicCoordinates + CoordinateTransitions 剩余（后者只有 3 个被用的声明）
    AffineEmbedding.lean       AffineEmbedding 的 Galois 部分
    AffineImage.lean           StrictAPF:54–250（AffineImage 节）+ AffineKernel + CyclotomicImage 的分解部分
  Cyclotomic/                  对 Padic/ 里 13 个文件的重组
    Basic.lean                 ← Cyclotomic 余部 + cyclotomicLayerRoot/IsCyclotomicExtension 实例
    Ramification.lean          ← CyclotomicRamification:82–250
    Character.lean             ← FiniteCharacter（autEquivPow 版，~60 行）+ InfiniteCharacter:96–200 + GeneralCharacter:127–201
    Restriction.lean           ← CyclotomicInertia:36–196（通用 K 的限制映射；替代 InfiniteCharacter:33–94）
    CyclicLayers.lean          ← GaloisStructure:31–192（奇素数分圆群循环、第一个非平凡层）
    LowerFiltration.lean       ← CyclotomicUpper:42–400（大部分 private）
    Herbrand.lean              ← CyclotomicUpper:428–545
    UpperFiltration.lean       ← CyclotomicUpper:546–631 + CyclotomicAPF:45–230
    ResidueBound.lean          ← CyclotomicResidueBound:36–244
    Inertia.lean               ← CyclotomicInertia:198–414 + CyclotomicInertiaCompletion:45–240
    APF.lean                   ← CyclotomicAPF:234–632
  Kummer/
    Eisenstein.lean            ← RadicalRamification:87–360（层的次数/分歧指数/不同式）
    StepProfile.lean           ← RadicalRamification:362–457 + KummerProfile:29–154（合并，去掉 SeparableTower）
    Breaks.lean                ← KummerProfile:426–476 + absoluteRamificationIdx
    FiniteProfile.lean         ← KummerProfile:478–646
    APF.lean                   ← KummerProfile:678–1046
  FalseTate/
    RadicalNotCyclotomic.lean  ← GaloisStructure:193–430（117 行的 radical_one_not_mem_cyclotomicExtension 拆三段）
    TranslationKernel.lean     ← GaloisStructure:433–538, 695–860（affineAdditiveKernel_eq_top, τ）
    LiuLemma.lean              ← GaloisStructure:861–1205（Liu 5.1.2 三条 + τ 刻画；References 块）
    StrictAPF.lean             ← StrictAPF:253–678
    FiniteGaloisStructure.lean ← FiniteGaloisStructure:139–455（注意：这一节是一般 CharZero K，不该在 Padic/ 下）
    TotalRamification.lean     ← FiniteGaloisStructure:456–818（目标 (5)）
    Viviani/
      RadicalDepth.lean        ← Viviani:39–158
      UpperGroups.lean         ← Viviani:413–610
      HerbrandTable.lean       ← Viviani:612–858
      LowerGroups.lean         ← Viviani:859–1147
      Corollary.lean           ← Viviani:1149–1200 + 补齐下分歧群 + 一条 `viviani_corollary_6_10`（目标 (6)）
    KummerBreak.lean           ← KummerRamification:27–150 压缩后
FalseTateExtension.lean        每层一个聚合文件；docstring 列出六个目标对应的声明
```

分层导入规则（与 FW 相同，脚本检查）：`Mathlib` → `Padic`,`Affine` → `Layers` → `Coordinates` → `Cyclotomic`,`Kummer` → `FalseTate`。
关键收益之一：`GaloisStructure` 现在 import `StrictAPF`（从而整个 APF 栈），实际只用 `AffineImage` 节的 4 个声明；拆开后 Liu 5.1.2 不再依赖 APF。

死代码处理：**删除**还是像 FW 一样移到 `Attic/`？—— 请选择。

---

## C. 编译性能（已定位到声明）　【已定稿 2026-10-19】

**决定**：目标线 **单文件 < 30 s，全量 < 4 min，`set_option maxHeartbeats`/`synthInstance.maxHeartbeats` 归零**。CI 不做编译时间硬检查，只在每阶段结束把各模块耗时记录到 `docs/BUILD_TIMES.md`。修法按下表执行。


全量 1115 s CPU，前五个文件占 320 s：

| 文件 | 秒 | 实测根因 | 修法 | 预期 |
|---|---|---|---|---|
| `KummerProfile` | 120 | profiler：`typeclass inference of Semiring/CommSemiring/Module.Free/Module.IsTorsionFree` 每次 2–3 s；根源是 `radicalSeparableLayer = (radicalLayer …).map radicalClosureEmbedding`，`IntermediateField.map ∘ fieldRange ∘ spectralIntegerRing` 的 coercion 塔每次重新 defeq。10 对 `maxHeartbeats` 全在 `SeparableTower` 节（两处挂在 `IsScalarTower.of_algebraMap_eq fun _ => rfl`、`Module.Finite.right` 这样的平凡实例上） | 删 `section SeparableTower`（:155–423，是 `PrimeStep` 节沿嵌入的逐字重证），改为在无限节顶部用一次 `apfIndex_algEquiv`/`apfPsi_algEquiv` | < 20 s，去掉 20 个 `set_option` |
| `CyclotomicUpper` | 67 | 截掉 :428 以后 → 34.6 s；即三条 `maxHeartbeats` 定理（:440 `integral_cyclotomic_lower_slope`、:487 `herbrandFunction_cyclotomic_threshold`、:544）占 32 s；前半 34 s 是 lower-group 的 `simp` 链（:204 `simp; norm_cast` 等 5 处非终结 simp） | 积分计算拆成"区间上 card 常值"引理 + 一次 `intervalIntegral.integral_const`；lower 节加记号、`simp only` | ~15 s |
| `CoordinateTransitions` | 46 | **bisect 确认**：删掉 `finiteLayerRestriction_comp` 的 calc 首步 `:= rfl`（:106）→ 2.8 s。`finiteLayerRestriction` 经 `finGaloisGroupMap ((homOfLE …).op)).hom.hom`（范畴论绕路）定义，kernel 要把它 unfold 到 `restrictNormal` 才能判 `rfl`，花 35 s 在 "type checking" | 直接定义为 `AlgEquiv.restrictNormalHom`（文件下一条引理本来就证明二者相等），删 `finiteGaloisLayer`、`open CategoryTheory` 和 `Galois.Profinite` import；`_refl`/`_comp` 变成免费 | ~3 s |
| `PadicCoordinates` | 46 | `infiniteLayerRestriction_comp` :83 有同样的 `:= rfl` calc 步（同一模式，未单独 bisect） | 同上 | ~3 s |
| `RadicalRamification` | 41 | 截掉 `section Relative`（:361–455）→ 6 s；两条 `maxHeartbeats` 定理的**陈述**里各带一条 `letI` 链（`Algebra F₀ F₁`、`IsScalarTower`、`spectralValuation_hasExtension_tower`），证明里再建一遍 | 合并进 `Kummer/StepProfile.lean`，实例提升为 section 级 `local instance` | ~8 s |

其他系统性问题：
- `let := cyclotomicBase_isCompleteDiscreteValuedField p K` 45 次（A2.3 解决）。
- 79 条陈述里的 `letI := isAPF_falseTateExtension`（A1/A3 解决）。
- `unfold X; infer_instance` 作为 instance 体：`Layers:78/154/218`、`GaloisLayers:116`、`FiniteCoordinates:227`、`CyclotomicInertia:236–246`、`CyclotomicInertiaCompletion:193/205` → `inferInstanceAs` 或把 def 改 `abbrev`。
- `have : NeZero (p ^ n) := ⟨…⟩` 重建 12 次 → 一个全局 instance。
- `have := falseTateExtension_isGalois …` / `falseTateLayer_isGalois …` 在 ~15 个证明里重建 → section `local instance`（A3 后可直接是 instance）。
- `cyclotomicLayer_spectral_residueDegree_le`（ResidueBound:169–244，77 行）：前 50 行是 9 个 `let :` 实例构造（两个手写 `NormedAlgebra` 结构、两个 `HasExtension`、三次 `IsDiscreteValuationRing`）→ 提到 section。
- `nlinarith`：`AffineIndex:438`（实为 `mul_comm`）、`FiniteGaloisStructure:447`（实为 `Nat.eq_of_mul_eq_mul_right`）、`RadicalRamification:453`/`KummerProfile:309,833`（ℕ 截断减法，改在 ℤ 算）、`KummerRamification:27–150` 的 9 处 → 随 14→5 压缩消失。
- `convert`：7 处，其中 `InfiniteCharacter:82` 与 `CyclotomicInertia:81` 是同一段 24 行连续性证明的两份拷贝。
- `exact_mod_cast (Fact.out : p.Prime).one_lt` 18 次 → 一条引理。
- `linarith [Nat.cast_nonneg (α := ℝ) i]` 在 Viviani 里 ~20 次 → section 级 `have`。

目标：**单文件 < 30 s，全量 < 4 min；`set_option maxHeartbeats` 归零**。

---

## D. 文档　【已定稿 2026-10-19】

**决定**：D.1 填充词归零并重写 docstring 为数学陈述；D.2 **blueprint 不恢复，删除全部 21 处 `ft:` 引用和根文件指针**，以 README 目标表 + 根文件 docstring 代替（leanblueprint 可作重构后的独立任务）；D.3 Mathlib 模块 docstring 模板 + `## References`；D.4 补 18 条 docstring；D.5 新增 `README.md`、`CLAUDE.md`、`LICENSE`（从 FW 复制）、`docs/MATHLIB_REUSE.md`、`docs/BUILD_TIMES.md`；D.6 根目录 `*.pdf` 加入 `.gitignore`，README 注明所需文献。


1. **填充词归零**：actual 536 / original 296 / canonical 89 / ordinary 48 / intrinsic 21 / literal 14 / prescribed / genuinely / corrected 以及 section 名 `ActualUpper`、`ActualGenerator`、`ActualNormField`、`OriginalCoordinates`。第一遍脚本删词，第二遍逐条重写为**陈述数学内容**（现在大量 docstring 只描述证明策略或 Lean 编码细节，如 "stated without truncated subtraction"、"never uses its missing-roots branch"、"rather than an isomorphic auxiliary copy"、"No nontriviality of `ZMod 1` is needed"、"Openness is a conclusion"）。
2. **删除 21 处 `blueprint ft:…` 引用**和根文件的 `blueprint/src/content.tex`（仓库没有 blueprint）。是否要重建 leanblueprint？instruction §4(4) 要求有 blueprint 和 DAG —— 请决定：(a) 不恢复，只删引用；(b) 恢复一个最小 blueprint，`\lean{}` 宏真正对应声明名并用 CI 校验。
3. 每个模块 docstring 用 Mathlib 模板：`# 标题` / 一段数学陈述 / `## Main results` / `## References`。必须补引用的文件：Liu Lemma 5.1.2（`FalseTate/LiuLemma`）、Viviani Cor 6.10 + FalseTateLift Rem 5.2（`Viviani/*`，目前**一次都没引**）、Wintenberger 1.2.3 / Serre IV（Kummer、Cyclotomic）。
4. 补 18 条缺失的 instance/def docstring（清单见审计记录）。
5. 新增 `README.md`（目标表：六个目标 ↔ 声明名，像 FW 的那张表）、`CLAUDE.md`（约定：`𝒪[K]`、无 `letI`、无 `set_option`、单文件 < 30 s、填充词黑名单）、`LICENSE`（文件头已声称 Apache 2.0 但文件不存在）。
6. `docs/MATHLIB_REUSE.md`：记录 A5 里"改用 Mathlib"的决定，避免再次重证。

---

## E. 死代码与接口收缩　【已定稿 2026-10-19】

**决定**：不设 `Attic/`。判据（数学判断）：是 false Tate 扩张 / 其子扩张本身的性质（如 `Gal(ℚ_p^cyc/ℚ_p) = ℤ_p^×`）→ 留在本项目；是 FalseTateLift 才需要的 → 迁 FalseTateNonliftability；只是中间包装/重索引/`∧` 打包/被更强结果取代 → 删除。删除前已核对 FalseTateNonliftability 未使用。
- 保留：`cyclotomicExtensionGaloisEquivUnits`、`cyclotomicImageEquiv`、`kummerKernelEquiv`、`herbrandFunction_falseTate_*` ×3、`cyclotomic_inertia_finiteIndex`/`_index_le`、`not_finiteDimensional_cyclotomicExtension_padic`、`residueChar_padic`。
- 随 A1 迁到 FalseTateNonliftability（那边在用）：`KummerRamification` 的 `section PadicLimit` 四条、`falseTateNormFieldLaurentEquiv_unique`；`relativeTameGenerator`、`orderOf_tameGenerator` 随 `TameGenerator` 走。
- 删除：`affineProjectionEquivOfTranslationKernelEqBot`+simp、`AffineCommutator:159–261`、`cyclotomicLayerGaloisEquivUnits`、`CyclotomicResidueBound:246–336`、`exists_ne_one_mem_cyclotomicInertiaCharacterImage`、`Layers` 的 `*_eq_iSup_succ` ×3 与 `mem_falseTateExtension_iff_pos`、`exists_compatible_roots`、`cyclotomicExtensionCharacter_index_bounds`、`finiteTranslationSubgroup_card`、`cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt_of_pos`、`span_cyclotomicUniformizer`、`closedAddSubgroupIdeal_toAddSubgroup`、`closedAddSubgroup_map_mulLeft_relIndex_pos`。
- E.2 合并、E.3 `private` 化、E.4 陈述形状与目标缺口按原文执行。

原始分析：

- 650/878 声明从未被其他文件引用。原则：**终结性结果**（六个目标 + 它们的直接刻画）保持公开；其余标 `private`（估计 ~450 条），或者删除。
- 已确认**整段无用**（删除/Attic，约 600 行）：`CyclotomicImage:196–236 cyclotomicImageEquiv`；`AffineKernel:113–134 kummerKernelEquiv`；`AffineIndex:617–641 affineProjectionEquivOfTranslationKernelEqBot`；`AffineCommutator:159–261`（被 `AffineIndex` 的统一界取代的旧论证）；`FiniteCharacter:95–126 cyclotomicLayerGaloisEquivUnits`；`InfiniteCharacter:172–197 cyclotomicExtensionGaloisEquivUnits`；`CyclotomicResidueBound:246–336`（90 行，终点 `cyclotomicLayer_residueDegree_le` 无人用）；`TameGenerator:142–175 relativeTameGenerator`；`KummerRamification:150–230 section PadicLimit`；`Viviani` 的 `herbrandFunction_falseTate_*` 三条、`finiteTranslationSubgroup_card`；`Layers` 的 `*_eq_iSup_succ`/`mem_*_iff_pos` 四条；`CompatibleRoots.exists_compatible_roots`；`GeneralCharacter.cyclotomicExtensionCharacter_index_bounds`；`Cyclotomic:95`、`CyclotomicRamification:194`、`ClosedAddSubgroup:54/117`、`TameGenerator:55`。
- 逐字重复（合并，约 700 行）：A4 的三个仿射群；`KummerProfile.SeparableTower`（350）；`InfiniteCharacter:33–94` ≡ `CyclotomicInertia:41–93`（65）；`Layers` 的 radical/cyclotomic 两塔 + `CoordinateTransitions:117–154` 三对幂引理（90）；`FiniteCharacter:35–61` ≡ `FiniteGaloisStructure:50–81`；`cyclotomicLayer_padic_upper_zero` ≡ `upperRamificationGroup_cyclotomic_zero`；`norm_cyclotomicLayerRoot_sub_one` ⊂ `norm_primitive_cyclotomic_sub_one`；三份 `rangeRestrict` 指数计算；三份 `continuous_id.prodMk continuous_const`；六份 `_mem_translations/_mem_units`；`normalizedValuation_kummerTauFinite_div_sub_one` ≡ `normLimitValuation_tau_pow_div_sub_one`。
- 陈述形状：`∧` 结论拆分（`viviani_fraction_pos_lt_one`、`affinePureUnit_*_bound` 两条、`cyclotomicExtensionCharacter_index_bounds`）；`let`/`letI` 进陈述归零；`cyclotomicLayerIntegerRingEquiv` 补类型标注。
- 目标 (6) 的缺口：`IntegerParameter` 节补下分歧群，并给出单条 `viviani_corollary_6_10`；目标 (5) 同样给一条总结定理 `falseTateExtension_totallyRamified_padic`。

---

## F. 执行顺序　【已定稿 2026-10-19】

每阶段一个分支；阶段内按步骤直接提交；阶段结束 0 警告 0 sorry，全量 build，耗时追加到 `docs/BUILD_TIMES.md`。F3 与 F4–F7 无硬依赖，F3 受阻时可先做 F4。

| 阶段 | 内容 | 涉及项目 |
|---|---|---|
| F0 | 工程底座：`LICENSE`、`README`、`CLAUDE.md`、`.gitignore` 加 pdf、`scripts/check_layers.py`、`docs/BUILD_TIMES.md` 基线 | 本项目 |
| F1 | 性能速赢，不改接口：两处 `:= rfl` → `restrictNormalHom` 定义；`cyclotomicBase_isCompleteDiscreteValuedField` 改 instance；`NeZero (p^n)` 实例；8 处 `unfold; infer_instance`。预期 1115 s → 约 900 s | 本项目 |
| F2 | A1：删 NormField*、TameUnits、TameGenerator、`KummerRamification:222–447`；留下的引理归位；根文件更新 | 本项目 |
| F3 | FW 分支 `false-tate-upstream`（`~/FontaineWintenberger`，提交 `6c9e973`，**尚未推送到 GitHub**；本项目 `lakefile.toml`/`lake-manifest.json` 已指向该提交，`.lake/packages/FontaineWintenberger` 从本地仓库 fetch）：A5.3 九个新叶子模块 + `irreducible_of_valuation_eq_exp_neg_one`；A2.2 (b) 失败退回 (a)。**完成后需要：推送 FW 分支并合并，使 GitHub 上存在该提交** | FW + 本项目 |
| F4 | A2.1/A2.3/A7：`𝒪[K]`、`𝓀[K]`、`ℚ_[p]`、`ℤ_[p]` 替换；`Padic/Basic.lean`；删旧记号；引入 `falseTateDiagonalLayer`、`FalseTateGaloisGroup`、`absoluteRamificationIdx`、`vivianiOffset` | 本项目 |
| F5 | A3：`[NeZero π]`、`[Fact (Irreducible π)]`、`[Fact (p ≠ 2)]`；`IsGalois`/`IsAPF`/`IsStrictlyAPF` 实例化；去 `hπ`/`hp₂` 穿参 | 本项目 |
| F6 | A4 + A5.1/A5.2：`Affine/Group.lean` 与半直积拓扑；`Mathlib/` 层；`restrictNormalHomOfLE`；`autEquivPow` 替换 | 本项目 |
| F7 | E：删除清单、合并重复（含 `SeparableTower`）、`private` 化、`set_option` 归零、陈述拆分 | 本项目 |
| F8 | B：目录重组与文件拆分（脚本，记录旧→新映射） | 本项目 |
| F9 | A6：批量重命名（脚本），`τ` scoped notation | 本项目 |
| F10 | D：docstring 重写、References、删 blueprint 引用；补目标 (5)(6) 总结定理；README 目标表 | 本项目 |
| F11 | FalseTateNonliftability 同步：升级 FW 与本项目 rev，吸收 F2 删除的文件并按新 API 重写。**另行计划** | FalseTateNonliftability |

## 决策记录

A1–A7、B、C、D、E、F 全部于 2026-10-19 与作者逐项定稿，决定写在各节开头的 **决定** 段落。
