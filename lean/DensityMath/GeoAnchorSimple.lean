import DensityMath.GeoAnchorCollapse

/-!
# 8vs7 陈述件：自避免宇宙 vs 自交商的类数差（挂账·主人确认单立 2026-09-30 晚）

对应: papers/几何锚数_8vs7形式句与归置_v0.1.md（FS-8v7 四句+归置建议单立·主人确认）
上游: papers/几何锚数_数值轮_A4承诺轴_判读档_v0.1.md §三（(0,0) 档上/下半域分裂 20+20·宽1走廊伪障碍）

陈述件口径（诚实边界·预声明）:
  本件立结构与实例——**走廊定理（触 y=0 的自避免圈必绕某井）与商映原像不可达性的完整证明
  不在本件**（大件·挂账）。三件:
  ① 分区互斥: InUpper E ∧ InLower E → E = []（自避免路径不可能同属上下半域）
  ② 两分区实例: up_loop/down_loop（互为 y 镜像的小矩形圈·绕数 0·顶点无重复·各在半域）
  ③ 原像分裂结构句: ∃ p q, InUpper p ∧ InLower q ∧ edgeSum p = edgeSum q ∧ p ≠ [] ∧ q ≠ []
     ——商映射原像 q⁻¹(0) 含两个互斥非空子集的成员（"非单连通"的成员级形态;
     "MasterEq 不可达"=两实例在自交商下同类但在自避免操作闭包中不连通——走廊层面·挂账）

数值对位: A'4 数值轮 808 条路径枚举实证 (0,0) 档 20+20 两分区（窗口 |S|≤6/|T|≤6）——
本件给该实证的 Lean 结构承载（实例级·非枚举完备性）。零 sorry。
-/

namespace GeoAnchorSimple

open GeoAnchor

/-! ### 半域谓词与自避免 -/

/-- 路径全部顶点在上半域（y ≥ 1）。 -/
def InUpper (E : List (Pt × Pt)) : Prop := ∀ v ∈ E.map Prod.fst, 1 ≤ v.2

/-- 路径全部顶点在下半域（y ≤ -1）。 -/
def InLower (E : List (Pt × Pt)) : Prop := ∀ v ∈ E.map Prod.fst, v.2 ≤ -1

/-- 自避免（顶点无重复）——自避免宇宙的合法性约束。 -/
def IsSimple (E : List (Pt × Pt)) : Prop := List.Nodup (E.map Prod.fst)

/-! ### ① 分区互斥 -/

theorem partition_disjoint (E : List (Pt × Pt)) (hU : InUpper E) (hL : InLower E) :
    E = [] := by
  cases E with
  | nil => rfl
  | cons a t =>
    exfalso
    have hv : a.1 ∈ (a :: t).map Prod.fst := List.mem_map_of_mem (a := a) (by simp)
    linarith [hU (a.1) hv, hL (a.1) hv]

/-! ### ② 两分区实例（互为 y 镜像的小矩形圈） -/

/-- 上半域实例：x∈[1,2]×y∈[1,2] 小矩形圈（闭合边显式给出·绕数 0）。 -/
def upLoop : List (Pt × Pt) :=
  [((1, 1), (2, 1)), ((2, 1), (2, 2)), ((2, 2), (1, 2)), ((1, 2), (1, 1))]

/-- 下半域实例：upLoop 的 y 镜像。 -/
def downLoop : List (Pt × Pt) :=
  [((1, -1), (2, -1)), ((2, -1), (2, -2)), ((2, -2), (1, -2)), ((1, -2), (1, -1))]

theorem upLoop_props : IsSimple upLoop ∧ InUpper upLoop ∧ edgeSum upLoop = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · show List.Nodup (upLoop.map Prod.fst)
    decide
  · intro v hv
    simp only [upLoop, List.map_cons, List.mem_cons, List.map_nil] at hv
    rcases hv with rfl | rfl | rfl | rfl | habs
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact absurd habs (by simp)
  · simp [edgeSum, upLoop, edgeW]

theorem downLoop_props : IsSimple downLoop ∧ InLower downLoop ∧ edgeSum downLoop = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · show List.Nodup (downLoop.map Prod.fst)
    decide
  · intro v hv
    simp only [downLoop, List.map_cons, List.mem_cons, List.map_nil] at hv
    rcases hv with rfl | rfl | rfl | rfl | habs
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact absurd habs (by simp)
  · simp [edgeSum, downLoop, edgeW]

/-! ### ③ 原像分裂结构句 -/

/-- **原像分裂结构句（FS-8v7 ③的成员级形态）**：商映射 edgeSum 的零原像含来自
上半域与下半域的两个不同非空成员——两实例绕数同值（=0）而分属互斥半域分区。
完整"非单连通"语义（MasterEq 不可达·走廊定理）不在本件·挂账。 -/
theorem origin_fiber_splits :
    ∃ p q : List (Pt × Pt),
      InUpper p ∧ InLower q ∧ p ≠ [] ∧ q ≠ [] ∧ edgeSum p = edgeSum q := by
  refine ⟨upLoop, downLoop, ?_, ?_, ?_, ?_, ?_⟩
  · exact upLoop_props.2.1
  · exact downLoop_props.2.1
  · intro h
    simp [upLoop] at h
  · intro h
    simp [downLoop] at h
  · exact (upLoop_props.2.2).trans downLoop_props.2.2

end GeoAnchorSimple
