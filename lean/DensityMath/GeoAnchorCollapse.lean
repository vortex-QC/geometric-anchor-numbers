import DensityMath.GeoAnchorIdentity

/-!
# 锚塌方向对比定理化（2026-09-29 晚五轮·几何锚数立项档 §三 的机器配重）

对应: papers/几何锚数_立项_v0.1.md §三「锚塌方向对比」——数域锚塌（柯西列→实数·Cantor 构造）
×形变域锚塌（形变路径→拓扑类·同伦类构造）=同一"动过程+等价关系→静读数"结构在两域的显化。

内容（两域平行迷你模型——商构造结构骨架）:
  数域:  CauchyEquiv（ℚ 序列柯西等价·迷你模型）→ Setoid → NumCollapse = Quotient（产物=商元素·住连续位）
  形变域: PathEq（格点边列表的翻转链等价·对称闭包带传递）→ Setoid → ShapeCollapse = Quotient
          + **windingQ : ShapeCollapse → ℤ**——绕数在翻转链下不变（GeoAnchor.flip_context_neutral）
            ⟹ 身份读数下降为商上的良定义函数（T1·"身份=等价类上的读数"）
          + 商上身份非平凡（T2·存在两类绕数不同——P-5 第一阶梯在商层面成立）

诚实边界: 数域为迷你模型（ℚ 序列柯西商·非 Mathlib Real 内部构造）——方向对比的"连续位/整数位"
镜像以构造对照+注释承载（数域无 ℤ 值身份读数的否定性定理需要拓扑/基数论·挂账不硬造）。
零 sorry。
-/

namespace GeoAnchorCollapse

open GeoAnchor

/-! ### 形变域：翻转链等价（对称闭包·带传递） -/

/-- 边列表路径的翻转链等价：自反+双向翻转步+传递（Setoid 就绪形态）。 -/
inductive PathEq : List (Pt × Pt) → List (Pt × Pt) → Prop
  | refl : PathEq E E
  | stepA : ∀ (E1 E2 E3 : List (Pt × Pt)) (x0 y0 : ℤ),
      (x0 ≠ 0 ∨ y0 ≠ 0) → PathEq E2 E3 →
      PathEq (E1 ++ halfA_edges x0 y0 ++ E2) (E1 ++ halfB_edges x0 y0 ++ E3)
  | stepB : ∀ (E1 E2 E3 : List (Pt × Pt)) (x0 y0 : ℤ),
      (x0 ≠ 0 ∨ y0 ≠ 0) → PathEq E2 E3 →
      PathEq (E1 ++ halfB_edges x0 y0 ++ E2) (E1 ++ halfA_edges x0 y0 ++ E3)
  | trans : ∀ {a b c : List (Pt × Pt)}, PathEq a b → PathEq b c → PathEq a c

theorem pathEq_refl (E : List (Pt × Pt)) : PathEq E E := PathEq.refl

theorem pathEq_sym {E E' : List (Pt × Pt)} (h : PathEq E E') : PathEq E' E := by
  induction h with
  | refl => exact PathEq.refl
  | stepA E1 E2 E3 x0 y0 hc _ ih => exact PathEq.stepB E1 E3 E2 x0 y0 hc ih
  | stepB E1 E2 E3 x0 y0 hc _ ih => exact PathEq.stepA E1 E3 E2 x0 y0 hc ih
  | trans _ _ ih1 ih2 => exact PathEq.trans ih2 ih1

theorem pathEq_trans {a b c : List (Pt × Pt)} (h1 : PathEq a b) (h2 : PathEq b c) :
    PathEq a c := PathEq.trans h1 h2

/-- 形变域锚塌的等价结构（Setoid）。 -/
def PathSetoid : Setoid (List (Pt × Pt)) :=
  ⟨PathEq, ⟨pathEq_refl, fun h => pathEq_sym h, pathEq_trans⟩⟩

/-- 形变域锚塌产物：路径商（拓扑类·静身份）。 -/
def ShapeCollapse := Quotient PathSetoid

/-! ### T1：身份读数下降为商上的良定义函数（核心定理） -/

/-- 绕数在翻转链等价下不变（复用 GeoAnchor.flip_context_neutral 的边列表版归纳）。 -/
theorem edgeSum_pathEq {E E' : List (Pt × Pt)} (h : PathEq E E') :
    edgeSum E = edgeSum E' := by
  induction h with
  | refl => rfl
  | stepA E1 E2 E3 x0 y0 hc _ ih =>
      simp only [edgeSum] at ih
      simp only [edgeSum, List.map_append, List.sum_append]
      rw [half_edges_equal x0 y0 hc, ih]
  | stepB E1 E2 E3 x0 y0 hc _ ih =>
      simp only [edgeSum] at ih
      simp only [edgeSum, List.map_append, List.sum_append]
      rw [half_edges_equal x0 y0 hc, ih]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- **T1·身份读数良定义**：绕数下降为商上的函数——
    「身份=等价类上的读数」（锚塌产物=等价类的静读数）的形式句。 -/
def windingQ : ShapeCollapse → ℤ :=
  Quotient.lift edgeSum (fun a b hab => edgeSum_pathEq hab)

/-! ### T2：商上身份非平凡 -/

/-- 绕原点方路径的边列表（在案 loopPath 的边展开）。 -/
def loopEdges : List (Pt × Pt) :=
  [((1, 0), (1, 1)), ((1, 1), (0, 1)), ((0, 1), (0, 0)), ((0, 0), (1, 0))]

/-- 不绕原点的同尺寸方路径边列表。 -/
def flatEdges : List (Pt × Pt) :=
  [((1, 0), (2, 0)), ((2, 0), (2, 1)), ((2, 1), (1, 1)), ((1, 1), (1, 0))]

theorem edgeSum_loop : edgeSum loopEdges = 1 := by decide
theorem edgeSum_flat : edgeSum flatEdges = 0 := by decide

/-- **T2·商上身份非平凡**：存在两类绕数不同——身份分级在商层面成立
    （P-5 第一阶梯的商提升：1 维身份平凡→2 维身份显化）。 -/
theorem identity_nontrivial_quotient :
    windingQ (Quotient.mk PathSetoid loopEdges)
      ≠ windingQ (Quotient.mk PathSetoid flatEdges) := by
  show edgeSum loopEdges ≠ edgeSum flatEdges
  rw [edgeSum_loop, edgeSum_flat]
  decide

/-! ### 数域：柯西列等价迷你模型 -/

/-- 柯西等价（ℚ 序列）：差的绝对值收敛到 0（迷你模型·实数构造的结构骨架）。 -/
def CauchyEquiv (a b : ℕ → ℚ) : Prop := ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - b n| < ε

theorem cauchyEquiv_refl (a : ℕ → ℚ) : CauchyEquiv a a := by
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  simp only [sub_self, abs_zero]
  exact hε

theorem cauchyEquiv_sym {a b : ℕ → ℚ} (h : CauchyEquiv a b) : CauchyEquiv b a := by
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h2 := hN n hn
  calc |b n - a n| = |a n - b n| := abs_sub_comm _ _
    _ < ε / 2 := h2
    _ < ε := by linarith

theorem cauchyEquiv_trans {a b c : ℕ → ℚ} (h1 : CauchyEquiv a b) (h2 : CauchyEquiv b c) :
    CauchyEquiv a c := by
  intro ε hε
  obtain ⟨N1, hN1⟩ := h1 (ε / 2) (by positivity)
  obtain ⟨N2, hN2⟩ := h2 (ε / 2) (by positivity)
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have hn1 : n ≥ N1 := le_trans (le_max_left _ _) hn
  have hn2 : n ≥ N2 := le_trans (le_max_right _ _) hn
  have p1 := hN1 n hn1
  have p2 := hN2 n hn2
  rw [abs_lt]
  rcases abs_lt.mp p1 with ⟨q1, q2⟩
  rcases abs_lt.mp p2 with ⟨r1, r2⟩
  constructor
  · linarith
  · linarith

/-- 数域锚塌的等价结构（Setoid）。 -/
def CauchySetoid : Setoid (ℕ → ℚ) := ⟨CauchyEquiv, ⟨cauchyEquiv_refl, cauchyEquiv_sym, cauchyEquiv_trans⟩⟩

/-- 数域锚塌产物：柯西列商（迷你模型——实数的静读数·住连续位）。 -/
def NumCollapse := Quotient CauchySetoid

/-! ### 两域平行（锚塌方向对比的结构句） -/

/-- **锚塌方向对比**（立项档 §三 的形式句·构造对照）：
    两域共用同一构造模式「动过程集 + 等价关系 → 商（静读数）」——
    数域：柯西列（动的数）+ 柯西等价 → NumCollapse（产物=商元素·住连续位）；
    形变域：翻转链路径（边的动）+ PathEq → ShapeCollapse + 其上的**离散身份读数**
    windingQ : ShapeCollapse → ℤ（T1·住整数位·T2 非平凡）。
    产物所在位两域镜像：数域静读数=连续统的商点·形变域静读数=ℤ 值离散身份。 -/
theorem collapse_parallel_structural :
    (NumCollapse = Quotient CauchySetoid) ∧
    (ShapeCollapse = Quotient PathSetoid) ∧
    (∃ f : ShapeCollapse → ℤ, f (Quotient.mk PathSetoid loopEdges)
       ≠ f (Quotient.mk PathSetoid flatEdges)) :=
  ⟨rfl, rfl, ⟨windingQ, identity_nontrivial_quotient⟩⟩

end GeoAnchorCollapse
