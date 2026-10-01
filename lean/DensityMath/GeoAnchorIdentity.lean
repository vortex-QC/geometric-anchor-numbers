import Mathlib

/-!
# 几何锚数 · P-5 身份余维律的最小机器核（2026-09-29 晚）

对应: papers/几何锚数_逐维形变_身份余维律_v0.1.md（§七 P-5 最小机器核）
上游: papers/几何锚数_立项_v0.1.md（A 落位·容纳判据）+ 几何锚数 = 动层锚数的几何显化

内容（离散格点模型——P-5 第一阶梯「1 维身份平凡 → 2 维身份显化」）:
  1D 侧（身份平凡性的代数面）: 闭合格点路径（±1 步·总和=0）长度必为偶数
    ——每步 ±1 ≡ 1 (mod 2)，总和 ≡ 步数 (mod 2)，闭合 ⟹ 步数偶
    ——「1D 闭合 = 纯往返型·无圈结构」的最小代数证据（往返可消 = 身份平凡）。
  2D 侧（身份非平凡性）: 格点路径绕原点绕数 = 正 x 轴带符号穿越计数
    （严格整数判定 ad − bc 的符号——穿越点 x* = (ad−bc)/(d−b)，x*>0 ⟺ 符号匹配）
    ——绕原点方路径绕数 = 1，不绕原点的同尺寸方路径绕数 = 0
    ——∃ 两条闭合路径身份不同（2D 形变身份分级非空）。

诚实边界: 本件为 P-5 的最小形式句——绕数在一般初等形变下的不变性
（组合同伦·局部翻转保绕数）为下一刀挂账，本件不含。
零 sorry。
-/

namespace GeoAnchor

/-! ### 1D 侧：闭合 = 往返型（偶长度定理） -/

/-- 每个合法步呈 2c−1 形（e=1 时 c=1·e=−1 时 c=0）——步列和 = 2·(计数和) − 步数。 -/
theorem sum_shape : ∀ l : List ℤ, (∀ e ∈ l, e = 1 ∨ e = -1) → ∃ k : ℕ, l.sum = 2 * (k : ℤ) - l.length := by
  intro l
  induction l with
  | nil => intro _; exact ⟨0, by norm_num⟩
  | cons a l ih =>
    intro h
    obtain ⟨k, hk⟩ := ih (fun e he => h e (List.mem_cons_of_mem _ he))
    rcases h a List.mem_cons_self with ha | ha
    · refine ⟨k + 1, ?_⟩
      rw [List.sum_cons, ha, hk, Nat.cast_succ, List.length_cons]
      push_cast
      ring
    · refine ⟨k, ?_⟩
      rw [List.sum_cons, ha, hk, List.length_cons]
      push_cast
      ring

/-- **1D 偶长度定理**：闭合格点路径（步 ±1·总和 =0）的步数为偶数。
    「1D 闭合 = 往返型」的代数面——奇数个 ±1 之和必非零，故闭合路径无奇长。 -/
theorem closed1D_even_length (steps : List ℤ)
    (hsteps : ∀ e ∈ steps, e = 1 ∨ e = -1) (hclosed : steps.sum = 0) : Even steps.length := by
  obtain ⟨k, hk⟩ := sum_shape steps hsteps
  rw [hclosed] at hk
  refine ⟨k, ?_⟩
  omega

/-! ### 2D 侧：绕数身份非平凡（穿越计数定义） -/

/-- 格点。 -/
abbrev Pt := ℤ × ℤ

/-- 上穿判定：边 (a,b)→(c,d) 从 y≤0 到 y>0 且穿越点在正 x 轴上
    （穿越点横坐标 x* = (ad−bc)/(d−b)，上穿 d−b>0 ⟹ x*>0 ⟺ ad−bc>0）。 -/
def isUpD : Pt × Pt → Bool
  | ((a, b), (c, d)) => decide (b ≤ 0 ∧ d > 0 ∧ a * d - b * c > 0)

/-- 下穿判定：从 y>0 到 y≤0 且穿越点在正 x 轴上
    （下穿 d−b<0 ⟹ x*>0 ⟺ ad−bc<0）。 -/
def isDownD : Pt × Pt → Bool
  | ((a, b), (c, d)) => decide (b > 0 ∧ d ≤ 0 ∧ a * d - b * c < 0)

/-- 点列的边集（相邻对；闭合路径点列末点=首点，故已含全部边）。 -/
def edgesOf (p : List Pt) : List (Pt × Pt) := p.zip p.tail

/-- 绕原点绕数 = 正 x 轴带符号穿越计数（上穿 +1·下穿 −1）。 -/
def winding (p : List Pt) : ℤ :=
  (edgesOf p).countP isUpD - (edgesOf p).countP isDownD

/-- 闭合：点列末点 = 首点。 -/
def closedPt (p : List Pt) : Prop := p.getLast? = p.head?

/-- 绕原点一圈的方路径（第一象限·逆时针）。 -/
def loopPath : List Pt := [(1, 0), (1, 1), (0, 1), (0, 0), (1, 0)]

/-- 不绕原点的同尺寸方路径（x≥1 区域）。 -/
def flatPath : List Pt := [(1, 0), (2, 0), (2, 1), (1, 1), (1, 0)]

theorem loopPath_closed : closedPt loopPath := by
  simp [closedPt, loopPath]

theorem flatPath_closed : closedPt flatPath := by
  simp [closedPt, flatPath]

/-- 绕圈路径绕数 = 1。 -/
theorem winding_loop : winding loopPath = 1 := by
  decide

/-- 平凡路径绕数 = 0。 -/
theorem winding_flat : winding flatPath = 0 := by
  decide

/-- **2D 身份非平凡定理**：存在两条闭合格点路径绕数不同
    ——2D 形变的身份分级非空（P-5 第一阶梯的 2D 侧）。 -/
theorem identity_nontrivial_2D :
    ∃ p q : List Pt, closedPt p ∧ closedPt q ∧ winding p ≠ winding q :=
  ⟨loopPath, flatPath, loopPath_closed, flatPath_closed,
    by rw [winding_loop, winding_flat]; simp⟩


/-! ### 初等形变不变性（单步翻转·挂账续件 2026-09-29 晚）

初等形变 = 格点正方形的两侧半圈互换（halfA ↔ halfB）。
定理：除「正方形以原点为顶点」的障碍情形外，翻转保持穿越计数绕数——
组合同伦的第一步（任意形变 = 初等形变序列的归纳挂账）。
例外定理（flip_origin_step）反而是「洞=绕行身份」的算术根：
翻转改变绕数当且仅当正方形绕过原点（障碍·洞）——绕数变化 = 跨过一个洞。 -/

/-- 带符号边贡献（上穿 +1·下穿 −1·其余 0）——winding 的逐边展开形式。 -/
def edgeW : Pt × Pt → ℤ
  | ((a, b), (c, d)) =>
      if b ≤ 0 ∧ d > 0 ∧ a * d - b * c > 0 then 1
      else if b > 0 ∧ d ≤ 0 ∧ a * d - b * c < 0 then -1 else 0

/-- 逐边求和版绕数（与 winding 在可计算点上一致）。 -/
def windingW (p : List Pt) : ℤ := (edgesOf p).map edgeW |>.sum

/-- 格点正方形的两半：halfA 经右下角·halfB 经左上角（初等形变的两端）。 -/
def halfA (x0 y0 : ℤ) : List Pt := [(x0, y0), (x0 + 1, y0), (x0 + 1, y0 + 1)]
def halfB (x0 y0 : ℤ) : List Pt := [(x0, y0), (x0, y0 + 1), (x0 + 1, y0 + 1)]

/-- 两边路径的穿越计数（windingW 在 2 边路径上的直接形式·iota 可归约）。 -/
def wind2 (p q r : Pt) : ℤ := edgeW (p, q) + edgeW (q, r)

/-- **初等形变不变性（单步）**：格点正方形不以原点为顶点时，两侧半圈互换保持穿越计数绕数。
    组合同伦第一步（任意形变=初等形变序列的归纳·挂账）。 -/
theorem flip_neutral_off_origin (x0 y0 : ℤ) (h : x0 ≠ 0 ∨ y0 ≠ 0) :
    wind2 (x0, y0) (x0 + 1, y0) (x0 + 1, y0 + 1)
      = wind2 (x0, y0) (x0, y0 + 1) (x0 + 1, y0 + 1) := by
  simp only [wind2, edgeW]
  by_cases hy0 : y0 = 0
  · subst hy0
    split_ifs <;> omega
  · split_ifs <;> omega

/-- **原点障碍例外**：正方形以原点为顶点时（x0=y0=0），翻转改变绕数 +1
    ——翻转改变绕数当且仅当正方形绕过障碍（洞）——「洞=绕行身份」的算术根。 -/
theorem flip_origin_step :
    wind2 (0, 0) (1, 0) (1, 1) = wind2 (0, 0) (0, 1) (1, 1) + 1 := by
  simp only [wind2, edgeW]
  omega

/-! ### 翻转链不变性（组合同伦离散版·2026-09-29 晚四轮）

路径用边列表表示（闭合边显式化——拼接可加性平凡化）：
初等形变 = 边列表中正方形两半边组互换；翻转链 = 有限次翻转。
定理：翻转链保持边贡献绕数——「任意形变=初等形变序列」的绕数不变性形式句
（拓扑连通分量内的形变不改变绕数身份——P-5/P-6 身份分级的存在性侧）。 -/

/-- 边列表的穿越计数绕数（逐边贡献和·闭合边在列表中显式给出）。 -/
def edgeSum (E : List (Pt × Pt)) : ℤ := (E.map edgeW).sum

/-- 正方形两半的边组（初等形变的两端）。 -/
def halfA_edges (x0 y0 : ℤ) : List (Pt × Pt) :=
  [((x0, y0), (x0 + 1, y0)), ((x0 + 1, y0), (x0 + 1, y0 + 1))]
def halfB_edges (x0 y0 : ℤ) : List (Pt × Pt) :=
  [((x0, y0), (x0, y0 + 1)), ((x0, y0 + 1), (x0 + 1, y0 + 1))]

/-- 两半边组的绕数相等（= flip_neutral_off_origin 的边列表形式）。 -/
theorem half_edges_equal (x0 y0 : ℤ) (h : x0 ≠ 0 ∨ y0 ≠ 0) :
    (List.map edgeW (halfA_edges x0 y0)).sum = (List.map edgeW (halfB_edges x0 y0)).sum := by
  have := flip_neutral_off_origin x0 y0 h
  simp only [wind2, halfA_edges, halfB_edges, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Int.add_zero] at *
  exact this

/-- **翻转中性（任意上下文）**：边列表中正方形两半互换，绕数不变——
    拼接可加性（List.map_append + List.sum_append）+ 两半相等。 -/
theorem flip_context_neutral (E1 E2 : List (Pt × Pt)) (x0 y0 : ℤ) (h : x0 ≠ 0 ∨ y0 ≠ 0) :
    edgeSum (E1 ++ halfA_edges x0 y0 ++ E2) = edgeSum (E1 ++ halfB_edges x0 y0 ++ E2) := by
  simp only [edgeSum, List.map_append, List.sum_append]
  rw [half_edges_equal x0 y0 h]

/-- 翻转链：有限次初等形变（每步在剩余路径的任意位置换正方形两半）。 -/
inductive FlipChain : List (Pt × Pt) → List (Pt × Pt) → Prop
  | refl : FlipChain E E
  | cons : ∀ (E1 E2 E3 : List (Pt × Pt)) (x0 y0 : ℤ),
      (x0 ≠ 0 ∨ y0 ≠ 0) → FlipChain E2 E3 →
      FlipChain (E1 ++ halfA_edges x0 y0 ++ E2) (E1 ++ halfB_edges x0 y0 ++ E3)

/-- **翻转链不变性定理**：有限次初等形变保持绕数——
    同伦连通分量内绕数身份不变（组合同伦的离散形式句·格点模型）。 -/
theorem flip_chain_neutral : ∀ {E E' : List (Pt × Pt)},
    FlipChain E E' → edgeSum E = edgeSum E' := by
  intro E E' ch
  induction ch with
  | refl => rfl
  | cons E1 E2 E3 x0 y0 hcond hch ih =>
      simp only [edgeSum] at ih
      simp only [edgeSum, List.map_append, List.sum_append]
      rw [half_edges_equal x0 y0 hcond, ih]

end GeoAnchor
