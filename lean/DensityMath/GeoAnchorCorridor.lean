import DensityMath.GeoAnchorSimple

/-!
# 走廊定理 · 格点化第一层（R2 路线·2026-10-02 上午·入口④大件推进）

对应: papers/几何锚数_走廊定理_证明设计_v0.1.md（引理 0-3 严格 + L-IVP 路线 + 三组合表）
上游: GeoAnchorSimple.lean（8vs7 陈述件·四定理零 sorry）· GeoAnchorIdentity.lean（edgeW/edgeSum 口径）

R2 落地口径（诚实边界·预声明）:
  本件 = 走廊定理的**格点化第一层**。「绕井」的读数取 edgeW / edgeWB（对井 A=(0,0)/B=(2,0)
  的定向射线穿越计数——GeoAnchorIdentity 在案口径·edgeWB 为其 (2,0) 平移版）的
  **mod 2 读数**：「绕某井」在本件陈述 = 「edgeSum 奇 ∨ edgeSumB 奇」。
  mod 2 桥在 edgeSum 口径下自动成立（edgeW 逐边即定向穿越计数·mod 2 时符号消失）——
  证明设计 §四 的一致性引理由此消解（edgeSum 的逐边定义就是射线穿越计数本身）。

  走廊形态（CorridorForm·引理 0/1/3 的合并形态）与 riser 计数前提（引理 2 的度结构）
  在本件**显式为前提**——从 IsSimple+闭合+域推出走廊形态的结构引理 = 件 B·挂账收窄。

三组合结论（与证明设计 §三 纸面表逐条对位）:
  {P₁,P₂} → edgeSum 奇（绕 A）· {P₁,P₃} → edgeSum 奇（绕 A）· {P₂,P₃} → edgeSum 偶但 edgeSumB 奇（绕 B）
  ——走廊点对决定绕哪口井（非对称结构读数）。零 sorry。
-/

namespace GeoAnchorCorridor

open GeoAnchor

/-! ### 对井 B 的穿越读数（edgeW 的平移版） -/

/-- 对井 B=(2,0) 的定向穿越贡献：edgeW 的 (2,0) 平移版（B 恰为 A 东移 2 格）。 -/
def edgeWB : Pt × Pt → ℤ := fun ((a, b), (c, d)) => edgeW ((a - 2, b), (c - 2, d))

/-- 对井 B 的逐边求和绕数。 -/
def edgeSumB (E : List (Pt × Pt)) : ℤ := (E.map edgeWB).sum

/-! ### 走廊形态前提（件 B 目标 = 从 IsSimple + 闭合 + 域推出） -/

/-- 半域同侧边：两端同在 y ≥ 1 或同在 y ≤ -1（不触 y=0）。 -/
def SameSide (e : Pt × Pt) : Prop :=
  (1 ≤ e.1.2 ∧ 1 ≤ e.2.2) ∨ (e.1.2 ≤ -1 ∧ e.2.2 ≤ -1)

/-- 走廊点列（引理 0：域 D 内 y=0 可用点恰此三点——(0,0)/(2,0) 为井、其余越界）。 -/
def CorridorCols : List ℤ := [-1, 1, 3]

/-- 竖直穿越边：竖直边·列在走廊点集·连接 (p,1)-(p,0) 或 (p,0)-(p,-1)（引理 1 形态）。 -/
def IsCrossEdge (e : Pt × Pt) : Prop :=
  e.1.1 = e.2.1 ∧ (e.1.1 ∈ CorridorCols ∧
    ((e.1.2 = 1 ∧ e.2.2 = 0) ∨ (e.1.2 = 0 ∧ e.2.2 = 1) ∨
      (e.1.2 = 0 ∧ e.2.2 = -1) ∨ (e.1.2 = -1 ∧ e.2.2 = 0)))

/-- riser 边（Bool 谓词·可计算）：连接 (w,1) 与 (w,0) 的边——edgeW 唯一可能非零的
    穿越边形态（(w,0)-(w,-1) 型边不触发正 x 射线的定向判定·贡献恒 0）。 -/
def isRiserAt (e : Pt × Pt) (w : ℤ) : Bool :=
  e.1.1 == w && e.2.1 == w &&
    ((e.1.2 == 1 && e.2.2 == 0) || (e.1.2 == 0 && e.2.2 == 1))

/-- 走廊形态：每条边要么半域同侧、要么竖直穿越（引理 0+1+3 合并·件 B 目标）。 -/
def CorridorForm (E : List (Pt × Pt)) : Prop := ∀ e ∈ E, SameSide e ∨ IsCrossEdge e

/-- 列 w 的 riser 边计数。 -/
def countRiser (E : List (Pt × Pt)) (w : ℤ) : ℕ := (E.filter (fun e => isRiserAt e w)).length

/-! ### 逐边计算（核心引理） -/

/-- 同侧边对 A 的穿越贡献为 0。 -/
theorem edgeW_eq_zero_of_sameSide (e : Pt × Pt) (h : SameSide e) : edgeW e = 0 := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := e
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have f1 : 1 ≤ b := h1
    have f2 : 1 ≤ d := h2
    simp only [edgeW]; split_ifs <;> omega
  · have f1 : b ≤ -1 := h1
    have f2 : d ≤ -1 := h2
    simp only [edgeW]; split_ifs <;> omega

/-- 同侧边对 B 的穿越贡献为 0（平移不改变 y 坐标）。 -/
theorem edgeWB_eq_zero_of_sameSide (e : Pt × Pt) (h : SameSide e) : edgeWB e = 0 := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := e
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have f1 : 1 ≤ b := h1
    have f2 : 1 ≤ d := h2
    simp only [edgeWB, edgeW]; split_ifs <;> omega
  · have f1 : b ≤ -1 := h1
    have f2 : d ≤ -1 := h2
    simp only [edgeWB, edgeW]; split_ifs <;> omega

/-- 同侧边不含 y=0 端 ⟹ 非 riser（各列·Bool 版）。 -/
theorem notRiser_of_sameSide (e : Pt × Pt) (h : SameSide e) (w : ℤ) :
    isRiserAt e w = false := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := e
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have f1 : 1 ≤ b := h1
    have f2 : 1 ≤ d := h2
    have n2 : b ≠ 0 := by omega
    have n3 : d ≠ 0 := by omega
    simp [isRiserAt, n2, n3]
  · have f1 : b ≤ -1 := h1
    have f2 : d ≤ -1 := h2
    have n1 : b ≠ 1 := by omega
    have n2 : b ≠ 0 := by omega
    have n3 : d ≠ 0 := by omega
    have n4 : d ≠ 1 := by omega
    simp [isRiserAt, n1, n2, n3, n4]

/-- **riser 边贡献引理（A 版）**：riser 边（列 w·连 (w,1)-(w,0)）对 A 的贡献 mod 2
    = 「w > 0」指示（w=1/3 时 ±1·w=-1 时 0——mod 2 下方向符号消失）。 -/
theorem edgeW_riser_mod2 (e : Pt × Pt) (w : ℤ) (h : isRiserAt e w = true) :
    edgeW e % 2 = if 0 < w then 1 else 0 := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := e
  simp only [isRiserAt, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
  obtain ⟨⟨rfl, rfl⟩, hd⟩ := h
  simp only [edgeW]
  rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · split_ifs <;> omega
  · split_ifs <;> omega

/-- **riser 边贡献引理（B 版）**：riser 边（列 w·**走廊列前提**）对 B 的贡献 mod 2
    = 「w = 3」指示（平移后 2-w < 0 ⟺ w > 2——走廊列中仅 P₃=(3,0) 满足；
    ★w=4 等非走廊列反例由 omega 拒证暴露——前提必须显式）。 -/
theorem edgeWB_riser_mod2 (e : Pt × Pt) (w : ℤ) (h : isRiserAt e w = true)
    (hcol : w ∈ CorridorCols) :
    edgeWB e % 2 = if w = 3 then 1 else 0 := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := e
  have hcol' : w = -1 ∨ w = 1 ∨ w = 3 := by simpa [CorridorCols] using hcol
  simp only [isRiserAt, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
  obtain ⟨⟨rfl, rfl⟩, hd⟩ := h
  simp only [edgeWB, edgeW]
  rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · split_ifs <;> omega
  · split_ifs <;> omega

/-- **逐边 mod 2 分类（A 版）**：走廊形态下，每条边对 A 的贡献 mod 2
    = 「该边为列 1 riser」+「该边为列 3 riser」的指示和（mod 2）。
    同侧边贡献 0·非 riser 穿越边贡献 0·列 -1 riser 贡献 0。 -/
theorem edgeW_mod2_of_form (e : Pt × Pt) (h : SameSide e ∨ IsCrossEdge e) :
    edgeW e % 2 =
      (((if isRiserAt e 1 then 1 else 0 : ℕ) : ℤ) +
        ((if isRiserAt e 3 then 1 else 0 : ℕ) : ℤ)) % 2 := by
  rcases h with hs | hc
  · rw [edgeW_eq_zero_of_sameSide e hs]
    simp [notRiser_of_sameSide e hs 1, notRiser_of_sameSide e hs 3]
  · obtain ⟨hx, hcol, hd⟩ := hc
    obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := e
    have hac : a = c := hx
    have hcol' : a = -1 ∨ a = 1 ∨ a = 3 := by simpa [CorridorCols] using hcol
    rcases hd with ⟨hb1, hd1⟩ | ⟨hb1, hd1⟩ | ⟨hb1, hd1⟩ | ⟨hb1, hd1⟩
    · have f1 : b = 1 := hb1
      have f2 : d = 0 := hd1
      rcases hcol' with rfl | rfl | rfl <;> subst hac <;>
        simp [edgeW, isRiserAt, f1, f2] <;> omega
    · have f1 : b = 0 := hb1
      have f2 : d = 1 := hd1
      rcases hcol' with rfl | rfl | rfl <;> subst hac <;>
        simp [edgeW, isRiserAt, f1, f2] <;> omega
    · have f1 : b = 0 := hb1
      have f2 : d = -1 := hd1
      rcases hcol' with rfl | rfl | rfl <;> subst hac <;>
        simp [edgeW, isRiserAt, f1, f2] <;> omega
    · have f1 : b = -1 := hb1
      have f2 : d = 0 := hd1
      rcases hcol' with rfl | rfl | rfl <;> subst hac <;>
        simp [edgeW, isRiserAt, f1, f2] <;> omega

/-- **逐边 mod 2 分类（B 版）**：走廊形态下，每条边对 B 的贡献 mod 2
    = 「该边为列 3 riser」指示（列 1 平移后 -1·列 -1 平移后 -3——皆在 B 射线西侧）。 -/
theorem edgeWB_mod2_of_form (e : Pt × Pt) (h : SameSide e ∨ IsCrossEdge e) :
    edgeWB e % 2 = ((if isRiserAt e 3 then 1 else 0 : ℕ) : ℤ) % 2 := by
  rcases h with hs | hc
  · rw [edgeWB_eq_zero_of_sameSide e hs]
    simp [notRiser_of_sameSide e hs 3]
  · obtain ⟨hx, hcol, hd⟩ := hc
    obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := e
    have hac : a = c := hx
    have hcol' : a = -1 ∨ a = 1 ∨ a = 3 := by simpa [CorridorCols] using hcol
    rcases hd with ⟨hb1, hd1⟩ | ⟨hb1, hd1⟩ | ⟨hb1, hd1⟩ | ⟨hb1, hd1⟩
    · have f1 : b = 1 := hb1
      have f2 : d = 0 := hd1
      rcases hcol' with rfl | rfl | rfl <;> subst hac <;>
        simp [edgeWB, edgeW, isRiserAt, f1, f2] <;> omega
    · have f1 : b = 0 := hb1
      have f2 : d = 1 := hd1
      rcases hcol' with rfl | rfl | rfl <;> subst hac <;>
        simp [edgeWB, edgeW, isRiserAt, f1, f2] <;> omega
    · have f1 : b = 0 := hb1
      have f2 : d = -1 := hd1
      rcases hcol' with rfl | rfl | rfl <;> subst hac <;>
        simp [edgeWB, edgeW, isRiserAt, f1, f2] <;> omega
    · have f1 : b = -1 := hb1
      have f2 : d = 0 := hd1
      rcases hcol' with rfl | rfl | rfl <;> subst hac <;>
        simp [edgeWB, edgeW, isRiserAt, f1, f2] <;> omega

/-! ### 全局奇偶（归纳） -/

/-- **走廊奇偶和（A 版）**：走廊形态下，全圈对 A 的绕数 mod 2
    = 列 1 与列 3 的 riser 计数和 mod 2（列 -1 riser 贡献 0·mod 2 下方向消失）。 -/
theorem edgeSum_parity (E : List (Pt × Pt)) (hForm : CorridorForm E) :
    edgeSum E % 2 =
      (((countRiser E 1 + countRiser E 3 : ℕ) : ℤ)) % 2 := by
  induction E with
  | nil => simp [edgeSum, countRiser]
  | cons e t ih =>
    have hFormT : CorridorForm t := fun x hx => hForm x (List.mem_cons_of_mem _ hx)
    have hFormE := hForm e (by simp)
    have hc1 : countRiser (e :: t) 1
        = countRiser t 1 + (if isRiserAt e 1 then 1 else 0) := by
      simp only [countRiser, List.filter_cons]
      cases hb : isRiserAt e 1 <;> simp [hb]
    have hc3 : countRiser (e :: t) 3
        = countRiser t 3 + (if isRiserAt e 3 then 1 else 0) := by
      simp only [countRiser, List.filter_cons]
      cases hb : isRiserAt e 3 <;> simp [hb]
    have hSum : edgeSum (e :: t) = edgeW e + edgeSum t := by
      simp [edgeSum, List.map_cons, List.sum_cons]
    rw [hSum]
    rcases hFormE with hs | hc
    · rw [Int.add_emod, edgeW_eq_zero_of_sameSide e hs, ih hFormT, hc1, hc3]
      simp [notRiser_of_sameSide e hs 1, notRiser_of_sameSide e hs 3]
    · rw [Int.add_emod, ih hFormT, edgeW_mod2_of_form e (Or.inr hc), hc1, hc3]
      cases hb1 : isRiserAt e 1 <;> cases hb3 : isRiserAt e 3 <;>
        simp [hb1, hb3] <;> omega

/-- **走廊奇偶和（B 版）**：走廊形态下，全圈对 B 的绕数 mod 2 = 列 3 riser 计数 mod 2。 -/
theorem edgeSumB_parity (E : List (Pt × Pt)) (hForm : CorridorForm E) :
    edgeSumB E % 2 = ((countRiser E 3 : ℕ) : ℤ) % 2 := by
  induction E with
  | nil => simp [edgeSumB, countRiser]
  | cons e t ih =>
    have hFormT : CorridorForm t := fun x hx => hForm x (List.mem_cons_of_mem _ hx)
    have hFormE := hForm e (by simp)
    have hc3 : countRiser (e :: t) 3
        = countRiser t 3 + (if isRiserAt e 3 then 1 else 0) := by
      simp only [countRiser, List.filter_cons]
      cases hb : isRiserAt e 3 <;> simp [hb]
    have hSum : edgeSumB (e :: t) = edgeWB e + edgeSumB t := by
      simp [edgeSumB, List.map_cons, List.sum_cons]
    rw [hSum]
    rcases hFormE with hs | hc
    · rw [Int.add_emod, edgeWB_eq_zero_of_sameSide e hs, ih hFormT, hc3]
      simp [notRiser_of_sameSide e hs 3]
    · rw [Int.add_emod, ih hFormT, edgeWB_mod2_of_form e (Or.inr hc), hc3]
      cases hb3 : isRiserAt e 3 <;> simp [hb3] <;> omega

/-! ### 三组合定理（与证明设计 §三 纸面表逐条对位） -/

/-- **三组合 {P₁,P₂}（走廊点对 = 列 -1 与列 1）**：绕 A（edgeSum 奇）。
    列 1 riser 计数奇·列 3 计数偶 ⟹ edgeSum mod 2 = 1。 -/
theorem corridor_P12 (E : List (Pt × Pt)) (hForm : CorridorForm E)
    (hc1 : (countRiser E 1 : ℤ) % 2 = 1) (hc3 : (countRiser E 3 : ℤ) % 2 = 0) :
    edgeSum E % 2 = 1 := by
  have h := edgeSum_parity E hForm
  omega

/-- **三组合 {P₁,P₃}（走廊点对 = 列 -1 与列 3）**：绕 A（edgeSum 奇）。 -/
theorem corridor_P13 (E : List (Pt × Pt)) (hForm : CorridorForm E)
    (hc1 : (countRiser E 1 : ℤ) % 2 = 0) (hc3 : (countRiser E 3 : ℤ) % 2 = 1) :
    edgeSum E % 2 = 1 := by
  have h := edgeSum_parity E hForm
  omega

/-- **三组合 {P₂,P₃}（走廊点对 = 列 1 与列 3）**：不绕 A（edgeSum 偶）但**绕 B**
    （edgeSumB 奇——仅列 3 在井 B 射线东侧）——走廊点对决定绕哪口井。 -/
theorem corridor_P23 (E : List (Pt × Pt)) (hForm : CorridorForm E)
    (hc1 : (countRiser E 1 : ℤ) % 2 = 1) (hc3 : (countRiser E 3 : ℤ) % 2 = 1) :
    edgeSum E % 2 = 0 ∧ edgeSumB E % 2 = 1 := by
  have hA := edgeSum_parity E hForm
  have hB := edgeSumB_parity E hForm
  constructor <;> omega

/-- **走廊定理 · 格点化第一层（总件）**：走廊形态下，至少一个 p>0 走廊点在场
    （列 1 或列 3 的 riser 计数奇——三走廊点中两两成对·至多一个为 P₁），
    则绕 A（edgeSum 奇）或绕 B（edgeSumB 奇）。 -/
theorem corridor_parity (E : List (Pt × Pt)) (hForm : CorridorForm E)
    (h : (countRiser E 1 : ℤ) % 2 = 1 ∨ (countRiser E 3 : ℤ) % 2 = 1) :
    edgeSum E % 2 = 1 ∨ edgeSumB E % 2 = 1 := by
  have hA := edgeSum_parity E hForm
  have hB := edgeSumB_parity E hForm
  rcases h with h1 | h3
  · by_cases hc3 : (countRiser E 3 : ℤ) % 2 = 0
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · exact Or.inr (by omega)


/-! ### 件 B：走廊形态前提的消解（2026-10-02 上午八）

从「单位边 + 域内」两个逐边前提推出 CorridorForm——件 A 的形态前提消解。
链结构（Chain'/Simple）只在 riser 计数（引理 2）才需要——留件 B'（挂账）。 -/

/-- 域谓词：双井格点域 D（矩形域 [-1,3]×[-2,2] 拔两井 A=(0,0)/B=(2,0)）。 -/
def InDomain (v : Pt) : Prop :=
  -1 ≤ v.1 ∧ v.1 ≤ 3 ∧ -2 ≤ v.2 ∧ v.2 ≤ 2 ∧ v ≠ (0, 0) ∧ v ≠ (2, 0)

/-- 单位边谓词：格点相邻（竖直或水平·一步）。 -/
def IsUnitEdge (e : Pt × Pt) : Prop :=
  (e.2.1 = e.1.1 ∧ (e.2.2 = e.1.2 + 1 ∨ e.2.2 = e.1.2 - 1)) ∨
    (e.2.2 = e.1.2 ∧ (e.2.1 = e.1.1 + 1 ∨ e.2.1 = e.1.1 - 1))

/-- **引理 0（走廊点枚举）**：域内 y=0 点恰在走廊列——(0,0)/(2,0) 为井、其余 y=0 点越界。 -/
theorem zero_col_of_domain {x y : ℤ} (hd : InDomain (x, y)) (hy : y = 0) :
    x ∈ CorridorCols := by
  obtain ⟨h1, h2, _, _, hnA, hnB⟩ := hd
  subst hy
  have x0 : x ≠ 0 := fun h => hnA (by rw [h])
  have x2 : x ≠ 2 := fun h => hnB (by rw [h])
  interval_cases x <;> simp_all [CorridorCols]


/-! ### 件 B 主体重写（2026-10-02 中午·结构化路线）

重写策略（相对十六轮失败版的改变）：放弃 py 五值暴力 by_cases+decide，
改三条小定理自下而上——①y=0 行无相邻域内点（矛盾引理）②触 y=0 的域内单位边
必为竖直穿越边（设计档 §二 引理 1）③逐边二分（竖直按 y 上下界三分/水平三 handle）
推出 CorridorForm。全程 proj 风格（e.1.1/e.1.2/e.2.1/e.2.2）避免解构 subst 方向陷阱，
IsCrossEdge 四分支用显式 Or 嵌套构造（不用匿名 sugar）。 -/

/-- **矛盾引理（引理 1 的核）**：y=0 行内不存在相邻的两个域内点——
    域内 y=0 点恰为走廊列 {-1,1,3}（引理 0），其中任意两点距离 ≥2，无单位水平边可连。 -/
theorem no_unit_horiz_zero_row {x1 y1 x2 y2 : ℤ} (h1 : InDomain (x1, y1))
    (h2 : InDomain (x2, y2)) (hy1 : y1 = 0) (hy2 : y2 = 0)
    (hadj : x2 = x1 + 1 ∨ x2 = x1 - 1) : False := by
  have c1 : x1 ∈ CorridorCols := zero_col_of_domain h1 hy1
  have c2 : x2 ∈ CorridorCols := zero_col_of_domain h2 hy2
  have l1 : x1 = -1 ∨ x1 = 1 ∨ x1 = 3 := by simpa [CorridorCols] using c1
  have l2 : x2 = -1 ∨ x2 = 1 ∨ x2 = 3 := by simpa [CorridorCols] using c2
  rcases l1 with rfl | rfl | rfl <;> rcases hadj with rfl | rfl <;> omega

/-- **引理 1（垂直穿越·机器定理级）**：域内单位边若触 y=0（某端纵坐标为 0），
    则必为竖直穿越边（IsCrossEdge）——水平边在 y=0 行被矛盾引理排除，
    竖直边 ±1 步长把四分支钉死。 -/
theorem isCrossEdge_of_unit_domain {e : Pt × Pt} (hu : IsUnitEdge e)
    (hd1 : InDomain e.1) (hd2 : InDomain e.2) (h0 : e.1.2 = 0 ∨ e.2.2 = 0) :
    IsCrossEdge e := by
  simp only [IsUnitEdge] at hu
  rcases hu with ⟨hx, hy⟩ | ⟨hy', hx'⟩
  · -- 竖直边：e.2.1 = e.1.1，e.2.2 = e.1.2 ± 1
    rcases h0 with hb | hd0
    · -- e.1.2 = 0：列从下端点 (e.1.1, 0) 读出
      have col : e.1.1 ∈ CorridorCols :=
        zero_col_of_domain (x := e.1.1) (y := e.1.2) hd1 hb
      rcases hy with hy1 | hy1
      · have hdv : e.2.2 = 1 := by omega
        exact ⟨hx.symm, ⟨col, Or.inr (Or.inl ⟨hb, hdv⟩)⟩⟩
      · have hdv : e.2.2 = -1 := by omega
        exact ⟨hx.symm, ⟨col, Or.inr (Or.inr (Or.inl ⟨hb, hdv⟩))⟩⟩
    · -- e.2.2 = 0：列从上端点 (e.2.1, 0) 读出，沿竖直边换到 e.1.1
      have hcol2 : e.2.1 ∈ CorridorCols :=
        zero_col_of_domain (x := e.2.1) (y := e.2.2) hd2 hd0
      have col : e.1.1 ∈ CorridorCols := by rw [← hx]; exact hcol2
      rcases hy with hy1 | hy1
      · have hbv : e.1.2 = -1 := by omega
        exact ⟨hx.symm, ⟨col, Or.inr (Or.inr (Or.inr ⟨hbv, hd0⟩))⟩⟩
      · have hbv : e.1.2 = 1 := by omega
        exact ⟨hx.symm, ⟨col, Or.inl ⟨hbv, hd0⟩⟩⟩
  · -- 水平边：y=0 行无相邻域内点（矛盾引理）⟹ 此分支在触 y=0 时不可能
    have hb0 : e.1.2 = 0 := by rcases h0 with h | h <;> omega
    exact (no_unit_horiz_zero_row (x1 := e.1.1) (y1 := e.1.2)
      (x2 := e.2.1) (y2 := e.2.2) hd1 hd2 hb0 (by omega) hx').elim

/-- **件 B 主体（CorridorForm 消解·机器定理级）**：若圈 E 的每条边都是
    域内单位边，则 E 具有走廊形态（每边半域同侧或竖直穿越）——
    竖直边按 e.1.2 的上下界三分（≥1 同侧上 / ≤-2 同侧下 / 触 y=0 走引理 1），
    水平边同三分（y=0 行由矛盾引理排除）。件 A 的形态前提自此消解。 -/
theorem corridorForm_of_unit_domain (E : List (Pt × Pt))
    (hu : ∀ e ∈ E, IsUnitEdge e) (hd : ∀ e ∈ E, InDomain e.1 ∧ InDomain e.2) :
    CorridorForm E := by
  intro e he
  have huE0 : IsUnitEdge e := hu e he
  have huE1 : IsUnitEdge e := hu e he
  have hdE : InDomain e.1 ∧ InDomain e.2 := hd e he
  simp only [IsUnitEdge] at huE1
  rcases huE1 with ⟨hx, hy⟩ | ⟨hy', hx'⟩
  · -- 竖直边：e.2.2 = e.1.2 + 1 或 e.1.2 - 1
    rcases hy with hy1 | hy1
    · by_cases hb1 : 1 ≤ e.1.2
      · exact Or.inl (Or.inl ⟨hb1, by omega⟩)
      · by_cases hb2 : e.1.2 ≤ -2
        · exact Or.inl (Or.inr ⟨by omega, by omega⟩)
        · have hv : e.1.2 = -1 ∨ e.1.2 = 0 := by omega
          have h0' : e.1.2 = 0 ∨ e.2.2 = 0 := by
            rcases hv with h | h
            · exact Or.inr (by omega)
            · exact Or.inl h
          exact Or.inr (isCrossEdge_of_unit_domain huE0 hdE.1 hdE.2 h0')
    · by_cases hb2 : 2 ≤ e.1.2
      · exact Or.inl (Or.inl ⟨by omega, by omega⟩)
      · by_cases hbm1 : e.1.2 ≤ -1
        · exact Or.inl (Or.inr ⟨hbm1, by omega⟩)
        · have hv : e.1.2 = 0 ∨ e.1.2 = 1 := by omega
          have h0' : e.1.2 = 0 ∨ e.2.2 = 0 := by
            rcases hv with h | h
            · exact Or.inl h
            · exact Or.inr (by omega)
          exact Or.inr (isCrossEdge_of_unit_domain huE0 hdE.1 hdE.2 h0')
  · -- 水平边：e.2.2 = e.1.2，e.2.1 = e.1.1 ± 1
    by_cases hb0 : e.1.2 = 0
    · exact (no_unit_horiz_zero_row (x1 := e.1.1) (y1 := e.1.2)
        (x2 := e.2.1) (y2 := e.2.2) hdE.1 hdE.2 hb0 (by omega) hx').elim
    · by_cases hb1 : 1 ≤ e.1.2
      · exact Or.inl (Or.inl ⟨hb1, by omega⟩)
      · have hbm1 : e.1.2 ≤ -1 := by omega
        exact Or.inl (Or.inr ⟨hbm1, by omega⟩)

/-! ### 件 B'：riser 计数奇偶的前提件（引理 2 度结构·2026-10-02 下午）

目标（设计档 §二 引理 2）：自避免闭合圈触 y=0 ⟹ y=0 起点计数 K=2。
证明树：T1 泛型（闭合 Bool 序列相邻变化偶）+ G1 几何逐项（upEdge 变化 ⟺ 共享顶点
y=0·异号性由无往返排除 2-圈）+ T2 主恒等式（zipCount+[头项]=K·纯归纳）+ T3（K 偶）
+ T4（K=2）。 -/

/-- 闭合链：相邻边首尾相接 + 末边终点 = 首边起点（边列表口径·设计档 §二 循环结构）。 -/
def ClosedLoop (E : List (Pt × Pt)) : Prop :=
  List.Chain' (fun e1 e2 : Pt × Pt => e1.2 = e2.1) E ∧
    ∀ l f, E.getLast? = some l → E.head? = some f → l.2 = f.1

/-- 无往返：不存在互为反向的两条边——格点简单图上排除 2-圈/重复走边
    （IsSimple 只查起点列表，不排除 ((a,1),(b,0)) 与 ((b,0),(a,1)) 型往返）。 -/
def NoBacktrack (E : List (Pt × Pt)) : Prop :=
  ∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁.1 = e₂.2 → e₁.2 = e₂.1 → e₁ = e₂

/-- **NoBacktrack 尾子集**：NoBacktrack (a :: l) → NoBacktrack l（∈E 对前提的归纳传递件）。 -/
theorem NoBacktrack_tail (a : Pt × Pt) (l : List (Pt × Pt)) (h : NoBacktrack (a :: l)) :
    NoBacktrack l := by
  show ∀ e₁ ∈ l, ∀ e₂ ∈ l, e₁.1 = e₂.2 → e₁.2 = e₂.1 → e₁ = e₂
  intro e₁ he₁ e₂ he₂ h1 h2
  exact h e₁ (List.mem_cons_of_mem _ he₁) e₂ (List.mem_cons_of_mem _ he₂) h1 h2

/-- **NoBacktrack 应用件**：E 中两条边的无往返实例（点对 hnb 的 ∈E 版来源）。 -/
theorem nbE_apply {E : List (Pt × Pt)} {e₁ e₂ : Pt × Pt} (h : NoBacktrack E)
    (he₁ : e₁ ∈ E) (he₂ : e₂ ∈ E) (h1 : e₁.1 = e₂.2) (h2 : e₁.2 = e₂.1) : e₁ = e₂ :=
  h e₁ he₁ e₂ he₂ h1 h2

/-- **全局形 → NoBacktrack E**（向后兼容桥：旧全局 hnb 直接喂新签名）。 -/
theorem NoBacktrack_of_strong (E : List (Pt × Pt))
    (hnb : ∀ e₁ e₂ : Pt × Pt, e₁.1 = e₂.2 → e₁.2 = e₂.1 → e₁ = e₂) : NoBacktrack E :=
  fun e₁ _ e₂ _ h1 h2 => hnb e₁ e₂ h1 h2

/-- 上半域触及指示：边是否触及 y ≥ 1。走廊形态下：同侧上边=true/下边=false/
    穿越边=（非 0 端是否 +1）。 -/
def upEdge (e : Pt × Pt) : Bool := decide (1 ≤ e.1.2 ∨ 1 ≤ e.2.2)


/-- Bool 指示函数。 -/
def b2n : Bool → ℕ
  | true => 1
  | false => 0

/-- 进入式变化奇偶读数：从状态 b 出发沿 Bool 序列行走的翻转次数奇偶（Bool 承载·xor 累积）。 -/
def auxPar : List Bool → Bool → Bool
  | [], _ => false
  | x :: xs, b => (x != b) != auxPar xs x

theorem bne_false (x : Bool) : (x != false) = x := by cases x <;> rfl

/-- **XOR 三角**：首段差 xor 末段差 = 首末差（Bool 三角不等式）。 -/
theorem bne_triangle (x b L : Bool) : ((x != b) != (L != x)) = (L != b) := by
  cases x <;> cases b <;> cases L <;> rfl

/-- **T1three（循环变化奇偶）**：非空 Bool 序列从任意状态 b 出发走一圈的变化奇偶
    = 末首差——循环中 up 段与下段交替，翻转次数必偶。 -/
theorem auxPar_getLast : ∀ bs : List Bool, ∀ b : Bool, bs ≠ [] →
    auxPar bs b = (bs.getLast! != b) := by
  intro bs
  induction bs with
  | nil => intro b hn; exact absurd rfl hn
  | cons c t ih =>
    intro b _
    cases t with
    | nil =>
      show auxPar [c] b = (c != b)
      rw [auxPar, auxPar, bne_false]
    | cons c2 t2 =>
      have h1 := ih c (by simp)
      have h2 : auxPar (c :: c2 :: t2) b = ((c != b) != auxPar (c2 :: t2) c) := by
        rw [auxPar]
      rw [h2, h1]
      exact bne_triangle c b ((c2 :: t2 : List Bool).getLast!)

/-- **G1（upChange_iff_zero：upEdge 变化 ⟺ 共享顶点 y=0）**：走廊形态+无往返下，
    两条首尾相接的边 upEdge 值不同当且仅当共享顶点纵坐标为 0。
    y=0 时两侧非 0 端必异号（同号则两边互为反向 2-圈——IsCrossEdge 竖直性
    强制四 x 相等 a1=c1=a2=c2，无往返排除）；非 0 时两侧 upEdge 同值。 -/
theorem upChange_iff_zero (e₁ e₂ : Pt × Pt)
    (hchain : e₁.2 = e₂.1)
    (hF1 : SameSide e₁ ∨ IsCrossEdge e₁) (hF2 : SameSide e₂ ∨ IsCrossEdge e₂)
    (hnb : e₁.1 = e₂.2 → e₁.2 = e₂.1 → e₁ = e₂) :
    (upEdge e₁ != upEdge e₂) = decide (e₂.1.2 = 0) := by
  obtain ⟨⟨a1, b1⟩, ⟨c1, d1⟩⟩ := e₁
  obtain ⟨⟨a2, b2⟩, ⟨c2, d2⟩⟩ := e₂
  have hcc : c1 = a2 := congrArg Prod.fst hchain
  have hdd : d1 = b2 := congrArg Prod.snd hchain
  have huE1 : upEdge ((a1, b1), (c1, d1)) = decide (1 ≤ b1 ∨ 1 ≤ d1) := rfl
  have huE2 : upEdge ((a2, b2), (c2, d2)) = decide (1 ≤ b2 ∨ 1 ≤ d2) := rfl
  simp only [SameSide, IsCrossEdge] at hF1 hF2
  rcases hF2 with hs2 | hc2
  · -- e₂ 同侧
    rcases hs2 with ⟨h21, h22⟩ | ⟨h23, h24⟩
    · -- 上同侧：1 ≤ b2 ∧ 1 ≤ d2 ⟹ 两侧 upEdge 均 true（d1 = b2 ≥ 1）
      have hu1 : decide (1 ≤ b1 ∨ 1 ≤ d1) = true := by simp; omega
      have hu2 : decide (1 ≤ b2 ∨ 1 ≤ d2) = true := by simp; omega
      have hr : decide (b2 = 0) = false := by simp; omega
      rw [huE1, huE2, hu1, hu2, hr]
      decide
    · -- 下同侧：b2 ≤ -1 ∧ d2 ≤ -1 ⟹ RHS false；upEdge e₂ = false；upEdge e₁ 必 false
      have hu2 : decide (1 ≤ b2 ∨ 1 ≤ d2) = false := by simp; omega
      have hr : decide (b2 = 0) = false := by simp; omega
      rw [huE2, hr, hu2]
      rcases hF1 with hs1 | hc1
      · rcases hs1 with ⟨h11, h12⟩ | ⟨h13, h14⟩
        · exfalso; omega
        · -- e₁ 下同侧：upEdge e₁ = false ✓
          have hu1 : decide (1 ≤ b1 ∨ 1 ≤ d1) = false := by simp; omega
          rw [huE1, hu1]
          decide
      · -- e₁ 穿越边四支（三层 rcases·支 4 tail 是原子）
        obtain ⟨hx1, hc1'⟩ := hc1
        obtain ⟨hcol1, hd1s⟩ := hc1'
        rcases hd1s with hd1 | hd1s
        · obtain ⟨hb11, hd11⟩ := hd1; exfalso; omega
        · rcases hd1s with hd1 | hd1s
          · obtain ⟨hb11, hd11⟩ := hd1; exfalso; omega
          · rcases hd1s with hd1 | hd1s
            · -- b1 = 0 ∧ d1 = -1：与下同侧一致（b2 = d1 = -1）⟹ upEdge e₁ = false ✓
              obtain ⟨hb11, hd11⟩ := hd1
              have hu1 : decide (1 ≤ b1 ∨ 1 ≤ d1) = false := by simp; omega
              rw [huE1, hu1]
              decide
            · -- b1 = -1 ∧ d1 = 0（原子支 hd1s）：d1 = 0 与 d1 = b2 ≤ -1 矛盾
              obtain ⟨hb11, hd11⟩ := hd1s
              exfalso; omega
  · -- e₂ 穿越边（三层 rcases·支 4 tail 是原子）
    obtain ⟨hx2, hc2'⟩ := hc2
    obtain ⟨hcol2, hd2s⟩ := hc2'
    rcases hd2s with hd2 | hd2s
    · -- b2 = 1 ∧ d2 = 0 ⟹ 两侧 upEdge 均 true（d1 = b2 = 1）
      obtain ⟨hb21, hd21⟩ := hd2
      have hu1 : decide (1 ≤ b1 ∨ 1 ≤ d1) = true := by simp; omega
      have hu2 : decide (1 ≤ b2 ∨ 1 ≤ d2) = true := by simp; omega
      have hr : decide (b2 = 0) = false := by simp; omega
      rw [huE1, huE2, hu1, hu2, hr]
      decide
    · rcases hd2s with hd2 | hd2s
      · -- b2 = 0 ∧ d2 = 1 ⟹ RHS true；upEdge e₂ = true；upEdge e₁ 必 false
        obtain ⟨hb21, hd21⟩ := hd2
        have hu2 : decide (1 ≤ b2 ∨ 1 ≤ d2) = true := by simp; omega
        have hr : decide (b2 = 0) = true := by simp; omega
        rw [huE2, hu2, hr]
        rcases hF1 with hs1 | hc1
        · rcases hs1 with ⟨h11, h12⟩ | ⟨h13, h14⟩
          · exfalso; omega
          · exfalso; omega
        · obtain ⟨hx1, hc1'⟩ := hc1
          obtain ⟨hcol1, hd1s⟩ := hc1'
          rcases hd1s with hd1 | hd1s
          · -- b1 = 1 ∧ d1 = 0：upEdge e₁ = true 与 e₂ 同值 ⟹ 2-圈反向矛盾
            obtain ⟨hb11, hd11⟩ := hd1
            exfalso
            have hax : a1 = c2 := by omega
            have hr1 : (a1, b1) = (c2, d2) := by rw [hax, hb11, hd21]
            have hr2 : (c1, d1) = (a2, b2) := by rw [hcc, hd11, hb21]
            have heq := hnb hr1 hr2
            have hcontra : d1 = d2 := congrArg (fun p : Pt × Pt => p.2.2) heq
            omega
          · rcases hd1s with hd1 | hd1s
            · obtain ⟨hb11, hd11⟩ := hd1; exfalso; omega
            · rcases hd1s with hd1 | hd1s
              · obtain ⟨hb11, hd11⟩ := hd1; exfalso; omega
              · -- b1 = -1 ∧ d1 = 0（原子支 hd1s）：upEdge e₁ = false ⟹ != true ✓
                obtain ⟨hb11, hd11⟩ := hd1s
                have hu1 : decide (1 ≤ b1 ∨ 1 ≤ d1) = false := by simp; omega
                rw [huE1, hu1]
                decide
      · rcases hd2s with hd2 | hd2s
        · -- b2 = 0 ∧ d2 = -1 ⟹ upEdge e₂ = false；upEdge e₁ 必 true
          obtain ⟨hb21, hd21⟩ := hd2
          have hu2 : decide (1 ≤ b2 ∨ 1 ≤ d2) = false := by simp; omega
          have hr : decide (b2 = 0) = true := by simp; omega
          rw [huE2, hu2, hr]
          rcases hF1 with hs1 | hc1
          · rcases hs1 with ⟨h11, h12⟩ | ⟨h13, h14⟩
            · -- e₁ 上同侧：upEdge e₁ = true ✓
              have hu1 : decide (1 ≤ b1 ∨ 1 ≤ d1) = true := by simp; omega
              rw [huE1, hu1]
              decide
            · exfalso; omega
          · obtain ⟨hx1, hc1'⟩ := hc1
            obtain ⟨hcol1, hd1s⟩ := hc1'
            rcases hd1s with hd1 | hd1s
            · -- b1 = 1 ∧ d1 = 0：upEdge e₁ = true ✓
              obtain ⟨hb11, hd11⟩ := hd1
              have hu1 : decide (1 ≤ b1 ∨ 1 ≤ d1) = true := by simp; omega
              rw [huE1, hu1]
              decide
            · rcases hd1s with hd1 | hd1s
              · obtain ⟨hb11, hd11⟩ := hd1; exfalso; omega
              · rcases hd1s with hd1 | hd1s
                · obtain ⟨hb11, hd11⟩ := hd1; exfalso; omega
                · -- b1 = -1 ∧ d1 = 0（原子支 hd1s）：upEdge e₁ = false 与 e₂ 同值 ⟹ 2-圈反向矛盾
                  obtain ⟨hb11, hd11⟩ := hd1s
                  exfalso
                  have hax : a1 = c2 := by omega
                  have hr1 : (a1, b1) = (c2, d2) := by rw [hax, hb11, hd21]
                  have hr2 : (c1, d1) = (a2, b2) := by rw [hcc, hd11, hb21]
                  have heq := hnb hr1 hr2
                  have hcontra : d1 = d2 := congrArg (fun p : Pt × Pt => p.2.2) heq
                  omega
        · -- b2 = -1 ∧ d2 = 0（原子支 hd2s）⟹ RHS false；upEdge e₂ = false；upEdge e₁ 必 false
          obtain ⟨hb21, hd21⟩ := hd2s
          have hu2 : decide (1 ≤ b2 ∨ 1 ≤ d2) = false := by simp; omega
          have hr : decide (b2 = 0) = false := by simp; omega
          rw [huE2, hr, hu2]
          rcases hF1 with hs1 | hc1
          · rcases hs1 with ⟨h11, h12⟩ | ⟨h13, h14⟩
            · exfalso; omega
            · have hu1 : decide (1 ≤ b1 ∨ 1 ≤ d1) = false := by simp; omega
              rw [huE1, hu1]
              decide
          · obtain ⟨hx1, hc1'⟩ := hc1
            obtain ⟨hcol1, hd1s⟩ := hc1'
            rcases hd1s with hd1 | hd1s
            · obtain ⟨hb11, hd11⟩ := hd1; exfalso; omega
            · rcases hd1s with hd1 | hd1s
              · obtain ⟨hb11, hd11⟩ := hd1; exfalso; omega
              · rcases hd1s with hd1 | hd1s
                · -- b1 = 0 ∧ d1 = -1：与 b2 = d1 = -1 一致 ⟹ upEdge e₁ = false ✓
                  obtain ⟨hb11, hd11⟩ := hd1
                  have hu1 : decide (1 ≤ b1 ∨ 1 ≤ d1) = false := by simp; omega
                  rw [huE1, hu1]
                  decide
                · obtain ⟨hb11, hd11⟩ := hd1s; exfalso; omega
/-! ### 件 B' 链条：循环零偶（LX2+T3'+LX3·2026-10-02 下午三）

**实现层教训（本轮新增·累计十六条）**：
⑪ rcases 拆四支 Or 只需三层（Or A (Or B (Or C D)) 三次 rcases 后 tail 是原子 D 非 Or）；
⑫ rw 链收尾封闭 Bool 等式需显式 decide（且 decide 目标禁含自由变量）；
⑬ 全边分类支的 RHS 侧（decide (b2 = 0)）在每个 e₂ 分支必须立即用 hr 锁死；
⑭ 本版 Lean 的 = 与 != 同 precedence 左结合——A = B != C 解析为 (A = B) != C，
   陈述/show 中等式一侧含 != 必须整侧加括号；
⑮ 本版 List API 名全面变更（List.chain'_cons/getLast!_map/head!_mem 全 Unknown）
   ——关键谓词自定义（AdjChain）+ 引理手写（head!_mem'/getLast!_mem'/map_getLast!'）；
⑯ 🚨**Pt × Pt 上的 v.2 是 Pt（ℤ×ℤ）不是 ℤ**——Prod 有 Zero 实例使 decide (v.2 = 0)
   静默 elaborate 成 Pt 层语义（不报类型错、defeq 失败才暴露）——y 坐标一律 v.1.2。

**件 B' 现势（T3' 循环零偶已落地）**：cycle_zero_xor = 引理 2 核心（闭合圈 y=0
顶点数为偶）。剩余：T4 riser 对应（每 y=0 顶点恰一 riser ⟹ countRiser E w = 列 w
顶点数 ⟹ 三组合接件 A corridor_parity）。 -/

/-- xor 求和：Bool 列表的 xor 累积（顺序无关语义·右折叠定义）。 -/
def accXor : List Bool → Bool
  | [] => false
  | x :: xs => x != accXor xs

/-- 相邻链谓词：边列内相邻边首尾相接（自定义·不依赖 List.Chain' API）。 -/
def AdjChain (E : List (Pt × Pt)) : Prop :=
  match E with
  | [] => True
  | [_] => True
  | e1 :: e2 :: t => e1.2 = e2.1 ∧ AdjChain (e2 :: t)

theorem bne_comm (a b : Bool) : (a != b) = (b != a) := by
  cases a <;> cases b <;> rfl

theorem bne_self (a : Bool) : (a != a) = false := by
  cases a <;> rfl

theorem bne_falseL (x : Bool) : (false != x) = x := by
  cases x <;> rfl

theorem bne_add (a b : Bool) : b2n (a != b) % 2 = (b2n a + b2n b) % 2 := by
  cases a <;> cases b <;> simp [b2n]

/-- 首边 ∈ 边列（手写·head! 在 cons 上定义归约为首元）。 -/
theorem head!_mem' (a : Pt × Pt) (t : List (Pt × Pt)) : (a :: t).head! ∈ a :: t :=
  List.mem_cons_self (a := a) (l := t)

/-- 末边 ∈ 非空边列（手写归纳）。 -/
theorem getLast!_mem' : ∀ E : List (Pt × Pt), E ≠ [] → E.getLast! ∈ E := by
  intro E
  induction E with
  | nil => intro hn; exact absurd rfl hn
  | cons a t ih =>
    intro _
    cases t with
    | nil => exact List.mem_cons_self (a := a) (l := [])
    | cons b t2 =>
      exact List.mem_cons_of_mem a (ih (by simp))

/-- map 的末元 = 末元的像（手写归纳）。 -/
theorem map_getLast!' (f : Pt × Pt → Bool) : ∀ E : List (Pt × Pt), E ≠ [] →
    (E.map f).getLast! = f E.getLast! := by
  intro E
  induction E with
  | nil => intro hn; exact absurd rfl hn
  | cons a t ih =>
    intro _
    cases t with
    | nil => rfl
    | cons b t2 =>
      show ((b :: t2).map f).getLast! = f (a :: b :: t2).getLast!
      rw [ih (by simp)]
      rfl

/-- **LX2（G1 逐项替换桥）**：upEdge 序列的差分 xor 读数 = 首差 +
    顶点 y=0 指示序列的 xor——每个相邻差由 G1 替换（走廊形态+全局无往返前提）。 -/
theorem auxPar_upEdge_accXor : ∀ E : List (Pt × Pt), E ≠ [] → ∀ c : Bool,
    AdjChain E →
    (∀ e ∈ E, SameSide e ∨ IsCrossEdge e) →
    NoBacktrack E →
    auxPar (E.map upEdge) c =
      (((upEdge E.head!) != c) !=
        accXor (E.tail.map (fun v : Pt × Pt => decide (v.1.2 = 0)))) := by
  intro E
  induction E with
  | nil => intro hn; exact absurd rfl hn
  | cons e t ih =>
    intro _ c _ hForm hnb
    cases t with
    | nil =>
      -- 单边：两侧均 (upEdge e != c) != false
      simp [auxPar, accXor]
    | cons e2 t2 =>
      have hHead : (e.2 = e2.1 ∧ AdjChain (e2 :: t2)) := ‹_›
      obtain ⟨hR, hAT⟩ := hHead
      have hChainT : AdjChain (e2 :: t2) := hAT
      have hFormT : ∀ x ∈ e2 :: t2, SameSide x ∨ IsCrossEdge x := fun x hx =>
        hForm x (List.mem_cons_of_mem _ hx)
      show ((upEdge e != c) != auxPar ((e2 :: t2).map upEdge) (upEdge e)) =
        ((upEdge e != c) !=
          accXor ((e2 :: t2).map (fun v : Pt × Pt => decide (v.1.2 = 0))))
      rw [ih (by simp) (upEdge e) hChainT hFormT (NoBacktrack_tail _ _ hnb)]
      simp only [List.head!_cons]
      have hG := upChange_iff_zero (e₁ := e) (e₂ := e2) hR
        (hForm e (List.mem_cons_self (a := e) (l := e2 :: t2)))
        (hForm e2 (List.mem_cons_of_mem e (List.mem_cons_self (a := e2) (l := t2))))
        (nbE_apply hnb (List.mem_cons_self (a := e) (l := e2 :: t2))
          (List.mem_cons_of_mem e (List.mem_cons_self (a := e2) (l := t2))))
      rw [bne_comm (upEdge e2) (upEdge e), hG]
      rfl

/-- **T3'（循环零偶·引理 2 的核心）**：闭合圈（相邻链+尾接头）上，
    全部顶点的 y=0 指示 xor = false——y=0 顶点数为偶。 -/
theorem cycle_zero_xor (E : List (Pt × Pt)) (hE : E ≠ [])
    (hChain : AdjChain E)
    (hLast : E.getLast!.2 = E.head!.1)
    (hForm : ∀ e ∈ E, SameSide e ∨ IsCrossEdge e)
    (hnb : NoBacktrack E) :
    accXor (E.map (fun v : Pt × Pt => decide (v.1.2 = 0))) = false := by
  cases E with
  | nil => exact absurd rfl hE
  | cons e t =>
    have hE' : e :: t ≠ [] := hE
    have hLast' : (e :: t).getLast!.2 = (e :: t).head!.1 := hLast
    have h1 := auxPar_upEdge_accXor (e :: t) hE' (upEdge (e :: t).head!) hChain hForm hnb
    rw [bne_self, bne_falseL] at h1
    -- h1 : auxPar ((e::t).map upEdge) (upEdge (e::t).head!) = accXor (map d (e::t).tail)
    have hP := auxPar_getLast ((e :: t).map upEdge) (upEdge (e :: t).head!) (by simp)
    rw [map_getLast!' upEdge (e :: t) hE'] at hP
    rw [h1] at hP
    -- hP : accXor (map d (e::t).tail) = upEdge (e::t).getLast! != upEdge (e::t).head!
    have hmemL : (e :: t).getLast! ∈ e :: t := getLast!_mem' _ hE'
    have hmemH : (e :: t).head! ∈ e :: t := head!_mem' e t
    have hG := upChange_iff_zero (e₁ := (e :: t).getLast!) (e₂ := (e :: t).head!) hLast'
      (hForm _ hmemL) (hForm _ hmemH) (nbE_apply hnb hmemL hmemH)
    rw [hG] at hP
    -- hP : accXor (map d (e::t).tail) = decide ((e::t).head!.1.2 = 0)
    have htail : (e :: t).tail = t := rfl
    have hhead : (e :: t).head! = e := rfl
    rw [htail, hhead] at hP
    -- hP : accXor (map d t) = decide (e.1.2 = 0)
    have hmap : List.map (fun v : Pt × Pt => decide (v.1.2 = 0)) (e :: t)
        = decide (e.1.2 = 0) :: List.map (fun v : Pt × Pt => decide (v.1.2 = 0)) t := by
      rw [List.map_cons]
    have hac : accXor (decide (e.1.2 = 0) ::
        List.map (fun v : Pt × Pt => decide (v.1.2 = 0)) t)
        = (decide (e.1.2 = 0) != accXor (List.map (fun v : Pt × Pt => decide (v.1.2 = 0)) t)) := rfl
    rw [hmap, hac, ← hP, bne_self]

/-- **LX3（奇偶桥）**：xor 求和读数 = true 计数的奇偶（为 T3 数值化 K=2 备料）。 -/
theorem accXor_count_parity (l : List Bool) :
    b2n (accXor l) % 2 = l.countP (fun x : Bool => x) % 2 := by
  induction l with
  | nil => simp [accXor, b2n]
  | cons x xs ih =>
    have h1 : accXor (x :: xs) = (x != accXor xs) := rfl
    rw [h1, bne_add x (accXor xs)]
    cases hx : x <;> cases hac : accXor xs <;>
      rw [hac] at ih <;>
      simp [b2n, hx, hac, List.countP_cons] at ih ⊢ <;> omega

/-! ### T3 数值化：K=2（2026-10-02 傍晚）

y=0 顶点计数 K：闭合圈+触 y=0+域内+顶点互异 ⟹ K=2。
链：countZeroV_cons（展开）→ eq0/le1/le2/le3（条件套娃）→ ge1（触桥）
→ map_fst_map_zero（对齐 cycle_zero_xor）→ countZero_even（K 偶）→ 组装。 -/

/-- 顶点无重复（自定义·避开 List.Nodup API 名变动）。 -/
def NoDupV : List Pt → Prop
  | [] => True
  | v :: t => v ∉ t ∧ NoDupV t

/-- 顶点列表的 y=0 计数（引理 2 的 K·Bool 指示序列的 true 计数）。 -/
def countZeroV (vs : List Pt) : ℕ :=
  (vs.map (fun w : Pt => decide (w.2 = 0))).countP (fun x : Bool => x)

/-- 边列表的 y=0 顶点计数（K 的边列表口径）。 -/
def countZero (E : List (Pt × Pt)) : ℕ := countZeroV (E.map Prod.fst)

/-- K 的 cons 展开。 -/
theorem countZeroV_cons (w : Pt) (t : List Pt) :
    countZeroV (w :: t) = countZeroV t + b2n (decide (w.2 = 0)) := by
  show List.countP (fun x : Bool => x)
    (List.map (fun w : Pt => decide (w.2 = 0)) (w :: t)) = _
  rw [List.map_cons, List.countP_cons]
  congr 1
  cases h : decide (w.2 = 0) <;> simp [b2n, h]

/-- 全列无 y=0 ⟹ K=0。 -/
theorem countZeroV_eq0 : ∀ l : List Pt, (∀ w ∈ l, w.2 ≠ 0) → countZeroV l = 0 := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons w t ih =>
    intro h
    rw [countZeroV_cons]
    have h1 : decide (w.2 = 0) = false := by simp [h w (List.mem_cons_self (a := w) (l := t))]
    rw [h1]
    simp [b2n]
    exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- le1：y=0 顶点全同一点 ⟹ K≤1。 -/
theorem countZeroV_le1 : ∀ (l : List Pt) (A : Pt), NoDupV l →
    (∀ w ∈ l, w.2 = 0 → w = A) → countZeroV l ≤ 1 := by
  intro l
  induction l with
  | nil => intro A _ _; simp [countZeroV]
  | cons w t ih =>
    intro A hnd hin
    obtain ⟨hvnt, hndt⟩ := hnd
    by_cases hw0 : w.2 = 0
    · have hA := hin w (List.mem_cons_self (a := w) (l := t)) hw0
      -- hA : w = A：t 无 y=0 顶点（u.2=0 → u=A=w → w∈t 矛盾）
      have ht0 : ∀ u ∈ t, u.2 ≠ 0 := by
        intro u hu hu0
        have huA : u = A := hin u (List.mem_cons_of_mem _ hu) hu0
        exact hvnt (Eq.subst (huA.trans hA.symm) hu)
      rw [countZeroV_cons, countZeroV_eq0 t ht0]
      have hdec : decide (w.2 = 0) = true := by simp [hw0]
      rw [hdec]; simp [b2n]
    · rw [countZeroV_cons]
      have hdec : decide (w.2 = 0) = false := by simp [hw0]
      rw [hdec]; simp [b2n]
      exact ih A hndt (fun u hu hu0 => hin u (List.mem_cons_of_mem _ hu) hu0)

/-- le2：y=0 顶点两点选一 ⟹ K≤2。 -/
theorem countZeroV_le2 : ∀ (l : List Pt) (A B : Pt), NoDupV l →
    (∀ w ∈ l, w.2 = 0 → w = A ∨ w = B) → countZeroV l ≤ 2 := by
  intro l
  induction l with
  | nil => intro A B _ _; simp [countZeroV]
  | cons w t ih =>
    intro A B hnd hin
    obtain ⟨hvnt, hndt⟩ := hnd
    by_cases hw0 : w.2 = 0
    · have hAB := hin w (List.mem_cons_self (a := w) (l := t)) hw0
      rcases hAB with hwA | hwB
      · -- w = A：t 的 y=0 顶点全 = B
        have htB : ∀ u ∈ t, u.2 = 0 → u = B := by
          intro u hu hu0
          have huu := hin u (List.mem_cons_of_mem _ hu) hu0
          rcases huu with huA | huB
          · exact absurd (Eq.subst (huA.trans hwA.symm) hu) hvnt
          · exact huB
        rw [countZeroV_cons]
        have hdec : decide (w.2 = 0) = true := by simp [hw0]
        rw [hdec]; simp [b2n]
        have h1 := countZeroV_le1 t B hndt htB
        omega
      · -- w = B：t 的 y=0 顶点全 = A
        have htA : ∀ u ∈ t, u.2 = 0 → u = A := by
          intro u hu hu0
          have huu := hin u (List.mem_cons_of_mem _ hu) hu0
          rcases huu with huA | huB
          · exact huA
          · exact absurd (Eq.subst (huB.trans hwB.symm) hu) hvnt
        rw [countZeroV_cons]
        have hdec : decide (w.2 = 0) = true := by simp [hw0]
        rw [hdec]; simp [b2n]
        have h1 := countZeroV_le1 t A hndt htA
        omega
    · rw [countZeroV_cons]
      have hdec : decide (w.2 = 0) = false := by simp [hw0]
      rw [hdec]; simp [b2n]
      exact ih A B hndt (fun u hu hu0 => hin u (List.mem_cons_of_mem _ hu) hu0)

/-- le3：y=0 顶点三点选一 ⟹ K≤3。 -/
theorem countZeroV_le3 : ∀ (l : List Pt) (A B C : Pt), NoDupV l →
    (∀ w ∈ l, w.2 = 0 → w = A ∨ w = B ∨ w = C) → countZeroV l ≤ 3 := by
  intro l
  induction l with
  | nil => intro A B C _ _; simp [countZeroV]
  | cons w t ih =>
    intro A B C hnd hin
    obtain ⟨hvnt, hndt⟩ := hnd
    by_cases hw0 : w.2 = 0
    · have hABC := hin w (List.mem_cons_self (a := w) (l := t)) hw0
      rcases hABC with hwA | hwB
      · -- w = A：t 的 y=0 顶点 ∈ {B, C}
        have htBC : ∀ u ∈ t, u.2 = 0 → u = B ∨ u = C := by
          intro u hu hu0
          have huu := hin u (List.mem_cons_of_mem _ hu) hu0
          rcases huu with h | h | h
          · exact absurd (Eq.subst (h.trans hwA.symm) hu) hvnt
          · exact Or.inl h
          · exact Or.inr h
        rw [countZeroV_cons]
        have hdec : decide (w.2 = 0) = true := by simp [hw0]
        rw [hdec]; simp [b2n]
        have h1 := countZeroV_le2 t B C hndt htBC
        omega
      · rcases hwB with hwB | hwC
        · -- w = B：t 的 y=0 顶点 ∈ {A, C}
          have htAC : ∀ u ∈ t, u.2 = 0 → u = A ∨ u = C := by
            intro u hu hu0
            have huu := hin u (List.mem_cons_of_mem _ hu) hu0
            rcases huu with h | h | h
            · exact Or.inl h
            · exact absurd (Eq.subst (h.trans hwB.symm) hu) hvnt
            · exact Or.inr h
          rw [countZeroV_cons]
          have hdec : decide (w.2 = 0) = true := by simp [hw0]
          rw [hdec]; simp [b2n]
          have h1 := countZeroV_le2 t A C hndt htAC
          omega
        · -- w = C：t 的 y=0 顶点 ∈ {A, B}
          have htAB : ∀ u ∈ t, u.2 = 0 → u = A ∨ u = B := by
            intro u hu hu0
            have huu := hin u (List.mem_cons_of_mem _ hu) hu0
            rcases huu with h | h | h
            · exact Or.inl h
            · exact Or.inr h
            · exact absurd (Eq.subst (h.trans hwC.symm) hu) hvnt
          rw [countZeroV_cons]
          have hdec : decide (w.2 = 0) = true := by simp [hw0]
          rw [hdec]; simp [b2n]
          have h1 := countZeroV_le2 t A B hndt htAB
          omega
    · rw [countZeroV_cons]
      have hdec : decide (w.2 = 0) = false := by simp [hw0]
      rw [hdec]; simp [b2n]
      exact ih A B C hndt (fun u hu hu0 => hin u (List.mem_cons_of_mem _ hu) hu0)


/-- 触桥：顶点在列且 y=0 ⟹ K≥1（y=0 专用特化版）。 -/
theorem countZeroV_ge1 : ∀ (l : List Pt), ∀ v : Pt, v ∈ l → v.2 = 0 → 1 ≤ countZeroV l := by
  intro l
  induction l with
  | nil => intro v hv _; cases hv
  | cons a t ih =>
    intro v hv h0
    show List.countP (fun x : Bool => x)
      (decide (a.2 = 0) :: List.map (fun w : Pt => decide (w.2 = 0)) t) ≥ 1
    rcases List.mem_cons.mp hv with heq | hvt
    · have hda : decide (a.2 = 0) = true := by rw [heq.symm]; simp [h0]
      rw [List.countP_cons, hda]
      simp
    · have h1 := ih v hvt h0
      rw [List.countP_cons]
      cases hda : decide (a.2 = 0)
      · show 1 ≤ countZeroV t
        exact h1
      · simp

/-- 顶点列对齐引理：fst 映射后再指示 = 边列表直接指示。 -/
theorem map_fst_map_zero : ∀ E : List (Pt × Pt),
    (E.map Prod.fst).map (fun w : Pt => decide (w.2 = 0))
      = E.map (fun v : Pt × Pt => decide (v.1.2 = 0)) := by
  intro E
  induction E with
  | nil => rfl
  | cons a t ih =>
    show decide (a.1.2 = 0) :: ((t.map Prod.fst).map (fun w : Pt => decide (w.2 = 0)))
      = decide (a.1.2 = 0) :: (t.map (fun v : Pt × Pt => decide (v.1.2 = 0)))
    rw [ih]

/-- **T3a（K 偶数值化）**：闭合圈+走廊形态+无往返 ⟹ K 偶。 -/
theorem countZero_even (E : List (Pt × Pt)) (hE : E ≠ [])
    (hChain : AdjChain E) (hLast : E.getLast!.2 = E.head!.1)
    (hForm : ∀ e ∈ E, SameSide e ∨ IsCrossEdge e)
    (hnb : NoBacktrack E) :
    countZero E % 2 = 0 := by
  have h1 := cycle_zero_xor E hE hChain hLast hForm hnb
  have h2 := accXor_count_parity (E.map (fun v : Pt × Pt => decide (v.1.2 = 0)))
  rw [h1] at h2
  -- h2 : b2n false % 2 = countP (fun x => x) (map d E) % 2
  have h3 : b2n false = 0 := rfl
  rw [h3] at h2
  -- h2 : 0 = countP ... % 2；目标 countZero E % 2 = 0
  show countZeroV (E.map Prod.fst) % 2 = 0
  have h4 : (E.map Prod.fst).map (fun w : Pt => decide (w.2 = 0))
      = E.map (fun v : Pt × Pt => decide (v.1.2 = 0)) := map_fst_map_zero E
  show List.countP (fun x : Bool => x)
      ((E.map Prod.fst).map (fun w : Pt => decide (w.2 = 0))) % 2 = 0
  rw [h4]
  omega

/-- **T3b（触桥）**：存在 y=0 顶点 ⟹ K≥1。 -/
theorem countZero_ge1 (E : List (Pt × Pt))
    (h : ∃ v : Pt, v ∈ E.map Prod.fst ∧ v.2 = 0) : 1 ≤ countZero E := by
  obtain ⟨v, hv, hy⟩ := h
  exact countZeroV_ge1 (E.map Prod.fst) v hv hy

/-- **T3（引理 2 数值化·K=2）**：闭合圈+走廊形态+无往返+触 y=0
    +逐顶点域内+顶点无重复 ⟹ y=0 顶点数恰为 2。 -/
theorem countZero_eq2 (E : List (Pt × Pt)) (hE : E ≠ [])
    (hChain : AdjChain E) (hLast : E.getLast!.2 = E.head!.1)
    (hForm : ∀ e ∈ E, SameSide e ∨ IsCrossEdge e)
    (hnb : NoBacktrack E)
    (hDom : ∀ v ∈ E.map Prod.fst, InDomain v)
    (hNoDup : NoDupV (E.map Prod.fst))
    (hTouch : ∃ v : Pt, v ∈ E.map Prod.fst ∧ v.2 = 0) :
    countZero E = 2 := by
  have heven := countZero_even E hE hChain hLast hForm hnb
  have hge1 := countZero_ge1 E hTouch
  -- le3 前提：y=0 顶点三选一（引理 0）
  obtain ⟨v, hv, hy⟩ := hTouch
  have hle3 : countZero E ≤ 3 := by
    show countZeroV (E.map Prod.fst) ≤ 3
    refine countZeroV_le3 _ (-1, 0) (1, 0) (3, 0) hNoDup ?_
    intro w hw hw0
    have hcol : w.1 ∈ CorridorCols := zero_col_of_domain (x := w.1) (y := w.2) (hDom w hw) hw0
    have l1 : w.1 = -1 ∨ w.1 = 1 ∨ w.1 = 3 := by simpa [CorridorCols] using hcol
    have h0 : w.2 = 0 := hw0
    rcases l1 with h | h | h
    · have hA : w = (-1, 0) := by
        obtain ⟨hx, hy'⟩ := w
        have h1 : hx = -1 := h
        have h2 : hy' = 0 := h0
        subst h1
        subst h2
        rfl
      exact Or.inl hA
    · have hB : w = (1, 0) := by
        obtain ⟨hx, hy'⟩ := w
        have h1 : hx = 1 := h
        have h2 : hy' = 0 := h0
        subst h1
        subst h2
        rfl
      exact Or.inr (Or.inl hB)
    · have hC : w = (3, 0) := by
        obtain ⟨hx, hy'⟩ := w
        have h1 : hx = 3 := h
        have h2 : hy' = 0 := h0
        subst h1
        subst h2
        rfl
      exact Or.inr (Or.inr hC)
  omega

/-! ### T4a：顶点数分解 K = n₋₁+n₁+n₃（2026-10-02 傍晚二）

y=0 顶点按列分拆计数——K=2+每列≤1 ⟹ 三组合分支形态（顶点侧完备）。
泛型件：countP_eq0/countP_le1（谓词唯一性）。 -/

/-- 列 w 的 y=0 顶点数（列指示序列的 true 计数）。 -/
def countColZero (vs : List Pt) (w : ℤ) : ℕ :=
  (vs.map (fun v : Pt => decide (v.1 = w ∧ v.2 = 0))).countP (fun x : Bool => x)

/-- 列计数的 cons 展开。 -/
theorem countColZero_cons (v : Pt) (t : List Pt) (x : ℤ) :
    countColZero (v :: t) x = countColZero t x + b2n (decide (v.1 = x ∧ v.2 = 0)) := by
  show List.countP (fun b : Bool => b)
    (List.map (fun v : Pt => decide (v.1 = x ∧ v.2 = 0)) (v :: t)) = _
  rw [List.map_cons, List.countP_cons]
  congr 1
  cases h : decide (v.1 = x ∧ v.2 = 0) <;> simp [b2n, h]

/-- 泛型 countP 零化：全列谓词 false ⟹ 计数=0。 -/
theorem countP_eq0' : ∀ (l : List Pt) (q : Pt → Bool),
    (∀ w ∈ l, q w = false) → (l.map q).countP (fun x : Bool => x) = 0 := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons a t ih =>
    intro q h
    show List.countP (fun x : Bool => x) (q a :: List.map q t) = 0
    rw [List.countP_cons, h a (List.mem_cons_self (a := a) (l := t))]
    show List.countP (fun x : Bool => x) (List.map q t) + 0 = 0
    rw [Nat.add_zero]
    exact ih q (fun w hw => h w (List.mem_cons_of_mem _ hw))

/-- 泛型 countP ≤1：谓词为 true 的点唯一 ⟹ 计数≤1。 -/
theorem countP_le1' : ∀ (l : List Pt) (q : Pt → Bool), NoDupV l →
    (∀ u v : Pt, q u = true → q v = true → u = v) →
    (l.map q).countP (fun x : Bool => x) ≤ 1 := by
  intro l
  induction l with
  | nil => intro _ _ _; simp
  | cons a t ih =>
    intro q hnd huniq
    obtain ⟨hvnt, hndt⟩ := hnd
    show List.countP (fun x : Bool => x) (q a :: List.map q t) ≤ 1
    rw [List.countP_cons]
    cases hqa : q a
    · show List.countP (fun x : Bool => x) (List.map q t) + 0 ≤ 1
      rw [Nat.add_zero]
      exact ih q hndt huniq
    · -- q a = true：t 中 q 全 false（q u = true → u = a → a ∈ t 矛盾）
      have ht0 : ∀ w ∈ t, q w = false := by
        intro w hw
        by_cases hqw : q w = true
        · have haw : a = w := huniq a w hqa hqw
          subst haw
          exact absurd hw hvnt
        · cases hw' : q w
          · rfl
          · exact absurd hw' hqw
      rw [countP_eq0' t q ht0]
      show 0 + 1 ≤ 1
      rfl

/-- 列计数 ≤1：列 w 的 y=0 点唯一（(w,0)）+顶点互异。 -/
theorem countColZero_le1 (vs : List Pt) (w : ℤ) (hnd : NoDupV vs) :
    countColZero vs w ≤ 1 := by
  refine countP_le1' vs (fun v : Pt => decide (v.1 = w ∧ v.2 = 0)) hnd ?_
  intro u v hu hv
  simp only [decide_eq_true_eq] at hu hv
  exact Prod.ext (hu.1.trans hv.1.symm) (hu.2.trans hv.2.symm)

/-- **T4a（顶点数分解）**：每个 y=0 顶点列三选一 ⟹ K = n₋₁+n₁+n₃。 -/
theorem countZeroV_split3 : ∀ l : List Pt,
    (∀ w ∈ l, w.2 = 0 → w.1 = -1 ∨ w.1 = 1 ∨ w.1 = 3) →
    countZeroV l = countColZero l (-1) + countColZero l 1 + countColZero l 3 := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
    intro hin
    have htail : ∀ w ∈ t, w.2 = 0 → w.1 = -1 ∨ w.1 = 1 ∨ w.1 = 3 := fun w hw h0 =>
      hin w (List.mem_cons_of_mem _ hw) h0
    rw [countZeroV_cons, countColZero_cons, countColZero_cons, countColZero_cons, ih htail]
    by_cases h0 : a.2 = 0
    · rcases hin a (List.mem_cons_self (a := a) (l := t)) h0 with h | h | h
      · have h1 : decide (a.2 = 0) = true := by simp [h0]
        have h2 : decide (a.1 = -1 ∧ a.2 = 0) = true := by simp [h, h0]
        have h3 : decide (a.1 = 1 ∧ a.2 = 0) = false := by simp [h, h0]
        have h4 : decide (a.1 = 3 ∧ a.2 = 0) = false := by simp [h, h0]
        rw [h1, h2, h3, h4]; simp only [b2n, if_true, if_false]
        omega
      · have h1 : decide (a.2 = 0) = true := by simp [h0]
        have h2 : decide (a.1 = -1 ∧ a.2 = 0) = false := by simp [h, h0]
        have h3 : decide (a.1 = 1 ∧ a.2 = 0) = true := by simp [h, h0]
        have h4 : decide (a.1 = 3 ∧ a.2 = 0) = false := by simp [h, h0]
        rw [h1, h2, h3, h4]; simp only [b2n, if_true, if_false]
        omega
      · have h1 : decide (a.2 = 0) = true := by simp [h0]
        have h2 : decide (a.1 = -1 ∧ a.2 = 0) = false := by simp [h, h0]
        have h3 : decide (a.1 = 1 ∧ a.2 = 0) = false := by simp [h, h0]
        have h4 : decide (a.1 = 3 ∧ a.2 = 0) = true := by simp [h, h0]
        rw [h1, h2, h3, h4]; simp only [b2n, if_true, if_false]
        omega
    · have h1 : decide (a.2 = 0) = false := by simp [h0]
      have h2 : decide (a.1 = -1 ∧ a.2 = 0) = false := by simp [h0]
      have h3 : decide (a.1 = 1 ∧ a.2 = 0) = false := by simp [h0]
      have h4 : decide (a.1 = 3 ∧ a.2 = 0) = false := by simp [h0]
      rw [h1, h2, h3, h4]; simp only [b2n, if_true, if_false]
      omega

/-- 三数 0/1 域内和为 2 ⟹ 三组合分支（omega 不产析取·手工分支）。 -/
theorem two_of_three (x y z : ℕ) (hx : x ≤ 1) (hy : y ≤ 1) (hz : z ≤ 1)
    (hsum : x + y + z = 2) :
    (x = 1 ∧ y = 1 ∧ z = 0) ∨ (x = 1 ∧ y = 0 ∧ z = 1) ∨ (x = 0 ∧ y = 1 ∧ z = 1) := by
  by_cases h1 : x = 1
  · subst h1
    have hy0 : y = 0 ∨ y = 1 := by omega
    rcases hy0 with hy0 | hy0
    · exact Or.inr (Or.inl ⟨rfl, hy0, by omega⟩)
    · exact Or.inl ⟨rfl, hy0, by omega⟩
  · have hx0 : x = 0 := by omega
    subst hx0
    exact Or.inr (Or.inr ⟨rfl, by omega, by omega⟩)

/-- **T4a 推论（三组合分支形态·顶点侧）**：K=2+每列≤1 ⟹
    (n₋₁,n₁,n₃) 三选一：{P₁,P₂}/{P₁,P₃}/{P₂,P₃}。 -/
theorem split3_two (vs : List Pt) (hnd : NoDupV vs)
    (hin : ∀ w ∈ vs, w.2 = 0 → w.1 = -1 ∨ w.1 = 1 ∨ w.1 = 3)
    (hK : countZeroV vs = 2) :
    (countColZero vs (-1) = 1 ∧ countColZero vs 1 = 1 ∧ countColZero vs 3 = 0) ∨
    (countColZero vs (-1) = 1 ∧ countColZero vs 1 = 0 ∧ countColZero vs 3 = 1) ∨
    (countColZero vs (-1) = 0 ∧ countColZero vs 1 = 1 ∧ countColZero vs 3 = 1) := by
  have hsum := countZeroV_split3 vs hin
  have h1 := countColZero_le1 vs (-1) hnd
  have h2 := countColZero_le1 vs 1 hnd
  have h3 := countColZero_le1 vs 3 hnd
  exact two_of_three _ _ _ h1 h2 h3 (by omega)

/-! ### T4b 核心：G2 riser 和引理（2026-10-02 晚）

y=0 顶点处的入边/出边恰一 riser：S1（同侧不触零）排除 SameSide →
eOut 四支仅 (0,±1) 两支合法（h0: b2=0）→ eIn（d1=b2=0 触零）走 IsCrossEdge
→ 反向对 ((1,0),(0,1))/((-1,0),(0,-1)) 由无往返排除 → 恒 b2n 和=1。 -/

/-- S1：同侧边两端都不触 y=0。 -/
theorem sameSide_y_ne0 (e : Pt × Pt) (h : SameSide e) : e.1.2 ≠ 0 ∧ e.2.2 ≠ 0 := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := e
  simp only [SameSide] at h
  show b ≠ 0 ∧ d ≠ 0
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · omega
  · omega

/-- **G2（riser 和引理·度结构核心）**：走廊形态+无往返下，y=0 顶点处的
    入边与出边恰一 riser——b2n 和 = 1（每顶点恰贡献一 riser 边）。 -/
theorem G2_riser_sum (eIn eOut : Pt × Pt)
    (hchain : eIn.2 = eOut.1) (h0 : eOut.1.2 = 0)
    (hFIn : SameSide eIn ∨ IsCrossEdge eIn) (hFOut : SameSide eOut ∨ IsCrossEdge eOut)
    (hnb : eIn.1 = eOut.2 → eIn.2 = eOut.1 → eIn = eOut) :
    b2n (isRiserAt eIn eOut.1.1) + b2n (isRiserAt eOut eOut.1.1) = 1 := by
  obtain ⟨⟨a1, b1⟩, ⟨c1, d1⟩⟩ := eIn
  obtain ⟨⟨a2, b2⟩, ⟨c2, d2⟩⟩ := eOut
  have hcc : c1 = a2 := congrArg Prod.fst hchain
  have hdd : d1 = b2 := congrArg Prod.snd hchain
  have h0' : b2 = 0 := h0
  subst h0'      -- 消 b2（RHS 字面·方向确定）
  have hccs : a2 = c1 := hcc.symm
  subst hccs     -- 消 c1（RHS 变量·保 a2）
  subst hdd      -- d1 = 0 → 消 d1
  simp only [SameSide, IsCrossEdge] at hFIn hFOut
  -- eOut 非 SameSide（b2 = 0）
  rcases hFOut with hs2 | hc2
  · rcases hs2 with ⟨h21, h22⟩ | ⟨h23, h24⟩
    · exfalso; omega
    · exfalso; omega
  · -- eOut 穿越四支：b2=0 排除支1/支4，剩支2 (0,1)/支3 (0,-1)
    obtain ⟨hx2, hcol2, hd2s⟩ := hc2
    subst hx2       -- a2 = c2 → 消 c2（保 a2）
    rcases hd2s with hd2 | hd2s'
    · obtain ⟨hb21, hd21⟩ := hd2
      exfalso; omega
    · rcases hd2s' with hd2 | hd2
      · -- 支2：eOut = (a2,0)-(a2,1) riser
        obtain ⟨hb21, hd21⟩ := hd2
        subst hd21
        rcases hFIn with hs1 | hc1
        · rcases hs1 with ⟨h11, h12⟩ | ⟨h13, h14⟩
          · exfalso; omega
          · exfalso; omega
        · obtain ⟨hx1, hcol1, hd1s⟩ := hc1
          have hx1s : a2 = a1 := hx1.symm
          subst hx1s      -- 消 a1（RHS）·保 a2
          rcases hd1s with hd1 | hd1s2
          · -- eIn 支1：eIn=(a2,1)-(a2,0) 与 eOut=(a2,0)-(a2,1) 反向 → 无往返排除
            obtain ⟨hb11, hd11⟩ := hd1
            exfalso
            subst hb11
            have heq := hnb rfl rfl
            have hfin : (0:ℤ) = 1 := congrArg (fun p : Pt × Pt => p.2.2) heq
            omega
          · rcases hd1s2 with hd1 | hd1s2
            · obtain ⟨hb11, hd11⟩ := hd1
              exfalso; omega
            · rcases hd1s2 with hd1 | hd1s2
              · -- eIn 支3：eIn=(a2,0)-(a2,-1) 非 riser；和=1
                obtain ⟨hb11, hd11⟩ := hd1
                subst hb11
                show b2n (isRiserAt ((a2, 0), (a2, -1)) a2)
                  + b2n (isRiserAt ((a2, 0), (a2, 1)) a2) = 1
                simp [isRiserAt, b2n]
              · -- eIn 支4：eIn=(a2,-1)-(a2,0) 非 riser；和=1
                obtain ⟨hb11, hd11⟩ := hd1s2
                subst hb11
                show b2n (isRiserAt ((a2, -1), (a2, 0)) a2)
                  + b2n (isRiserAt ((a2, 0), (a2, 1)) a2) = 1
                simp [isRiserAt, b2n]
      · rcases hd2 with hd2 | hd2
        · -- 支3：eOut = (a2,0)-(a2,-1) 非 riser
          obtain ⟨hb21, hd21⟩ := hd2
          subst hd21
          rcases hFIn with hs1 | hc1
          · rcases hs1 with ⟨h11, h12⟩ | ⟨h13, h14⟩
            · exfalso; omega
            · exfalso; omega
          · obtain ⟨hx1, hcol1, hd1s⟩ := hc1
            have hx1s : a2 = a1 := hx1.symm
            subst hx1s      -- 消 a1（RHS）·保 a2
            rcases hd1s with hd1 | hd1s2
            · -- eIn 支1：eIn=(a2,1)-(a2,0) riser；和=1
              obtain ⟨hb11, hd11⟩ := hd1
              subst hb11
              show b2n (isRiserAt ((a2, 1), (a2, 0)) a2)
                + b2n (isRiserAt ((a2, 0), (a2, -1)) a2) = 1
              simp [isRiserAt, b2n]
            · rcases hd1s2 with hd1 | hd1s2
              · obtain ⟨hb11, hd11⟩ := hd1
                exfalso; omega
              · rcases hd1s2 with hd1 | hd1s2
                · -- eIn 支3：d1=-1 与 d1=b2=0 矛盾
                  obtain ⟨hb11, hd11⟩ := hd1
                  exfalso; omega
                · -- eIn 支4：eIn=(a2,-1)-(a2,0) 与 eOut=(a2,0)-(a2,-1) 反向 → 无往返排除
                  obtain ⟨hb11, hd11⟩ := hd1s2
                  exfalso
                  subst hb11
                  have heq := hnb rfl rfl
                  have hfin : (0:ℤ) = (-1:ℤ) := congrArg (fun p : Pt × Pt => p.2.2) heq
                  omega
        · -- 支4：eOut 支 (b2=-1, d2=0)——b2=0 矛盾 → 不可能
          obtain ⟨hb21, hd21⟩ := hd2
          exfalso; omega

/-! ### T4c：全链组装（2026-10-02 晚二）

countRiser 的 cons 展开（件 A 侧必备件）+ corridor_full（格点化第一层全链组装·
计数桥假设形态）：K=2 → split3_two 三选一 → hBridge 转 countRiser 奇偶 →
件 A corridor_parity ⟹ 绕井结论。计数桥（hBridge 的无条件证明）为最后单件挂账。 -/

/-- countRiser 的 cons 展开（filter.length 形态）。 -/
theorem countRiser_cons (e : Pt × Pt) (t : List (Pt × Pt)) (w : ℤ) :
    countRiser (e :: t) w = countRiser t w + b2n (isRiserAt e w) := by
  show (List.filter (fun x : Pt × Pt => isRiserAt x w) (e :: t)).length = _
  rw [List.filter_cons]
  cases hf : isRiserAt e w <;> simp [hf, b2n, List.length_cons, countRiser]

/-- 顶点三选一前提的组装（引理 0 逐顶点版）。 -/
theorem vertices_three (E : List (Pt × Pt))
    (hDom : ∀ v ∈ E.map Prod.fst, InDomain v) :
    ∀ w ∈ E.map Prod.fst, w.2 = 0 → w.1 = -1 ∨ w.1 = 1 ∨ w.1 = 3 := by
  intro w hw hw0
  have hcol : w.1 ∈ CorridorCols := zero_col_of_domain (x := w.1) (y := w.2) (hDom w hw) hw0
  have l1 : w.1 = -1 ∨ w.1 = 1 ∨ w.1 = 3 := by simpa [CorridorCols] using hcol
  have h0 : w.2 = 0 := hw0
  exact l1

/-- **走廊定理·格点化第一层全链组装（计数桥假设形态）**：
    全部已落地前提 + 计数桥假设 ⟹ 触 y=0 的圈绕某井。
    计数桥（hBridge 的无条件证明）= 最后单件挂账。 -/
theorem corridor_full (E : List (Pt × Pt)) (hE : E ≠ [])
    (hChain : AdjChain E) (hLast : E.getLast!.2 = E.head!.1)
    (hForm : ∀ e ∈ E, SameSide e ∨ IsCrossEdge e)
    (hnb : NoBacktrack E)
    (hDom : ∀ v ∈ E.map Prod.fst, InDomain v)
    (hNoDup : NoDupV (E.map Prod.fst))
    (hTouch : ∃ v : Pt, v ∈ E.map Prod.fst ∧ v.2 = 0)
    (hBridge : ∀ w : ℤ, countRiser E w = countColZero (E.map Prod.fst) w) :
    edgeSum E % 2 = 1 ∨ edgeSumB E % 2 = 1 := by
  have hk2 := countZero_eq2 E hE hChain hLast hForm hnb hDom hNoDup hTouch
  have hvs := vertices_three E hDom
  have hsplit := split3_two (E.map Prod.fst) hNoDup (hvs) hk2
  rcases hsplit with h | h | h
  · -- (n₋₁,n₁,n₃)=(1,1,0)：{P₁,P₂} → countRiser 1 奇
    have hr1 : (countRiser E 1 : ℤ) % 2 = 1 := by
      rw [hBridge 1]
      have : countColZero (E.map Prod.fst) 1 = 1 := h.2.1
      omega
    exact corridor_parity E hForm (Or.inl hr1)
  · -- (1,0,1)：{P₁,P₃} → countRiser 3 奇
    have hr3 : (countRiser E 3 : ℤ) % 2 = 1 := by
      rw [hBridge 3]
      have : countColZero (E.map Prod.fst) 3 = 1 := h.2.2
      omega
    exact corridor_parity E hForm (Or.inr hr3)
  · -- (0,1,1)：{P₂,P₃} → countRiser 1 奇
    have hr1 : (countRiser E 1 : ℤ) % 2 = 1 := by
      rw [hBridge 1]
      have : countColZero (E.map Prod.fst) 1 = 1 := h.2.1
      omega
    exact corridor_parity E hForm (Or.inl hr1)

/-! ### 计数桥：hBridge 无条件证明（路线甲·差项归纳·2026-10-02 晚四）

差 D(E) = countRiser E w − countColZero (E.map Prod.fst) w 的差项归纳。访问 (w,0) 的
两类形态逐访问差项归零：{下沉riser入 (w,1)-(w,0)（+1）×下沉cross出 (w,0)-(w,−1)（−1）}
与 {上cross入 (w,−1)-(w,0)（0）×上riser出 (w,0)-(w,1)（0）}——G2（入出边恰一 riser）
钉死两类归属。前缀不变量（bridge_invariant）把头顶点访问的出边项留在左端、入边项留在
右端；闭合（hLast）处头尾边界项经 G2 相等相消（bridge_boundary_eq）。
相消即桥（countRiser_eq_countColZero）⟹ corridor_final（格点化第一层全闭合·无条件版）。 -/

/-- ℤ 自等 beq（变量上 rfl 不归约·显式件）。 -/
theorem int_beq_self (x : ℤ) : (x == x) = true := beq_iff_eq.mpr rfl

/-- 下沉 riser：(w,1)-(w,0)——riser 中零端为终点的形态（差项 +1）。 -/
def isDownRiser (e : Pt × Pt) (w : ℤ) : Bool :=
  e.1.1 == w && e.1.2 == 1 && e.2.1 == w && e.2.2 == 0

/-- 下沉穿越：(w,0)-(w,−1)——自零点向下的非 riser 穿越边（差项 −1）。 -/
def isDownCross (e : Pt × Pt) (w : ℤ) : Bool :=
  e.1.1 == w && e.1.2 == 0 && e.2.1 == w && e.2.2 == -1

/-- **计数桥·闭合对引理**：入边-出边对（共享顶点）上，头尾边界项相等——
    b2n(isDownCross 出边 w) = b2n(isDownRiser 入边 w)。
    共享顶点触 (w,0) 时由 G2（入出恰一 riser）钉死两类访问形态同真同假；
    列不匹配或共享顶点不触零时两侧皆假。 -/
theorem bridge_boundary_pair (eIn eOut : Pt × Pt) (w : ℤ)
    (hchain : eIn.2 = eOut.1)
    (hFe : SameSide eIn ∨ IsCrossEdge eIn) (hFf : SameSide eOut ∨ IsCrossEdge eOut)
    (hnb : eIn.1 = eOut.2 → eIn.2 = eOut.1 → eIn = eOut) :
    b2n (isDownCross eOut w) = b2n (isDownRiser eIn w) := by
  by_cases hz : eOut.1.2 = 0
  · by_cases hx : eOut.1.1 = w
    · -- 共享顶点 = (w,0)：G2 钉死形态
      obtain ⟨⟨p1, q1⟩, ⟨r1, s1⟩⟩ := eIn
      obtain ⟨⟨p2, q2⟩, ⟨r2, s2⟩⟩ := eOut
      have hcc : r1 = p2 := congrArg Prod.fst hchain
      have hdd : s1 = q2 := congrArg Prod.snd hchain
      subst hdd; subst hcc
      have hz' : s1 = 0 := hz
      have hx' : r1 = w := hx
      subst hz'; subst hx'
      -- eIn = ((p1,q1),(r1,0))·eOut = ((r1,0),(r2,s2))·列 = r1
      have hG : b2n (isRiserAt ((p1, q1), (r1, 0)) r1)
          + b2n (isRiserAt ((r1, 0), (r2, s2)) r1) = 1 :=
        G2_riser_sum ((p1, q1), (r1, 0)) ((r1, 0), (r2, s2)) rfl rfl hFe hFf hnb
      by_cases hI : isRiserAt ((p1, q1), (r1, 0)) r1 = true
      · -- 入边 = 下沉 riser ⟹ 出边非 riser = 下沉 cross（两侧同真）
        have hin : b2n (isRiserAt ((p1, q1), (r1, 0)) r1) = 1 := by rw [hI]; rfl
        rw [hin] at hG
        have hO0 : isRiserAt ((r1, 0), (r2, s2)) r1 = false := by
          cases hh : isRiserAt ((r1, 0), (r2, s2)) r1
          · rfl
          · rw [hh] at hG; simp [b2n] at hG
        simp [isRiserAt] at hI
        obtain ⟨hp1, hq1⟩ := hI
        rcases hFf with hs2 | ⟨hx2, hcol2, hd2s⟩
        · exfalso
          rcases hs2 with ⟨k1, k2⟩ | ⟨k1, k2⟩
          · have k1' : (1:ℤ) ≤ (0:ℤ) := k1; omega
          · have k1' : (0:ℤ) ≤ (-1:ℤ) := k1; omega
        · have kr : r1 = r2 := hx2
          subst kr
          rcases hd2s with ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩
          · exfalso; have hz1 : (0:ℤ) = 1 := k1; omega
          · exfalso
            have ks : s2 = 1 := k2
            rw [ks] at hO0
            rw [show isRiserAt ((r1, 0), (r1, 1)) r1 = true from by simp [isRiserAt]] at hO0
            simp at hO0
          · -- (0,−1)：出边 = 下沉 cross·入边 = 下沉 riser ✓
            have ks : s2 = -1 := k2
            subst ks
            rw [show b2n (isDownCross ((r1, 0), (r1, -1)) r1) = 1 from by
                  simp [isDownCross, b2n, int_beq_self],
                show b2n (isDownRiser ((p1, q1), (r1, 0)) r1) = 1 from by
                  simp [isDownRiser, b2n, int_beq_self, hp1, hq1]]
          · exfalso; have hz1 : (0:ℤ) = (-1:ℤ) := k1; omega
      · -- 入边非 riser ⟹ 出边 = 上 riser（isDownCross 假）+ 入边 = 上 cross（isDownRiser 假）
        have hin0 : b2n (isRiserAt ((p1, q1), (r1, 0)) r1) = 0 := by
          cases hh : isRiserAt ((p1, q1), (r1, 0)) r1
          · rfl
          · exact absurd hh hI
        rw [hin0] at hG
        have hO1 : isRiserAt ((r1, 0), (r2, s2)) r1 = true := by
          cases hh : isRiserAt ((r1, 0), (r2, s2)) r1
          · rw [hh] at hG; simp [b2n] at hG
          · rfl
        rcases hFf with hs2 | ⟨hx2, hcol2, hd2s⟩
        · exfalso
          rcases hs2 with ⟨k1, k2⟩ | ⟨k1, k2⟩
          · have k1' : (1:ℤ) ≤ (0:ℤ) := k1; omega
          · have k1' : (0:ℤ) ≤ (-1:ℤ) := k1; omega
        · have kr : r1 = r2 := hx2
          subst kr
          rcases hd2s with ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩
          · exfalso; have hz1 : (0:ℤ) = 1 := k1; omega
          · -- (0,1)：出边 = 上 riser ✓
            have ks : s2 = 1 := k2
            subst ks
            rw [show b2n (isDownCross ((r1, 0), (r1, 1)) r1) = 0 from by
                  simp [isDownCross, b2n, int_beq_self]]
            rcases hFe with hsi | ⟨hxi, hcoli, hdsi⟩
            · exfalso
              rcases hsi with ⟨k1, k2⟩ | ⟨k1, k2⟩
              · have k2' : (1:ℤ) ≤ (0:ℤ) := k2; omega
              · have k2' : (0:ℤ) ≤ (-1:ℤ) := k2; omega
            · rcases hdsi with ⟨j1, j2⟩ | ⟨j1, j2⟩ | ⟨j1, j2⟩ | ⟨j1, j2⟩
              · exfalso
                have jq : q1 = 1 := j1
                subst jq
                have hraw : ((p1, 1), (r1, 0)).1.1 = ((p1, 1), (r1, 0)).2.1 := hxi
                rw [show ((p1, 1), (r1, 0)).1.1 = p1 from rfl,
                    show ((p1, 1), (r1, 0)).2.1 = r1 from rfl] at hraw
                rw [show isRiserAt ((p1, 1), (r1, 0)) r1 = true from by
                      simp [isRiserAt, int_beq_self, hraw]] at hI
                simp at hI
              · exfalso; have jz : (0:ℤ) = 1 := j2; omega
              · exfalso; have jz : (0:ℤ) = (-1:ℤ) := j2; omega
              · -- (−1,0)：入边 = 上 cross ✓
                have jq : q1 = -1 := j1
                subst jq
                have hraw : ((p1, -1), (r1, 0)).1.1 = ((p1, -1), (r1, 0)).2.1 := hxi
                rw [show ((p1, -1), (r1, 0)).1.1 = p1 from rfl,
                    show ((p1, -1), (r1, 0)).2.1 = r1 from rfl] at hraw
                rw [show b2n (isDownRiser ((p1, -1), (r1, 0)) r1) = 0 from by
                      simp [isDownRiser, b2n, int_beq_self, hraw]]
          · exfalso
            have ks : s2 = -1 := k2
            rw [ks] at hO1
            rw [show isRiserAt ((r1, 0), (r1, -1)) r1 = false from by simp [isRiserAt]] at hO1
            simp at hO1
          · exfalso; have hz1 : (0:ℤ) = (-1:ℤ) := k1; omega
    · -- 列不匹配：两侧皆假
      have hb1 : (eOut.1.1 == w) = false := by
        cases hb : eOut.1.1 == w
        · rfl
        · exact absurd (beq_iff_eq.mp hb) hx
      have hb2 : (eIn.2.1 == w) = false := by
        cases hb : eIn.2.1 == w
        · rfl
        · exact absurd (beq_iff_eq.mp hb)
            (fun hh => hx (by rw [← congrArg Prod.fst hchain]; exact hh))
      rw [show b2n (isDownCross eOut w) = 0 from by simp [isDownCross, b2n, hb1],
          show b2n (isDownRiser eIn w) = 0 from by simp [isDownRiser, b2n, hb2]]
  · -- 共享顶点不触零：出边非下沉cross（起点 y≠0）、入边非 riser（终点 y≠0）
    have hb1 : (eOut.1.2 == 0) = false := by
      cases hb : eOut.1.2 == 0
      · rfl
      · exact absurd (beq_iff_eq.mp hb) hz
    have hb2 : (eIn.2.2 == 0) = false := by
      cases hb : eIn.2.2 == 0
      · rfl
      · exact absurd (beq_iff_eq.mp hb)
          (fun hh => hz (by rw [← congrArg Prod.snd hchain]; exact hh))
    rw [show b2n (isDownCross eOut w) = 0 from by simp [isDownCross, b2n, hb1],
        show b2n (isDownRiser eIn w) = 0 from by simp [isDownRiser, b2n, hb2]]

/-- **计数桥·步进引理**：走廊形态+无往返下（f = e 的后继边），
    b2n(isRiserAt e w) + b2n(isDownCross e w) = b2n(e.1 触 (w,0)) + b2n(isDownCross f w)。
    e 同侧⟹四项全零；e 穿越四形态分类——(1,0)/(−1,0) 支 f 起点 y=0 由 G2 钉死 f 形态
    （下沉riser⟹f=下沉cross·上cross⟹f=上riser）；(0,±1) 支 f 起点非零纯 Bool 归约。 -/
theorem bridge_step (e f : Pt × Pt) (w : ℤ)
    (hchain : e.2 = f.1)
    (hFe : SameSide e ∨ IsCrossEdge e) (hFf : SameSide f ∨ IsCrossEdge f)
    (hnb : e.1 = f.2 → e.2 = f.1 → e = f) :
    b2n (isRiserAt e w) + b2n (isDownCross e w)
      = b2n (decide (e.1.1 = w ∧ e.1.2 = 0)) + b2n (isDownCross f w) := by
  obtain ⟨⟨a1, b1⟩, ⟨c1, d1⟩⟩ := e
  obtain ⟨⟨a2, b2⟩, ⟨c2, d2⟩⟩ := f
  have hcc : c1 = a2 := congrArg Prod.fst hchain
  have hdd : d1 = b2 := congrArg Prod.snd hchain
  subst hdd; subst hcc
  -- e = ((a1,b1),(c1,d1))·f = ((c1,d1),(c2,d2))
  have eY1 : ((a1, b1), (c1, d1)).1.2 = b1 := rfl
  have eY2 : ((a1, b1), (c1, d1)).2.2 = d1 := rfl
  have hFe0 : SameSide ((a1, b1), (c1, d1)) ∨ IsCrossEdge ((a1, b1), (c1, d1)) := hFe
  rcases hFe with hs1 | ⟨hx1, hcol1, hd1s⟩
  · -- e 同侧：两端 y ≠ 0 ⟹ 四项全零（Prop 层 n 事实杀 decide 项·Bool 层 q 事实杀 == 项）
    rcases hs1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have n1 : b1 ≠ 0 := by omega
      have n2 : d1 ≠ 0 := by omega
      have q1' : (b1 == 0) = false := by
        cases q : b1 == 0
        · rfl
        · exact absurd (beq_iff_eq.mp q) n1
      have q2' : (d1 == 0) = false := by
        cases q : d1 == 0
        · rfl
        · exact absurd (beq_iff_eq.mp q) n2
      simp [isRiserAt, isDownCross, b2n, q1', q2', n1, n2]
    · have n0 : b1 ≠ 0 := by omega
      have n1 : b1 ≠ 1 := by omega
      have n2 : d1 ≠ 0 := by omega
      have q0' : (b1 == 0) = false := by
        cases q : b1 == 0
        · rfl
        · exact absurd (beq_iff_eq.mp q) n0
      have q1' : (b1 == 1) = false := by
        cases q : b1 == 1
        · rfl
        · exact absurd (beq_iff_eq.mp q) n1
      have q2' : (d1 == 0) = false := by
        cases q : d1 == 0
        · rfl
        · exact absurd (beq_iff_eq.mp q) n2
      simp [isRiserAt, isDownCross, b2n, q0', q1', q2', n0, n1, n2]
  · rcases hd1s with ⟨hb1, hd1⟩ | ⟨hb1, hd1⟩ | ⟨hb1, hd1⟩ | ⟨hb1, hd1⟩
    · -- 支1：(1,0) 下沉 riser——f 起点 y=0 ⟹ G2 ⟹ f = (0,−1) 下沉 cross
      have hb1' : b1 = 1 := hb1
      have hd1' : d1 = 0 := hd1
      subst hb1'; subst hd1'
      have hx1' : a1 = c1 := hx1
      subst hx1'
      -- e = ((a1,1),(a1,0))·f = ((a1,0),(c2,d2))
      have hG : b2n (isRiserAt ((a1, 1), (a1, 0)) a1)
          + b2n (isRiserAt ((a1, 0), (c2, d2)) a1) = 1 :=
        G2_riser_sum ((a1, 1), (a1, 0)) ((a1, 0), (c2, d2)) rfl rfl hFe0 hFf hnb
      have hin : b2n (isRiserAt ((a1, 1), (a1, 0)) a1) = 1 := by simp [isRiserAt, b2n]
      rw [hin] at hG
      have hout : isRiserAt ((a1, 0), (c2, d2)) a1 = false := by
        cases hh : isRiserAt ((a1, 0), (c2, d2)) a1
        · rfl
        · rw [hh] at hG; simp [b2n] at hG
      rcases hFf with hs2 | ⟨hx2, hcol2, hd2s⟩
      · exfalso
        rcases hs2 with ⟨k1, k2⟩ | ⟨k1, k2⟩
        · have k1' : (1:ℤ) ≤ (0:ℤ) := k1; omega
        · have k1' : (0:ℤ) ≤ (-1:ℤ) := k1; omega
      · have hx2' : a1 = c2 := hx2
        subst hx2'
        rcases hd2s with ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩
        · exfalso; have hz1 : (0:ℤ) = 1 := k1; omega
        · exfalso
          have kd2 : d2 = 1 := k2
          rw [kd2] at hout
          rw [show isRiserAt ((a1, 0), (a1, 1)) a1 = true from by simp [isRiserAt]] at hout
          simp at hout
        · -- (0,−1) ✓
          have kd2 : d2 = -1 := k2
          subst kd2
          by_cases haw : a1 = w
          · subst haw
            simp [isRiserAt, isDownCross, b2n, int_beq_self]
          · have hb'' : (a1 == w) = false := by
              cases hb'' : a1 == w
              · rfl
              · exact absurd (beq_iff_eq.mp hb'') haw
            simp [isRiserAt, isDownCross, b2n, hb'', haw]
        · exfalso; have hz1 : (0:ℤ) = (-1:ℤ) := k1; omega
    · -- 支2：(0,1) 上 riser——f 起点 y=1 非零，纯归约
      have hb1' : b1 = 0 := hb1
      have hd1' : d1 = 1 := hd1
      subst hb1'; subst hd1'
      have hx1' : a1 = c1 := hx1
      subst hx1'
      by_cases haw : a1 = w
      · subst haw
        simp [isRiserAt, isDownCross, b2n, int_beq_self]
      · have hb'' : (a1 == w) = false := by
          cases hb'' : a1 == w
          · rfl
          · exact absurd (beq_iff_eq.mp hb'') haw
        simp [isRiserAt, isDownCross, b2n, hb'', haw]
    · -- 支3：(0,−1) 下沉 cross——f 起点 y=−1 非零，纯归约
      have hb1' : b1 = 0 := hb1
      have hd1' : d1 = -1 := hd1
      subst hb1'; subst hd1'
      have hx1' : a1 = c1 := hx1
      subst hx1'
      by_cases haw : a1 = w
      · subst haw
        simp [isRiserAt, isDownCross, b2n, int_beq_self]
      · have hb'' : (a1 == w) = false := by
          cases hb'' : a1 == w
          · rfl
          · exact absurd (beq_iff_eq.mp hb'') haw
        simp [isRiserAt, isDownCross, b2n, hb'', haw]
    · -- 支4：(−1,0) 上 cross——f 起点 y=0 ⟹ G2 ⟹ f = (0,1) 上 riser
      have hb1' : b1 = -1 := hb1
      have hd1' : d1 = 0 := hd1
      subst hb1'; subst hd1'
      have hx1' : a1 = c1 := hx1
      subst hx1'
      have hG : b2n (isRiserAt ((a1, -1), (a1, 0)) a1)
          + b2n (isRiserAt ((a1, 0), (c2, d2)) a1) = 1 :=
        G2_riser_sum ((a1, -1), (a1, 0)) ((a1, 0), (c2, d2)) rfl rfl hFe0 hFf hnb
      have hin0 : b2n (isRiserAt ((a1, -1), (a1, 0)) a1) = 0 := by simp [isRiserAt, b2n]
      rw [hin0] at hG
      have hout : isRiserAt ((a1, 0), (c2, d2)) a1 = true := by
        cases hh : isRiserAt ((a1, 0), (c2, d2)) a1
        · rw [hh] at hG; simp [b2n] at hG
        · rfl
      rcases hFf with hs2 | ⟨hx2, hcol2, hd2s⟩
      · exfalso
        rcases hs2 with ⟨k1, k2⟩ | ⟨k1, k2⟩
        · have k1' : (1:ℤ) ≤ (0:ℤ) := k1; omega
        · have k1' : (0:ℤ) ≤ (-1:ℤ) := k1; omega
      · have hx2' : a1 = c2 := hx2
        subst hx2'
        rcases hd2s with ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩
        · exfalso; have hz1 : (0:ℤ) = 1 := k1; omega
        · -- (0,1) ✓
          have kd2 : d2 = 1 := k2
          subst kd2
          by_cases haw : a1 = w
          · subst haw
            simp [isRiserAt, isDownCross, b2n, int_beq_self]
          · have hb'' : (a1 == w) = false := by
              cases hb'' : a1 == w
              · rfl
              · exact absurd (beq_iff_eq.mp hb'') haw
            simp [isRiserAt, isDownCross, b2n, hb'', haw]
        · exfalso
          have kd2 : d2 = -1 := k2
          rw [kd2] at hout
          rw [show isRiserAt ((a1, 0), (a1, -1)) a1 = false from by simp [isRiserAt]] at hout
          simp at hout
        · exfalso; have hz1 : (0:ℤ) = (-1:ℤ) := k1; omega

/-- **计数桥·前缀不变量**：非空边链（走廊形态+无往返）上，
    countRiser E w + b2n(isDownCross E.head! w)
      = countColZero (E.map Prod.fst) w + b2n(isDownRiser E.getLast! w)。
    头顶点访问的出边项留左端、入边项留右端——逐边步进（bridge_step）归纳。 -/
theorem bridge_invariant : ∀ (E : List (Pt × Pt)), E ≠ [] → ∀ (w : ℤ),
    AdjChain E → (∀ x ∈ E, SameSide x ∨ IsCrossEdge x) →
    NoBacktrack E →
    countRiser E w + b2n (isDownCross E.head! w)
      = countColZero (E.map Prod.fst) w + b2n (isDownRiser E.getLast! w) := by
  intro E
  induction E with
  | nil => intro hn; exact absurd rfl hn
  | cons e t ih =>
    intro _ w hChain hForm hnb
    cases t with
    | nil =>
      -- 单边：head! = getLast! = e
      rw [show (e :: []).head! = e from rfl, show (e :: []).getLast! = e from rfl,
          show (e :: []).map Prod.fst = [e.1] from rfl,
          countRiser_cons e [] w, countColZero_cons e.1 [] w,
          show countRiser ([] : List (Pt × Pt)) w = 0 from rfl,
          show countColZero ([] : List Pt) w = 0 from rfl]
      rcases hForm e (List.mem_cons_self (a := e) (l := [])) with hs | hc
      · rw [notRiser_of_sameSide e hs w]
        rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have n1 : e.1.2 ≠ 0 := by omega
          have n2 : e.2.2 ≠ 0 := by omega
          have q1' : (e.1.2 == 0) = false := by
            cases q : e.1.2 == 0
            · rfl
            · exact absurd (beq_iff_eq.mp q) n1
          have q2' : (e.2.2 == 0) = false := by
            cases q : e.2.2 == 0
            · rfl
            · exact absurd (beq_iff_eq.mp q) n2
          simp [isDownCross, isDownRiser, b2n, q1', q2', n1, n2]
        · have n1 : e.1.2 ≠ 0 := by omega
          have n1' : e.1.2 ≠ 1 := by omega
          have n2 : e.2.2 ≠ 0 := by omega
          have q1' : (e.1.2 == 0) = false := by
            cases q : e.1.2 == 0
            · rfl
            · exact absurd (beq_iff_eq.mp q) n1
          have q1'' : (e.1.2 == 1) = false := by
            cases q : e.1.2 == 1
            · rfl
            · exact absurd (beq_iff_eq.mp q) n1'
          have q2' : (e.2.2 == 0) = false := by
            cases q : e.2.2 == 0
            · rfl
            · exact absurd (beq_iff_eq.mp q) n2
          simp [isDownCross, isDownRiser, b2n, q1', q1'', q2', n1, n1', n2]
      · obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := e
        obtain ⟨hx, hcol, hd⟩ := hc
        have hx' : a = c := hx
        subst hx'
        rcases hd with ⟨hb, hd2⟩ | ⟨hb, hd2⟩ | ⟨hb, hd2⟩ | ⟨hb, hd2⟩
        · have hb' : b = 1 := hb
          have hd' : d = 0 := hd2
          subst hb'; subst hd'
          by_cases haw : a = w
          · subst haw
            simp [isRiserAt, isDownCross, isDownRiser, b2n, int_beq_self]
          · have hb'' : (a == w) = false := by
              cases hb'' : a == w
              · rfl
              · exact absurd (beq_iff_eq.mp hb'') haw
            simp [isRiserAt, isDownCross, isDownRiser, b2n, hb'', haw]
        · have hb' : b = 0 := hb
          have hd' : d = 1 := hd2
          subst hb'; subst hd'
          by_cases haw : a = w
          · subst haw
            simp [isRiserAt, isDownCross, isDownRiser, b2n, int_beq_self]
          · have hb'' : (a == w) = false := by
              cases hb'' : a == w
              · rfl
              · exact absurd (beq_iff_eq.mp hb'') haw
            simp [isRiserAt, isDownCross, isDownRiser, b2n, hb'', haw]
        · have hb' : b = 0 := hb
          have hd' : d = -1 := hd2
          subst hb'; subst hd'
          by_cases haw : a = w
          · subst haw
            simp [isRiserAt, isDownCross, isDownRiser, b2n, int_beq_self]
          · have hb'' : (a == w) = false := by
              cases hb'' : a == w
              · rfl
              · exact absurd (beq_iff_eq.mp hb'') haw
            simp [isRiserAt, isDownCross, isDownRiser, b2n, hb'', haw]
        · have hb' : b = -1 := hb
          have hd' : d = 0 := hd2
          subst hb'; subst hd'
          by_cases haw : a = w
          · subst haw
            simp [isRiserAt, isDownCross, isDownRiser, b2n, int_beq_self]
          · have hb'' : (a == w) = false := by
              cases hb'' : a == w
              · rfl
              · exact absurd (beq_iff_eq.mp hb'') haw
            simp [isRiserAt, isDownCross, isDownRiser, b2n, hb'', haw]
    | cons c t2 =>
      obtain ⟨hR, hAT⟩ : e.2 = c.1 ∧ AdjChain (c :: t2) := hChain
      have hFormT : ∀ x ∈ c :: t2, SameSide x ∨ IsCrossEdge x :=
        fun x hx => hForm x (List.mem_cons_of_mem _ hx)
      have hstep := bridge_step e c w hR
        (hForm e (List.mem_cons_self (a := e) (l := c :: t2)))
        (hForm c (List.mem_cons_of_mem e (List.mem_cons_self (a := c) (l := t2))))
        (fun h1 h2 => nbE_apply hnb (List.mem_cons_self (a := e) (l := c :: t2))
          (List.mem_cons_of_mem e (List.mem_cons_self (a := c) (l := t2))) h1 h2)
      rw [countRiser_cons e (c :: t2) w,
          show (e :: c :: t2).map Prod.fst = e.1 :: (c :: t2).map Prod.fst from rfl,
          countColZero_cons e.1 ((c :: t2).map Prod.fst) w,
          show (e :: c :: t2).head! = e from rfl,
          show (e :: c :: t2).getLast! = (c :: t2).getLast! from rfl]
      rw [show (c :: t2).head! = c from rfl] at ih
      have ih' := ih (by simp) w hAT hFormT (NoBacktrack_tail _ _ hnb)
      omega

/-- head ∈ 非空边列（一般版·head!_mem' 的非空列表形态）。 -/
theorem head!_mem'' : ∀ E : List (Pt × Pt), E ≠ [] → E.head! ∈ E := by
  intro E hE
  cases E with
  | nil => exact absurd rfl hE
  | cons a t => exact head!_mem' a t

/-- **计数桥·闭合引理（清单级）**：hLast 下头尾边界项相等——
    b2n(isDownCross E.head! w) = b2n(isDownRiser E.getLast! w)。
    入边 = getLast!、出边 = head!、共享顶点 = head 顶点，直接接闭合对引理。 -/
theorem bridge_boundary_eq (E : List (Pt × Pt)) (hE : E ≠ []) (w : ℤ)
    (hChain : AdjChain E) (hLast : E.getLast!.2 = E.head!.1)
    (hForm : ∀ x ∈ E, SameSide x ∨ IsCrossEdge x)
    (hnb : NoBacktrack E) :
    b2n (isDownCross E.head! w) = b2n (isDownRiser E.getLast! w) :=
  bridge_boundary_pair E.getLast! E.head! w hLast
    (hForm _ (getLast!_mem' E hE)) (hForm _ (head!_mem'' E hE))
    (fun he1 he2 => nbE_apply hnb (getLast!_mem' E hE) (head!_mem'' E hE) he1 he2)

/-- **计数桥（无条件）**：闭合圈+走廊形态+无往返下，riser 计数 = 零点列计数（∀ w）。
    不变量（bridge_invariant）+ 闭合（bridge_boundary_eq）相消即得。 -/
theorem countRiser_eq_countColZero (E : List (Pt × Pt)) (hE : E ≠ []) (w : ℤ)
    (hChain : AdjChain E) (hLast : E.getLast!.2 = E.head!.1)
    (hForm : ∀ x ∈ E, SameSide x ∨ IsCrossEdge x)
    (hnb : NoBacktrack E) :
    countRiser E w = countColZero (E.map Prod.fst) w := by
  have hi := bridge_invariant E hE w hChain hForm hnb
  have hb := bridge_boundary_eq E hE w hChain hLast hForm hnb
  rw [hb] at hi
  omega

/-- **走廊定理·格点化第一层（无条件全链）**：计数桥已证——件 A（奇偶）×件 B（形态前提
    消解）×件 B'（引理 2 链条）×T4（计数桥）全线闭合：触 y=0 的圈绕某井。 -/
theorem corridor_final (E : List (Pt × Pt)) (hE : E ≠ [])
    (hChain : AdjChain E) (hLast : E.getLast!.2 = E.head!.1)
    (hForm : ∀ e ∈ E, SameSide e ∨ IsCrossEdge e)
    (hnb : NoBacktrack E)
    (hDom : ∀ v ∈ E.map Prod.fst, InDomain v)
    (hNoDup : NoDupV (E.map Prod.fst))
    (hTouch : ∃ v : Pt, v ∈ E.map Prod.fst ∧ v.2 = 0) :
    edgeSum E % 2 = 1 ∨ edgeSumB E % 2 = 1 :=
  corridor_full E hE hChain hLast hForm hnb hDom hNoDup hTouch
    (fun w => countRiser_eq_countColZero E hE w hChain hLast hForm hnb)

/-! ### 挂账清偿三小件（2026-10-02 晚五·主人令"开始"承接盘点 #2/#3/#4）

④countZeroV ↔ IsSimple 对接引理（NoDupV ↔ List.Nodup 等价——8vs7 域的 IsSimple
直接喂走廊定理系）；②hForm 组装接线（单位边+两端域内前提版 corridor_final_unit
——件 B corridorForm_of_unit_domain 直接喂 hForm）；③NoBacktrack 局部化桥件
（hnb 全局形 ⟹ NoBacktrack E·反向 nbE_apply 应用件+tail 子集引理——为全链泛化备料）。 -/

/-- **NoDupV ↔ List.Nodup（双向·对接引理）**：自定义顶点无重复谓词与标准 API 等价——
    IsSimple（GeoAnchorSimple 的 List.Nodup (map Prod.fst)）经此直接喂走廊定理系。 -/
theorem nodupV_of_nodup : ∀ l : List Pt, List.Nodup l → NoDupV l := by
  intro l
  induction l with
  | nil => intro _; trivial
  | cons a t ih =>
    intro h
    rw [List.nodup_cons] at h
    exact ⟨h.1, ih h.2⟩

theorem nodup_of_nodupV : ∀ l : List Pt, NoDupV l → List.Nodup l := by
  intro l
  induction l with
  | nil => intro _; exact List.nodup_nil
  | cons a t ih =>
    intro h
    rw [List.nodup_cons]
    exact ⟨h.1, ih h.2⟩

/-- **IsSimple 对接（组合件）**：8vs7 域的 IsSimple ⟹ NoDupV (E.map Prod.fst)。 -/
theorem nodupV_of_isSimple (E : List (Pt × Pt)) (h : GeoAnchorSimple.IsSimple E) :
    NoDupV (E.map Prod.fst) := nodupV_of_nodup _ h

/-- **corridor_final · 单位边+两端域内前提版（hForm 接线）**：件 B 的
    corridorForm_of_unit_domain 直接喂 hForm，起点域内前提 hDom 由两端域内 hd 导出
    （v ∈ map fst ⟹ ∃ e ∈ E, e.1 = v ⟹ hd 给 InDomain v）——走廊定理最简入口。 -/
theorem corridor_final_unit (E : List (Pt × Pt)) (hE : E ≠ [])
    (hChain : AdjChain E) (hLast : E.getLast!.2 = E.head!.1)
    (hu : ∀ e ∈ E, IsUnitEdge e)
    (hd : ∀ e ∈ E, InDomain e.1 ∧ InDomain e.2)
    (hnb : NoBacktrack E)
    (hNoDup : NoDupV (E.map Prod.fst))
    (hTouch : ∃ v : Pt, v ∈ E.map Prod.fst ∧ v.2 = 0) :
    edgeSum E % 2 = 1 ∨ edgeSumB E % 2 = 1 :=
  corridor_final E hE hChain hLast (corridorForm_of_unit_domain E hu hd) hnb
    (fun v hv => by
      obtain ⟨e, he, hfv⟩ := List.mem_map.mp hv
      obtain ⟨d1, _⟩ := hd e he
      exact hfv ▸ d1)
    hNoDup hTouch

end GeoAnchorCorridor
