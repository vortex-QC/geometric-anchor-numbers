import Mathlib
import DensityMath.GeoAnchorCollapse

/-!
# 几何锚数 · 格点 π₁ 完整分类·第一块（2026-09-30 晨）

对应: papers/几何锚数_数值轮_A4承诺轴_判读档_v0.1.md §七 挂账——格点 π₁ 完整分类（Lean 大件）
上游: GeoAnchorIdentity（翻转链·声张面·flip_origin_step 门障碍）/ GeoAnchorCollapse（锚塌商·T1/T2）

内容（主形移动框架 + 完备方向的第一组规约引擎）:

  1. **主形移动 MasterStep**：同端点同绕数子列替换（端点固定·PathEnds 连接性谓词）
     ——「形变 = 把子列 S 换成同端点同绕数的 T」。单元格推挤（halfA↔halfB·在案）与
     去刺（刺→空）皆为其实例；MasterEq = 自反+双向+传递（Setoid 就绪）。
     注：既有 FlipChain 推挤保边数（长度不变量）——完备分类需主形移动（可缩长）。
  2. **声张面（主形版）**：edgeSum 在 MasterEq 下不变 → windingMQ : MasterCollapse → ℤ 良定义
     （锚塌商结构延续：T1"身份=等价类上的读数"在主形世界里重立）。
  3. **容纳面**：pathEq_imp_masterEq——旧翻转链世界（GeoAnchorCollapse.PathEq）嵌入主形世界
     （推挤=主形步实例·上下文同态引理 congr_left）——两代机件兼容不翻案。
  4. **去刺引擎**：edgeW_reverse（边反向 ⟹ 贡献反号）+ 刺剥离（闭零绕数子列整块摘除·严格缩长）
     ——「往返可消」（1D 身份平凡定理 closed1D_even_length 的 2D 算术面）。
  5. **门阶跃定理**：edgeW_up_step / edgeW_down_step——穿越贡献 = 0/1 条带 × x≥1 列的阶跃函数
     ——绕数的算术根（洞=绕行身份·flip_origin_step 的闭式版）；行拱摊平 rowArch_flatten
     （上行走 H 下行 → 行内零绕数直跑）——条带外 (r≠0) 无条件·条带内 (r=0) 以门条件为前提
     （x₁≥1 ↔ x₂≥1）——完备方向剥层归纳的工作母机。
  6. **规范形 canon**：triUp/triDown（三边三角·绕数 ±1·闭合）+ canon w 闭合且 edgeSum = w
     ——完备方向的靶形（每类含规范形）。

第二块（2026-09-30 晨续·枢纽-门规范化）: 完备方向不需要 Jordan 剥层——
  主形移动的自由度直接完成：每条边单步主形替换为过固定点 HUB=(-1,0)（死列·勾边贡献恒 0）
  与门环 g=H→A→B→H 的规范路径（canonPath p q c = 勾出 + mid(c) + 勾入）——
  相邻规范路径间原顶点两两成刺（H→pᵢ→H）被剥净（hooksAndMids_bridge·桥形式定理）
  ——闭行走收缩为门环幂：masterEq_pi1（closed E → MasterEq E (canonAt p (edgeSum E))）
  ——**pi1_classification_iff：同基点闭合路径 MasterEq E E' ↔ edgeSum E = edgeSum E'**
  （格点 π₁ = ℤ·门环生成·身份类=绕数——完整分类落地）。
-/

namespace GeoAnchorPi1

open GeoAnchor GeoAnchorCollapse

/-! ### 端点对接谓词（边列路径的连接性 + 端点） -/

/-- 边列从 u 到 v：逐边首尾相接·空列视为 u=v 的零长路径。 -/
def PathEnds : List (Pt × Pt) → Pt → Pt → Prop
  | [], u, v => u = v
  | e :: rest, u, v => u = e.1 ∧ PathEnds rest e.2 v

theorem pathEnds_nil (u : Pt) : PathEnds [] u u := rfl

/-- 端点对接的拼接律。 -/
theorem PathEnds_append {P Q : List (Pt × Pt)} {u w v : Pt}
    (hp : PathEnds P u w) (hq : PathEnds Q w v) : PathEnds (P ++ Q) u v := by
  cases P with
  | nil => rw [hp]; exact hq
  | cons e rest =>
      exact ⟨hp.1, PathEnds_append hp.2 hq⟩

/-! ### 主形移动与主形等价 -/

/-- **主形移动**：E = A++S++B → A++T++B，S、T 同为 u→v 的边列且 edgeSum 相等。
    「形变 = 同端点同绕数的子列替换」——推挤与去刺皆为其实例。 -/
inductive MasterStep : List (Pt × Pt) → List (Pt × Pt) → Prop
  | mk : ∀ (A S T B : List (Pt × Pt)) (u v : Pt),
      PathEnds S u v → PathEnds T u v → edgeSum S = edgeSum T →
      MasterStep (A ++ S ++ B) (A ++ T ++ B)

/-- 主形等价：主形移动的对称传递闭包（Setoid 就绪）。 -/
inductive MasterEq : List (Pt × Pt) → List (Pt × Pt) → Prop
  | refl : MasterEq E E
  | fwd : MasterStep E E' → MasterEq E E'
  | bwd : MasterStep E' E → MasterEq E E'
  | trans : MasterEq a b → MasterEq b c → MasterEq a c

theorem masterEq_refl (E : List (Pt × Pt)) : MasterEq E E := MasterEq.refl

theorem masterEq_sym {E E' : List (Pt × Pt)} (h : MasterEq E E') : MasterEq E' E := by
  induction h with
  | refl => exact MasterEq.refl
  | fwd hs => exact MasterEq.bwd hs
  | bwd hs => exact MasterEq.fwd hs
  | trans _ _ ih1 ih2 => exact MasterEq.trans ih2 ih1

theorem masterEq_trans {a b c : List (Pt × Pt)} (h1 : MasterEq a b) (h2 : MasterEq b c) :
    MasterEq a c := MasterEq.trans h1 h2

/-- 主形等价的左同态（上下文 C 中替换）。 -/
theorem MasterEq.congr_left : ∀ (C : List (Pt × Pt)) {E E' : List (Pt × Pt)},
    MasterEq E E' → MasterEq (C ++ E) (C ++ E') := by
  intro C E E' h
  induction h with
  | refl => exact MasterEq.refl
  | fwd hs =>
      rcases hs with ⟨A, S, T, B, u, v, hp, hq, hsum⟩
      refine MasterEq.fwd ?_
      simpa only [List.append_assoc] using
        MasterStep.mk (C ++ A) S T B u v hp hq hsum
  | bwd hs =>
      rcases hs with ⟨A, S, T, B, u, v, hp, hq, hsum⟩
      refine MasterEq.bwd ?_
      simpa only [List.append_assoc] using
        MasterStep.mk (C ++ A) S T B u v hp hq hsum
  | trans _ _ ih1 ih2 => exact MasterEq.trans ih1 ih2

/-- 主形等价的右同态（上下文 C 中替换）。 -/
theorem MasterEq.congr_right : ∀ {E E' : List (Pt × Pt)}, MasterEq E E' →
    ∀ (C : List (Pt × Pt)), MasterEq (E ++ C) (E' ++ C) := by
  intro E E' h C
  induction h with
  | refl => exact MasterEq.refl
  | fwd hs =>
      rcases hs with ⟨A, S, T, B, u, v, hp, hq, hsum⟩
      refine MasterEq.fwd ?_
      have hstep : MasterStep (A ++ S ++ (B ++ C)) (A ++ T ++ (B ++ C)) :=
        MasterStep.mk A S T (B ++ C) u v hp hq hsum
      simpa only [List.append_assoc] using hstep
  | bwd hs =>
      rcases hs with ⟨A, S, T, B, u, v, hp, hq, hsum⟩
      refine MasterEq.bwd ?_
      have hstep : MasterStep (A ++ S ++ (B ++ C)) (A ++ T ++ (B ++ C)) :=
        MasterStep.mk A S T (B ++ C) u v hp hq hsum
      simpa only [List.append_assoc] using hstep
  | trans _ _ ih1 ih2 => exact MasterEq.trans ih1 ih2

/-- 主形等价的中间同态（任意上下文 X/Y 中的子列替换）。 -/
theorem MasterEq.congr_mid {A B : List (Pt × Pt)} (h : MasterEq A B) :
    ∀ (X Y : List (Pt × Pt)), MasterEq (X ++ A ++ Y) (X ++ B ++ Y) := by
  induction h with
  | refl => intro X Y; exact masterEq_refl _
  | fwd hs =>
      intro X Y
      rcases hs with ⟨A1, S, T, B1, u, v, hp, hq, hsum⟩
      refine MasterEq.fwd ?_
      have hstep := MasterStep.mk (X ++ A1) S T (B1 ++ Y) u v hp hq hsum
      simpa only [List.append_assoc] using hstep
  | bwd hs =>
      intro X Y
      rcases hs with ⟨A1, S, T, B1, u, v, hp, hq, hsum⟩
      refine MasterEq.bwd ?_
      have hstep := MasterStep.mk (X ++ A1) S T (B1 ++ Y) u v hp hq hsum
      simpa only [List.append_assoc] using hstep
  | trans _ _ ih1 ih2 => intro X Y; exact MasterEq.trans (ih1 X Y) (ih2 X Y)

/-! ### 声张面：edgeSum 在主形等价下不变 -/

theorem edgeSum_masterStep {E E' : List (Pt × Pt)} (h : MasterStep E E') :
    edgeSum E = edgeSum E' := by
  rcases h with ⟨A, S, T, B, u, v, _, _, hsum⟩
  have hsum' : (S.map edgeW).sum = (T.map edgeW).sum := hsum
  simp only [edgeSum, List.map_append, List.sum_append, hsum']

/-- **声张面（主形版）**：主形等价保持绕数——T1"身份=等价类上的读数"在主形世界重立。 -/
theorem edgeSum_masterEq {E E' : List (Pt × Pt)} (h : MasterEq E E') :
    edgeSum E = edgeSum E' := by
  induction h with
  | refl => rfl
  | fwd hs => exact edgeSum_masterStep hs
  | bwd hs => exact (edgeSum_masterStep hs).symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- 主形商（锚塌产物·主形世界版）。 -/
def MasterSetoid : Setoid (List (Pt × Pt)) :=
  ⟨MasterEq, ⟨masterEq_refl, masterEq_sym, masterEq_trans⟩⟩

def MasterCollapse := Quotient MasterSetoid

/-- **T1·主形版**：绕数下降为主形商上的良定义函数（身份=等价类上的读数）。 -/
def windingMQ : MasterCollapse → ℤ :=
  Quotient.lift edgeSum (fun _ _ h => edgeSum_masterEq h)

/-! ### 容纳面：旧翻转链世界嵌入主形世界 -/

theorem pathEnds_halfA (x0 y0 : ℤ) : PathEnds (halfA_edges x0 y0) (x0, y0) (x0 + 1, y0 + 1) := by
  simp [PathEnds, halfA_edges]

theorem pathEnds_halfB (x0 y0 : ℤ) : PathEnds (halfB_edges x0 y0) (x0, y0) (x0 + 1, y0 + 1) := by
  simp [PathEnds, halfB_edges]

/-- 单元格推挤 = 主形移动的实例（两半同端点·half_edges_equal 在案）。 -/
theorem masterStep_half (x0 y0 : ℤ) (h : x0 ≠ 0 ∨ y0 ≠ 0) (A B : List (Pt × Pt)) :
    MasterStep (A ++ halfA_edges x0 y0 ++ B) (A ++ halfB_edges x0 y0 ++ B) := by
  refine MasterStep.mk A (halfA_edges x0 y0) (halfB_edges x0 y0) B (x0, y0) (x0 + 1, y0 + 1)
    (pathEnds_halfA x0 y0) (pathEnds_halfB x0 y0) ?_
  exact half_edges_equal x0 y0 h

/-- **容纳定理**：旧翻转链等价（PathEq）嵌入主形等价——两代机件兼容·不翻案。 -/
theorem pathEq_imp_masterEq {E E' : List (Pt × Pt)} (h : PathEq E E') : MasterEq E E' := by
  induction h with
  | refl => exact MasterEq.refl
  | stepA E1 E2 E3 x0 y0 hc _ ih =>
      exact MasterEq.trans
        (MasterEq.fwd (masterStep_half x0 y0 hc E1 E2))
        (MasterEq.congr_left _ ih)
  | stepB E1 E2 E3 x0 y0 hc _ ih =>
      exact MasterEq.trans
        (MasterEq.bwd (masterStep_half x0 y0 hc E1 E2))
        (MasterEq.congr_left _ ih)
  | trans _ _ ih1 ih2 => exact MasterEq.trans ih1 ih2

/-! ### 去刺引擎：边反向贡献反号 + 刺剥离 -/

/-- **边反向引理**：穿越贡献在边反向时反号（往返相消的算术根）。 -/
theorem edgeW_reverse (a b c d : ℤ) :
    edgeW ((a, b), (c, d)) = -edgeW ((c, d), (a, b)) := by
  have hswap : c * b - d * a = -(a * d - b * c) := by ring
  simp only [edgeW]
  by_cases h1 : (b ≤ 0 ∧ d > 0 ∧ a * d - b * c > 0)
  · have hc1 : ¬(d ≤ 0 ∧ b > 0 ∧ c * b - d * a > 0) := by
      rintro ⟨hd, _, _⟩; have := h1.2.1; omega
    have hc2 : d > 0 ∧ b ≤ 0 ∧ c * b - d * a < 0 :=
      ⟨h1.2.1, h1.1, by rw [hswap]; linarith [h1.2.2]⟩
    rw [if_pos h1, if_neg hc1, if_pos hc2]; norm_num
  · by_cases h2 : (b > 0 ∧ d ≤ 0 ∧ a * d - b * c < 0)
    · have hc1 : d ≤ 0 ∧ b > 0 ∧ c * b - d * a > 0 :=
        ⟨h2.2.1, h2.1, by rw [hswap]; linarith [h2.2.2]⟩
      have hc2 : ¬(d > 0 ∧ b ≤ 0 ∧ c * b - d * a < 0) := by
        rintro ⟨hd, _, _⟩; have := h2.2.1; omega
      rw [if_neg h1, if_pos h2, if_pos hc1]
    · have hc1 : ¬(d ≤ 0 ∧ b > 0 ∧ c * b - d * a > 0) := by
        rintro ⟨hd, hb, hs⟩
        rw [hswap] at hs
        have hx : ¬(a * d - b * c < 0) := fun hx => h2 ⟨hb, hd, hx⟩
        linarith
      have hc2 : ¬(d > 0 ∧ b ≤ 0 ∧ c * b - d * a < 0) := by
        rintro ⟨hd, hb, hs⟩
        rw [hswap] at hs
        have hx : ¬(a * d - b * c > 0) := fun hx => h1 ⟨hb, hd, hx⟩
        linarith
      rw [if_neg h1, if_neg h2, if_neg hc1, if_neg hc2]; norm_num

theorem edgeW_reverse' (p q : Pt) : edgeW (p, q) = -edgeW (q, p) := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  exact edgeW_reverse a b c d

theorem edgeSum_spur (p q : Pt) : edgeSum [(p, q), (q, p)] = 0 := by
  have h := edgeW_reverse' q p
  simp only [edgeSum, h, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
  ring

/-- **去刺**：往返刺（边+逆边）整块摘除——主形移动实例（T = 空列·零长路径）。 -/
theorem masterStep_spur (A B : List (Pt × Pt)) (p q : Pt) :
    MasterStep (A ++ [(p, q), (q, p)] ++ B) (A ++ B) := by
  have hsp : MasterStep (A ++ [(p, q), (q, p)] ++ B) (A ++ [] ++ B) :=
    MasterStep.mk A [(p, q), (q, p)] [] B p p
      (by simp [PathEnds]) (pathEnds_nil _) (edgeSum_spur p q)
  simpa using hsp

theorem masterEq_strip_spur (A B : List (Pt × Pt)) (p q : Pt) :
    MasterEq (A ++ [(p, q), (q, p)] ++ B) (A ++ B) :=
  MasterEq.fwd (masterStep_spur A B p q)

/-! ### 门阶跃定理：绕数的算术根（0/1 条带 × x≥1 列） -/

theorem edgeW_up_step (x : ℤ) : edgeW ((x, 0), (x, 1)) = if 1 ≤ x then 1 else 0 := by
  simp only [edgeW, mul_one, zero_mul, sub_zero]
  split_ifs <;> omega

theorem edgeW_down_step (x : ℤ) : edgeW ((x, 1), (x, 0)) = if 1 ≤ x then -1 else 0 := by
  simp only [edgeW, mul_one, zero_mul, sub_zero]
  split_ifs <;> omega

/-- 条带内行拱的门条件（同侧列 ⟹ 可摊平）：两竖边贡献相消。 -/
theorem gate_arch_ok (x₁ x₂ : ℤ) (h : (1 ≤ x₁ ↔ 1 ≤ x₂)) :
    edgeW ((x₁, 0), (x₁, 1)) + edgeW ((x₂, 1), (x₂, 0)) = 0 := by
  rw [edgeW_up_step, edgeW_down_step]
  by_cases h1 : 1 ≤ x₁
  · rw [if_pos h1, if_pos (h.1 h1)]; ring
  · rw [if_neg h1, if_neg (fun hx : 1 ≤ x₂ => h1 (h.mpr hx))]; ring

/-- **门障碍（绕数量子）**：异侧列 ⟹ 贡献 = ±1——摊平被门挡住
    （绕数恰好是「门条件失败的次数」——洞=绕行身份的闭式算术根）。 -/
theorem gate_arch_blocked (x₁ x₂ : ℤ) (h₁ : 1 ≤ x₁) (h₂ : x₂ ≤ 0) :
    edgeW ((x₁, 0), (x₁, 1)) + edgeW ((x₂, 1), (x₂, 0)) = 1 := by
  rw [edgeW_up_step, edgeW_down_step]
  simp only [if_pos h₁, if_neg (by omega : ¬(1 ≤ x₂))]
  omega

/-- **行拱摊平**：上行走+横行+下行 → 同端点零绕数行内直跑。
    条件 = 拱的两条竖边贡献相消（条带外自动成立·条带内=门条件）。 -/
theorem rowArch_flatten (A B : List (Pt × Pt)) (r x₁ x₂ : ℤ)
    (H H' : List (Pt × Pt))
    (hH : PathEnds H (x₁, r + 1) (x₂, r + 1)) (hH0 : edgeSum H = 0)
    (hH' : PathEnds H' (x₁, r) (x₂, r)) (hH'0 : edgeSum H' = 0)
    (hgate : edgeW ((x₁, r), (x₁, r + 1)) + edgeW ((x₂, r + 1), (x₂, r)) = 0) :
    MasterEq (A ++ (((x₁, r), (x₁, r + 1)) :: (H ++ [((x₂, r + 1), (x₂, r))])) ++ B)
             (A ++ H' ++ B) := by
  refine MasterEq.fwd
    (MasterStep.mk A (((x₁, r), (x₁, r + 1)) :: (H ++ [((x₂, r + 1), (x₂, r))])) H' B
      (x₁, r) (x₂, r) ?_ hH' ?_)
  · refine ⟨rfl, PathEnds_append hH ⟨rfl, rfl⟩⟩
  · have hexp : edgeSum (((x₁, r), (x₁, r + 1)) :: (H ++ [((x₂, r + 1), (x₂, r))]))
        = edgeW ((x₁, r), (x₁, r + 1)) + (edgeSum H + edgeW ((x₂, r + 1), (x₂, r))) := by
      simp [edgeSum]
    rw [hexp, hH0, hH'0]
    linarith [hgate]

/-- 竖边贡献归零·下侧（两端 y ≤ 0：不跨 0/1 条带）。 -/
theorem edgeW_vert_below (x y z : ℤ) (hy : y ≤ 0) (hz : z ≤ 0) :
    edgeW ((x, y), (x, z)) = 0 := by
  simp only [edgeW]
  have h1 : ¬ (y ≤ 0 ∧ z > 0 ∧ x * z - y * x > 0) := by
    rintro ⟨_, hz', _⟩; omega
  have h2 : ¬ (y > 0 ∧ z ≤ 0 ∧ x * z - y * x < 0) := by
    rintro ⟨hy', _, _⟩; omega
  rw [if_neg h1, if_neg h2]

/-- 竖边贡献归零·上侧（两端 y > 0：不跨 0/1 条带）。 -/
theorem edgeW_vert_above (x y z : ℤ) (hy : y > 0) (hz : z > 0) :
    edgeW ((x, y), (x, z)) = 0 := by
  simp only [edgeW]
  have h1 : ¬ (y ≤ 0 ∧ z > 0 ∧ x * z - y * x > 0) := by
    rintro ⟨hy', _, _⟩; omega
  have h2 : ¬ (y > 0 ∧ z ≤ 0 ∧ x * z - y * x < 0) := by
    rintro ⟨_, hz', _⟩; omega
  rw [if_neg h1, if_neg h2]

/-- 条带外行拱无条件摊平（r ≠ 0：竖边贡献恒 0）。 -/
theorem rowArch_flatten_off_strip (A B : List (Pt × Pt)) (r x₁ x₂ : ℤ) (hr : r ≠ 0)
    (H H' : List (Pt × Pt))
    (hH : PathEnds H (x₁, r + 1) (x₂, r + 1)) (hH0 : edgeSum H = 0)
    (hH' : PathEnds H' (x₁, r) (x₂, r)) (hH'0 : edgeSum H' = 0) :
    MasterEq (A ++ (((x₁, r), (x₁, r + 1)) :: (H ++ [((x₂, r + 1), (x₂, r))])) ++ B)
             (A ++ H' ++ B) := by
  have hv1 : edgeW ((x₁, r), (x₁, r + 1)) = 0 := by
    by_cases hr0 : r ≤ 0
    · have hz : r + 1 ≤ 0 := by omega
      exact edgeW_vert_below x₁ r (r + 1) hr0 hz
    · have hp : r > 0 := by omega
      have hz : r + 1 > 0 := by omega
      exact edgeW_vert_above x₁ r (r + 1) hp hz
  have hv2 : edgeW ((x₂, r + 1), (x₂, r)) = 0 := by
    by_cases hr0 : r ≤ 0
    · have hy : r + 1 ≤ 0 := by omega
      exact edgeW_vert_below x₂ (r + 1) r hy hr0
    · have hp : r > 0 := by omega
      have hy : r + 1 > 0 := by omega
      exact edgeW_vert_above x₂ (r + 1) r hy hp
  exact rowArch_flatten A B r x₁ x₂ H H' hH hH0 hH' hH'0 (by rw [hv1, hv2]; omega)

/-! ### 规范形 canon：绕数 w 的靶形 -/

/-- 逆时针三边三角（绕数 +1·闭合于 (1,0)）。 -/
def triUp : List (Pt × Pt) := [((1, 0), (1, 1)), ((1, 1), (0, 0)), ((0, 0), (1, 0))]

/-- 顺时针三边三角（绕数 −1·闭合于 (1,0)·与 triUp 同起点可链）。 -/
def triDown : List (Pt × Pt) := [((1, 0), (0, 0)), ((0, 0), (1, 1)), ((1, 1), (1, 0))]

theorem edgeSum_triUp : edgeSum triUp = 1 := by decide

theorem edgeSum_triDown : edgeSum triDown = -1 := by decide

theorem pathEnds_triUp : PathEnds triUp (1, 0) (1, 0) := by
  simp [PathEnds, triUp]

theorem pathEnds_triDown : PathEnds triDown (1, 0) (1, 0) := by
  simp [PathEnds, triDown]

/-! ### 第二块：门环规范形与完备性主定理

路线（枢纽-门规范化——主形移动自由度直接完成完备方向·无需 Jordan 剥层）：
  固定点 H=(-1,0)（死列：column −1 竖边贡献恒 0）·A=(1,0)·B=(1,1)·门环 g=H→A→B→H（绕数+1）。
  每条边 e(p→q·贡献 c) 单步主形替换为 canonPath p q c = [p→H] ++ mid(c) ++ [H→q]
  （勾边贡献恒 0·mid(c)=g^c）——原顶点在相邻规范路径间两两成刺（H→pᵢ→H）被剥净
  ——闭行走收缩为门环幂：MasterEq E (canonAt p (edgeSum E))——分类定理随之。 -/

/-- 枢纽 H（死列 -1 上的轴点·勾边贡献恒零）-/ def HUB : Pt := (-1, 0)
/-- 门环下点 A -/ def GATA : Pt := (1, 0)
/-- 门环上点 B -/ def GATB : Pt := (1, 1)

/-- 门环 g = H→A→B→H（绕数 +1·闭合于 H·π₁ 生成元）。 -/
def gLoop : List (Pt × Pt) := [(HUB, GATA), (GATA, GATB), (GATB, HUB)]

/-- 门环逆 g⁻¹ = H→B→A→H（绕数 −1·闭合于 H）。 -/
def gLoopInv : List (Pt × Pt) := [(HUB, GATB), (GATB, GATA), (GATA, HUB)]

theorem edgeSum_gLoop : edgeSum gLoop = 1 := by decide
theorem edgeSum_gLoopInv : edgeSum gLoopInv = -1 := by decide
theorem pathEnds_gLoop : PathEnds gLoop HUB HUB := by simp [PathEnds, gLoop]
theorem pathEnds_gLoopInv : PathEnds gLoopInv HUB HUB := by simp [PathEnds, gLoopInv]

/-- 规范形：w ≥ 0 取 w 个门环·w < 0 取 |w| 个门环逆（基底=门环 gLoop——
    9-30 晨第二块换基：triUp 版与 gLoop 版同为合法规范形·gLoop 版直接承载主定理）。 -/
def canon (w : ℤ) : List (Pt × Pt) :=
  if 0 ≤ w then (List.replicate w.toNat gLoop).flatten
  else (List.replicate (-w).toNat gLoopInv).flatten

theorem edgeSum_flatRep (n : ℕ) (L : List (Pt × Pt)) :
    edgeSum (List.replicate n L).flatten = n * edgeSum L := by
  induction n with
  | zero => simp [edgeSum]
  | succ k ih =>
      simp only [List.replicate_succ, List.flatten_cons]
      have hApp : edgeSum (L ++ (List.replicate k L).flatten)
          = edgeSum L + edgeSum (List.replicate k L).flatten := by
        simp [edgeSum]
      rw [hApp, ih]
      push_cast
      ring

theorem PathEnds_flatRep (n : ℕ) (L : List (Pt × Pt)) (u : Pt) (h : PathEnds L u u) :
    PathEnds (List.replicate n L).flatten u u := by
  induction n with
  | zero => simpa using pathEnds_nil u
  | succ k ih =>
      simp only [List.replicate_succ, List.flatten_cons]
      exact PathEnds_append h ih

theorem edgeSum_canon (w : ℤ) : edgeSum (canon w) = w := by
  unfold canon
  split_ifs with h
  · have hw : ((w.toNat : ℤ)) = w := by omega
    rw [edgeSum_flatRep, hw, edgeSum_gLoop]
    ring
  · have hw : (((-w).toNat : ℤ)) = -w := by omega
    rw [edgeSum_flatRep, hw, edgeSum_gLoopInv]
    ring

/-- 规范形闭合（可链：triUp/triDown 同闭于 (1,0)）。 -/
theorem pathEnds_canon (w : ℤ) : PathEnds (canon w) HUB HUB := by
  unfold canon
  split_ifs with h
  · exact PathEnds_flatRep _ _ _ pathEnds_gLoop
  · exact PathEnds_flatRep _ _ _ pathEnds_gLoopInv

/-! ### 勾边与规范路径（枢纽-门规范化） -/

/-- **勾边引理·出**：任意点 (a,b) 到枢纽 H 的边贡献恒 0。 -/
theorem edgeW_hook_out (a b : ℤ) : edgeW ((a, b), HUB) = 0 := by
  have hH : HUB = (-1, 0) := rfl
  simp only [edgeW, hH, mul_zero, neg_mul, sub_neg_eq_add, zero_add]
  split_ifs <;> first | omega | rfl

/-- **勾边引理·入**：枢纽 H 到任意点 (c,d) 的边贡献恒 0。 -/
theorem edgeW_hook_in (c d : ℤ) : edgeW (HUB, (c, d)) = 0 := by
  have hH : HUB = (-1, 0) := rfl
  simp only [edgeW, hH, neg_mul, zero_mul, sub_zero]
  split_ifs <;> first | omega | rfl

theorem edgeW_hook_out' (p : Pt) : edgeW (p, HUB) = 0 := by
  obtain ⟨a, b⟩ := p
  exact edgeW_hook_out a b

theorem edgeW_hook_in' (q : Pt) : edgeW (HUB, q) = 0 := by
  obtain ⟨c, d⟩ := q
  exact edgeW_hook_in c d

theorem edgeSum_hook_out (p : Pt) : edgeSum [(p, HUB)] = 0 := by
  simp [edgeSum, edgeW_hook_out']

theorem edgeSum_hook_in (q : Pt) : edgeSum [(HUB, q)] = 0 := by
  simp [edgeSum, edgeW_hook_in']

/-- 门环幂读数 mid(c)：c=1 取 g·c=−1 取 g⁻¹·其余空（c ∈ {−1,0,1}）。 -/
def mid (c : ℤ) : List (Pt × Pt) :=
  if c = 1 then gLoop else if c = -1 then gLoopInv else []

theorem mid_one : mid 1 = gLoop := rfl
theorem mid_neg : mid (-1) = gLoopInv := rfl
theorem mid_zero : mid 0 = [] := rfl

theorem pathEnds_mid (c : ℤ) : PathEnds (mid c) HUB HUB := by
  unfold mid; split_ifs <;> simp [pathEnds_gLoop, pathEnds_gLoopInv, pathEnds_nil]

theorem edgeSum_mid (c : ℤ) (hc : c = 1 ∨ c = -1 ∨ c = 0) : edgeSum (mid c) = c := by
  rcases hc with hc | hc | hc
  · subst hc; simp [mid, edgeSum_gLoop]
  · subst hc; simp [mid, edgeSum_gLoopInv]
  · subst hc; simp [mid, edgeSum]

/-- **规范路径**：p→q 贡献 c 的主形规范形 = 勾出 + 门环幂 + 勾入（过固定点集）。 -/
def canonPath (p q : Pt) (c : ℤ) : List (Pt × Pt) := [(p, HUB)] ++ mid c ++ [(HUB, q)]

theorem pathEnds_canonPath (p q : Pt) (c : ℤ) : PathEnds (canonPath p q c) p q := by
  unfold canonPath
  exact PathEnds_append (PathEnds_append ⟨rfl, pathEnds_nil HUB⟩ (pathEnds_mid c))
    ⟨rfl, pathEnds_nil q⟩

theorem edgeSum_canonPath (p q : Pt) (c : ℤ) (hc : c = 1 ∨ c = -1 ∨ c = 0) :
    edgeSum (canonPath p q c) = c := by
  show edgeSum ([(p, HUB)] ++ mid c ++ [(HUB, q)]) = c
  have h1 : edgeSum ([(p, HUB)] ++ mid c ++ [(HUB, q)])
      = edgeSum [(p, HUB)] + (edgeSum (mid c) + edgeSum [(HUB, q)]) := by simp [edgeSum]
  rw [h1, edgeSum_hook_out, edgeSum_hook_in, edgeSum_mid c hc]
  ring

/-- **贡献值域**：edgeW 只取 ±1/0。 -/
theorem edgeW_range (e : Pt × Pt) : edgeW e = 1 ∨ edgeW e = -1 ∨ edgeW e = 0 := by
  obtain ⟨p, q⟩ := e
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  simp only [edgeW]
  split_ifs <;> simp

/-! ### 逐边规范化与刺剥净 -/

/-- **单边规范化**：每条边单步主形替换为过枢纽的规范路径（同端点·同贡献）。 -/
theorem masterEq_edge_canon (e : Pt × Pt) :
    MasterEq [e] (canonPath e.1 e.2 (edgeW e)) := by
  have h := MasterStep.mk [] [e] (canonPath e.1 e.2 (edgeW e)) [] e.1 e.2
    (by simp [PathEnds]) (pathEnds_canonPath e.1 e.2 (edgeW e))
    (by rw [edgeSum_canonPath e.1 e.2 (edgeW e) (edgeW_range e)]; simp [edgeSum])
  exact MasterEq.fwd (by simpa using h)

/-- 逐边规范化（整列）。 -/
def hooksAndMids : List (Pt × Pt) → List (Pt × Pt)
  | [] => []
  | e :: rest => canonPath e.1 e.2 (edgeW e) ++ hooksAndMids rest

/-- 门环幂段（剥刺后的剩余）。 -/
def concatMid : List (Pt × Pt) → List (Pt × Pt)
  | [] => []
  | e :: rest => mid (edgeW e) ++ concatMid rest

/-- **逐边规范化定理**：整列主形等价于其规范化列。 -/
theorem masterEq_hooksAndMids : ∀ E : List (Pt × Pt), MasterEq E (hooksAndMids E) := by
  intro E
  induction E with
  | nil => exact MasterEq.refl
  | cons e rest ih =>
      have hstep := MasterStep.mk [] [e] (canonPath e.1 e.2 (edgeW e)) rest e.1 e.2
        (by simp [PathEnds]) (pathEnds_canonPath e.1 e.2 (edgeW e)) (by
          rw [edgeSum_canonPath e.1 e.2 (edgeW e) (edgeW_range e)]; simp [edgeSum])
      have h1 : MasterEq (e :: rest) (canonPath e.1 e.2 (edgeW e) ++ rest) :=
        MasterEq.fwd (by simpa using hstep)
      exact MasterEq.trans h1 (MasterEq.congr_left _ ih)

/-- **桥形式定理**：非空列的规范化列经刺剥净 = 勾出 + 门环幂段 + 勾入
    （相邻规范路径间 H→pᵢ→H 两两成刺——原顶点全部消失）。 -/
theorem hooksAndMids_bridge : ∀ (E : List (Pt × Pt)) (s t : Pt), E ≠ [] →
    PathEnds E s t → MasterEq (hooksAndMids E) ([(s, HUB)] ++ concatMid E ++ [(HUB, t)]) := by
  intro E
  induction E with
  | nil => intro s t hne; exact absurd rfl hne
  | cons e rest ih =>
      intro s t _ hE
      cases rest with
      | nil =>
        have h1 : s = e.1 := hE.1
        have h2 : e.2 = t := hE.2
        subst h1
        subst h2
        simp only [hooksAndMids, concatMid, canonPath, List.append_nil]
        exact masterEq_refl _
      | cons e2 rest2 =>
        have hq : PathEnds (e2 :: rest2) e.2 t := hE.2
        have hne : (e2 :: rest2) ≠ [] := by simp
        have hihr := ih e.2 t hne hq
        have hcong : MasterEq
            (canonPath e.1 e.2 (edgeW e) ++ hooksAndMids (e2 :: rest2))
            (canonPath e.1 e.2 (edgeW e)
              ++ ([(e.2, HUB)] ++ concatMid (e2 :: rest2) ++ [(HUB, t)])) :=
          MasterEq.congr_left _ hihr
        have hstrip := masterEq_strip_spur
          ([(e.1, HUB)] ++ mid (edgeW e)) (concatMid (e2 :: rest2) ++ [(HUB, t)]) HUB e.2
        have hstep : MasterEq
            (canonPath e.1 e.2 (edgeW e)
              ++ ([(e.2, HUB)] ++ concatMid (e2 :: rest2) ++ [(HUB, t)]))
            ([(e.1, HUB)] ++ (mid (edgeW e) ++ concatMid (e2 :: rest2)) ++ [(HUB, t)]) := by
          have hpair : [(HUB, e.2), (e.2, HUB)] = [(HUB, e.2)] ++ [(e.2, HUB)] := rfl
          simpa only [hpair, List.append_assoc, hooksAndMids, canonPath] using hstrip
        show MasterEq (hooksAndMids (e :: e2 :: rest2))
          ([(s, HUB)] ++ concatMid (e :: e2 :: rest2) ++ [(HUB, t)])
        rw [hE.1]
        have hlhs : hooksAndMids (e :: e2 :: rest2)
            = canonPath e.1 e.2 (edgeW e) ++ hooksAndMids (e2 :: rest2) := rfl
        rw [hlhs]
        have hcm : concatMid (e :: e2 :: rest2)
            = mid (edgeW e) ++ concatMid (e2 :: rest2) := rfl
        rw [hcm]
        exact MasterEq.trans hcong hstep

/-! ### 门环对消与幂归约 -/

/-- **门环对消**：g ++ g⁻¹ 三步剥刺归零（B→H/H→B、A→B/B→A、H→A/A→H）。 -/
theorem gPairNil : MasterEq (gLoop ++ gLoopInv) [] := by
  have s1 : MasterStep (gLoop ++ gLoopInv)
      ([(HUB, GATA), (GATA, GATB), (GATB, GATA), (GATA, HUB)]) :=
    MasterStep.mk [(HUB, GATA), (GATA, GATB)] [(GATB, HUB), (HUB, GATB)] []
      [(GATB, GATA), (GATA, HUB)] GATB GATB
      (by simp [PathEnds]) (pathEnds_nil _)
      (by have h := edgeW_reverse' HUB GATB
          simp only [edgeSum, h, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
          ring)
  have s2 : MasterStep ([(HUB, GATA), (GATA, GATB), (GATB, GATA), (GATA, HUB)])
      ([(HUB, GATA), (GATA, HUB)]) :=
    MasterStep.mk [(HUB, GATA)] [(GATA, GATB), (GATB, GATA)] [] [(GATA, HUB)] GATA GATA
      (by simp [PathEnds]) (pathEnds_nil _)
      (by have h := edgeW_reverse' GATB GATA
          simp only [edgeSum, h, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
          ring)
  have s3 : MasterStep ([(HUB, GATA), (GATA, HUB)]) [] :=
    MasterStep.mk [] [(HUB, GATA), (GATA, HUB)] [] [] HUB HUB
      (by simp [PathEnds]) (pathEnds_nil _)
      (by have h := edgeW_reverse' GATA HUB
          simp only [edgeSum, h, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
          ring)
  exact MasterEq.trans (MasterEq.fwd s1) (MasterEq.trans (MasterEq.fwd s2) (MasterEq.fwd s3))

/-- **门环逆对消**：g⁻¹ ++ g 三步剥刺归零（对称）。 -/
theorem gInvPairNil : MasterEq (gLoopInv ++ gLoop) [] := by
  have s1 : MasterStep (gLoopInv ++ gLoop)
      ([(HUB, GATB), (GATB, GATA), (GATA, GATB), (GATB, HUB)]) :=
    MasterStep.mk [(HUB, GATB), (GATB, GATA)] [(GATA, HUB), (HUB, GATA)] []
      [(GATA, GATB), (GATB, HUB)] GATA GATA
      (by simp [PathEnds]) (pathEnds_nil _)
      (by have h := edgeW_reverse' HUB GATA
          simp only [edgeSum, h, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
          ring)
  have s2 : MasterStep ([(HUB, GATB), (GATB, GATA), (GATA, GATB), (GATB, HUB)])
      ([(HUB, GATB), (GATB, HUB)]) :=
    MasterStep.mk [(HUB, GATB)] [(GATB, GATA), (GATA, GATB)] [] [(GATB, HUB)] GATB GATB
      (by simp [PathEnds]) (pathEnds_nil _)
      (by have h := edgeW_reverse' GATA GATB
          simp only [edgeSum, h, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
          ring)
  have s3 : MasterStep ([(HUB, GATB), (GATB, HUB)]) [] :=
    MasterStep.mk [] [(HUB, GATB), (GATB, HUB)] [] [] HUB HUB
      (by simp [PathEnds]) (pathEnds_nil _)
      (by have h := edgeW_reverse' GATB HUB
          simp only [edgeSum, h, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
          ring)
  exact MasterEq.trans (MasterEq.fwd s1) (MasterEq.trans (MasterEq.fwd s2) (MasterEq.fwd s3))

theorem gPairCancel (X Y : List (Pt × Pt)) :
    MasterEq (X ++ (gLoop ++ gLoopInv) ++ Y) (X ++ Y) := by
  have h := MasterEq.congr_mid gPairNil X Y
  simpa only [List.nil_append, List.append_nil] using h

theorem gInvPairCancel (X Y : List (Pt × Pt)) :
    MasterEq (X ++ (gLoopInv ++ gLoop) ++ Y) (X ++ Y) := by
  have h := MasterEq.congr_mid gInvPairNil X Y
  simpa only [List.nil_append, List.append_nil] using h

/-- 复制拼接（定义性）：L ++ (replicate n L).flatten = (replicate (n+1) L).flatten。 -/
theorem flatten_rep_succ (L : List (Pt × Pt)) (n : ℕ) :
    L ++ (List.replicate n L).flatten = (List.replicate (n + 1) L).flatten := by
  rw [List.replicate_succ, List.flatten_cons]

/-- **门环幂-规范形交互（g）**：g ++ canon(w) ~ canon(1+w)——
    w ≥ 0 同号幂定义性拼接；w < 0 异号幂门环对消。 -/
theorem midG_canon (w : ℤ) : MasterEq (gLoop ++ canon w) (canon (1 + w)) := by
  by_cases hw : 0 ≤ w
  · have hrep : (1 + w).toNat = w.toNat + 1 := by omega
    show MasterEq (gLoop ++ canon w) (canon (1 + w))
    unfold canon
    rw [if_pos hw, if_pos (show (0:ℤ) ≤ 1 + w from by omega), hrep,
      List.replicate_succ, List.flatten_cons]
    exact masterEq_refl _
  · rcases Decidable.em (w = -1) with hw0 | hw0
    · subst hw0
      show MasterEq (gLoop ++ canon (-1)) (canon 0)
      rw [show canon (-1) = gLoopInv from rfl, show canon 0 = [] from rfl]
      exact gPairNil
    · have hw1 : ((-w).toNat : ℤ) = -w := Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ -w)
      have hw3 : (((-(1 + w)).toNat : ℤ)) = -(1 + w) :=
        Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ -(1 + w))
      obtain ⟨k, hk⟩ : ∃ k : ℕ, (-w).toNat = k + 1 := ⟨(-w).toNat - 1, by omega⟩
      have hk2 : (-(1 + w)).toNat = k := by omega
      show MasterEq (gLoop ++ canon w) (canon (1 + w))
      unfold canon
      rw [if_neg hw, if_neg (show ¬(0:ℤ) ≤ 1 + w from by omega), hk, hk2,
        List.replicate_succ, List.flatten_cons]
      simpa only [List.append_assoc, List.nil_append, List.append_nil] using
        gPairCancel [] ((List.replicate k gLoopInv).flatten)

/-- **门环幂-规范形交互（g⁻¹）**：g⁻¹ ++ canon(w) ~ canon(w−1)——对称。 -/
theorem midGInv_canon (w : ℤ) : MasterEq (gLoopInv ++ canon w) (canon (w - 1)) := by
  by_cases hw : w ≤ 0
  · rcases Decidable.em (w = 0) with hw0 | hw0
    · subst hw0
      show MasterEq (gLoopInv ++ canon 0) (canon (-1))
      rw [show canon 0 = [] from rfl, show canon (-1) = gLoopInv from rfl, List.append_nil]
      exact MasterEq.refl
    · have hw1 : ((-w).toNat : ℤ) = -w := Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ -w)
      have hw4 : (((-(w - 1)).toNat : ℤ)) = -(w - 1) :=
        Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ -(w - 1))
      have hrep : (-(w - 1)).toNat = (-w).toNat + 1 := by omega
      show MasterEq (gLoopInv ++ canon w) (canon (w - 1))
      unfold canon
      rw [if_neg (show ¬(0:ℤ) ≤ w from by omega),
        if_neg (show ¬(0:ℤ) ≤ w - 1 from by omega), hrep,
        List.replicate_succ, List.flatten_cons]
      exact masterEq_refl _
  · have hw1 : ((w.toNat : ℤ)) = w := Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ w)
    have hw3 : (((w - 1).toNat : ℤ)) = w - 1 := Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ w - 1)
    obtain ⟨k, hk⟩ : ∃ k : ℕ, w.toNat = k + 1 := ⟨w.toNat - 1, by omega⟩
    have hk2 : (w - 1).toNat = k := by omega
    show MasterEq (gLoopInv ++ canon w) (canon (w - 1))
    unfold canon
    rw [if_pos (show (0:ℤ) ≤ w from by omega), if_pos (show (0:ℤ) ≤ w - 1 from by omega),
      hk, hk2, List.replicate_succ, List.flatten_cons]
    simpa only [List.append_assoc, List.nil_append, List.append_nil] using
      gInvPairCancel [] ((List.replicate k gLoop).flatten)

/-- **门环幂-规范形交互**：mid(c) ++ canon(w) ~ canon(c + w)（c ∈ {−1,0,1}）。 -/
theorem mid_canon (c w : ℤ) (hc : c = 1 ∨ c = -1 ∨ c = 0) :
    MasterEq (mid c ++ canon w) (canon (c + w)) := by
  rcases hc with hc | hc | hc
  · subst hc
    rw [mid_one]
    exact midG_canon w
  · subst hc
    rw [mid_neg, show (-1 : ℤ) + w = w - 1 from by ring]
    exact midGInv_canon w
  · subst hc
    rw [mid_zero, show (0 : ℤ) + w = w from by ring, List.nil_append]
    exact masterEq_refl _

/-- **门环幂归约定理**：门环幂段 ~ canon(edgeSum E)——同号幂定义性拼接·异号幂对消。 -/
theorem masterEq_concatMid : ∀ E : List (Pt × Pt), MasterEq (concatMid E) (canon (edgeSum E)) := by
  intro E
  induction E with
  | nil =>
      have h1 : concatMid [] = [] := rfl
      have h2 : canon (edgeSum ([] : List (Pt × Pt))) = [] := rfl
      rw [h1, h2]
      exact masterEq_refl _
  | cons e rest ih =>
      have hes : edgeSum (e :: rest) = edgeW e + edgeSum rest := by
        simp [edgeSum]
      show MasterEq (mid (edgeW e) ++ concatMid rest) (canon (edgeSum (e :: rest)))
      rw [hes]
      exact MasterEq.trans (MasterEq.congr_left (mid (edgeW e)) ih)
        (mid_canon (edgeW e) (edgeSum rest) (edgeW_range e))

/-! ### 主定理：π₁ 完整分类 -/

/-- 基点规范形：勾出 + canon w + 勾入（闭合于 p·绕数 w）。 -/
def canonAt (p : Pt) (w : ℤ) : List (Pt × Pt) := [(p, HUB)] ++ canon w ++ [(HUB, p)]

theorem pathEnds_canonAt (p : Pt) (w : ℤ) : PathEnds (canonAt p w) p p := by
  unfold canonAt
  exact PathEnds_append (PathEnds_append ⟨rfl, pathEnds_nil HUB⟩ (pathEnds_canon w))
    ⟨rfl, pathEnds_nil p⟩

theorem edgeSum_canonAt (p : Pt) (w : ℤ) : edgeSum (canonAt p w) = w := by
  have h : edgeSum ([(p, HUB)] ++ canon w ++ [(HUB, p)])
      = edgeSum [(p, HUB)] + (edgeSum (canon w) + edgeSum [(HUB, p)]) := by simp [edgeSum]
  show edgeSum ([(p, HUB)] ++ canon w ++ [(HUB, p)]) = w
  rw [h, edgeSum_hook_out, edgeSum_hook_in, edgeSum_canon]
  ring

/-- **π₁ 完备性主定理**：闭合格点路径 ~ 基点规范形（同绕数）——
    逐边规范化 → 刺剥净（原顶点消失）→ 门环幂归约 —— 完备方向成立。 -/
theorem masterEq_pi1 (E : List (Pt × Pt)) (p : Pt) (hE : PathEnds E p p) :
    MasterEq E (canonAt p (edgeSum E)) := by
  cases E with
  | nil =>
      have h0 : edgeSum [] = 0 := by simp [edgeSum]
      show MasterEq [] (canonAt p (edgeSum []))
      rw [h0]
      exact MasterEq.bwd (masterStep_spur [] [] p HUB)
  | cons e rest =>
      have h1 := masterEq_hooksAndMids (e :: rest)
      have h2 := hooksAndMids_bridge (e :: rest) p p (by simp) hE
      have h3 := masterEq_concatMid (e :: rest)
      have h4 : MasterEq (([(p, HUB)] ++ concatMid (e :: rest)) ++ [(HUB, p)])
          (([(p, HUB)] ++ canon (edgeSum (e :: rest))) ++ [(HUB, p)]) :=
        MasterEq.congr_right (MasterEq.congr_left [(p, HUB)] h3) [(HUB, p)]
      exact MasterEq.trans h1 (MasterEq.trans h2 h4)

/-- **π₁ 完整分类定理**：同基点闭合路径——主形等价 ⟺ 同绕数。
    （声张面 edgeSum_masterEq + 完备面 masterEq_pi1 合成。） -/
theorem pi1_classification {E E' : List (Pt × Pt)} {p : Pt}
    (hE : PathEnds E p p) (hE' : PathEnds E' p p) (hw : edgeSum E = edgeSum E') :
    MasterEq E E' := by
  have h1 := masterEq_pi1 E p hE
  have h2 := masterEq_pi1 E' p hE'
  rw [hw] at h1
  exact MasterEq.trans h1 (masterEq_sym h2)

/-- **π₁ 分类双条件**（本大件主定理）：同基点闭合路径——
    MasterEq E E' ↔ edgeSum E = edgeSum E'——身份类 = 绕数 ℤ（格点 π₁ = ℤ·门环生成）。 -/
theorem pi1_classification_iff {E E' : List (Pt × Pt)} {p : Pt}
    (hE : PathEnds E p p) (hE' : PathEnds E' p p) :
    MasterEq E E' ↔ edgeSum E = edgeSum E' :=
  ⟨fun h => edgeSum_masterEq h, fun hw => pi1_classification hE hE' hw⟩

end GeoAnchorPi1
