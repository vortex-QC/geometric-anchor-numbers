import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Rat.Cast.Order
import DensityMath.GeoAnchorCollapse
import DensityMath.GeoAnchorCollapse

/-!
# 数域不可离散化（挂账19/20·2026-09-30 按主人令 19+20 合并路线执行）

对应: papers/几何锚数_数值轮_不可离散化定理_预注册_v0.1.md（TH-20 主定理 + TH-20a 势不对称）
上游: papers/几何锚数_挂账_锚塌方向对比定理化_判读档_v0.1.md（NumCollapse 迷你模型在案）

定理清单:
  ① 编码唯一性: 2^k·3^m 分解唯一（两两无穷不相交块族的对角坐标系）
  ② TH-20 核心: 对角序列 diag r 与任何序列族代表 r m 渐近不等价（每 m 在无穷多坐标上差恒 1）
  ③ TH-20: ¬∃ surjection ℕ → NumCollapse（数域锚塌产物不可枚举=不可离散化形式句）
  ④ TH-20: ¬Countable NumCollapse（Countable+Nonempty→满射存在→对角矛盾）
  ⑤ TH-20a: Countable ShapeCollapse（形变域可数）∧ ¬Countable NumCollapse（数域不可数）
     = 两域锚塌的势不对称（S2 方向对比的势层配重）

路线注记（预注册三路线执行记录）: R1 对角线走通（2^k·3^m 编码唯一性 + phi 提取 + 逐块差恒 1）;
R2（Real 桥接传递）在 API 盘点后弃——Mathlib Real = SeparationQuotient (CauchyFilter ℚ)（滤子结构,
无序列代表抽取的轻量接口）; R3（库件引用）同弃——不可数性对本件迷你模型无现成库件（mk_real 作用于 ℝ
非迷你模型）。预注册一致（R1 为首选路线）。

诚实边界: NumCollapse = ℚ 序列渐近等价商（含非柯西序列的渐近轨道·GeoAnchorCollapse 迷你模型口径）;
本件证其不可数（不可枚举），"与 ℝ 的构造级对接"（挂账 19 完整形态）不在本件——相容件（柯西列收敛
同极限⟹同类）维持挂账 19 开放; 两域"势不对称"读法为推理级（预注册跑前锁定·不因定理成立升格）。
零 sorry。
-/

namespace GeoAnchorNum

open GeoAnchorCollapse
open GeoAnchor

/-! ### ① 编码唯一性：2^k·3^m 分解唯一 -/

theorem odd_pow_three : ∀ m : ℕ, Odd (3 ^ m)
  | 0 => ⟨0, by norm_num⟩
  | m + 1 => by
    obtain ⟨k, hk⟩ := odd_pow_three m
    have hstep : 3 ^ (m + 1) = 3 * 3 ^ m := pow_succ' _ _
    exact ⟨3 * k + 1, by rw [hstep, hk]; ring⟩

theorem two_not_dvd_pow_three : ∀ m : ℕ, ¬ (2 : ℕ) ∣ 3 ^ m
  | 0 => by norm_num
  | m + 1 => by
    intro h
    obtain ⟨c, hc⟩ := h
    have heven : Even (3 ^ (m + 1)) := ⟨c, by omega⟩
    exact Nat.not_even_iff_odd.mpr (odd_pow_three (m + 1)) heven

theorem unique_pow2_pow3_le {k m k' m' : ℕ} (hle : k ≤ k')
    (h : 2 ^ k * 3 ^ m = 2 ^ k' * 3 ^ m') : k = k' ∧ m = m' := by
  obtain ⟨j, hj⟩ : ∃ j, k' = k + j := ⟨k' - k, by omega⟩
  rw [hj] at h
  have hcancel : 3 ^ m = 2 ^ j * 3 ^ m' := by
    refine Nat.mul_left_cancel (show (0 : ℕ) < 2 ^ k from by norm_num) ?_
    calc 2 ^ k * 3 ^ m = 2 ^ (k + j) * 3 ^ m' := h
      _ = 2 ^ k * (2 ^ j * 3 ^ m') := by rw [pow_add]; ring
  have hj0 : j = 0 := by
    by_contra hpos
    have h1 : 1 ≤ j := by omega
    obtain ⟨i, hi⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have heven : Even (3 ^ m) := by
      rw [hcancel, hi, pow_succ]
      exact ⟨2 ^ i * 3 ^ m', by ring⟩
    obtain ⟨c, hc⟩ := heven
    exact two_not_dvd_pow_three m ⟨c, by omega⟩
  rw [hj0] at hj hcancel
  simp only [Nat.add_zero] at hj
  simp only [pow_zero, one_mul] at hcancel
  refine ⟨hj.symm, ?_⟩
  by_contra hmm
  rcases lt_or_gt_of_ne hmm with hlt | hgt
  · exact absurd hcancel
      (Nat.ne_of_lt (Nat.pow_lt_pow_right (show (1 : ℕ) < 3 from by norm_num) hlt))
  · exact absurd hcancel.symm
      (Nat.ne_of_lt (Nat.pow_lt_pow_right (show (1 : ℕ) < 3 from by norm_num) hgt))

theorem unique_pow2_pow3 {k m k' m' : ℕ} (h : 2 ^ k * 3 ^ m = 2 ^ k' * 3 ^ m') :
    k = k' ∧ m = m' := by
  rcases le_total k k' with hle | hgt
  · exact unique_pow2_pow3_le hle h
  · obtain ⟨h1, h2⟩ := unique_pow2_pow3_le hgt h.symm
    exact ⟨h1.symm, h2.symm⟩

theorem lt_two_pow_self : ∀ n : ℕ, n < (2 : ℕ) ^ n
  | 0 => by norm_num
  | n + 1 => by
    have hkey : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
    have h1 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
    have him := lt_two_pow_self n
    linarith

/-! ### ② 对角坐标提取与对角序列 -/

-- 从 n 提取 3 的幂指数 m（若 n = 2^k·3^m 则 phi n = m；否则 0）——对角坐标提取函数
open Classical in
noncomputable def phi (n : ℕ) : ℕ :=
  if h : ∃ p : ℕ × ℕ, n = 2 ^ p.2 * 3 ^ p.1 then h.choose.1 else 0

theorem phi_spec_of_mem {n m k : ℕ} (h : n = 2 ^ k * 3 ^ m) : phi n = m := by
  have hex : ∃ p : ℕ × ℕ, n = 2 ^ p.2 * 3 ^ p.1 := ⟨(m, k), h⟩
  have hd : phi n = (hex.choose).1 := dif_pos hex
  rw [hd]
  have hkey : 2 ^ (hex.choose).2 * 3 ^ (hex.choose).1 = 2 ^ k * 3 ^ m :=
    hex.choose_spec.symm.trans h
  exact (unique_pow2_pow3 (k := (hex.choose).2) (m := (hex.choose).1)
    (k' := k) (m' := m) hkey).2

-- 对角序列：在每个 2^k·3^m 坐标上取第 m 个代表序列的值加 1——对每个 m 在无穷多坐标上差恒 1
noncomputable def diag (r : ℕ → (ℕ → ℚ)) : ℕ → ℚ := fun n => r (phi n) n + 1

theorem diag_not_equiv (r : ℕ → (ℕ → ℚ)) (m : ℕ) :
    ¬ GeoAnchorCollapse.CauchyEquiv (diag r) (r m) := by
  intro he
  unfold GeoAnchorCollapse.CauchyEquiv at he
  obtain ⟨N, hN⟩ := he (1 / 2) (by norm_num)
  have hpow : (2 : ℕ) ^ N * 3 ^ m ≥ N := by
    have h1 : (1 : ℕ) ≤ 3 ^ m := Nat.one_le_pow _ _ (by norm_num)
    calc (2 : ℕ) ^ N * 3 ^ m ≥ (2 : ℕ) ^ N := Nat.le_mul_of_pos_right _ (by norm_num)
      _ ≥ N := Nat.le_of_lt (lt_two_pow_self N)
  have habs := hN ((2 : ℕ) ^ N * 3 ^ m) hpow
  have hphi : phi ((2 : ℕ) ^ N * 3 ^ m) = m := phi_spec_of_mem rfl
  simp only [diag, hphi] at habs
  have h1 : |r m ((2 : ℕ) ^ N * 3 ^ m) + 1 - r m ((2 : ℕ) ^ N * 3 ^ m)| = (1 : ℚ) := by
    rw [show r m ((2 : ℕ) ^ N * 3 ^ m) + 1 - r m ((2 : ℕ) ^ N * 3 ^ m) = (1 : ℚ) from by ring,
      abs_one]
  rw [h1] at habs
  norm_num at habs

/-! ### ③④ TH-20：无满射 ℕ → NumCollapse · 不可数 -/

def zero_class : GeoAnchorCollapse.NumCollapse :=
  Quotient.mk CauchySetoid (fun _ => 0)

theorem not_surjective_numCollapse : ∀ (g : ℕ → GeoAnchorCollapse.NumCollapse),
    ¬ Function.Surjective g := by
  intro g hsurj
  unfold GeoAnchorCollapse.NumCollapse at g hsurj
  obtain ⟨m, hm⟩ := hsurj
    (Quotient.mk CauchySetoid (diag (fun n => Quotient.out (g n))))
  refine diag_not_equiv (fun n => Quotient.out (g n)) m ?_
  have h1 : g m = Quotient.mk CauchySetoid (diag (fun n => Quotient.out (g n))) := hm
  have h2 : Quotient.mk CauchySetoid (diag (fun n => Quotient.out (g n))) =
      Quotient.mk CauchySetoid (Quotient.out (g m)) := by
    rw [← h1, Quotient.out_eq (g m)]
  exact Quotient.eq.mp h2

theorem not_countable_numCollapse : ¬ Countable GeoAnchorCollapse.NumCollapse := by
  intro hc
  have : Nonempty GeoAnchorCollapse.NumCollapse := ⟨zero_class⟩
  obtain ⟨g, hgs⟩ := exists_surjective_nat (α := GeoAnchorCollapse.NumCollapse)
  exact not_surjective_numCollapse g hgs

/-! ### ⑤ TH-20a：两域锚塌的势不对称 -/

theorem countable_shapeCollapse : Countable GeoAnchorCollapse.ShapeCollapse := by
  have h1 : Countable (Quotient PathSetoid) := by
    refine Function.Surjective.countable (f := Quotient.mk PathSetoid) ?_
    intro b
    exact ⟨b.out, Quotient.out_eq b⟩
  exact h1

/-- **势不对称主定理（TH-20a）**：形变域锚塌产物（拓扑类）可数 × 数域锚塌产物不可数——
两域锚塌的第二差异（第一差异=离散读数存在性·GeoAnchorCollapse S2）。 -/
theorem potential_asymmetry :
    Countable GeoAnchorCollapse.ShapeCollapse ∧ ¬ Countable GeoAnchorCollapse.NumCollapse :=
  ⟨countable_shapeCollapse, not_countable_numCollapse⟩

/-! ### ⑥ 挂账19 相容件：柯西核 ↔ 极限的双射对应（2026-09-30 晚续·SeqTendsTo 纯 ε-N 口径零拓扑依赖） -/

-- 序列收敛的 ε-N 形式（本件局部定义——Real 上收敛的纯序数表述·零拓扑库依赖）
def SeqTendsTo (u : ℕ → ℝ) (x : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |u n - x| < ε

-- ②同极限⟹同类（类只依赖极限·良定义性方向）
theorem cauchy_same_limit_same_class (a b : ℕ → ℚ) (x : ℝ)
    (ha : SeqTendsTo (fun n => ((a n : ℚ) : ℝ)) x)
    (hb : SeqTendsTo (fun n => ((b n : ℚ) : ℝ)) x) :
    GeoAnchorCollapse.CauchyEquiv a b := by
  rw [GeoAnchorCollapse.CauchyEquiv]
  intro ε hε
  obtain ⟨Na, haN⟩ := ha ((ε : ℝ) / 2) (by positivity)
  obtain ⟨Nb, hbN⟩ := hb ((ε : ℝ) / 2) (by positivity)
  refine ⟨max Na Nb, fun n hn => ?_⟩
  have h1 := haN n (le_trans (Nat.le_max_left _ _) hn)
  have h2 := hbN n (le_trans (Nat.le_max_right _ _) hn)
  have h5 : |(((a n - b n : ℚ) : ℝ))| < (ε : ℝ) := by
    have h6 : ((a n : ℚ) : ℝ) - ((b n : ℚ) : ℝ) = ((a n - b n : ℚ) : ℝ) := by norm_cast
    have h7 : ((a n : ℚ) : ℝ) - ((b n : ℚ) : ℝ)
        = (((a n : ℚ) : ℝ) - x) + (x - ((b n : ℚ) : ℝ)) := by ring
    have htri : |(((a n : ℚ) : ℝ) - x) + (x - ((b n : ℚ) : ℝ))| ≤
        |((a n : ℚ) : ℝ) - x| + |((b n : ℚ) : ℝ) - x| := by
      have h8 := abs_sub (((a n : ℚ) : ℝ) - x) (-(x - ((b n : ℚ) : ℝ)))
      rw [sub_neg_eq_add] at h8
      simpa [abs_neg] using h8
    calc |((a n - b n : ℚ) : ℝ)| = |((a n : ℚ) : ℝ) - ((b n : ℚ) : ℝ)| := by norm_cast
      _ = |(((a n : ℚ) : ℝ) - x) + (x - ((b n : ℚ) : ℝ))| := by rw [h7]
      _ ≤ |((a n : ℚ) : ℝ) - x| + |((b n : ℚ) : ℝ) - x| := htri
      _ < (ε : ℝ) / 2 + (ε : ℝ) / 2 := by linarith
      _ = (ε : ℝ) := by ring
  rw [← Rat.cast_abs] at h5
  exact_mod_cast h5

-- ③同类⟹同极限（单射性方向）
theorem class_same_limit (a b : ℕ → ℚ) (x y : ℝ)
    (ha : SeqTendsTo (fun n => ((a n : ℚ) : ℝ)) x)
    (hb : SeqTendsTo (fun n => ((b n : ℚ) : ℝ)) y)
    (heq : GeoAnchorCollapse.CauchyEquiv a b) : x = y := by
  by_contra hne
  obtain ⟨q, hq0, hq1⟩ := exists_rat_btwn (show (0 : ℝ) < |x - y| / 3 by positivity)
  have hq0' : (0 : ℚ) < q := Rat.cast_pos.mp hq0
  obtain ⟨Na, haN⟩ := ha (|x - y| / 3) (by positivity)
  obtain ⟨Nb, hbN⟩ := hb (|x - y| / 3) (by positivity)
  obtain ⟨N, hN⟩ := heq q hq0'
  set n := max (max Na Nb) N with hn
  have e1 : |x - ((a n : ℚ) : ℝ)| < |x - y| / 3 := by
    have h := haN n (le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
      (Nat.le_refl _))
    rw [abs_sub_comm] at h
    exact h
  have e2 : |((a n : ℚ) : ℝ) - ((b n : ℚ) : ℝ)| < |x - y| / 3 := by
    have hNi := hN n (Nat.le_max_right _ _)
    have h8 : (((|a n - b n| : ℚ) : ℝ)) < ((q : ℚ) : ℝ) := Rat.cast_lt.mpr hNi
    have h9 : ((a n : ℚ) : ℝ) - ((b n : ℚ) : ℝ) = ((a n - b n : ℚ) : ℝ) := by norm_cast
    rw [Rat.cast_abs, ← h9] at h8
    have hq : ((q : ℚ) : ℝ) < |x - y| / 3 := hq1
    linarith
  have e3 : |((b n : ℚ) : ℝ) - y| < |x - y| / 3 := by
    have h := hbN n (le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
    exact h
  have hsplit : x - y = (x - ((a n : ℚ) : ℝ))
      + (((a n : ℚ) : ℝ) - ((b n : ℚ) : ℝ) + (((b n : ℚ) : ℝ) - y)) := by ring
  have habs : |x - y| ≤ |x - ((a n : ℚ) : ℝ)|
      + (|((a n : ℚ) : ℝ) - ((b n : ℚ) : ℝ)| + |((b n : ℚ) : ℝ) - y|) := by
    rw [hsplit]
    have step1 : |(x - ((a n : ℚ) : ℝ))
        + (((a n : ℚ) : ℝ) - ((b n : ℚ) : ℝ) + (((b n : ℚ) : ℝ) - y))| ≤
        |x - ((a n : ℚ) : ℝ)|
        + |((a n : ℚ) : ℝ) - ((b n : ℚ) : ℝ) + (((b n : ℚ) : ℝ) - y)| := by
      have h8 : |(x - ((a n : ℚ) : ℝ)) - (-(((a n : ℚ) : ℝ) - ((b n : ℚ) : ℝ)
          + (((b n : ℚ) : ℝ) - y)))| ≤ |x - ((a n : ℚ) : ℝ)|
          + |-(((a n : ℚ) : ℝ) - ((b n : ℚ) : ℝ) + (((b n : ℚ) : ℝ) - y))| :=
        abs_sub (x - ((a n : ℚ) : ℝ)) (-(((a n : ℚ) : ℝ) - ((b n : ℚ) : ℝ)
          + (((b n : ℚ) : ℝ) - y)))
      rw [sub_neg_eq_add, abs_neg] at h8
      exact h8
    have step2 : |((a n : ℚ) : ℝ) - ((b n : ℚ) : ℝ) + (((b n : ℚ) : ℝ) - y)| ≤
        |((a n : ℚ) : ℝ) - ((b n : ℚ) : ℝ)| + |((b n : ℚ) : ℝ) - y| := by
      have h8 : |(((a n : ℚ) : ℝ) - ((b n : ℚ) : ℝ)) - (-(((b n : ℚ) : ℝ) - y))| ≤
          |((a n : ℚ) : ℝ) - ((b n : ℚ) : ℝ)| + |-(((b n : ℚ) : ℝ) - y)| :=
        abs_sub (((a n : ℚ) : ℝ) - ((b n : ℚ) : ℝ)) (-(((b n : ℚ) : ℝ) - y))
      rw [sub_neg_eq_add, abs_neg] at h8
      exact h8
    linarith
  linarith

/-- **柯西核双射对应（挂账19 相容件·冠件）**：柯西列的 NumCollapse 类由其极限唯一决定——
良定义性（同极限⟹同类）× 单射性（同类⟹同极限）合取——迷你模型在柯西核上与 ℝ
完全一致的形式句（19 对接面的定理级形态：对接不用换构造，柯西核自动相容）。 -/
theorem cauchy_core_bijection :
    (∀ (a b : ℕ → ℚ) (x : ℝ),
        SeqTendsTo (fun n => ((a n : ℚ) : ℝ)) x →
        SeqTendsTo (fun n => ((b n : ℚ) : ℝ)) x →
        GeoAnchorCollapse.CauchyEquiv a b) ∧
    (∀ (a b : ℕ → ℚ) (x y : ℝ),
        SeqTendsTo (fun n => ((a n : ℚ) : ℝ)) x →
        SeqTendsTo (fun n => ((b n : ℚ) : ℝ)) y →
        GeoAnchorCollapse.CauchyEquiv a b → x = y) :=
  ⟨cauchy_same_limit_same_class, class_same_limit⟩

/-! ### ⑦ 挂账19 全域函数余项：ℝ 嵌入 NumCollapse（2026-09-30 晚三续） -/

-- 典范逼近序列：每点取左邻域有理点（Archimedean 逐点选取·Classical.choose）
noncomputable def approxSeq (x : ℝ) : ℕ → ℚ := fun n =>
  Classical.choose (exists_rat_btwn (show x - 1 / ((n:ℝ) + 1) < x from by
    have hδ : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
    linarith))

theorem approxSeq_close (x : ℝ) (n : ℕ) :
    |(((approxSeq x n : ℚ) : ℝ)) - x| < 1 / ((n:ℝ) + 1) := by
  have hex : ∃ q : ℚ, x - 1 / ((n:ℝ) + 1) < q ∧ q < x :=
    exists_rat_btwn (show x - 1 / ((n:ℝ) + 1) < x from by
      have hδ : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
      linarith)
  have hq1 := hex.choose_spec.1
  have hq2 := hex.choose_spec.2
  have hdef : approxSeq x n = hex.choose := rfl
  rw [hdef, abs_lt]
  constructor <;> linarith

theorem approxSeq_tendsto (x : ℝ) :
    SeqTendsTo (fun n => ((approxSeq x n : ℚ) : ℝ)) x := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, fun n hn => ?_⟩
  have hclose := approxSeq_close x n
  have h1 : (0:ℝ) < (n:ℝ) + 1 := by positivity
  have h6 : (1:ℝ) < ε * ((n:ℝ) + 1) := by
    have h3 : (1:ℝ) / ε < (n:ℝ) + 1 := by
      have h7 : ((1:ℝ) / ε) < ((N:ℕ):ℝ) := by exact_mod_cast hN
      have h8 : ((N:ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      linarith
    have h9 : (0:ℝ) < ε := hε
    calc (1:ℝ) = ε * ((1:ℝ) / ε) := (mul_one_div_cancel (ne_of_gt h9)).symm
      _ < ε * ((n:ℝ) + 1) := mul_lt_mul_of_pos_left h3 h9
  have hkey : (1:ℝ) / ((n:ℝ) + 1) < ε := by
    field_simp
    linarith
  linarith

-- 典范嵌入：实数 ↦ 其逼近序列的 NumCollapse 类（19 全域函数·choice 构造）
noncomputable def nuOf (x : ℝ) : GeoAnchorCollapse.NumCollapse :=
  Quotient.mk CauchySetoid (approxSeq x)

theorem nuOf_tendsto (x : ℝ) :
    SeqTendsTo (fun n => ((approxSeq x n : ℚ) : ℝ)) x := approxSeq_tendsto x

theorem nuOf_injective : Function.Injective nuOf := by
  intro x y hxy
  unfold nuOf at hxy
  have heq : GeoAnchorCollapse.CauchyEquiv (approxSeq x) (approxSeq y) :=
    Quotient.eq.mp hxy
  exact class_same_limit (approxSeq x) (approxSeq y) x y
    (nuOf_tendsto x) (nuOf_tendsto y) heq

-- 兼容件：任何逼近 x 的有理序列与典范逼近同类——嵌入像=极限处的全部类
theorem real_embedding_compat (x : ℝ) (u : ℕ → ℚ)
    (hu : SeqTendsTo (fun n => ((u n : ℚ) : ℝ)) x) :
    GeoAnchorCollapse.CauchyEquiv u (approxSeq x) :=
  cauchy_same_limit_same_class u (approxSeq x) x hu (nuOf_tendsto x)

/-- **ℝ 核心嵌入（挂账19 全域函数余项·冠件）**：nuOf 单射 × 嵌入像=收敛类全体——
ℝ 作为 NumCollapse 的（柯西核上的）子结构定理级——19 对接完成形态：
迷你模型 ⊇ ℝ（嵌入）且柯西核自动相容（cauchy_core_bijection）——
NumCollapse = 「ℝ 的柯西核 + 非柯西渐近轨道」的显式结构。 -/
theorem real_core_embedding :
    Function.Injective nuOf ∧
    (∀ (x : ℝ) (u : ℕ → ℚ), SeqTendsTo (fun n => ((u n : ℚ) : ℝ)) x →
      GeoAnchorCollapse.CauchyEquiv u (approxSeq x)) :=
  ⟨nuOf_injective, real_embedding_compat⟩

end GeoAnchorNum
