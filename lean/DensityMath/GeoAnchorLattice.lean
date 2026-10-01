import DensityMath.GeoAnchorSimple

/-!
# 二维塌缩格：承诺多少 × 承诺多强（特例族立档后第一刀·2026-10-01）

对应: papers/几何锚数_谱系特例族_形变约束强度分级_推演档_v0.1.md §二（与 A'4 承诺轴正交·二维塌缩格候选）
上游: papers/几何锚数_立项_v0.1.md §56/§86（特例族=形变约束强度分级·10-01 主人定调'立'）
      papers/几何锚数_数值轮_A4承诺轴_判读档_v0.1.md（纵向=承诺集合基数维 8→3→1 在案）

迷你模型口径（诚实边界·预声明）:
  字表 ℤ 上路径·两井读数族（A 井 invA_full/B 井 invB_full）·约束四档的读数=满表 take 前缀
  （约束强=前缀长=等价细=身份分辨率高）·承诺三档=L0 两井/L1 单井/L2 空（A'4 纵向档）。
  **定理（非公理）**:
    T1 纵向单调（承诺收缩→等价变粗）: 承诺档下降 → sameId 保持（细分等价蕴含粗分等价）
    T2 横向单调（约束减弱→等价变粗）: 约束档下降 → sameId 保持
    T3 双轴组合: 两轴同松 → sameId 保持（"身份坐标双重塌缩"结构句）
    T4 谱分离实例: 同伦级同类而等距级异类的字对存在（粗类合并细类分开）
    T5 空承诺塌基底: L2 → 一切字同类（A'4 L2 的格点版）
  迷你 toy 非物理宣称·几何层正交不动。零 sorry。
-/

namespace GeoAnchorLattice

/-! ### 基础读数函数 -/

def lsum : List ℤ → ℤ | [] => 0 | x :: xs => x + lsum xs
def lhead : List ℤ → ℤ | [] => 0 | x :: _ => x
def lcount1 : List ℤ → ℕ | [] => 0 | x :: xs => (if x = 1 then 1 else 0) + lcount1 xs
def bump : List ℤ → List ℤ | [] => [] | x :: xs => (x + 7) :: bump xs

/-- A 井满指纹：绕数类（sum）+形状（head）+内容（count1）+自身（等距级全保）。 -/
def invA_full (w : List ℤ) : List ℤ := [lsum w, lhead w, (lcount1 w : ℤ)] ++ w

/-- B 井满指纹（另一族读数·前缀结构相容）。 -/
def invB_full (w : List ℤ) : List ℤ := [(lcount1 w : ℤ), 0 - lsum w, 2 * lhead w] ++ bump w

/-! ### 约束四档（横向：形变约束强度分级） -/

inductive Constraint | homotopy | diffeo | conformal | isometry
deriving DecidableEq, Repr

open Constraint

/-- 约束强度序数（链序：同伦 0 < 微分 1 < 共形 2 < 等距 3）。 -/
def rid : Constraint → ℕ | homotopy => 0 | diffeo => 1 | conformal => 2 | isometry => 3

def cleB : Constraint → Constraint → Bool
  | homotopy, homotopy => true
  | homotopy, diffeo => true
  | homotopy, conformal => true
  | homotopy, isometry => true
  | diffeo, homotopy => false
  | diffeo, diffeo => true
  | diffeo, conformal => true
  | diffeo, isometry => true
  | conformal, homotopy => false
  | conformal, diffeo => false
  | conformal, conformal => true
  | conformal, isometry => true
  | isometry, homotopy => false
  | isometry, diffeo => false
  | isometry, conformal => false
  | isometry, isometry => true

def cle (a b : Constraint) : Prop := cleB a b = true

/-- 约束强度→读数前缀长度（同伦 1/微分 2/共形 3/等距=全表）。 -/
def prec : Constraint → ℕ | homotopy => 1 | diffeo => 2 | conformal => 3 | isometry => 100

theorem prec_le : ∀ c c' : Constraint, cle c c' → prec c ≤ prec c' := by
  intro c c' h
  cases c <;> cases c' <;> simp [cle, cleB] at h
  all_goals decide

/-! ### 约束级读数 = 满表前缀 -/

def fineA (c : Constraint) (w : List ℤ) : List ℤ := (invA_full w).take (prec c)
def fineB (c : Constraint) (w : List ℤ) : List ℤ := (invB_full w).take (prec c)

theorem take_le_take' : ∀ (n m : ℕ) (xs : List ℤ), n ≤ m →
    xs.take n = (xs.take m).take n := by
  intro n m xs h
  rw [List.take_take, min_eq_left h]

theorem take_mono_helper : ∀ (n m : ℕ) (h : n ≤ m) (F G : List ℤ),
    F.take m = G.take m → F.take n = G.take n := by
  intro n m h F G hEq
  calc F.take n = (F.take m).take n := take_le_take' n m F h
    _ = (G.take m).take n := by rw [hEq]
    _ = G.take n := (take_le_take' n m G h).symm

theorem fineA_mono : ∀ (c c' : Constraint) (h : cle c c') (w w' : List ℤ),
    fineA c' w = fineA c' w' → fineA c w = fineA c w' := by
  intro c c' h w w' hEq
  unfold fineA at hEq ⊢
  cases c <;> cases c' <;> simp [cle, cleB] at h
  all_goals
    first
      | exact hEq
      | exact take_mono_helper _ _ (by decide) _ _ hEq

theorem fineB_mono : ∀ (c c' : Constraint) (h : cle c c') (w w' : List ℤ),
    fineB c' w = fineB c' w' → fineB c w = fineB c w' := by
  intro c c' h w w' hEq
  unfold fineB at hEq ⊢
  cases c <;> cases c' <;> simp [cle, cleB] at h
  all_goals
    first
      | exact hEq
      | exact take_mono_helper _ _ (by decide) _ _ hEq

/-! ### 承诺三档（纵向：A'4 承诺集合基数维） -/

inductive Prom | L0 | L1 | L2
deriving DecidableEq, Repr

open Prom

/-- 身份读数总表（积编码：A 段 × B 段）。
L0=两井全读（身份坐标满）/L1=仅 B 井（wA 坐标塌）/L2=空（塌向无身份基底）。 -/
def invariants : Prom → Constraint → List ℤ → List ℤ × List ℤ
  | L0, c, w => (fineA c w, fineB c w)
  | L1, c, w => ([], fineB c w)
  | L2, _c, _w => ([], [])

def sameId (P : Prom) (c : Constraint) (w w' : List ℤ) : Prop :=
  invariants P c w = invariants P c w'

def ple (a b : Prom) : Prop := a = b ∨ (a = L2 ∧ b ≠ L2) ∨ (a = L1 ∧ b = L0)

/-! ### T2 横向单调：约束减弱→等价变粗（细类等价蕴含粗类等价） -/

theorem T2_horizontal : ∀ (P : Prom) (c c' : Constraint) (h : cle c c') (w w' : List ℤ),
    sameId P c' w w' → sameId P c w w' := by
  intro P c c' h w w' hEq
  cases P with
  | L0 =>
    unfold sameId at hEq
    show (fineA c w, fineB c w) = (fineA c w', fineB c w')
    unfold invariants at hEq
    have h1 := congrArg Prod.fst hEq
    have h2 := congrArg Prod.snd hEq
    rw [fineA_mono c c' h w w' h1, fineB_mono c c' h w w' h2]
  | L1 =>
    unfold sameId at hEq
    show ([], fineB c w) = ([], fineB c w')
    unfold invariants at hEq
    have h2 := congrArg Prod.snd hEq
    rw [fineB_mono c c' h w w' h2]
  | L2 => exact hEq

/-! ### T1 纵向单调：承诺收缩→等价变粗（身份坐标塌·A'4 方向） -/

theorem T1_vertical : ∀ (P₁ P₂ : Prom) (h : ple P₁ P₂) (c : Constraint) (w w' : List ℤ),
    sameId P₂ c w w' → sameId P₁ c w w' := by
  intro P₁ P₂ h c w w' hEq
  cases P₁ <;> cases P₂
  · exact hEq                                             -- L0 L0
  · exact absurd h (by unfold ple; decide)                -- L0 L1 不可达
  · exact absurd h (by unfold ple; decide)                -- L0 L2 不可达
  · -- L1 L0: 承诺从单井升两井·snd 段相等传递
    unfold sameId at hEq
    show ([], fineB c w) = ([], fineB c w')
    unfold invariants at hEq
    have h2 := congrArg Prod.snd hEq
    exact congrArg (fun l => ([], l)) h2
  · exact hEq                                             -- L1 L1
  · exact absurd h (by unfold ple; decide)                -- L1 L2 不可达
  · rfl                                                   -- L2 L0 塌基底
  · rfl                                                   -- L2 L1 塌基底
  · exact hEq                                             -- L2 L2

/-! ### T3 双轴组合：两轴同松→单调（"身份坐标双重塌缩"结构句） -/

theorem T3_double_collapse : ∀ (P₁ P₂ : Prom) (hP : ple P₁ P₂)
    (c c' : Constraint) (hC : cle c c') (w w' : List ℤ),
    sameId P₂ c' w w' → sameId P₁ c w w' :=
  fun P₁ P₂ hP c c' hC w w' hEq =>
    T1_vertical P₁ P₂ hP c w w' (T2_horizontal P₂ c c' hC w w' hEq)

/-! ### T4 谱分离实例：同伦级同类·等距级异类（粗类合并细类分开） -/

theorem T4_spectral_split :
    sameId Prom.L0 Constraint.homotopy [1, -1] [1, -1, 0] ∧
    ¬ sameId Prom.L0 Constraint.isometry [1, -1] [1, -1, 0] := by
  constructor
  · show invariants Prom.L0 Constraint.homotopy [1, -1] = invariants Prom.L0 Constraint.homotopy [1, -1, 0]
    unfold invariants fineA fineB invA_full invB_full lsum lhead lcount1
    decide
  · intro hEq
    have h1 := congrArg Prod.fst hEq
    unfold sameId invariants fineA invA_full at h1
    simp [prec, lsum, lhead, lcount1] at h1

/-! ### T5 空承诺塌基底：L2→一切字同类（A'4 L2 格点版） -/

theorem T5_empty_collapse : ∀ (c : Constraint) (w w' : List ℤ),
    sameId Prom.L2 c w w' := by
  intro c w w'
  rfl

end GeoAnchorLattice
