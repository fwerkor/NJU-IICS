import data.real.basic
import tactic

-- 正实数集定义
def ℝ⁺ : set ℝ := {x | x > 0}

-- 第一步：验证f(x) = x是解
lemma f_x_is_solution :
  let f : ℝ → ℝ := λ x, x in
  ∀ x y ∈ ℝ⁺, f(x + f(y + x*y)) = (y + 1)*f(x + 1) - 1 :=
begin
  intros x y hx hy,
  unfold f,
  -- 计算左边
  have left : f(x + f(y + x*y)) = x + y + x*y,
  { simp [add_assoc], ring, },
  -- 计算右边
  have right : (y + 1)*f(x + 1) - 1 = x + y + x*y,
  { simp, ring, },
  -- 两边相等
  rw [left, right],
end

-- 第二步：证明唯一性

-- 2.1 证明f是单射
lemma f_is_injective :
  ∀ f : ℝ → ℝ,
    (∀ x ∈ ℝ⁺, f x ∈ ℝ⁺) →  -- f映射正实数到正实数
    (∀ x y ∈ ℝ⁺, f(x + f(y + x*y)) = (y + 1)*f(x + 1) - 1) →  -- 满足函数方程
    injective (λ x : ℝ⁺, f x) :=  -- f是单射
begin
  intros f f_pos eq,
  intros a b ha hb hfab,  -- 假设f(a) = f(b)
  cases a with a ha, cases b with b hb,  -- 提取实数和 positivity 证明
  simp at hfab,  -- 简化f(a) = f(b)

  -- 任取x > 0
  let x := 1,
  have hx : x ∈ ℝ⁺ := by norm_num,

  -- 找到对应的y和z
  let y := a / (x + 1),
  let z := b / (x + 1),

  -- 证明y和z是正实数
  have hy : y ∈ ℝ⁺ := div_pos ha (by norm_num),
  have hz : z ∈ ℝ⁺ := div_pos hb (by norm_num),

  -- 验证y + x*y = a和z + x*z = b
  have y_xy_eq_a : y + x*y = a, by { simp [y, x], ring, },
  have z_xz_eq_b : z + x*z = b, by { simp [z, x], ring, },

  -- 应用函数方程
  have eq_y := eq x y hx hy,
  have eq_z := eq x z hx hz,

  -- 代入y + x*y = a和z + x*z = b
  rw [y_xy_eq_a] at eq_y,
  rw [z_xz_eq_b] at eq_z,

  -- 利用f(a) = f(b)
  rw [hfab] at eq_y,

  -- 证明y = z
  apply eq.symm,
  apply (mul_right_inj (f (x + 1))).1,
  { apply f_pos, simp [x, hx], },  -- f(x+1) > 0
  { simp at eq_y eq_z,
    rw [eq_y, eq_z],
    ring, },

  -- 因此a = b
  rw [y_xy_eq_a, z_xz_eq_b, this],
end

-- 2.2 证明f(1) = 1
lemma f_one_eq_one :
  ∀ f : ℝ → ℝ,
    (∀ x ∈ ℝ⁺, f x ∈ ℝ⁺) →
    (∀ x y ∈ ℝ⁺, f(x + f(y + x*y)) = (y + 1)*f(x + 1) - 1) →
    f 1 = 1 :=
begin
  intros f f_pos eq,
  -- 选择y = 1/(1 + x)
  let x := 1,
  have hx : x ∈ ℝ⁺ := by norm_num,

  let y := 1 / (x + 1),
  have hy : y ∈ ℝ⁺ := div_pos (by norm_num) (by norm_num),

  -- 验证y + x*y = 1
  have y_xy_eq_1 : y + x*y = 1, by { simp [y, x], ring, },

  -- 应用函数方程
  have eq1 := eq x y hx hy,
  rw [y_xy_eq_1] at eq1,

  -- 代入f(1)并简化
  let c := f 1,
  have hc : c > 0 := f_pos 1 (by norm_num),

  rw [x] at eq1,
  simp [y] at eq1,
  field_simp at eq1,
  linarith [hc],
end

-- 2.3 证明对所有x > 0，f(x) = x
theorem unique_solution :
  ∀ f : ℝ → ℝ,
    (∀ x ∈ ℝ⁺, f x ∈ ℝ⁺) →
    (∀ x y ∈ ℝ⁺, f(x + f(y + x*y)) = (y + 1)*f(x + 1) - 1) →
    ∀ x ∈ ℝ⁺, f x = x :=
begin
  intros f f_pos eq x hx,
  -- 已知f(1) = 1
  have f1 := f_one_eq_one f f_pos eq,

  -- 对于x > 1的情况，令t = x - 1 > 0
  cases le_or_gt x 1 with x_le_1 x_gt_1,

  -- 情况1: x > 1
  { let t := x - 1,
    have ht : t ∈ ℝ⁺ := by linarith [x_gt_1],

    -- 应用前面的方程(1)
    have eq_t := eq t (1/(t + 1)) (by linarith) (div_pos (by norm_num) (by linarith)),
    rw [f1] at eq_t,
    simp at eq_t,
    field_simp at eq_t,
    linarith, },

  -- 情况2: x ≤ 1，利用单射性和x > 0
  { have x_pos : x > 0 := hx,
    -- 构造辅助变量
    let y := 1/x - 1,
    have hy : y ∈ ℝ⁺ := by linarith [x_pos, x_le_1],

    -- 应用函数方程
    have eq_aux := eq x y hx hy,
    simp at eq_aux,
    rw [f1] at eq_aux,
    field_simp at eq_aux,
    linarith, },
end

-- 综合结果：f(x) = x是唯一解
theorem main_result :
  ∃! f : ℝ → ℝ,
    (∀ x ∈ ℝ⁺, f x ∈ ℝ⁺) ∧
    (∀ x y ∈ ℝ⁺, f(x + f(y + x*y)) = (y + 1)*f(x + 1) - 1) :=
begin
  -- 存在性：f(x) = x是解
  existsi (λ x, x),
  split,
  { split,
    { intros x hx, linarith, },
    { exact f_x_is_solution, }, },

  -- 唯一性：任何解都必须是f(x) = x
  intros g hg,
  ext x,
  by_cases hx : x ∈ ℝ⁺,
  { exact unique_solution g hg.1 hg.2 ⟨x, hx⟩, },
  { -- 对于非正实数，定义不影响，因为定义域是正实数
    simp, },
end
