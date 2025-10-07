/-记录Lean的基本玩法（备忘）-/


--这样可以写单行注释

/-
这样可以写多行注释
-/


#check 5
#check true
#check "Castronaut"
#eval 3 + 4
#eval 10 > 5


-- 函数定义：注意参数之间要有空格
def square (x: Nat): Nat := x * x

#eval square 5
#check square


def add (a : Nat) (b : Nat) : Nat := a + b

#eval add 3 7


-- 分支逻辑：模式匹配
-- 函数：判断自然数是否为 0
def isZero (n : Nat) : Bool :=
  match n with
  | 0 => true
  | _ => false   -- 下划线是通配符

#eval isZero 0
#eval isZero 1


-- 递归计算阶乘
def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1        -- 基例：0!=1
  | k + 1 => (k + 1) * factorial k

#eval factorial 5


-- 定义一个自然数列表
def nums : List Nat := [1, 2, 3, 4]

#check nums
#eval nums ++ [5] -- 列表拼接

-- 新语法！网上有些教程是错的！
#eval nums.head?
#eval nums.length
#eval nums[0]? --据说加个问号更安全


/-
用 theorem 关键字定义定理，语法为：theorem 定理名 : 命题 := by 证明过程。
命题：需要证明的数学陈述（如 ∀ n : Nat, n + 0 = n，即 "对所有自然数 n，n+0 = n"）；
by：引入 "战术模式"，后续用战术逐步构造证明；
战术（Tactics）：证明的 "工具"，如 refl（反射，证明等式两边相等）、induction（数学归纳法）、cases（分情况讨论）等。
-/

-- 加法结合律的一个步骤
theorem add_assoc_step (a b : Nat) : a + (b + 1) = (a + b) + 1 := by
  rfl  -- rfl 是 refl 的简写

-- 简单的等式证明（这个在 Lean 4 中已经内置）
theorem zero_add (n : Nat) : 0 + n = n :=
  Nat.zero_add n

-- 验证定理（注意：定理本身不能用 #eval，但可以应用到具体值）
example : 2 + (3 + 1) = (2 + 3) + 1 := by
  rfl

#check add_assoc_step
