import tactic
import init.logic -- 引用关于逻辑的基本定理

-- Let `Ω` be a "big underlying set" and let `X` and `Y` and `Z` be subsets

variables (Ω : Type) (X Y Z : set Ω) (a b c x y z : Ω)

namespace xena

/-!

# subsets

Let's think about `X ⊆ Y`. Typeset `⊆` with `\sub` or `\ss`
-/

-- `X ⊆ Y` is the same as `∀ a, a ∈ X → a ∈ Y` , by definition.

lemma subset_def : X ⊆ Y ↔ ∀ a, a ∈ X → a ∈ Y :=
begin
  -- true by definition
  refl
end


lemma subset_refl : X ⊆ X :=
begin
  -- 想要证明一个新概念的性质，先从其定义入手
  rw subset_def,
  -- 遇到包含 ∀ 的命题，可以尝试intro策略
  intro a,
  intro a_in_X,
  exact a_in_X,
end
--  ⊆ 的自反性(reflexivity)在mathlib中已经证明过了，所以你也可以使用一个relf策略完成证明

-- 
lemma subset_trans (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) : X ⊆ Z :=
begin
  -- If you start with `rw subset_def at *` then you
  -- will have things like `hYZ : ∀ (a : Ω), a ∈ Y → a ∈ Z`

  -- You need to think of `hYZ` as a function, which has two
  -- inputs: first a term `a` of type `Ω`, and second a proof `haY` that `a ∈ Y`.
  -- It then produces one output `haZ`, a proof that `a ∈ Z`.

  -- You can also think of it as an implication:
  -- "if a is in Ω, and if a ∈ Y, then a ∈ Z". Because it's an implication,
  -- you can `apply hYZ`. This is a really useful skill!
  
  rw subset_def at *, -- 把已知条件和目标中所有 ⊆ 用定义替换
  intro a,
  intro a_in_X,

  apply hYZ,  -- 已知条件中有 a : Ω , 满足hYZ的前提: "a : Ω "
  apply hXY,  -- 同上
  exact a_in_X,
end

/-!

# Equality of sets

Two sets are equal if and only if they have the same elements.
The name of this theorem is `set.ext_iff`.
-/

example : X = Y ↔ (∀ a, a ∈ X ↔ a ∈ Y) :=
begin
  exact set.ext_iff
end

-- In practice, you often have a goal `⊢ X = Y` and you want to reduce
-- it to `a ∈ X ↔ a ∈ Y` for an arbitary `a : Ω`. This can be done with
-- the `ext` tactic. 

--    此证明的名称      (已知条件1)     (已知条件2)    :  目标  :=
lemma subset.antisymm (hXY : X ⊆ Y) (hYX : Y ⊆ X) : X = Y :=
begin
  -- start with `ext a`,
  ext? a,
  -- 在 ext 后加问号可以看到此处的 ext 等效于哪些证明策略

  split,
  { -- ⊢ x ∈ X → x ∈ Y
    intro a_in_X,
    apply hXY,      -- 无需手动按定义展开也可以直接 apply
    exact a_in_X,
    },
  { -- ⊢ x ∈ Y → x ∈ X
    intro a_in_Y,
    apply hYX,
    exact a_in_Y,
    }
  -- 如果你对如下事实感到困惑：
  --  对目标 a ∈ X 使用 apply hYX (Y ⊆ X) 会得到 a ∈ Y
  -- 那么请注意此处 a ∈ X 是需要证明的目标，而非已知条件；apply在修改证明目标，而非推出结论。
  -- 如果仍然无法理解，请在证明开头添加 rw subset_def at * 
end

/-!

### Unions and intersections

Type `\cup` or `\un` for `∪`, and `\cap` or `\i` for `∩`

-/

lemma union_def : a ∈ X ∪ Y ↔ a ∈ X ∨ a ∈ Y :=
begin
  -- true by definition
  refl,
end

lemma inter_def : a ∈ X ∩ Y ↔ a ∈ X ∧ a ∈ Y :=
begin
  -- true by definition
  refl,
end


-- You can rewrite with those lemmas above if you're not comfortable with
-- assuming they're true by definition.

-- union lemmas

lemma union_self : X ∪ X = X :=
begin
  ext a,
  rw union_def,
  split,
  { -- ⊢ a ∈ X ∨ a ∈ X → a ∈ X
    intro h,
    cases h with h1 h2,
    exact h1,
    exact h2,
  },
  { -- ⊢ a ∈ X → a ∈ X ∨ a ∈ X
    intro h,
    left,
    exact h,
  }
end

lemma subset_union_left : X ⊆ X ∪ Y :=
begin
  rw subset_def,
  intros a a_in_X,

  -- rw union_def,  -- 形如 a ∈ X ∪ Y 的目标可以直接使用left right策略，如果不理解 请删去行首注释再查看
  left,
  exact a_in_X,
end

lemma subset_union_right : Y ⊆ X ∪ Y :=
begin
  rw subset_def,
  intros a a_in_Y,
  
  -- rw union_def,  -- 同上题
  right,
  exact a_in_Y,
end

lemma union_subset_iff : X ∪ Y ⊆ Z ↔ X ⊆ Z ∧ Y ⊆ Z :=
begin
  split,
  { -- ⊢ X ∪ Y ⊆ Z → X ⊆ Z ∧ Y ⊆ Z
    intro hXunYssZ,
    split,
    -- ⊢ X ⊆ Z
      -- rw subset_def,  
      intros a a_in_X,    -- 对于 X ⊆ Z , 可以使用intros得出 a : Ω 和 a_in_X : a ∈ X , 定义如此
      -- rw subset_def at hXunYssZ,   
      apply hXunYssZ,     -- 若不理解请去掉rw前的注释以查看定义
      left,
      exact a_in_X,

    -- ⊢ Y ⊆ Z
      intros a a_in_Y,
      apply hXunYssZ,
      right,
      exact a_in_Y,
  },
  {
    intros h a a_in_XuY,
    cases h with XssZ YssZ,
    cases a_in_XuY with a_in_X a_in_Y,
    -- z ∈ X
      apply XssZ,
      exact a_in_X,
    -- a ∈ Y
      apply YssZ,
      exact a_in_Y,
  }
end

/- 
  目标是关于集合的命题，该如何处理？
    1，最基本的方法：使用rewrite(rw)将其改写成定义
    2，形如 X ⊆ Z, 用intros或两次intro
    3，形如 X = Y, 考虑 ext
    4，形如 a ∈ X ∪ Y, 可使用left right

  已知条件是关于集合的命题，如何使用?
    1.使用定义重写: rw _ at _
    2.形如 X ⊆ Z, 考虑apply
    3.形如 X ∪ Y , X ∩ Y , 可以cases（本质上是对 ∧ ∨ cases）
    4.形如 X = Y , 可以使用 rw
  -/

variable (W : set Ω)

lemma union_subset_union (hWX : W ⊆ X) (hYZ : Y ⊆ Z) : W ∪ Y ⊆ X ∪ Z :=
begin
  intros a a_in_WuY,
  cases a_in_WuY with a_in_W a_in_Y,
  { -- known:
    left,
    apply hWX,
    exact a_in_W,
  },
  {
    right,
    apply hYZ,
    exact a_in_Y,
  }
end

lemma union_subset_union_left (hXY : X ⊆ Y) : X ∪ Z ⊆ Y ∪ Z :=
begin
  have ZssZ : Z ⊆ Z, {
    refl
  },
  apply union_subset_union,
  exact hXY,
  exact ZssZ,
end

-- etc etc

-- intersection lemmas

lemma inter_subset_left : X ∩ Y ⊆ X :=
begin
  intros a a_in_XiY,
  cases a_in_XiY with a_in_X a_in_Y,
  exact a_in_X,
end

-- don't forget `ext` to make progress with equalities of sets

lemma inter_self : X ∩ X = X :=
begin
  ext,
  split,
  { -- ⊢ x ∈ X ∩ X → x ∈ X
    intro x_in_XiX,
    cases x_in_XiX with x_in_X x_in_X,
    exact x_in_X,
  },
  { -- ⊢ x ∈ X → x ∈ X ∩ X
    intro x_in_X,
    split,
    exact x_in_X,
    exact x_in_X,
  },
end


lemma inter_comm : X ∩ Y = Y ∩ X :=
begin
  ext,
  split, 
  { -- ⊢ x ∈ X ∩ Y → x ∈ Y ∩ X
    intro h,
    cases h with x_in_X x_in_Y,
    split,
    exact x_in_Y,
    exact x_in_X,
  },
  { -- ⊢ x ∈ Y ∩ X → x ∈ X ∩ Y
    intro h,
    cases h with x_in_Y x_in_X,
    split,
    exact x_in_X,
    exact x_in_Y,
  }
end

-- inter_def : a ∈ X ∩ Y ↔ a ∈ X ∧ a ∈ Y
lemma inter_assoc : X ∩ (Y ∩ Z) = (X ∩ Y) ∩ Z :=
begin
  ext,
  split,
  { -- ⊢ x ∈ X ∩ (Y ∩ Z) → x ∈ X ∩ Y ∩ Z
    intro h,
    -- rcases：等价于两条cases
    -- cases h with x_in_X h,
    -- cases h with x_in_Y x_in_Z,
    rcases h with ⟨x_in_X, x_in_Y, x_in_Z⟩, 
    
    split,
    split,
    exact x_in_X,
    exact x_in_Y,
    exact x_in_Z,
  },
  { -- ⊢ x ∈ X ∩ Y ∩ Z → x ∈ X ∩ (Y ∩ Z)
    intro h,
    -- 请尝试将这里改写为一条rcases
    cases h with h x_in_Z,
    cases h with x_in_X x_in_Y,

    split,
    exact x_in_X,
    split,
    exact x_in_Y,
    exact x_in_Z,
  }
end

/-!

### Forall and exists

-/
-- 关于存在命题的证明和使用方法，请查阅手册
-- https://leanprover-community.github.io/mathlib_docs/init/logic.html#Exists
-- 请在手册中自行查找全称命题的说明

lemma not_exists_iff_forall_not : ¬ (∃ a, a ∈ X) ↔ ∀ b, ¬ (b ∈ X) :=
begin
  split,
  { -- ¬ ∃ → ∀ 
    intro h,
    intro b,
    intro b_in_X,
    apply h,
    use b,      -- 指出满足goal的元素b
    -- existsi b, -- 与use等价
    exact b_in_X,
  },
  { -- ∀ → ¬ ∃ 
    intro h,
    intro hExist,
    -- cases 从存在命题抽出 a 及其性质 a ∈ X
    cases hExist with a ha,
    apply (h a),  -- (h a) : a ∉ X
    exact ha,
  }
end

example : ¬ (∀ a, a ∈ X) ↔ ∃ b, ¬ (b ∈ X) :=
begin
  split,
  { -- ¬ ∀ → ∃ 
    -- 此处的goal不是直觉主义逻辑中的定理，仅使用构造方式无法证明，需要用到反证法
    intro h,
    by_contra hE,
    apply h,
    intro a,
    by_contra aNotInX,
    apply hE,
    use a,
  },
  { -- ∃ → ¬ ∀ 
    intro h,
    intro hAll,
    cases h with a ha,
    apply ha,
    apply hAll,
  }
end

end xena

