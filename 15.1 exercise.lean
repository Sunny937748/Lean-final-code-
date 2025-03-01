

-- 定义左偏树 (LeftistTree)
inductive LeftistTree (α : Type) where
  | empty : LeftistTree α
  | node : α → LeftistTree α → LeftistTree α → Nat → LeftistTree α
  deriving Repr

-- 计算 `rank`（右脊的长度）
def rank {α : Type} : LeftistTree α → Nat
  | LeftistTree.empty => 0
  | LeftistTree.node _ _ r rnk => rnk + 1

-- 计算 `size`（树的大小）
def size {α : Type} : LeftistTree α → Nat
  | LeftistTree.empty => 0
  | LeftistTree.node _ l r _ => 1 + size l + size r

-- 递归检查 `ltree_by` 是否满足某个性质
def ltree_by {α : Type} (f : LeftistTree α → Nat) : LeftistTree α → Bool
  | LeftistTree.empty => true
  | LeftistTree.node _ l r _ => (f r ≤ f l) && ltree_by f l && ltree_by f r

-- 证明 `ltree_by rank = ltree_by size`
theorem ltree_by_rank_eq_ltree_by_size {α : Type} (t : LeftistTree α) :
  ltree_by rank t = ltree_by size t := by
  induction t with
  | empty => rfl  -- 空树情况，两者都为 true
  | node _ l r _ =>
    simp only [ltree_by, rank, size]
    -- 证明 `rank r ≤ rank l` ↔ `size r ≤ size l`
    have h_equiv : rank r ≤ rank l ↔ size r ≤ size l := by
      constructor
      · intro h
        cases r with
        | empty => simp
        | node _ _ _ _ => simp [rank, size]; linarith
      · intro h
        cases r with
        | empty => simp
        | node _ _ _ _ => simp [rank, size]; linarith
    -- 使用 `rw` 替代 `decide`
    rw [h_equiv]
    congr 1 -- 让 Lean 识别结构相同的部分

-- 证明 `2^rank t ≤ size t + 1`
theorem leftist_tree_logarithmic_bound {α : Type} (t : LeftistTree α)
  (h : ltree_by size t) : 2^(rank t) ≤ size t + 1 := by
  induction t with
  | empty => simp [rank, size]  -- 空树情况
  | node _ l r _ =>
    -- 确保左右子树满足 `ltree_by size`
    cases h with
    | intro hl hr =>
      simp only [ltree_by, rank, size] at hl hr
      -- 归纳假设
      have IHl := leftist_tree_logarithmic_bound l hl
      have IHr := leftist_tree_logarithmic_bound r hr
      -- 计算 `rank` 和 `size` 关系
      have rank_eq : rank (LeftistTree.node _ l r _) = rank r + 1 := by simp [rank]
      have size_eq : size (LeftistTree.node _ l r _) = 1 + size l + size r := by simp [size]
      -- 归纳推导
      rw [rank_eq, size_eq]
      calc
        2 ^ (rank r + 1) ≤ 2 * (size r + 1) := by apply Nat.pow_le_pow_of_le_right; linarith
        _ ≤ 2 * size r + 2 := by ring
        _ ≤ size l + size r + 2 := by linarith
        _ = size (LeftistTree.node _ l r _) + 1 := by linarith
