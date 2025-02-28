inductive LeftistTree (α : Type) where
  | empty : LeftistTree α  -- 空树
  | node : α → LeftistTree α → LeftistTree α → Nat → LeftistTree α  -- 具有左子树、右子树和秩的节点
  deriving Repr

-- 计算左偏树的秩（rank）
def rank {α : Type} : LeftistTree α → Nat
  | LeftistTree.empty => 0
  | LeftistTree.node _ _ r rnk => rnk

-- 计算左偏树的大小（size）
def size {α : Type} : LeftistTree α → Nat
  | LeftistTree.empty => 0
  | LeftistTree.node _ l r _ => 1 + size l + size r

-- 递归检查左偏树是否满足某个性质 f
-- f 可能是 rank 或 size

def ltree_by {α : Type} (f : LeftistTree α → Nat) : LeftistTree α → Bool
  | LeftistTree.empty => true
  | LeftistTree.node _ l r _ => (f r ≤ f l) && ltree_by f l && ltree_by f r

-- 通过 rank 判断是否是左偏树
def ltree_by_rank {α : Type} (t : LeftistTree α) : Bool := ltree_by rank t

-- 通过 size 判断是否是左偏树
def ltree_by_mh {α : Type} (t : LeftistTree α) : Bool := ltree_by size t

-- 证明：ltree_by_rank 和 ltree_by_mh 是等价的
-- 证明 rank r ≤ rank l 当且仅当 size r ≤ size l
theorem ltree_by_rank_eq_ltree_by_mh {α : Type} (t : LeftistTree α) :
  ltree_by_rank t = ltree_by_mh t := by
  induction t with
  | empty => rfl  -- 空树的情况下，两个性质都为 true
  | node _ l r rnk =>
    simp_all [ltree_by_rank, ltree_by_mh, ltree_by, rank, size]
    -- 证明 rank r ≤ rank l ↔ size r ≤ size l
    have : rank r ≤ rank l ↔ size r ≤ size l := by
      constructor <;> intro h
      · induction r <;> induction l <;> simp_all [rank, size] <;> linarith
      · induction r <;> induction l <;> simp_all [rank, size] <;> linarith
    -- 处理 decide 等式
    cases (rank r).decLe (rank l) <;> cases (size r).decLe (size l) <;> simp_all

-- 证明左偏树满足 2^(rank t) ≤ size t + 1
theorem leftist_tree_logarithmic_bound {α : Type} (t : LeftistTree α)
  (h : ltree_by size t) : 2^(rank t) ≤ size t + 1 := by
  induction t with
  | empty => simp [rank, size]  -- 空树的情况下，显然成立
  | node _ l r rnk =>
    -- 解析前提 h，确保左右子树满足 ltree_by size 性质
    cases h : ltree_by size (LeftistTree.node _ l r rnk) <;> simp_all [ltree_by, rank, size]
    -- 获取左右子树的归纳假设
    have IHl := leftist_tree_logarithmic_bound l (by assumption)
    have IHr := leftist_tree_logarithmic_bound r (by assumption)
    -- 处理 rank 和 size 的等式
    have rank_eq : rank (LeftistTree.node _ l r rnk) = rank r + 1 := by
      cases r <;> simp [rank]
    have size_eq : size (LeftistTree.node _ l r rnk) = 1 + size l + size r := by
      simp [size]
    -- 组合证明步骤
    rw [rank_eq, size_eq]
    calc
      2 ^ (rank r + 1) ≤ 2 * (size r + 1) := by gcongr
      _ ≤ 2 * size r + 2 := by ring
      _ ≤ size l + size r + 2 := by
        have : size r ≤ size l := by linarith  -- 根据左偏树性质
        linarith
      _ = size (LeftistTree.node _ l r rnk) + 1 := by linarith
