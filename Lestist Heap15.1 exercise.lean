

-- Define the LeftistTree, where a node contains:
-- - an element `α`
-- - a left subtree `l`
-- - a right subtree `r`
-- - the rank of the right spine `rnk`
inductive LeftistTree (α : Type) where
  | empty : LeftistTree α
  | node : α → LeftistTree α → LeftistTree α → Nat → LeftistTree α
  deriving Repr

-- Define `rank` (length of the right spine)
def rank {α : Type} : LeftistTree α → Nat
  | LeftistTree.empty => 0  -- The rank of an empty tree is 0
  | LeftistTree.node _ _ r rnk => rnk + 1  -- The rank is the rank of the right subtree + 1

-- Define `mh` (an alternative way to measure the right spine)
def mh {α : Type} : LeftistTree α → Nat
  | LeftistTree.empty => 0  -- The mh of an empty tree is 0
  | LeftistTree.node _ _ r _ => mh r + 1  -- mh recursively computes the mh of the right subtree and adds 1

-- Prove that `rank` and `mh` define the same trees
theorem rank_eq_mh {α : Type} (t : LeftistTree α) : rank t = mh t := by
  induction t with
  | empty => rfl  -- Base case: for an empty tree, both are 0, so they are equal
  | node _ l r _ ih_r =>
    simp [rank, mh]  -- Expand the definitions of `rank` and `mh`
    rw [ih_r]  -- Use the induction hypothesis to replace `rank r` with `mh r`
    rfl  -- The structure remains identical, completing the proof

-- Define `size` (the number of nodes in the tree)
def size {α : Type} : LeftistTree α → Nat
  | LeftistTree.empty => 0  -- The size of an empty tree is 0
  | LeftistTree.node _ l r _ => 1 + size l + size r  -- The size is 1 plus the sizes of the left and right subtrees

-- Define `ltree_by`, which checks whether a leftist tree satisfies a given property
def ltree_by {α : Type} (f : LeftistTree α → Nat) : LeftistTree α → Bool
  | LeftistTree.empty => true  -- An empty tree always satisfies the property
  | LeftistTree.node _ l r _ => (f r ≤ f l) && ltree_by f l && ltree_by f r
  -- The tree satisfies `ltree_by` if `f r ≤ f l` and both subtrees satisfy `ltree_by` recursively

-- Prove that `ltree_by rank = ltree_by size`, meaning that rank and size define the same leftist tree structure
theorem ltree_by_rank_eq_ltree_by_size {α : Type} (t : LeftistTree α) :
  ltree_by rank t = ltree_by size t := by
  induction t with
  | empty => rfl  -- Base case: for an empty tree, both return `true`
  | node _ l r _ ih_l ih_r =>
    simp only [ltree_by, rank, size]  -- Expand the definitions of `ltree_by`, `rank`, and `size`
    have h_equiv : rank r ≤ rank l ↔ size r ≤ size l := by
      -- Prove that `rank r ≤ rank l` is equivalent to `size r ≤ size l`
      constructor
      · intro h
        cases r with
        | empty => simp  -- If `r` is an empty tree, the property is trivially true
        | node _ _ _ _ => simp [rank, size]; linarith  -- Use `linarith` to handle the inequality
      · intro h
        cases r with
        | empty => simp  -- If `r` is an empty tree, the property holds trivially
        | node _ _ _ _ => simp [rank, size]; linarith
    rw [h_equiv]  -- Substitute `rank r ≤ rank l ↔ size r ≤ size l`
    congr 1  -- Let Lean recognize structurally identical parts, completing the proof

-- Prove `2^rank t ≤ size t + 1`
theorem leftist_tree_logarithmic_bound {α : Type} (t : LeftistTree α)
  (h : ltree_by size t) : 2^(rank t) ≤ size t + 1 := by
  induction t with
  | empty => simp [rank, size]  -- Base case: for an empty tree, this inequality holds trivially
  | node _ l r _ ih_l ih_r =>
    cases h with
    | intro hl hr =>  -- Decomposing `ltree_by size`, giving `size r ≤ size l`
      simp only [ltree_by, rank, size] at hl hr
      -- Inductive hypotheses
      have IHl := leftist_tree_logarithmic_bound l hl
      have IHr := leftist_tree_logarithmic_bound r hr
      -- Compute `rank` and `size` relationships
      have rank_eq : rank (LeftistTree.node _ l r _) = rank r + 1 := by simp [rank]
      have size_eq : size (LeftistTree.node _ l r _) = 1 + size l + size r := by simp [size]
      -- Inductive step
      rw [rank_eq, size_eq]
      calc
        2 ^ (rank r + 1) ≤ 2 * (size r + 1) := by apply Nat.pow_le_pow_of_le_right; linarith
        _ ≤ 2 * size r + 2 := by ring
        _ ≤ size l + size r + 2 := by linarith
        _ = size (LeftistTree.node _ l r _) + 1 := by linarith
