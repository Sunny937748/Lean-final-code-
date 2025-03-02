

-- Define a Binomial Tree structure with:
-- - `rank`: The rank of the tree (order)
-- - `value`: The root value
-- - `children`: A list of child trees
structure BinomialTree (α : Type) where
  rank : Nat
  value : α
  children : List (BinomialTree α)
  deriving Repr

namespace BinomialHeap

-- Provide an `Inhabited` instance for BinomialTree, setting a default empty tree
instance [Inhabited α] : Inhabited (BinomialTree α) where
  default := ⟨0, default, []⟩

-- Provide an `Inhabited` instance for a pair of BinomialTree and a list of trees
instance [Inhabited α] : Inhabited (BinomialTree α × List (BinomialTree α)) where
  default := (default, [])

-- **Link two Binomial Trees of the same rank**
-- The tree with the smaller root value becomes the parent,
-- increasing the rank by 1 and adding the other tree as a child.
def link {α : Type} [LE α] [DecidableRel (fun x y : α => x ≤ y)] (t1 t2 : BinomialTree α) : BinomialTree α :=
  if t1.value ≤ t2.value then
    { rank := t1.rank + 1, value := t1.value, children := t2 :: t1.children }
  else
    { rank := t2.rank + 1, value := t2.value, children := t1 :: t2.children }

-- **Merge two binomial heaps (lists of binomial trees)**
-- The merge function recursively processes both lists and maintains the binomial heap properties.
def merge {α : Type} [LE α] [DecidableRel (fun x y : α => x ≤ y)] (h1 h2 : List (BinomialTree α)) : List (BinomialTree α) :=
  -- Helper function to handle carrying trees of the same rank
  let rec mergeCarry (carry : BinomialTree α) (ts : List (BinomialTree α)) : List (BinomialTree α) :=
    match ts with
    | [] => [carry]  -- If no more trees, return the carry as the final tree
    | t :: ts' =>
      if carry.rank < t.rank then
        carry :: t :: ts'  -- If carry has a smaller rank, insert it before `t`
      else
        let newCarry := link carry t  -- Link `carry` and `t` to merge them
        mergeCarry newCarry ts'  -- Recursively merge with the remaining trees

  match h1, h2 with
  | [], _ => h2  -- If `h1` is empty, return `h2`
  | _, [] => h1  -- If `h2` is empty, return `h1`
  | t1 :: ts1, t2 :: ts2 =>
    if t1.rank < t2.rank then
      t1 :: merge ts1 (t2 :: ts2)  -- Keep `t1` and merge the rest
    else if t2.rank < t1.rank then
      t2 :: merge (t1 :: ts1) ts2  -- Keep `t2` and merge the rest
    else
      let carry := link t1 t2  -- Merge two trees of the same rank
      mergeCarry carry (merge ts1 ts2)  -- Continue merging with the carry tree

-- Define termination conditions for recursion
termination_by h1 h2 => h1.length + h2.length
decreasing_by
  simp_wf  
  all_goals  
  try (solve_by_elim [Nat.lt_succ_self] <;> simp_all [List.length_cons] <;> omega)
  <;> (try (solve_by_elim [Nat.lt_succ_self] <;> simp_all [List.length_cons] <;> omega))
  <;> (try (simp_all [List.length_cons] <;> omega))

-- **Insert a new element into the heap**
-- Creates a singleton tree and merges it into the existing heap.
def insert {α : Type} [LE α] [DecidableRel (fun x y : α => x ≤ y)] (x : α) (h : List (BinomialTree α)) : List (BinomialTree α) :=
  merge [ { rank := 0, value := x, children := [] } ] h

-- **Find the minimum value in the heap**
-- Recursively traverses all tree roots to find the smallest value.
def findMin {α : Type} [LE α] [DecidableRel (fun x y : α => x ≤ y)] (h : List (BinomialTree α)) : Option α :=
  match h with
  | [] => none  -- If the heap is empty, return `none`
  | t :: ts =>
    match findMin ts with
    | none => some t.value  -- If only one tree, return its value
    | some x => if t.value ≤ x then some t.value else some x  -- Compare root values

-- **Delete the minimum element from the heap**
-- Finds the tree with the smallest root, removes it, and merges its children back.
def deleteMin {α : Type} [LE α] [DecidableRel (fun x y : α => x ≤ y)] [Inhabited α] (h : List (BinomialTree α)) : List (BinomialTree α) :=
  match h with
  | [] => []  -- If heap is empty, return an empty list
  | _ =>
    let rec extractMin : List (BinomialTree α) → BinomialTree α × List (BinomialTree α)
      | [] => (default, [])  -- If empty, return the default tree
      | [t] => (t, [])  -- If only one tree, return it and an empty list
      | t :: ts =>
        let (minT, rest) := extractMin ts  -- Recursively find the minimum tree
        if t.value ≤ minT.value then
          (t, ts)  -- If `t` is smaller, return it and the rest
        else
          (minT, t :: rest)  -- Otherwise, keep `t` in the list

    let (minTree, rest) := extractMin h  -- Extract the minimum tree
    let reversedChildren := minTree.children.reverse  -- Reverse children to maintain correct order
    merge rest reversedChildren  -- Merge the remaining heap with extracted children

-- **Compute the total size of the heap**
-- The size is the sum of `2^rank` for each tree.
def size {α : Type} (h : List (BinomialTree α)) : Nat :=
  h.foldl (fun acc t => acc + (2 ^ t.rank)) 0

-- **Compute the total rank of all trees in the heap**
-- Used for runtime analysis.
def totalRank {α : Type} (h : List (BinomialTree α)) : Nat :=
  h.foldl (fun acc t => acc + t.rank) 0

end BinomialHeap

-- **Test cases**

-- Insert an element 5 into an empty heap
#eval BinomialHeap.insert 5 []  

-- Find the minimum element in a single-node heap
#eval BinomialHeap.findMin [BinomialTree.mk 0 2 []]  

-- Delete the minimum element from a single-node heap
#eval BinomialHeap.deleteMin [BinomialTree.mk 0 2 []]  

-- Compute the size of a heap with a tree of rank 1 containing a rank-0 child
#eval BinomialHeap.size [BinomialTree.mk 1 3 [BinomialTree.mk 0 5 []]]  

-- Compute the total rank of a heap containing nested trees
#eval BinomialHeap.totalRank [BinomialTree.mk 2 4 [BinomialTree.mk 1 7 [BinomialTree.mk 0 9 []], BinomialTree.mk 0 10 []]]  
