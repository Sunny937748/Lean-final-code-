structure BinomialTree (α : Type) where
  rank : Nat
  value : α
  children : List (BinomialTree α)
  deriving Repr

namespace BinomialHeap

-- 添加 Inhabited 实例
instance [Inhabited α] : Inhabited (BinomialTree α) where
  default := ⟨0, default, []⟩

instance [Inhabited α] : Inhabited (BinomialTree α × List (BinomialTree α)) where
  default := (default, [])

-- 连接两个同 rank 的 binomial tree
-- 使较小值成为根，并增加 rank

def link {α : Type} [LE α] [DecidableRel (fun x y : α => x ≤ y)] (t1 t2 : BinomialTree α) : BinomialTree α :=
  if t1.value ≤ t2.value then
    { rank := t1.rank + 1, value := t1.value, children := t2 :: t1.children }
  else
    { rank := t2.rank + 1, value := t2.value, children := t1 :: t2.children }

-- 合并两个堆

def merge {α : Type} [LE α] [DecidableRel (fun x y : α => x ≤ y)] (h1 h2 : List (BinomialTree α)) : List (BinomialTree α) :=
  let rec mergeCarry (carry : BinomialTree α) (ts : List (BinomialTree α)) : List (BinomialTree α) :=
    match ts with
    | [] => [carry]
    | t :: ts' =>
      if carry.rank < t.rank then
        carry :: t :: ts'
      else
        let newCarry := link carry t
        mergeCarry newCarry ts'
  match h1, h2 with
  | [], _ => h2
  | _, [] => h1
  | t1 :: ts1, t2 :: ts2 =>
    if t1.rank < t2.rank then
      t1 :: merge ts1 (t2 :: ts2)
    else if t2.rank < t1.rank then
      t2 :: merge (t1 :: ts1) ts2
    else
      let carry := link t1 t2
      mergeCarry carry (merge ts1 ts2)
termination_by h1 h2 => h1.length + h2.length

decreasing_by
  simp_wf  -- 显式显示长度计算
  all_goals  -- 处理所有递归分支
  try (solve_by_elim [Nat.lt_succ_self] <;> simp_all [List.length_cons] <;> omega)
  <;> (try (solve_by_elim [Nat.lt_succ_self] <;> simp_all [List.length_cons] <;> omega))
  <;> (try (simp_all [List.length_cons] <;> omega))

-- 插入新元素
def insert {α : Type} [LE α] [DecidableRel (fun x y : α => x ≤ y)] (x : α) (h : List (BinomialTree α)) : List (BinomialTree α) :=
  merge [ { rank := 0, value := x, children := [] } ] h

-- 获取堆中的最小元素
def findMin {α : Type} [LE α] [DecidableRel (fun x y : α => x ≤ y)] (h : List (BinomialTree α)) : Option α :=
  match h with
  | [] => none
  | t :: ts =>
    match findMin ts with
    | none => some t.value
    | some x => if t.value ≤ x then some t.value else some x

-- 删除最小元素
def deleteMin {α : Type} [LE α] [DecidableRel (fun x y : α => x ≤ y)] [Inhabited α] (h : List (BinomialTree α)) : List (BinomialTree α) :=
  match h with
  | [] => []
  | _ =>
    let rec extractMin : List (BinomialTree α) → BinomialTree α × List (BinomialTree α)
      | [] => (default, [])  -- 使用默认实例
      | [t] => (t, [])
      | t :: ts =>
        let (minT, rest) := extractMin ts
        if t.value ≤ minT.value then
          (t, ts)
        else
          (minT, t :: rest)
    let (minTree, rest) := extractMin h
    let reversedChildren := minTree.children.reverse
    merge rest reversedChildren

-- 获取堆的大小（所有树的节点总数）
def size {α : Type} (h : List (BinomialTree α)) : Nat :=
  h.foldl (fun acc t => acc + (2 ^ t.rank)) 0

-- 运行时间分析（大致计算总 rank 数）
def totalRank {α : Type} (h : List (BinomialTree α)) : Nat :=
  h.foldl (fun acc t => acc + t.rank) 0

end BinomialHeap

-- 测试代码
#eval BinomialHeap.insert 5 []  -- 插入元素5到空堆
#eval BinomialHeap.findMin [BinomialTree.mk 0 2 []]  -- 返回some 2
#eval BinomialHeap.deleteMin [BinomialTree.mk 0 2 []]  -- 返回空列表[]
#eval BinomialHeap.size [BinomialTree.mk 1 3 [BinomialTree.mk 0 5 []]]  -- 计算堆大小
#eval BinomialHeap.totalRank [BinomialTree.mk 2 4 [BinomialTree.mk 1 7 [BinomialTree.mk 0 9 []], BinomialTree.mk 0 10 []]]  -- 计算总rank
