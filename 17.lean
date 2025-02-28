structure BinomialTree (α : Type) where
  rank : Nat
  value : α
  children : List (BinomialTree α)
  deriving Repr

namespace BinomialHeap

-- 添加默认实例
instance [Inhabited α] : Inhabited (BinomialTree α) where
  default := ⟨0, default, []⟩

instance [Inhabited α] : Inhabited (BinomialTree α × List (BinomialTree α)) where
  default := (default, [])

-- 合并两个二项树
def link {α : Type} [LE α] [DecidableRel (fun x y : α => x ≤ y)] (t1 t2 : BinomialTree α) : BinomialTree α :=
  if t1.value ≤ t2.value then
    { rank := t1.rank + 1, value := t1.value, children := t2 :: t1.children }
  else
    { rank := t2.rank + 1, value := t2.value, children := t1 :: t2.children }

-- 合并两个二项堆
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
termination_by h1 h2 => h1.length + h2.length  -- ✅ 直接引用参数名
decreasing_by
  simp_wf  -- 显式显示长度计算
  all_goals  -- 处理所有递归分支
  try (solve_by_elim [Nat.lt_succ_self] <;> simp_all [List.length_cons] <;> omega)
  <;> (try (solve_by_elim [Nat.lt_succ_self] <;> simp_all [List.length_cons] <;> omega))
  <;> (try (simp_all [List.length_cons] <;> omega))

-- 插入元素到堆中
def insert {α : Type} [LE α] [DecidableRel (fun x y : α => x ≤ y)] (x : α) (h : List (BinomialTree α)) : List (BinomialTree α) :=
  merge [ { rank := 0, value := x, children := [] } ] h

-- 查找最小值
def findMin {α : Type} [LE α] [DecidableRel (fun x y : α => x ≤ y)] (h : List (BinomialTree α)) : Option α :=
  match h with
  | [] => none
  | t :: ts =>
    match findMin ts with
    | none => some t.value
    | some x => if t.value ≤ x then some t.value else some x

-- 删除最小值
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

end BinomialHeap

-- 测试案例
#eval BinomialHeap.insert 5 []  -- 插入元素5到空堆，结果为[{ rank := 0, value := 5, children := [] }]
#eval BinomialHeap.findMin [BinomialTree.mk 0 2 []]  -- 返回some 2
#eval BinomialHeap.deleteMin [BinomialTree.mk 0 2 []]  -- 返回空列表[]structure BinomialTree (α : Type) where
  rank : Nat
  value : α
  children : List (BinomialTree α)
  deriving Repr

namespace BinomialHeap

-- 添加默认实例
instance [Inhabited α] : Inhabited (BinomialTree α) where
  default := ⟨0, default, []⟩

instance [Inhabited α] : Inhabited (BinomialTree α × List (BinomialTree α)) where
  default := (default, [])

-- 合并两个二项树
def link {α : Type} [LE α] [DecidableRel (fun x y : α => x ≤ y)] (t1 t2 : BinomialTree α) : BinomialTree α :=
  if t1.value ≤ t2.value then
    { rank := t1.rank + 1, value := t1.value, children := t2 :: t1.children }
  else
    { rank := t2.rank + 1, value := t2.value, children := t1 :: t2.children }

-- 合并两个二项堆
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
termination_by h1 h2 => h1.length + h2.length  -- ✅ 直接引用参数名
decreasing_by
  simp_wf  -- 显式显示长度计算
  all_goals  -- 处理所有递归分支
  try (solve_by_elim [Nat.lt_succ_self] <;> simp_all [List.length_cons] <;> omega)
  <;> (try (solve_by_elim [Nat.lt_succ_self] <;> simp_all [List.length_cons] <;> omega))
  <;> (try (simp_all [List.length_cons] <;> omega))

-- 插入元素到堆中
def insert {α : Type} [LE α] [DecidableRel (fun x y : α => x ≤ y)] (x : α) (h : List (BinomialTree α)) : List (BinomialTree α) :=
  merge [ { rank := 0, value := x, children := [] } ] h

-- 查找最小值
def findMin {α : Type} [LE α] [DecidableRel (fun x y : α => x ≤ y)] (h : List (BinomialTree α)) : Option α :=
  match h with
  | [] => none
  | t :: ts =>
    match findMin ts with
    | none => some t.value
    | some x => if t.value ≤ x then some t.value else some x

-- 删除最小值
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

end BinomialHeap

-- 测试案例
#eval BinomialHeap.insert 5 []  -- 插入元素5到空堆，结果为[{ rank := 0, value := 5, children := [] }]
#eval BinomialHeap.findMin [BinomialTree.mk 0 2 []]  -- 返回some 2
#eval BinomialHeap.deleteMin [BinomialTree.mk 0 2 []]  -- 返回空列表[]
