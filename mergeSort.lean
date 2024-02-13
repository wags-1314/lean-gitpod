-- TODO remove the `partial`s and convince Lean that mergeSort terminates

def merge [Ord A] (xs : List A) (ys : List A) : List A :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x'::xs', y'::ys' =>
    match Ord.compare x' y' with
    | .lt | .eq => x' :: merge xs' (y' :: ys')
    | .gt => y' :: merge (x'::xs') ys'
termination_by merge xs ys => (xs, ys)

def splitList (lst : List A) : (List A × List A) :=
  match lst with
  | [] => ([], [])
  | x :: xs =>
    let (a, b) := splitList xs
    (x :: b, a)

theorem succ_plus_1 (n : Nat):
  (n + 1) = Nat.succ n := by simp

theorem splitList_shorter (l : List A):
  (splitList l).fst.length <= l.length /\
  (splitList l).snd.length <= l.length := by
  induction l
  case nil =>
    simp [splitList]
  case cons x' l' IHl' =>
    simp [splitList]
    cases IHl'
    constructor
    case left =>
      apply Nat.succ_le_succ
      assumption
    case right =>
      apply Nat.le_succ_of_le
      assumption

theorem splitList_shorter_lt (l : List A) (Hlength : l.length >= 2) :
  (splitList l).fst.length < l.length /\
  (splitList l).snd.length < l.length := by
    match l with
    | a :: b :: l' =>
      have Hshort : _ := splitList_shorter l'
      cases Hshort
      simp [splitList]
      constructor
      case left =>
        apply Nat.succ_lt_succ
        apply Nat.lt_succ_of_le
        assumption
      case right =>
        apply Nat.succ_lt_succ
        apply Nat.lt_succ_of_le
        assumption

theorem splitList_shorter_fst (l : List A) (Hlength : l.length >= 2):
  (splitList l).fst.length < l.length := by
  have H:_ := splitList_shorter_lt l Hlength
  cases H
  assumption

theorem splitList_shorter_snd (l : List A) (Hlength : l.length >= 2):
  (splitList l).snd.length < l.length := by
  have H:_ := splitList_shorter_lt l Hlength
  cases H
  assumption

def mergeSort [Ord A] (xs : List A) : List A :=
  if h : xs.length < 2 then
    match xs with
    | [] => []
    | [x] => [x]
  else
    let halves := splitList xs
    have H: _ := Nat.ge_of_not_lt h
    have: halves.fst.length < xs.length := by
      apply splitList_shorter_fst
      assumption
    have: halves.snd.length < xs.length := by
      apply splitList_shorter_snd
      assumption
    merge (mergeSort halves.fst) (mergeSort halves.snd)
termination_by mergeSort xs => xs.length

def sorted (xs : List Nat) : Prop :=
  match xs with
  | [] => True
  | _ :: [] => True
  | x :: y :: xs => x <= y /\ sorted (y :: xs)

theorem merge_invariant (l1 l2 : List Nat):
  sorted l1 -> sorted l2 -> sorted (merge l1 l2) := by sorry
  -- intro H1 H2
  -- induction l1
  -- case nil =>
  --   induction l2
  --   case nil => simp [merge, sorted]
  --   case cons =>
  --     simp [merge]
  --     assumption
  -- case cons x1 l1' IHl1' =>
  --   induction l2
  --   case nil =>
  --     simp [merge]
  --     assumption
  --   case cons x2 l2' IHl2' =>
  --     simp [merge]
  --     cases compare x1 x2

theorem mergeSort_sorts (xs : List Nat) :
  sorted (mergeSort xs) := by
  sorry
