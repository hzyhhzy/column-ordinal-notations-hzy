import Lean.Elab.Tactic.Omega

/-!
The finite recursive syntax used by strong BT*(-1)Y-nSS v2.

`Expr.cons a hs t` is a column with numerical label `a`, attached list of
forests `hs`, and the remaining columns `t`. A forest and a list of attached
forests are different types: an empty attached forest is not an absent slot.
There are no axioms asserting standardness or well-founded expansion here.
-/
namespace BTnSSBMS

mutual
  inductive Expr (α : Type) where
    | nil
    | cons (label : α) (attached : Forests α) (tail : Expr α)
    deriving Repr, DecidableEq
  inductive Forests (α : Type) where
    | nil
    | cons (forest : Expr α) (tail : Forests α)
    deriving Repr, DecidableEq
end

instance : Inhabited (Expr α) := ⟨.nil⟩
instance : Inhabited (Forests α) := ⟨.nil⟩

mutual
  def Expr.nodes : Expr α → Nat
    | .nil => 0
    | .cons _ hs t => 1 + hs.nodes + t.nodes
  def Forests.nodes : Forests α → Nat
    | .nil => 0
    | .cons h hs => h.nodes + hs.nodes
end

mutual
  def Expr.slots : Expr α → Nat
    | .nil => 0
    | .cons _ hs t => hs.slots + t.slots
  def Forests.slots : Forests α → Nat
    | .nil => 0
    | .cons h hs => 1 + h.slots + hs.slots
end

mutual
  def Expr.map (f : α → β) : Expr α → Expr β
    | .nil => .nil
    | .cons a hs t => .cons (f a) (hs.map f) (t.map f)
  def Forests.map (f : α → β) : Forests α → Forests β
    | .nil => .nil
    | .cons h hs => .cons (h.map f) (hs.map f)
end

/- Source ordering: coordinates, then attached forests, then remaining columns. -/
mutual
  def Expr.compare (cmp : α → α → Ordering) : Expr α → Expr α → Ordering
    | .nil, .nil => .eq
    | .nil, .cons .. => .lt
    | .cons .., .nil => .gt
    | .cons a hs t, .cons b ks u =>
        match cmp a b with
        | .eq => match hs.compare cmp ks with
            | .eq => t.compare cmp u
            | c => c
        | c => c
  def Forests.compare (cmp : α → α → Ordering) : Forests α → Forests α → Ordering
    | .nil, .nil => .eq
    | .nil, .cons .. => .lt
    | .cons .., .nil => .gt
    | .cons h hs, .cons k ks =>
        match h.compare cmp k with
        | .eq => hs.compare cmp ks
        | c => c
end

def listCompare (cmp : α → α → Ordering) : List α → List α → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => match cmp a b with
      | .eq => listCompare cmp as bs
      | c => c

abbrev NumericalExpr := Expr (List Nat)
abbrev Matrix := List (List Nat)

def matrixCompare : Matrix → Matrix → Ordering :=
  listCompare (listCompare compare)

/-- The finite diagonal seeds of the frozen NER source; `d` is UI n minus 1. -/
def diagonalTail (d : Nat) : Nat → Nat → NumericalExpr
  | 0, _ => .nil
  | k + 1, level =>
      .cons (List.replicate d level)
        (.cons (diagonalTail d k (level + 1)) .nil) .nil

def seed (d k : Nat) : NumericalExpr :=
  .cons (List.replicate d 0) .nil (diagonalTail d k 1)

def diagonalMatrix (rows length : Nat) : Matrix :=
  (List.range length).map (fun i => List.replicate rows i)

def ceiling (d : Nat) : Matrix := diagonalMatrix (d + 2) 4

theorem listCompare_eq_imp (cmp : α → α → Ordering)
    (faithful : ∀ a b, cmp a b = .eq → a = b) (xs ys : List α)
    (same : listCompare cmp xs ys = .eq) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [listCompare]
  | cons x xs ih =>
    cases ys with
    | nil => simp [listCompare] at same
    | cons y ys =>
      cases first : cmp x y with
      | lt => simp [listCompare, first] at same
      | gt => simp [listCompare, first] at same
      | eq =>
        have hxy := faithful x y first
        have rest : listCompare cmp xs ys = .eq := by simpa [listCompare, first] using same
        cases hxy
        cases ih ys rest
        rfl

mutual
  theorem Expr.compare_eq_imp (cmp : α → α → Ordering)
      (faithful : ∀ a b, cmp a b = .eq → a = b) (e f : Expr α)
      (same : e.compare cmp f = .eq) : e = f := by
    cases e with
    | nil => cases f <;> simp_all [Expr.compare]
    | cons a hs t =>
      cases f with
      | nil => simp [Expr.compare] at same
      | cons b ks u =>
        cases first : cmp a b with
        | lt => simp [Expr.compare, first] at same
        | gt => simp [Expr.compare, first] at same
        | eq =>
          have hab := faithful a b first
          cases second : hs.compare cmp ks with
          | lt => simp [Expr.compare, first, second] at same
          | gt => simp [Expr.compare, first, second] at same
          | eq =>
            have hhs := Forests.compare_eq_imp cmp faithful hs ks second
            have ht : t.compare cmp u = .eq := by simpa [Expr.compare, first, second] using same
            have htu := Expr.compare_eq_imp cmp faithful t u ht
            cases hab; cases hhs; cases htu; rfl
  theorem Forests.compare_eq_imp (cmp : α → α → Ordering)
      (faithful : ∀ a b, cmp a b = .eq → a = b) (hs ks : Forests α)
      (same : hs.compare cmp ks = .eq) : hs = ks := by
    cases hs with
    | nil => cases ks <;> simp_all [Forests.compare]
    | cons h hs =>
      cases ks with
      | nil => simp [Forests.compare] at same
      | cons k ks =>
        cases first : h.compare cmp k with
        | lt => simp [Forests.compare, first] at same
        | gt => simp [Forests.compare, first] at same
        | eq =>
          have hh := Expr.compare_eq_imp cmp faithful h k first
          have rest : hs.compare cmp ks = .eq := by simpa [Forests.compare, first] using same
          have ht := Forests.compare_eq_imp cmp faithful hs ks rest
          cases hh; cases ht; rfl
end

mutual
  theorem Expr.map_nodes (f : α → β) (e : Expr α) :
      (e.map f).nodes = e.nodes := by
    cases e with
    | nil => rfl
    | cons a hs t =>
      simp only [Expr.map, Expr.nodes, Forests.map_nodes f hs, Expr.map_nodes f t]
  theorem Forests.map_nodes (f : α → β) (hs : Forests α) :
      (hs.map f).nodes = hs.nodes := by
    cases hs with
    | nil => rfl
    | cons h hs =>
      simp only [Forests.map, Forests.nodes, Expr.map_nodes f h, Forests.map_nodes f hs]
end

mutual
  theorem Expr.map_slots (f : α → β) (e : Expr α) :
      (e.map f).slots = e.slots := by
    cases e with
    | nil => rfl
    | cons a hs t =>
      simp only [Expr.map, Expr.slots, Forests.map_slots f hs, Expr.map_slots f t]
  theorem Forests.map_slots (f : α → β) (hs : Forests α) :
      (hs.map f).slots = hs.slots := by
    cases hs with
    | nil => rfl
    | cons h hs =>
      simp only [Forests.map, Forests.slots, Expr.map_slots f h, Forests.map_slots f hs]
end

end BTnSSBMS
