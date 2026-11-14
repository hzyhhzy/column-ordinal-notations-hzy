import BTnSSBMS.Parents

namespace BTnSSBMS

/-- Signed differences matter on virtual material; no truncated Nat subtraction. -/
abbrev KeyAtom := Bool × Int
abbrev Key := Forests (List KeyAtom)

namespace Keys

def atomCompare (a b : KeyAtom) : Ordering :=
  if a.1 == b.1 then compare a.2 b.2 else if a.1 then .gt else .lt

def compare (a b : Key) : Ordering :=
  a.compare (listCompare atomCompare) b

def threshold (d owner : Nat) (history : List Nat) (a : ParentLabel) : Nat :=
  ((List.range d).takeWhile fun j =>
    match a.parents[j]?.join with
    | none => false
    | some p => decide (owner ≤ p ∧ j < history[p]?.getD 0)).length

def atom (base current : Nat) (active : Bool) : KeyAtom :=
  if active then (true, Int.ofNat current - Int.ofNat base) else (false, Int.ofNat current)

def normalize (d t : Nat) (base current : List Nat) : List KeyAtom :=
  (List.range d).map fun j => atom (base[j]?.getD 0) (current[j]?.getD 0) (decide (j < t))

mutual
  def forest (d owner : Nat) (base : List Nat) (history : List Nat) :
      ParentExpr → Expr (List KeyAtom)
    | .nil => .nil
    | .cons a hs t =>
      let threshold' := threshold d owner history a
      let history' := history ++ [threshold']
      .cons (normalize d threshold' base a.coordinates)
        (forests d owner base history' hs) (forest d owner base history' t)
  def forests (d owner : Nat) (base : List Nat) (history : List Nat) :
      Forests ParentLabel → Key
    | .nil => .nil
    | .cons h hs =>
      .cons (forest d owner base history h) (forests d owner base history hs)
end

def ofColumn (d index : Nat) (a : ParentLabel) (hs : Forests ParentLabel) : Key :=
  forests d index a.coordinates (List.replicate index 0 ++ [d]) hs

theorem leaf_key (d index : Nat) (a : ParentLabel) :
    ofColumn d index a .nil = .nil := rfl

theorem normalize_length (d t : Nat) (base current : List Nat) :
    (normalize d t base current).length = d := by
  simp only [normalize, List.length_map, List.length_range]

end Keys
end BTnSSBMS
