import BTnSSBMS.Keys

/-! Complete normalized keys retain the entire attachment, at a fixed base.
The proof allows different activation histories on the two sides. -/
namespace BTnSSBMS
namespace Keys

def decodeAtom (base : Nat) (a : KeyAtom) : Nat :=
  (if a.1 then Int.ofNat base + a.2 else a.2).toNat

theorem decode_atom (base current : Nat) (active : Bool) :
    decodeAtom base (atom base current active) = current := by
  cases active with
  | false => rfl
  | true =>
    change (Int.ofNat base + (Int.ofNat current - Int.ofNat base)).toNat = current
    rw [Int.add_comm, Int.sub_add_cancel]
    rfl

def decodeVector (d : Nat) (base : List Nat) (v : List KeyAtom) : List Nat :=
  (List.range d).map fun j => decodeAtom (base[j]?.getD 0) (v[j]?.getD (false, 0))

theorem decode_normalize (d t : Nat) (base current : List Nat)
    (width : current.length = d) :
    decodeVector d base (normalize d t base current) = current := by
  apply List.ext_getElem
  · simp only [decodeVector, List.length_map, List.length_range, width]
  · intro i h₁ h₂
    have hi : i < d := by simpa only [width] using h₂
    simp [decodeVector, normalize, hi, decode_atom, List.getElem?_eq_getElem h₂]

/-- Equality of vector keys determines the numerical vector, even if the
two activation thresholds are different. -/
theorem normalize_injective (d t u : Nat) (base a b : List Nat)
    (ha : a.length = d) (hb : b.length = d)
    (same : normalize d t base a = normalize d u base b) : a = b := by
  calc
    a = decodeVector d base (normalize d t base a) := (decode_normalize d t base a ha).symm
    _ = decodeVector d base (normalize d u base b) := congrArg (decodeVector d base) same
    _ = b := decode_normalize d u base b hb

mutual
  def HasWidth (d : Nat) : ParentExpr → Prop
    | .nil => True
    | .cons a hs t => a.coordinates.length = d ∧ HasWidthForests d hs ∧ HasWidth d t
  def HasWidthForests (d : Nat) : Forests ParentLabel → Prop
    | .nil => True
    | .cons h hs => HasWidth d h ∧ HasWidthForests d hs
end

mutual
  theorem forest_reconstruct (d owner : Nat) (base : List Nat) (history : List Nat)
      (e : ParentExpr) (width : HasWidth d e) :
      (forest d owner base history e).map (decodeVector d base) =
        e.map ParentLabel.coordinates := by
    cases e with
    | nil => rfl
    | cons a hs t =>
      rcases width with ⟨ha, hh, ht⟩
      simp only [forest, Expr.map, decode_normalize d _ base _ ha,
        forests_reconstruct d owner base _ hs hh, forest_reconstruct d owner base _ t ht]
  theorem forests_reconstruct (d owner : Nat) (base : List Nat) (history : List Nat)
      (hs : Forests ParentLabel) (width : HasWidthForests d hs) :
      (forests d owner base history hs).map (decodeVector d base) =
        hs.map ParentLabel.coordinates := by
    cases hs with
    | nil => rfl
    | cons h hs =>
      rcases width with ⟨hh, ht⟩
      simp only [forests, Forests.map, forest_reconstruct d owner base _ h hh,
        forests_reconstruct d owner base _ hs ht]
end

theorem complete_key_reconstruct (d index : Nat) (a : ParentLabel)
    (hs : Forests ParentLabel) (width : HasWidthForests d hs) :
    (ofColumn d index a hs).map (decodeVector d a.coordinates) =
      hs.map ParentLabel.coordinates :=
  forests_reconstruct d index a.coordinates _ hs width

theorem same_key_same_attachment (d i j : Nat) (a b : ParentLabel)
    (hs ks : Forests ParentLabel) (ha : HasWidthForests d hs) (hb : HasWidthForests d ks)
    (sameBase : a.coordinates = b.coordinates)
    (sameKey : ofColumn d i a hs = ofColumn d j b ks) :
    hs.map ParentLabel.coordinates = ks.map ParentLabel.coordinates := by
  calc
    hs.map ParentLabel.coordinates =
        (ofColumn d i a hs).map (decodeVector d a.coordinates) :=
      (complete_key_reconstruct d i a hs ha).symm
    _ = (ofColumn d j b ks).map (decodeVector d b.coordinates) := by rw [sameKey, sameBase]
    _ = ks.map ParentLabel.coordinates := complete_key_reconstruct d j b ks hb

end Keys
end BTnSSBMS
