import OrdinalFormal.ColumnMap
import OrdinalFormal.LRDCanonical
import OrdinalFormal.LRDRowDecrease

/-!
Faithful lifting of actual canonical LRD diagrams to the equality-correct row
carrier. Raw syntax is normalized, not asserted equal to its normal form.
Erasure is inverse on Canonical (hence Standard) diagrams. All expansion rules,
comparators and generated packages are the executable ones.
-/

set_option maxHeartbeats 600000
set_option maxRecDepth 2048

namespace OrdinalFormal.LRDNormalLift
open Columns LRDStructure

def toNormal (a : LRD.Row) : NormalRow := ⟨a.normal, normal_idempotent a⟩
def liftGraph (g : LRD.Diagram) : Graph NormalRow := ColumnMap.mapGraph toNormal g
def eraseGraph (g : Graph NormalRow) : LRD.Diagram := ColumnMap.mapGraph Subtype.val g

def normalPackage (a : NormalRow) (b : Nat) : List NormalRow :=
  (LRD.package a.val b).map toNormal

def normalLt (a b : NormalRow) : Prop := normalRowCmp a b = .lt

@[simp] theorem toNormal_val (a : LRD.Row) : (toNormal a).val = a.normal := rfl
@[simp] theorem toNormal_of_normal (a : NormalRow) : toNormal a.val = a := by
  apply Subtype.ext
  exact a.property

@[simp] theorem isFinite_normal (a : LRD.Row) : a.normal.isFinite = a.isFinite := by
  cases a <;> simp [LRD.Row.normal, LRD.Row.isFinite]

@[simp] theorem approx_normal_input (a : LRD.Row) (t : Nat) :
    a.normal.approx t = a.approx t := by
  cases a <;> simp [LRD.Row.normal, LRD.Row.approx]

/-- Generated packages are invariant under normalizing their input row. -/
@[simp] theorem package_normal_input (a : LRD.Row) (b : Nat) :
    LRD.package a.normal b = LRD.package a b := by
  simp only [LRD.package, isFinite_normal]
  split
  · rfl
  · congr 1
    apply List.map_congr_left
    intro t ht
    exact approx_normal_input a t

theorem normalPackage_toNormal (a : LRD.Row) (b : Nat) :
    normalPackage (toNormal a) b = (LRD.package a b).map toNormal := by
  simp [normalPackage]

theorem cmp_toNormal (a b : LRD.Row) :
    normalRowCmp (toNormal a) (toNormal b) = LRD.Row.cmp a b := row_cmp_normal a b

theorem compare_lift (a b : LRD.Diagram) :
    graphCompare normalRowCmp (liftGraph a) (liftGraph b) = LRD.cmp a b :=
  ColumnMap.graphCompare_map toNormal LRD.Row.cmp normalRowCmp cmp_toNormal a b

/-- Every actual raw expansion lifts exactly, including noncanonical inputs. -/
theorem fs_lift (g : LRD.Diagram) (n : Nat) :
    liftGraph (LRD.fs g n) = expand normalRowCmp normalPackage (liftGraph g) n :=
  (ColumnMap.expand_map toNormal LRD.Row.cmp normalRowCmp cmp_toNormal
    LRD.package normalPackage normalPackage_toNormal g n).symm

theorem valid_lift_iff (g : LRD.Diagram) : Valid (liftGraph g) ↔ Valid g :=
  ColumnMap.valid_map_iff toNormal g

theorem valid_erase_iff (g : Graph NormalRow) : Valid (eraseGraph g) ↔ Valid g :=
  ColumnMap.valid_map_iff Subtype.val g

private theorem erase_lift_entry {e : Entry LRD.Row} (he : e.row.normal = e.row) :
    ColumnMap.mapEntry Subtype.val (ColumnMap.mapEntry toNormal e) = e := by
  cases e
  simp only [ColumnMap.mapEntry, toNormal] at he ⊢
  rw [he]

theorem erase_lift_canonical {g : LRD.Diagram} (hg : LRDCanonical.Canonical g) :
    eraseGraph (liftGraph g) = g := by
  unfold eraseGraph liftGraph ColumnMap.mapGraph
  rw [List.map_map]
  have hmap : ∀ c ∈ g, (ColumnMap.mapColumn Subtype.val ∘ ColumnMap.mapColumn toNormal) c = c := by
    intro c hc
    dsimp only [Function.comp_def, ColumnMap.mapColumn]
    rw [List.map_map]
    have heq : ∀ e ∈ c, (ColumnMap.mapEntry Subtype.val ∘ ColumnMap.mapEntry toNormal) e = e := by
      intro e he
      exact erase_lift_entry (hg c hc e he)
    calc
      _ = c.map id := List.map_congr_left heq
      _ = c := List.map_id _
  calc
    _ = g.map id := List.map_congr_left hmap
    _ = g := List.map_id _

theorem erase_lift_standard {g : LRD.Diagram} (hg : LRD.Standard g) :
    eraseGraph (liftGraph g) = g := erase_lift_canonical (LRDCanonical.standard_canonical hg)

theorem lift_erase (g : Graph NormalRow) : liftGraph (eraseGraph g) = g := by
  unfold liftGraph eraseGraph
  rw [ColumnMap.mapGraph_comp]
  have heq : toNormal ∘ (Subtype.val : NormalRow → LRD.Row) = id :=
    funext toNormal_of_normal
  rw [heq, ColumnMap.mapGraph_id]

theorem erase_canonical (g : Graph NormalRow) : LRDCanonical.Canonical (eraseGraph g) := by
  intro c hc e he
  obtain ⟨source, _, rfl⟩ := List.mem_map.mp hc
  obtain ⟨edge, _, rfl⟩ := List.mem_map.mp he
  exact edge.row.property

theorem lift_injective_on_canonical {a b : LRD.Diagram}
    (ha : LRDCanonical.Canonical a) (hb : LRDCanonical.Canonical b)
    (h : liftGraph a = liftGraph b) : a = b := by
  have he := congrArg eraseGraph h
  simpa only [erase_lift_canonical ha, erase_lift_canonical hb] using he

theorem lift_injective_on_standard {a b : LRD.Diagram}
    (ha : LRD.Standard a) (hb : LRD.Standard b) (h : liftGraph a = liftGraph b) : a = b :=
  lift_injective_on_canonical (LRDCanonical.standard_canonical ha)
    (LRDCanonical.standard_canonical hb) h

theorem erase_normalPackage (a : NormalRow) (b : Nat) :
    (normalPackage a b).map Subtype.val = LRD.package a.val b := by
  unfold normalPackage
  rw [List.map_map]
  have heq : ∀ r ∈ LRD.package a.val b, (Subtype.val ∘ toNormal) r = r := by
    intro r hr
    exact package_normal hr
  calc
    _ = (LRD.package a.val b).map id := List.map_congr_left heq
    _ = LRD.package a.val b := List.map_id _

/-- Erasure commutes with expansion on every NormalRow graph. -/
theorem expand_erase (g : Graph NormalRow) (n : Nat) :
    LRD.fs (eraseGraph g) n = eraseGraph (expand normalRowCmp normalPackage g n) :=
  ColumnMap.expand_map Subtype.val normalRowCmp LRD.Row.cmp (fun _ _ => rfl)
    normalPackage LRD.package (fun a b => (erase_normalPackage a b).symm) g n

theorem normalRowCompareSound : ColumnRepresentation.RowCompareSound normalRowCmp normalLt :=
  ⟨fun {a b} h => (normalRowCmp_eq_iff a b).mp h, fun h => h⟩

/-- The actual generated rows are strictly lower in the equality-correct carrier. -/
theorem normalPackage_lt {a r : NormalRow} {b : Nat} (hr : r ∈ normalPackage a b) :
    normalLt r a := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
  change LRD.Row.cmp s.normal a.val = .lt
  rw [package_normal hs]
  exact LRDRowDecrease.package_lt hs

theorem normalLt_trans {a b c : NormalRow} (hab : normalLt a b) (hbc : normalLt b c) :
    normalLt a c := normalRowCmp_lt_trans hab hbc

theorem normalLt_irrefl (a : NormalRow) : ¬ normalLt a a := row_cmp_lt_irrefl a.val

#print axioms fs_lift
#print axioms erase_lift_standard
#print axioms expand_erase
#print axioms normalRowCompareSound
#print axioms normalPackage_lt

end OrdinalFormal.LRDNormalLift
