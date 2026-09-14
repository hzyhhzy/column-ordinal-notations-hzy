import OrdinalFormal.Columns

/-!
Naturality of the actual column algorithm under a row map. The map need not be
injective: preservation of comparator outputs and generated row lists suffices.
No order, validity or well-foundedness premise is assumed.
-/

set_option maxHeartbeats 600000
set_option maxRecDepth 2048

namespace OrdinalFormal.ColumnMap
open Columns
universe u v
variable {A : Type u} {B : Type v}

def mapEntry (f : A → B) (e : Entry A) : Entry B := ⟨f e.row, e.parent, e.root⟩
def mapColumn (f : A → B) (c : Column A) : Column B := c.map (mapEntry f)
def mapGraph (f : A → B) (g : Graph A) : Graph B := g.map (mapColumn f)

@[simp] theorem mapEntry_row (f : A → B) (e : Entry A) : (mapEntry f e).row = f e.row := rfl
@[simp] theorem mapEntry_parent (f : A → B) (e : Entry A) : (mapEntry f e).parent = e.parent := rfl
@[simp] theorem mapEntry_root (f : A → B) (e : Entry A) : (mapEntry f e).root = e.root := rfl

@[simp] theorem mapColumn_nil (f : A → B) : mapColumn f [] = [] := rfl
@[simp] theorem mapGraph_nil (f : A → B) : mapGraph f [] = [] := rfl
@[simp] theorem mapColumn_cons (f : A → B) (e : Entry A) (c : Column A) :
    mapColumn f (e :: c) = mapEntry f e :: mapColumn f c := rfl
@[simp] theorem mapGraph_cons (f : A → B) (c : Column A) (g : Graph A) :
    mapGraph f (c :: g) = mapColumn f c :: mapGraph f g := rfl
@[simp] theorem mapColumn_append (f : A → B) (c d : Column A) :
    mapColumn f (c ++ d) = mapColumn f c ++ mapColumn f d := List.map_append
@[simp] theorem mapGraph_append (f : A → B) (g h : Graph A) :
    mapGraph f (g ++ h) = mapGraph f g ++ mapGraph f h := List.map_append
@[simp] theorem mapGraph_length (f : A → B) (g : Graph A) :
    (mapGraph f g).length = g.length := List.length_map _
@[simp] theorem mapGraph_take (f : A → B) (g : Graph A) (n : Nat) :
    (mapGraph f g).take n = mapGraph f (g.take n) := by simp [mapGraph]

theorem listCompare_map {X : Type u} {Y : Type v}
    (f : X → Y) (cmpX : X → X → Ordering) (cmpY : Y → Y → Ordering)
    (hc : ∀ a b, cmpY (f a) (f b) = cmpX a b) (as bs : List X) :
    listCompare cmpY (as.map f) (bs.map f) = listCompare cmpX as bs := by
  induction as generalizing bs with
  | nil => cases bs <;> rfl
  | cons a as ih =>
    cases bs with
    | nil => rfl
    | cons b bs => simp only [List.map_cons, listCompare, hc, ih]

section Compare
variable (f : A → B) (cmpA : A → A → Ordering) (cmpB : B → B → Ordering)
variable (hc : ∀ a b, cmpB (f a) (f b) = cmpA a b)
include hc

theorem entryCompare_map (a b : Entry A) :
    entryCompare cmpB (mapEntry f a) (mapEntry f b) = entryCompare cmpA a b := by
  simp only [entryCompare, mapEntry, hc]

theorem controlCompare_map (a b : Entry A) :
    controlCompare cmpB (mapEntry f a) (mapEntry f b) = controlCompare cmpA a b := by
  simp only [controlCompare, mapEntry, hc]

theorem columnCompare_map (a b : Column A) :
    listCompare (entryCompare cmpB) (mapColumn f a) (mapColumn f b) =
      listCompare (entryCompare cmpA) a b :=
  listCompare_map (mapEntry f) _ _ (entryCompare_map f cmpA cmpB hc) a b

theorem graphCompare_map (a b : Graph A) :
    graphCompare cmpB (mapGraph f a) (mapGraph f b) = graphCompare cmpA a b :=
  listCompare_map (mapColumn f) _ _ (columnCompare_map f cmpA cmpB hc) a b

theorem insertDescending_map (a : Entry A) (c : Column A) :
    insertDescending cmpB (mapEntry f a) (mapColumn f c) =
      mapColumn f (insertDescending cmpA a c) := by
  induction c with
  | nil => rfl
  | cons b bs ih =>
    simp only [mapColumn_cons, insertDescending, entryCompare_map f cmpA cmpB hc]
    split <;> simp only [mapColumn_cons, ih]

theorem sortDescending_map (c : Column A) :
    sortDescending cmpB (mapColumn f c) = mapColumn f (sortDescending cmpA c) := by
  induction c with
  | nil => rfl
  | cons a as ih =>
    simp only [mapColumn_cons, sortDescending, ih, insertDescending_map f cmpA cmpB hc]

theorem dedupSorted_map (c : Column A) :
    dedupSorted cmpB (mapColumn f c) = mapColumn f (dedupSorted cmpA c) := by
  induction c with
  | nil => rfl
  | cons a as ih =>
    simp only [mapColumn_cons, dedupSorted, ih]
    generalize hr : dedupSorted cmpA as = rest
    cases rest with
    | nil => rfl
    | cons b bs =>
      simp only [mapColumn_cons, entryCompare_map f cmpA cmpB hc]
      split <;> rfl

theorem normalizeColumn_map (c : Column A) :
    normalizeColumn cmpB (mapColumn f c) = mapColumn f (normalizeColumn cmpA c) := by
  have hroots :
      (mapColumn f c).flatMap (fun e => (List.range (e.root + 1)).map fun q => {e with root := q}) =
      mapColumn f (c.flatMap (fun e => (List.range (e.root + 1)).map fun q => {e with root := q})) := by
    simp [mapColumn, List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def, mapEntry]
  unfold normalizeColumn
  rw [hroots, sortDescending_map f cmpA cmpB hc, dedupSorted_map f cmpA cmpB hc]

theorem normalize_map (g : Graph A) :
    normalize cmpB (mapGraph f g) = mapGraph f (normalize cmpA g) := by
  simp only [normalize, mapGraph, List.map_map, Function.comp_def,
    normalizeColumn_map f cmpA cmpB hc]

private theorem controlFold_map (c : Column A) (a : Entry A) :
    (mapColumn f c).foldl (fun a b => if controlCompare cmpB a b == .lt then b else a)
      (mapEntry f a) = mapEntry f
        (c.foldl (fun a b => if controlCompare cmpA a b == .lt then b else a) a) := by
  induction c generalizing a with
  | nil => rfl
  | cons b bs ih =>
    simp only [mapColumn_cons, List.foldl_cons, controlCompare_map f cmpA cmpB hc]
    split <;> exact ih _

theorem control_map (c : Column A) :
    Columns.control cmpB (mapColumn f c) = (Columns.control cmpA c).map (mapEntry f) := by
  cases c with
  | nil => rfl
  | cons a as => simp only [mapColumn_cons, Columns.control, controlFold_map f cmpA cmpB hc,
      Option.map_some]

end Compare

@[simp] theorem mapEntry_move (f : A → B) (cut len b : Nat) (e : Entry A) :
    moveEntry cut len b (mapEntry f e) = mapEntry f (moveEntry cut len b e) := rfl

theorem mapColumn_move (f : A → B) (cut len b : Nat) (c : Column A) :
    (mapColumn f c).map (moveEntry cut len b) = mapColumn f (c.map (moveEntry cut len b)) := by
  simp only [mapColumn, List.map_map, Function.comp_def, mapEntry_move]

@[simp] theorem mapGraph_lookup (f : A → B) (g : Graph A) (i : Nat) :
    ((mapGraph f g)[i]?.getD []) = mapColumn f (g[i]?.getD []) := by
  simp only [mapGraph, List.getElem?_map]
  cases g[i]? <;> rfl

@[simp] theorem mapGraph_last (f : A → B) (g : Graph A) :
    ((mapGraph f g).getLast?.getD []) = mapColumn f (g.getLast?.getD []) := by
  simp only [List.getLast?_eq_getElem?, mapGraph_length, mapGraph_lookup]

/-- Coordinates are unchanged, so geometric validity is reflected as well as preserved,
even if several rows have the same image. -/
theorem valid_map_iff (f : A → B) (g : Graph A) : Valid (mapGraph f g) ↔ Valid g := by
  constructor
  · intro h i e he
    have hm : mapEntry f e ∈ ((mapGraph f g)[i]?.getD []) := by
      rw [mapGraph_lookup]
      exact List.mem_map.mpr ⟨e, he, rfl⟩
    exact h i (mapEntry f e) hm
  · intro h i e he
    rw [mapGraph_lookup] at he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    exact h i a ha

@[simp] theorem mapEntry_id (e : Entry A) : mapEntry id e = e := rfl
@[simp] theorem mapColumn_id (c : Column A) : mapColumn id c = c := by
  induction c with
  | nil => rfl
  | cons e es ih => simp only [mapColumn_cons, mapEntry_id, ih]
@[simp] theorem mapGraph_id (g : Graph A) : mapGraph id g = g := by
  induction g with
  | nil => rfl
  | cons c cs ih => simp only [mapGraph_cons, mapColumn_id, ih]

theorem mapGraph_comp {C : Type u} (f : A → B) (h : B → C) (g : Graph A) :
    mapGraph h (mapGraph f g) = mapGraph (h ∘ f) g := by
  simp [mapGraph, mapColumn, List.map_map, Function.comp_def, mapEntry]

section Expand
variable (f : A → B) (cmpA : A → A → Ordering) (cmpB : B → B → Ordering)
variable (hc : ∀ a b, cmpB (f a) (f b) = cmpA a b)
variable (packageA : Package A) (packageB : Package B)
variable (hp : ∀ row b, packageB (f row) b = (packageA row b).map f)

include hc in
theorem ordinarySeam_map (last : Column A) (e : Entry A) (len b : Nat) :
    ordinarySeam cmpB (mapColumn f last) (mapEntry f e) len b =
      mapColumn f (ordinarySeam cmpA last e len b) := by
  simp [ordinarySeam, mapColumn, List.map_flatMap, List.flatMap_map,
    List.map_map, Function.comp_def, mapEntry, hc]
  rfl

include hp in
theorem generatedSeam_map (e : Entry A) (len b : Nat) :
    generatedSeam packageB (mapEntry f e) len b =
      mapColumn f (generatedSeam packageA e len b) := by
  simp [generatedSeam, mapColumn, List.map_flatMap, List.flatMap_map,
    List.map_map, Function.comp_def, mapEntry, hp]

include hc hp

/-- Exact naturality of the literal appended block, including normalization. -/
theorem block_map (g : Graph A) (e : Entry A) (b : Nat) :
    block cmpB packageB (mapGraph f g) (mapEntry f e) b =
      mapGraph f (block cmpA packageA g e b) := by
  unfold block
  simp only [mapGraph_length, mapEntry_parent, mapGraph_lookup, mapGraph_last,
    mapColumn_move, ordinarySeam_map f cmpA cmpB hc,
    generatedSeam_map f packageA packageB hp]
  simp only [mapGraph, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro i hi
  split
  · simp only [← mapColumn_append, normalizeColumn_map f cmpA cmpB hc]
  · simp only [List.append_nil, normalizeColumn_map f cmpA cmpB hc]

/-- Exact naturality of the complete actual fundamental-sequence expansion.
No injectivity, row-order law, input validity or well-foundedness is required. -/
theorem expand_map (g : Graph A) (n : Nat) :
    expand cmpB packageB (mapGraph f g) n = mapGraph f (expand cmpA packageA g n) := by
  unfold expand
  simp only [mapGraph_length, mapGraph_take, mapGraph_last, control_map f cmpA cmpB hc]
  cases he : Columns.control cmpA (g.getLast?.getD []) with
  | none => rfl
  | some e =>
    simp only [Option.map_some]
    rw [mapGraph_append]
    have hb := block_map f cmpA cmpB hc packageA packageB hp g e
    have hh := congrArg (fun xs => mapGraph f (g.take (g.length - 1)) ++ xs)
      (congrArg (fun k => (List.range n).flatMap k) (funext hb))
    simpa only [mapGraph, List.map_flatMap] using hh

end Expand

#print axioms graphCompare_map
#print axioms normalizeColumn_map
#print axioms control_map
#print axioms block_map
#print axioms expand_map
#print axioms valid_map_iff

end OrdinalFormal.ColumnMap
