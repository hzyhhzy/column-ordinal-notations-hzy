import BTnSSBMS.NumericalRelocation

/-!
Composition of actual finite numerical transports. This gives equality
of the complete output syntax, with arbitrary nesting and scope exits,
not merely equality of root coordinates or of an ordinal interpretation.
-/
namespace BTnSSBMS.Parents

theorem point_map (first second : List Nat) (p : Nat) (inside : p < first.length) :
    point (first.map (point second)) p = point second (point first p) := by
  simp only [point, List.getElem?_map, List.getElem?_eq_getElem inside, Option.map_some, Option.getD_some]

theorem point_composition_append {d : Nat} {source middle : ParentContext} {first : List Nat}
    (view : NumericalView d source middle first) (second : List Nat) (length : second.length = middle.length)
    (next : Nat) :
    (first ++ [middle.length]).map (point (second ++ [next])) = first.map (point second) ++ [next] := by
  rw [List.map_append]
  have old : first.map (point (second ++ [next])) = first.map (point second) := by
    apply List.map_congr_left
    intro p member
    obtain ⟨i, inside, lookup⟩ := List.getElem_of_mem member
    have bound := view.bounded i (by rw [← view.length]; exact inside)
    have actual : point first i = p := by simp only [point, List.getElem?_eq_getElem inside, Option.getD_some, lookup]
    rw [actual] at bound
    exact point_append_old second p next (by omega)
  rw [old]
  simp only [List.map_cons, List.map_nil, ← length, point_append_last]

end BTnSSBMS.Parents

namespace BTnSSBMS.Source

theorem relocationHead_compose {d : Nat} {source middle : ParentContext} {first : List Nat}
    (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
    (middleCoherent : Parents.Coherent d middle) (middleValid : Parents.ContextValid middle)
    (view : Parents.NumericalView d source middle first)
    (target : ParentContext) (second a : List Nat) :
    relocationHead d middle target second (relocationHead d source middle first a) =
      relocationHead d source target (first.map (Parents.point second)) a := by
  apply List.ext_getElem
  · simp only [relocationHead_width]
  · intro j left right
    have room : j < d := by simpa only [relocationHead_width] using left
    have value : (relocationHead d middle target second (relocationHead d source middle first a))[j]?.getD 0 =
        (relocationHead d source target (first.map (Parents.point second)) a)[j]?.getD 0 := by
      rw [relocationHead_value d middle target second _ room,
        relocationHead_value d source target _ a room]
      unfold Parents.representedValue
      rw [relocationHead_parents sourceCoherent sourceValid middleCoherent middleValid view a j room]
      cases found : (Parents.label d source a).parents[j]?.join with
      | none => rfl
      | some p =>
        have bound := Parents.label_parent_bound d source a j p found
        simp only [Option.map_some, Option.getD_some,
          Parents.point_map first second p (by rw [view.length]; exact bound)]
    simpa only [List.getElem?_eq_getElem left, List.getElem?_eq_getElem right, Option.getD_some] using value

mutual
  theorem relocate_compose (d : Nat) (e : NumericalExpr) (source middle target : ParentContext)
      (first second : List Nat)
      (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
      (middleCoherent : Parents.Coherent d middle) (middleValid : Parents.ContextValid middle)
      (view : Parents.NumericalView d source middle first) (length : second.length = middle.length) :
      relocate d middle target second (relocate d source middle first e) =
        relocate d source target (first.map (Parents.point second)) e := by
    cases e with
    | nil => rfl
    | cons a hs tail =>
      let b := relocationHead d source middle first a
      let c := relocationHead d source target (first.map (Parents.point second)) a
      have head := relocationHead_compose sourceCoherent sourceValid middleCoherent middleValid view target second a
      have nextView := relocation_view_append sourceCoherent sourceValid middleCoherent middleValid view a
      have nextLength : (second ++ [target.length]).length =
          (middle ++ [Parents.label d middle b]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil, length]
      have inside := relocateForests_compose d hs
        (source ++ [Parents.label d source a]) (middle ++ [Parents.label d middle b])
        (target ++ [Parents.label d target c]) (first ++ [middle.length]) (second ++ [target.length])
        (Parents.coherent_append_label sourceCoherent a) (Parents.context_valid_append_label d source sourceValid a)
        (Parents.coherent_append_label middleCoherent b) (Parents.context_valid_append_label d middle middleValid b)
        nextView nextLength
      have after := relocate_compose d tail
        (source ++ [Parents.label d source a]) (middle ++ [Parents.label d middle b])
        (target ++ [Parents.label d target c]) (first ++ [middle.length]) (second ++ [target.length])
        (Parents.coherent_append_label sourceCoherent a) (Parents.context_valid_append_label d source sourceValid a)
        (Parents.coherent_append_label middleCoherent b) (Parents.context_valid_append_label d middle middleValid b)
        nextView nextLength
      rw [Parents.point_composition_append view second length target.length] at inside after
      simp only [relocate, head]
      rw [inside, after]

  theorem relocateForests_compose (d : Nat) (hs : Forests (List Nat)) (source middle target : ParentContext)
      (first second : List Nat)
      (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
      (middleCoherent : Parents.Coherent d middle) (middleValid : Parents.ContextValid middle)
      (view : Parents.NumericalView d source middle first) (length : second.length = middle.length) :
      relocateForests d middle target second (relocateForests d source middle first hs) =
        relocateForests d source target (first.map (Parents.point second)) hs := by
    cases hs with
    | nil => rfl
    | cons h hs =>
      simp only [relocateForests,
        relocate_compose d h source middle target first second sourceCoherent sourceValid
          middleCoherent middleValid view length,
        relocateForests_compose d hs source middle target first second sourceCoherent sourceValid
          middleCoherent middleValid view length]
end

end BTnSSBMS.Source
