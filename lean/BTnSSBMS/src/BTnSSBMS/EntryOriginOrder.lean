import BTnSSBMS.EncoderEntryFibers

/-!
Visible source origins strictly preserve source position order. The proof
uses their actual entering views and prefix snapshots, not an unproved
global injectivity of the recursive execution trace.
-/
namespace BTnSSBMS.Encoder

theorem Entry.OriginAt.first_lt {d : Nat} {source : ParentContext} {visible owners : List Nat}
    {materials : List (Forests (List Nat))} {state : State d} {left right : Entry d} {i k : Nat}
    (leftOrigin : left.OriginAt source visible owners materials state i)
    (rightOrigin : right.OriginAt source visible owners materials state k)
    (rightSound : right.Sound) (before : i < k) (inside : k < source.length) :
    left.state.length < right.state.length := by
  have sourceLength : right.source.length = k := by
    rw [rightOrigin.sourceEq, List.length_take, Nat.min_eq_left (by omega)]
  have viewBound := rightSound.view.bounded i (by omega)
  have visibleBound : i < right.visible.length := by rw [rightSound.view.length, sourceLength]; exact before
  have samePoint : Parents.point right.visible i = Parents.point visible i := by
    rw [rightOrigin.visibleEq]
    simp only [Parents.point, List.getElem?_take_of_lt before]
  rw [table_length, samePoint] at viewBound
  have beforeRepresentative := leftOrigin.beforeRepresentative
  omega

theorem Entry.OriginAt.index_eq_of_first_eq {d : Nat} {source : ParentContext} {visible owners : List Nat}
    {materials : List (Forests (List Nat))} {state : State d} {left right : Entry d} {i k : Nat}
    (leftOrigin : left.OriginAt source visible owners materials state i)
    (rightOrigin : right.OriginAt source visible owners materials state k)
    (leftSound : left.Sound) (rightSound : right.Sound)
    (leftBound : i < source.length) (rightBound : k < source.length)
    (same : left.state.length = right.state.length) : i = k := by
  by_cases before : i < k
  · have strict := leftOrigin.first_lt rightOrigin rightSound before rightBound
    omega
  · by_cases after : k < i
    · have strict := rightOrigin.first_lt leftOrigin leftSound after leftBound
      omega
    · omega

theorem Entry.Sound.first_numericalHead_in {d : Nat} {entry : Entry d} {state : State d}
    (sound : entry.Sound) (zero : VisibleZero entry.state entry.visible)
    (extended : entry.result <+: state) : NumericalHead state entry.state.length := by
  intro j room root edge
  rw [sound.first_parent_in extended room] at edge
  obtain ⟨p, selected, named⟩ := Option.map_eq_some_iff.mp edge
  have bound := Parents.label_parent_bound d entry.source entry.coordinates j p selected
  have visibleBound : p < entry.visible.length := by rw [sound.view.length]; exact bound
  have pointMember : Parents.point entry.visible p ∈ entry.visible := by
    simpa only [Parents.point, List.getElem?_eq_getElem visibleBound, Option.getD_some] using
      List.getElem_mem visibleBound
  obtain ⟨height, output⟩ := zero _ pointMember
  refine ⟨height, ?_⟩
  rw [← named]
  exact readout_extends (entry.state_prefix_result.trans extended) output

theorem standard_entry_numericalHead {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {entry : Entry d}
    (member : entry ∈ entries d e [] [] [] [] []) :
    NumericalHead (encode d (Parents.annotate d [] e) [] []) entry.state.length :=
  (standard_entries_sound positive standard entry member).first_numericalHead_in
    (standard_entries_fibers positive standard entry member).zero
    (entries_execution d e [] [] [] [] [] entry member).resultPrefix

end BTnSSBMS.Encoder
