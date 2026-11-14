import BTnSSBMS.ZeroCopyShape

/-! The zero-class seam lowers the numerical floor. Old heads above
that floor cannot be siblings of any new externally parented head.
The root itself is treated by a complete-block comparison. -/
namespace BTnSSBMS.Source

theorem BN.splice_zero_above_floor {d : Nat} {context : ParentContext}
    {e replacement : NumericalExpr} {root : List Nat}
    (ordered : BN d context e) (positive : 0 < d) (legal : FiniteLegal d context e)
    (above : ∀ a ∈ labels e, root[0]?.getD 0 < a[0]?.getD 0)
    {terminal : List Nat} {attached : Forests (List Nat)}
    (last : last? e = some (terminal, attached))
    (good : BN d (outerContext d context (Source.dropLast e)) replacement)
    (finite : FiniteLegal d (outerContext d context (Source.dropLast e)) replacement)
    (lower : ExprLE replacement (.cons terminal attached .nil))
    (floor : TerminalFloor root replacement) : BN d context (splice 0 replacement e) := by
  cases e with
  | nil => simp [last?] at last
  | cons a hs rest =>
    cases rest with
    | nil => simpa only [Source.dropLast, outerContext, splice] using good
    | cons c js more =>
      have lastRest : last? (.cons c js more) = some (terminal, attached) := by simpa only [last?] using last
      let entry := context ++ [Parents.label d context a]
      let before := outerContext d entry (Source.dropLast (.cons c js more))
      have good' : BN d before replacement := by simpa only [Source.dropLast, outerContext] using good
      have finite' : FiniteLegal d before replacement := by simpa only [Source.dropLast, outerContext] using finite
      rw [splice]
      refine ⟨?_, ordered.2.1, ordered.2.2.splice_zero_above_floor positive legal.2.2.2.2
        (fun col member => above col (List.mem_cons_of_mem a member)) lastRest good' finite' lower floor⟩
      intro index b ks tail found same
      rcases splice_zero_drop_cases d entry (.cons c js more) replacement index found with
        ⟨after, old, nonempty, contexts, value⟩ | ⟨offset, selected, contexts⟩
      · rw [contexts] at same
        have prior := ordered.1 index b ks after old same
        have laterLegal := legal.2.2.2.2.drop index
        rw [old] at laterLegal
        have equalZero := same_zero_parent_value positive
          ((List.prefix_append context _).trans (dropContext_prefix d entry index (.cons c js more)))
          a b legal.2.1 laterLegal.2.1 same
        have unchanged := takeAbove_splice_zero_surviving replacement index (a[0]?.getD 0)
          old nonempty (Nat.le_of_eq equalZero)
        change ExprLE (rootBlock (.cons b ks tail))
          (.cons a hs (takeAbove (a[0]?.getD 0) (splice 0 replacement (.cons c js more))))
        rw [unchanged]
        have afterLast := (last_drop_of_cons index (.cons c js more) old).trans lastRest
        have decrease := rootBlock_mono (splice_zero_le (.cons b ks after) replacement afterLast lower)
        rw [← value] at decrease
        exact decrease.trans prior
      · change dropContext d entry index (splice 0 replacement (.cons c js more)) =
          dropContext d before offset replacement at contexts
        rw [contexts] at same
        cases replacement with
        | nil => cases offset <;> simp [Source.drop] at selected
        | cons first forests remaining =>
          have fenced : ∀ v ∈ labels (.cons first forests remaining), first[0]?.getD 0 ≤ v[0]?.getD 0 := by
            intro v member
            rw [floor.1]
            exact floor.2 v member
          have initial : context <+: before :=
            (List.prefix_append context _).trans (outerContext_prefix d entry (Source.dropLast (.cons c js more)))
          have external : ∀ p,
              (Parents.label d (dropContext d before offset (.cons first forests remaining)) b).parents[0]?.join = some p →
                p < before.length := by
            intro p hit
            rw [same] at hit
            exact Nat.lt_of_lt_of_le (Parents.label_parent_bound d context a 0 p hit) initial.length_le
          have atFloor := external_suffix_floor positive before first forests remaining offset selected fenced external
          have laterLegal := finite'.drop offset
          rw [selected] at laterLegal
          have equalZero := same_zero_parent_value positive
            (initial.trans (dropContext_prefix d before offset (.cons first forests remaining)))
            a b legal.2.1 laterLegal.2.1 same
          have higher := above a (by simp [labels])
          rw [floor.1] at atFloor
          omega

theorem BN.splice_zero_root {d : Nat} {context : ParentContext}
    {a : List Nat} {hs : Forests (List Nat)} {rest replacement : NumericalExpr}
    (ordered : BN d context (.cons a hs rest)) (positive : 0 < d)
    (legal : FiniteLegal d context (.cons a hs rest)) (nonempty : rest ≠ .nil)
    (above : ∀ b ∈ labels rest, a[0]?.getD 0 < b[0]?.getD 0)
    {terminal : List Nat} {attached : Forests (List Nat)}
    (last : last? (.cons a hs rest) = some (terminal, attached))
    (good : BN d (outerContext d context (Source.dropLast (.cons a hs rest))) replacement)
    (finite : FiniteLegal d (outerContext d context (Source.dropLast (.cons a hs rest))) replacement)
    (lower : ExprLE replacement (.cons terminal attached .nil))
    (floor : TerminalFloor a replacement)
    (blocks : ExprLE (rootBlock replacement) (Source.dropLast (.cons a hs rest))) :
    BN d context (splice 0 replacement (.cons a hs rest)) := by
  have lastRest : last? rest = some (terminal, attached) := by
    cases rest with
    | nil => exact False.elim (nonempty rfl)
    | cons b ks tail => simpa only [last?] using last
  let entry := context ++ [Parents.label d context a]
  let before := outerContext d entry (Source.dropLast rest)
  have good' : BN d before replacement := by
    cases rest with
    | nil => exact False.elim (nonempty rfl)
    | cons b ks tail => simpa only [Source.dropLast, outerContext] using good
  have finite' : FiniteLegal d before replacement := by
    cases rest with
    | nil => exact False.elim (nonempty rfl)
    | cons b ks tail => simpa only [Source.dropLast, outerContext] using finite
  have cut : takeAbove (a[0]?.getD 0) replacement = .nil := by
    cases replacement with
    | nil => rfl
    | cons first forests remaining => rw [takeAbove, if_neg (by rw [floor.1]; omega)]
  have complete := rootBlock_splice_zero_high (hs := hs) nonempty above replacement cut
  rw [splice_cons_tail 0 replacement a hs rest nonempty] at complete ⊢
  refine ⟨?_, ordered.2.1,
    ordered.2.2.splice_zero_above_floor positive legal.2.2.2.2 above lastRest good' finite' lower floor⟩
  intro index b ks tail found same
  rcases splice_zero_drop_cases d entry rest replacement index found with
    ⟨after, old, _, contexts, _⟩ | ⟨offset, selected, contexts⟩
  · rw [contexts] at same
    have laterLegal := legal.2.2.2.2.drop index
    rw [old] at laterLegal
    have equalZero := same_zero_parent_value positive
      ((List.prefix_append context _).trans (dropContext_prefix d entry index rest))
      a b legal.2.1 laterLegal.2.1 same
    have higher := above b (List.mem_of_getElem? (labels_drop_head index rest old))
    omega
  · change dropContext d entry index (splice 0 replacement rest) = dropContext d before offset replacement at contexts
    rw [contexts] at same
    cases replacement with
    | nil => cases offset <;> simp [Source.drop] at selected
    | cons first forests remaining =>
      have fenced : ∀ v ∈ labels (.cons first forests remaining), first[0]?.getD 0 ≤ v[0]?.getD 0 := by
        intro v member
        rw [floor.1]
        exact floor.2 v member
      have initial : context <+: before := (List.prefix_append context _).trans (outerContext_prefix d entry (Source.dropLast rest))
      have external : ∀ p,
          (Parents.label d (dropContext d before offset (.cons first forests remaining)) b).parents[0]?.join = some p →
            p < before.length := by
        intro p hit
        rw [same] at hit
        exact Nat.lt_of_lt_of_le (Parents.label_parent_bound d context a 0 p hit) initial.length_le
      have bound := good'.external_block_le positive offset selected fenced external
      change ExprLE (rootBlock (.cons b ks tail)) (rootBlock (.cons a hs (splice 0 (.cons first forests remaining) rest)))
      rw [complete]
      exact bound.trans blocks

end BTnSSBMS.Source
