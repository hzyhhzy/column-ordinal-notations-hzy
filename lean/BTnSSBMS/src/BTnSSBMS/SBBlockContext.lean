import BTnSSBMS.SourceSB

/-! The historical blocks used by SB really start at the corresponding
visible source positions and are legal in their original prefixes.
Appending a current source entry proves these facts; they are not
requirements hidden in the definition of a standard source. -/
namespace BTnSSBMS.Source

structure BlockContext (d : Nat) (context : ParentContext) (history : List NumericalExpr) : Prop where
  length : history.length = context.length
  entries : ∀ root, root < context.length → ∃ a hs rest,
    history[root]? = some (.cons a hs rest) ∧
    Parents.label d (context.take root) a = context[root]?.getD default ∧
    FiniteLegal d (context.take root) (.cons a hs rest)

theorem empty_blockContext (d : Nat) : BlockContext d [] [] :=
  ⟨rfl, by intro root inside; simp at inside⟩

theorem BlockContext.append {d : Nat} {context : ParentContext} {history : List NumericalExpr}
    (known : BlockContext d context history) (a : List Nat) (hs : Forests (List Nat))
    (rest : NumericalExpr) (legal : FiniteLegal d context (.cons a hs rest)) :
    BlockContext d (context ++ [Parents.label d context a]) (history ++ [.cons a hs rest]) := by
  refine ⟨by simp only [List.length_append, List.length_cons, List.length_nil, known.length], ?_⟩
  intro root inside
  by_cases old : root < context.length
  · obtain ⟨b, ks, tail, found, label, allowed⟩ := known.entries root old
    refine ⟨b, ks, tail, ?_, ?_, ?_⟩
    · simpa only [List.getElem?_append_left (by rw [known.length]; exact old)] using found
    · simpa only [List.take_append_of_le_length (Nat.le_of_lt old), List.getElem?_append_left old] using label
    · simpa only [List.take_append_of_le_length (Nat.le_of_lt old)] using allowed
  · have last : root = context.length := by
      simp only [List.length_append, List.length_cons, List.length_nil] at inside
      omega
    subst root
    refine ⟨a, hs, rest, ?_, ?_, ?_⟩
    · rw [← known.length, List.getElem?_concat_length]
    · simp only [List.take_left, List.getElem?_concat_length, Option.getD_some]
    · simpa only [List.take_left] using legal

theorem BlockContext.material {d : Nat} {context : ParentContext} {history : List NumericalExpr}
    (known : BlockContext d context history) {root : Nat} (inside : root < context.length) :
    ∃ hs rest, history[root]?.getD .nil = .cons (context[root]?.getD default).coordinates hs rest ∧
      FiniteLegal d (context.take root) (.cons (context[root]?.getD default).coordinates hs rest) := by
  obtain ⟨a, hs, rest, found, label, legal⟩ := known.entries root inside
  have coordinates : a = (context[root]?.getD default).coordinates := congrArg ParentLabel.coordinates label
  subst a
  exact ⟨hs, rest, by simp only [found, Option.getD_some], legal⟩

theorem BlockContext.rebaseBlock_finiteLegal {d cut root : Nat} {context : ParentContext}
    {history : List NumericalExpr} (known : BlockContext d context history)
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (unit : Parents.UnitSteps d context) (a : List Nat)
    (currentUnit : Parents.UnitSteps d (context ++ [Parents.label d context a]))
    (positive : 0 < cut) (room : cut < d) (inside : root < context.length)
    (path : Parents.Ancestor (context ++ [Parents.label d context a]) (cut - 1) root context.length)
    (same : (Parents.label d context a).parents[cut]?.join = Parents.parent context cut root) :
    FiniteLegal d context (rebaseBlock d cut context root a (history[root]?.getD .nil)) := by
  obtain ⟨hs, rest, material, legal⟩ := known.material inside
  rw [material]
  exact partial_rebase_finiteLegal coherent valid unit a currentUnit positive room inside path same
    hs (takeAbove ((context[root]?.getD default).coordinates[0]?.getD 0) rest)
    (rootBlock_finiteLegal legal)

end BTnSSBMS.Source
