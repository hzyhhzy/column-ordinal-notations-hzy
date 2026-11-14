import BTnSSBMS.PartialRebaseCopyComparison
import BTnSSBMS.SourceBlockOrder

/-!
The source SB condition uses the actual scoped parent context together
with the complete original remaining material at each visible position.
An open forest owner is deliberately retained: SB ancestors are not
restricted to columns in the same forest or to non-owner positions.
This is a finite proof-side invariant, not part of Source.Standard.
-/
namespace BTnSSBMS.Source

def rebaseBlock (d cut : Nat) (context : ParentContext) (root : Nat)
    (position : List Nat) (material : NumericalExpr) : NumericalExpr :=
  copied d root cut ((List.range cut).map
    (fun row => position[row]?.getD 0 -
      (context[root]?.getD default).coordinates[row]?.getD 0))
    1 (context.take root) (List.replicate root 0) (rootBlock material)

def HeadSB (d cut : Nat) (context : ParentContext) (history : List NumericalExpr)
    (a : List Nat) (hs : Forests (List Nat)) (rest : NumericalExpr) : Prop :=
  0 < cut → cut < d → ∀ root, root < context.length →
    Parents.Ancestor (context ++ [Parents.label d context a]) (cut - 1) root context.length →
    (Parents.label d context a).parents[cut]?.join = Parents.parent context cut root →
    ExprLE (rootBlock (.cons a hs rest))
      (rebaseBlock d cut context root a (history[root]?.getD .nil))

mutual
  def SB (d cut : Nat) (context : ParentContext) (history : List NumericalExpr) : NumericalExpr → Prop
    | .nil => True
    | .cons a hs rest =>
        HeadSB d cut context history a hs rest ∧
        SBForests d cut (context ++ [Parents.label d context a])
          (history ++ [.cons a hs rest]) hs ∧
        SB d cut (context ++ [Parents.label d context a])
          (history ++ [.cons a hs rest]) rest
  def SBForests (d cut : Nat) (context : ParentContext) (history : List NumericalExpr) :
      Forests (List Nat) → Prop
    | .nil => True
    | .cons h rest => SB d cut context history h ∧ SBForests d cut context history rest
end

def dropBlockHistory (history : List NumericalExpr) : Nat → NumericalExpr → List NumericalExpr
  | 0, _ => history
  | _, .nil => history
  | index + 1, e@(.cons _ _ rest) => dropBlockHistory (history ++ [e]) index rest

theorem SB.drop {d cut : Nat} {context : ParentContext} {history : List NumericalExpr}
    {e : NumericalExpr} (ordered : SB d cut context history e) (index : Nat) :
    SB d cut (dropContext d context index e) (dropBlockHistory history index e) (drop index e) := by
  induction index generalizing context history e with
  | zero => exact ordered
  | succ index ih =>
    cases e with
    | nil => trivial
    | cons a hs rest => exact ih ordered.2.2

theorem SBForests.append {d cut : Nat} {context : ParentContext} {history : List NumericalExpr}
    {hs ks : Forests (List Nat)} (left : SBForests d cut context history hs)
    (right : SBForests d cut context history ks) :
    SBForests d cut context history (appendForests hs ks) := by
  cases hs with
  | nil => exact right
  | cons h rest => exact ⟨left.1, left.2.append right⟩

theorem headSB_empty_context (d cut : Nat) (history : List NumericalExpr)
    (a : List Nat) (hs : Forests (List Nat)) (rest : NumericalExpr) :
    HeadSB d cut [] history a hs rest := by
  intro positive room root inside
  simp at inside

theorem headSB_no_shared_parent {d cut : Nat} {context : ParentContext}
    (history : List NumericalExpr) (a : List Nat) (hs : Forests (List Nat)) (rest : NumericalExpr)
    (distinct : cut < d → ∀ root, root < context.length →
      (Parents.label d context a).parents[cut]?.join ≠ Parents.parent context cut root) :
    HeadSB d cut context history a hs rest := by
  intro positive room root inside path same
  exact False.elim (distinct room root inside same)

theorem same_row_parent_reading {d cut root : Nat} {context : ParentContext}
    (a : List Nat) (inside : root < context.length) (room : cut < d)
    (unit : Parents.UnitSteps d (context ++ [Parents.label d context a]))
    (same : (Parents.label d context a).parents[cut]?.join = Parents.parent context cut root) :
    Parents.reading context cut root = a[cut]?.getD 0 := by
  have old := unit root (by simp; omega) cut room
  have current := unit context.length (by simp) cut room
  rw [← Parents.reading_prefix (List.prefix_append context [Parents.label d context a]) cut root inside,
    ← Parents.parent_prefix_eq (List.prefix_append context [Parents.label d context a]) cut root inside] at old
  rw [Parents.reading_append_label, Parents.append_label_parent, same] at current
  exact old.trans current.symm

theorem headSB_strict_row_max {d cut : Nat} {context : ParentContext}
    (history : List NumericalExpr) (a : List Nat) (hs : Forests (List Nat)) (rest : NumericalExpr)
    (unit : Parents.UnitSteps d (context ++ [Parents.label d context a]))
    (higher : cut < d → ∀ root, root < context.length →
      Parents.reading context cut root < a[cut]?.getD 0) :
    HeadSB d cut context history a hs rest := by
  apply headSB_no_shared_parent history a hs rest
  intro room root inside same
  have equal := same_row_parent_reading a inside room unit same
  have strict := higher room root inside
  omega

theorem diagonalTail_SB (d cut depth level : Nat) (context : ParentContext)
    (history : List NumericalExpr)
    (higher : ∀ root, root < context.length → ∀ row, row < d →
      Parents.reading context row root < level)
    (legal : FiniteLegal d context (diagonalTail d depth level)) :
    SB d cut context history (diagonalTail d depth level) := by
  induction depth generalizing context history level with
  | zero => trivial
  | succ depth ih =>
    let a := List.replicate d level
    let next := context ++ [Parents.label d context a]
    have newHigher : ∀ root, root < next.length → ∀ row, row < d →
        Parents.reading next row root < level + 1 := by
      intro root inside row room
      by_cases before : root < context.length
      · have prior := higher root before row room
        rw [← Parents.reading_prefix (List.prefix_append context [Parents.label d context a]) row root before]
        omega
      · have last : root = context.length := by simp only [next, List.length_append, List.length_cons, List.length_nil] at inside; omega
        subst root
        rw [Parents.reading_append_label]
        simp only [a, List.getElem?_replicate, if_pos room, Option.getD_some]
        omega
    refine ⟨headSB_strict_row_max history a _ _ legal.2.1 ?_, ?_, trivial⟩
    · intro room root inside
      simpa only [a, List.getElem?_replicate, if_pos room, Option.getD_some] using higher root inside cut room
    · exact ⟨ih (level + 1) next _ newHigher legal.2.2.2.1.2.1, trivial⟩

theorem seed_SB (d cut depth : Nat) (positive : 0 < d) :
    SB d cut [] [] (seed d depth) := by
  have legal := seed_finiteLegal d depth positive
  refine ⟨headSB_empty_context d cut [] _ _ _, trivial, ?_⟩
  apply diagonalTail_SB d cut depth 1 _ _ ?_ legal.2.2.2.2
  intro root inside row room
  have first : root = 0 := by simpa using inside
  subst root
  simp [Parents.reading, Parents.label, room]

end BTnSSBMS.Source
