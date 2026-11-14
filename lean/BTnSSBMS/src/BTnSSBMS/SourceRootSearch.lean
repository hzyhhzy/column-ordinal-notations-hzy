import BTnSSBMS.DonationIteration

/-!
Soundness of the actual highest-key search and highest-parent selector.
These finite facts are independent of source standardness. The scoped
owner list still has to be connected to the extracted right-spine piece.
-/
namespace BTnSSBMS.Source

theorem topSearch_sound (d : Nat) (context : KeyContext) (owners : List Nat)
    (key : Key) (cursor root : Nat) (found : topSearch d context owners key cursor = some root) :
    root < cursor ∧ ∃ a k, context[root]? = some (a, k) ∧ owners.contains root = false ∧
      Keys.compare k key = .lt ∧
      Parents.Ancestor (context.map Prod.fst) (d - 1) root (cursor - 1) := by
  induction cursor using Nat.strongRecOn with
  | ind cursor ih =>
    cases cursor with
    | zero => simp [topSearch] at found
    | succ position =>
      rw [topSearch] at found
      cases lookup : context[position]? with
      | none => simp [lookup] at found
      | some entry =>
        obtain ⟨a, k⟩ := entry
        simp only [lookup] at found
        by_cases hit : (!owners.contains position && Keys.compare k key == .lt) = true
        · simp only [hit, if_true, Option.some.injEq] at found
          subst root
          have components := Bool.and_eq_true_iff.mp hit
          refine ⟨by omega, a, k, lookup, ?_, ?_, ?_⟩
          · cases ownerCase : owners.contains position <;> simp_all
          · simpa only [beq_iff_eq] using components.2
          · simpa only [Nat.add_sub_cancel] using
              (Parents.Ancestor.refl position : Parents.Ancestor (context.map Prod.fst) (d - 1) position position)
        · simp only [hit] at found
          cases parent : a.parents[d - 1]?.join with
          | none => simp [parent] at found
          | some p =>
            by_cases earlier : p < position
            · simp only [parent, earlier, if_true] at found
              obtain ⟨before, b, h, atRoot, unowned, smaller, path⟩ := ih (p + 1) (by omega) found
              refine ⟨by omega, b, h, atRoot, unowned, smaller, ?_⟩
              have edge : Parents.parent (context.map Prod.fst) (d - 1) position = some p := by
                simp only [Parents.parent, List.getElem?_map, lookup, Option.map_some, Option.bind_some, parent]
              simpa only [Nat.add_sub_cancel] using
                (Parents.Ancestor.up edge (by simpa only [Nat.add_sub_cancel] using path))
            · simp [parent, earlier] at found

/-- Attach the successful search path to the terminal's actual highest
numerical parent. Appended key-parent fields do not interfere with this
path, which uses only row d-1. -/
theorem topSearch_parent_sound (d : Nat) (context : KeyContext) (owners : List Nat)
    (key : Key) (terminal : ParentLabel) (parent root : Nat)
    (input : terminal.parents[d - 1]?.join = some parent) (inside : parent < context.length)
    (found : topSearch d context owners key
      ((terminal.parents[d - 1]?.join).map (· + 1) |>.getD 0) = some root) :
    root < context.length ∧ owners.contains root = false ∧
      Parents.Ancestor (context.map Prod.fst ++ [terminal]) (d - 1) root context.length := by
  rw [input, Option.map_some, Option.getD_some] at found
  obtain ⟨before, a, k, _, unowned, _, path⟩ := topSearch_sound d context owners key (parent + 1) root found
  refine ⟨by omega, unowned, ?_⟩
  have edge : Parents.parent (context.map Prod.fst ++ [terminal]) (d - 1) context.length = some parent := by
    simp only [Parents.parent, List.getElem?_append_right
      (show (context.map Prod.fst).length ≤ context.length by simp), List.length_map, Nat.sub_self,
      List.getElem?_cons_zero, Option.bind_some, input]
  exact .up edge ((by simpa only [Nat.add_sub_cancel] using path :
    Parents.Ancestor (context.map Prod.fst) (d - 1) root parent).prefix (List.prefix_append ..))

theorem highestParent_found (parents : List (Option Nat)) (offset branch root : Nat)
    (found : highestParent offset parents = some (branch, root)) :
    offset ≤ branch ∧ branch < offset + parents.length ∧ parents[branch - offset]? = some (some root) := by
  induction parents generalizing offset with
  | nil => simp [highestParent] at found
  | cons p ps ih =>
    rw [highestParent] at found
    cases next : highestParent (offset + 1) ps with
    | none =>
      simp only [next] at found
      cases p with
      | none => simp at found
      | some q =>
        have equal : (offset, q) = (branch, root) := by simpa only [Option.map_some, Option.some.injEq] using found
        have first := congrArg Prod.fst equal
        have second := congrArg Prod.snd equal
        dsimp only at first second
        subst branch
        subst root
        exact ⟨Nat.le_refl _, by simp, by simp⟩
    | some pair =>
      have equal : pair = (branch, root) := by simpa only [next, Option.some.injEq] using found
      subst pair
      obtain ⟨lower, upper, selected⟩ := ih (offset + 1) next
      refine ⟨by omega, by simp only [List.length_cons]; omega, ?_⟩
      have index : branch - offset = (branch - (offset + 1)) + 1 := by omega
      rw [index, List.getElem?_cons_succ]
      exact selected

theorem highestParent_none_iff (parents : List (Option Nat)) (offset : Nat) :
    highestParent offset parents = none ↔ ∀ p ∈ parents, p = none := by
  induction parents generalizing offset with
  | nil => simp [highestParent]
  | cons p ps ih =>
    rw [highestParent]
    cases next : highestParent (offset + 1) ps with
    | none =>
      have rest := (ih (offset + 1)).mp next
      cases p with
      | none =>
        constructor
        · intro _ q member
          simp only [List.mem_cons] at member
          exact member.elim id (rest q)
        · intro _; rfl
      | some q => simp
    | some result =>
      constructor
      · intro impossible; cases impossible
      · intro all
        have empty := (ih (offset + 1)).mpr (fun q member => all q (List.mem_cons_of_mem p member))
        rw [next] at empty
        cases empty

theorem highestParent_numerical_or_top (d : Nat) (parents : List (Option Nat))
    (top : Option Nat) (branch root : Nat) (width : parents.length = d)
    (found : highestParent 0 (parents ++ [top]) = some (branch, root)) :
    (branch < d ∧ parents[branch]? = some (some root)) ∨ (branch = d ∧ top = some root) := by
  obtain ⟨_, bound, selected⟩ := highestParent_found (parents ++ [top]) 0 branch root found
  simp only [Nat.zero_add, List.length_append, width, List.length_cons, List.length_nil] at bound
  simp only [Nat.sub_zero] at selected
  by_cases low : branch < d
  · left
    exact ⟨low, by simpa only [List.getElem?_append_left (by omega : branch < parents.length)] using selected⟩
  · right
    have same : branch = d := by omega
    refine ⟨same, ?_⟩
    rw [same, ← width, List.getElem?_concat_length] at selected
    exact Option.some.inj selected

end BTnSSBMS.Source
