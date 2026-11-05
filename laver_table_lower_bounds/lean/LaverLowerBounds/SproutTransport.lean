import LaverLowerBounds.LiveCoverBirth

set_option autoImplicit false

namespace LaverLowerBounds.ParentBMS

def CopyFrame.advance : Nat → CopyFrame → CopyFrame
  | 0, f => f
  | n + 1, f => advance n f.next

def CopyFrame.initialLiveCover (f : CopyFrame) : LiveCover f f.toSproutState where
  coverage := {
    column := id
    bounded := by intro i hi; rw [f.toSproutState_base]; exact hi
    strict := fun _ _ hij _ => hij
    edge := by intro q p i hp; rw [f.toSproutState_base]; exact .direct hp
    last := by intro _; rw [f.toSproutState_base]; rfl }
  width_eq := by simp [CopyFrame.toSproutState, CopyFrame.width]
  block_map i _ := by
    simp only [CopyFrame.toSproutState, List.length_take_of_le (Nat.le_of_lt f.root_lt), id_eq]
  template_eq := by simp [CopyFrame.toSproutState]

theorem mixed_run_graph {s t : Matrix} {n : Nat}
    (h : PrefixDescent.MixedRun (fun a => expand a 1) s t n) (hl : Leftward s) (hn : Nested s) :
    Leftward t ∧ Nested t := by
  induction h with
  | refl s => exact ⟨hl, hn⟩
  | step _ hp _ ih =>
      have hh := expand_graph hl hn
      exact ih (leftward_prefix hp hh.1) (nested_prefix hp hh.1 hh.2)

theorem SproutTrace.cover {s target : SproutState} {ranks : List Nat} {steps births : Nat}
    (h : SproutTrace s ranks target steps births) {f : CopyFrame} (hc : LiveCover f s)
    (hl : Leftward (s.full ranks)) (hn : Nested (s.full ranks)) :
    Nonempty (Cover (f.advance births).stem target.base) := by
  induction h generalizing f with
  | done s => exact ⟨hc.coverage⟩
  | @split s rest k target steps births _ ih =>
      have hg := expand_graph hl hn
      rw [s.split_step] at hg
      exact ih hc hg.1 hg.2
  | @birth s rest target steps births _ ih =>
      have hg := expand_graph hl hn
      rw [s.birth_step] at hg
      exact ih (hc.next rest hl hn) hg.1 hg.2

theorem append_leaves_graph {s : Matrix} {root : Nat} (hr : root < s.length)
    (hl : Leftward s) (hn : Nested s) (n : Nat) :
    Leftward (s ++ List.replicate n [root]) ∧ Nested (s ++ List.replicate n [root]) := by
  have leaf_parent {q i p : Nat} (hi : s.length ≤ i)
      (hp : parent (s ++ List.replicate n [root]) q i = some p) : q = 0 ∧ p = root := by
    rw [parent, List.getElem?_append_right hi] at hp
    cases he : (List.replicate n [root])[i - s.length]? with
    | none => simp [he] at hp
    | some c =>
        have hc : c = [root] := List.eq_of_mem_replicate (List.mem_of_getElem? he)
        subst c
        simp only [he, Option.bind_some] at hp
        cases q with
        | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hp; exact ⟨rfl, hp.symm⟩
        | succ q => simp at hp
  constructor
  · intro q i p hp
    by_cases hi : i < s.length
    · rw [parent_append_left hi] at hp
      exact hl q i p hp
    · obtain ⟨_, rfl⟩ := leaf_parent (by omega) hp
      omega
  · intro q i p hp
    by_cases hi : i < s.length
    · rw [parent_append_left hi] at hp
      exact (hn q i p hp).to_prefix_extension ⟨List.replicate n [root], rfl⟩
    · have hh := (leaf_parent (by omega) hp).1
      omega

theorem CopyFrame.sprout_graph (f : CopyFrame) (x : Nat) :
    Leftward (sprout f.stem f.last x) ∧ Nested (sprout f.stem f.last x) :=
  append_leaves_graph (by simp) f.leftward f.nested x

theorem CopyFrame.sprout_state_eq (f : CopyFrame) (x : Nat) :
    f.toSproutState.full [x] = sprout f.stem f.last x := by
  rw [SproutState.full_cons, SproutState.full_nil, f.toSproutState_base]
  rfl

/-- Binary sprout processing generates 2^x complete source copies, even with
arbitrarily many frozen columns between the actual target blocks. -/
theorem CopyFrame.sprout_transport (f : CopyFrame) (x : Nat) :
    ∃ target : SproutState,
      PrefixDescent.MixedRun (fun a => expand a 1) (sprout f.stem f.last x) target.base
        (2 ^ (x + 1) - 1) ∧
      Nonempty (Cover (f.advance (2 ^ x)).stem target.base) ∧
      Leftward target.base ∧ Nested target.base := by
  obtain ⟨target, ht⟩ := sprout_run f.toSproutState [x]
  have hg := f.sprout_graph x
  have hinitial : Leftward (f.toSproutState.full [x]) ∧ Nested (f.toSproutState.full [x]) := by
    rw [f.sprout_state_eq]
    exact hg
  have hc := ht.cover f.initialLiveCover hinitial.1 hinitial.2
  have hr := ht.mixedRun
  rw [f.sprout_state_eq] at hr
  simp only [forestSteps, forestBirths, Nat.add_zero] at hr hc
  have hfinal := mixed_run_graph hr hg.1 hg.2
  exact ⟨target, hr, hc, hfinal.1, hfinal.2⟩

theorem CopyFrame.sprout_budget {f : CopyFrame} {x n : Nat}
    (ht : PrefixDescent.Stops (fun s => expand s 1) (sprout f.stem f.last x) n) :
    ∃ k, PrefixDescent.Stops (fun s => expand s 1) (f.advance (2 ^ x)).stem k ∧
      (2 ^ (x + 1) - 1) + k ≤ n := by
  obtain ⟨target, hr, ⟨hc⟩, hl, hn⟩ := f.sprout_transport x
  obtain ⟨remaining, hremaining, hbudget⟩ := PrefixDescent.mixed_run_budget (expand_preserves_stem 1) hr ht
  let source := f.advance (2 ^ x)
  obtain ⟨k, hk, hkr⟩ := hc.stops hremaining
    (leftward_prefix ⟨[source.last], rfl⟩ source.leftward)
    (nested_prefix ⟨[source.last], rfl⟩ source.leftward source.nested) hl hn
  exact ⟨k, hk, by omega⟩

#print axioms CopyFrame.sprout_transport
#print axioms CopyFrame.sprout_budget

end LaverLowerBounds.ParentBMS
