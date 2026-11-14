import BTnSSBMS.SourceLegality
import BTnSSBMS.SourceHead

/-!
Finite legality under actual deletion and special forest replication.
Each replicated forest is checked in the original owner context, never
in the output context of a previous replica.
-/
namespace BTnSSBMS.Source

theorem last_none_iff (e : Expr α) : last? e = none ↔ e = .nil := by
  cases e with
  | nil => simp [last?]
  | cons a hs t =>
    cases t with
    | nil => simp [last?]
    | cons b ks u => simpa [last?] using last_none_iff (.cons b ks u)

theorem lastForest_none_iff (hs : Forests α) : lastForest? hs = none ↔ hs = .nil := by
  cases hs with
  | nil => simp [lastForest?]
  | cons h rest =>
    cases rest with
    | nil => simp [lastForest?]
    | cons k ks =>
      simpa [lastForest?] using lastForest_none_iff (.cons k ks)

theorem labels_dropLast_subset (e : Expr α) : ∀ a ∈ labels (dropLast e), a ∈ labels e := by
  cases e with
  | nil => simp [dropLast, labels]
  | cons a hs t =>
    cases t with
    | nil => simp [dropLast, labels]
    | cons b ks u =>
      intro x member
      simp only [dropLast, labels, List.mem_cons] at member ⊢
      exact member.elim Or.inl (fun later => Or.inr
        (by simpa only [labels, List.mem_cons] using labels_dropLast_subset (.cons b ks u) x later))

theorem FiniteLegal.dropLast {d : Nat} {context : ParentContext} {e : NumericalExpr}
    (legal : FiniteLegal d context e) : FiniteLegal d context (Source.dropLast e) := by
  cases e with
  | nil => simp [Source.dropLast, FiniteLegal]
  | cons a hs t =>
    cases t with
    | nil => simp [Source.dropLast, FiniteLegal]
    | cons b ks u =>
      simp only [Source.dropLast, FiniteLegal]
      exact ⟨legal.1, legal.2.1, legal.2.2.1, legal.2.2.2.1, legal.2.2.2.2.dropLast⟩

theorem FiniteLegalForests.dropLast {d : Nat} {context : ParentContext} {owner : Nat}
    {hs : Forests (List Nat)} (legal : FiniteLegalForests d context owner hs) :
    FiniteLegalForests d context owner (dropLastForest hs) := by
  cases hs with
  | nil => simp [dropLastForest, FiniteLegalForests]
  | cons h rest =>
    cases rest with
    | nil => simp [dropLastForest, FiniteLegalForests]
    | cons k ks =>
      simp only [dropLastForest, FiniteLegalForests]
      exact ⟨legal.1, legal.2.1, legal.2.2.dropLast⟩

theorem FiniteLegalForests.last {d : Nat} {context : ParentContext} {owner : Nat}
    {hs : Forests (List Nat)} (legal : FiniteLegalForests d context owner hs)
    {h : NumericalExpr} (selected : lastForest? hs = some h) :
    (∀ a ∈ labels h, owner < a[0]?.getD 0) ∧ FiniteLegal d context h := by
  cases hs with
  | nil => simp [lastForest?] at selected
  | cons first rest =>
    cases rest with
    | nil =>
      have same : first = h := by simpa [lastForest?] using selected
      subst h
      exact ⟨legal.1, legal.2.1⟩
    | cons k ks => exact legal.2.2.last (by simpa only [lastForest?] using selected)

theorem FiniteLegalForests.append {d : Nat} {context : ParentContext} {owner : Nat}
    {hs ks : Forests (List Nat)} (left : FiniteLegalForests d context owner hs)
    (right : FiniteLegalForests d context owner ks) :
    FiniteLegalForests d context owner (appendForests hs ks) := by
  cases hs with
  | nil => exact right
  | cons h rest => exact ⟨left.1, left.2.1, left.2.2.append right⟩

theorem repeatForest_finiteLegal {d : Nat} {context : ParentContext} {owner : Nat}
    {h : NumericalExpr} (above : ∀ a ∈ labels h, owner < a[0]?.getD 0)
    (legal : FiniteLegal d context h) (count : Nat) :
    FiniteLegalForests d context owner (repeatForest h count) := by
  induction count with
  | zero => trivial
  | succ count ih => exact ⟨above, legal, ih⟩

theorem FiniteLegal.modifyLast {d : Nat} {context : ParentContext} {e : NumericalExpr}
    (legal : FiniteLegal d context e)
    (f : List Nat × Forests (List Nat) → List Nat × Forests (List Nat))
    (preserves : ∀ ctx a hs, last? e = some (a, hs) →
      FiniteLegal d ctx (.cons a hs .nil) →
      FiniteLegal d ctx (.cons (f (a, hs)).1 (f (a, hs)).2 .nil)) :
    FiniteLegal d context (Source.modifyLast f e) := by
  cases e with
  | nil => simp [Source.modifyLast, FiniteLegal]
  | cons a hs t =>
    cases t with
    | nil =>
      simp only [Source.modifyLast]
      exact preserves context a hs (by simp [last?]) legal
    | cons b ks u =>
      simp only [Source.modifyLast, FiniteLegal]
      exact ⟨legal.1, legal.2.1, legal.2.2.1, legal.2.2.2.1,
        legal.2.2.2.2.modifyLast f (fun ctx c js selected finite =>
          preserves ctx c js (by simpa only [last?] using selected) finite)⟩

theorem FiniteLegalForests.modifyLast {d : Nat} {context : ParentContext} {owner : Nat}
    {hs : Forests (List Nat)} (legal : FiniteLegalForests d context owner hs)
    (f : NumericalExpr → NumericalExpr)
    (keepsLabels : ∀ h a, a ∈ labels (f h) → a ∈ labels h)
    (preserves : ∀ h, lastForest? hs = some h → FiniteLegal d context h → FiniteLegal d context (f h)) :
    FiniteLegalForests d context owner (modifyLastForest f hs) := by
  cases hs with
  | nil => simp [modifyLastForest, FiniteLegalForests]
  | cons h rest =>
    cases rest with
    | nil =>
      simp only [modifyLastForest, FiniteLegalForests]
      exact ⟨fun a member => legal.1 a (keepsLabels h a member),
        preserves h (by simp [lastForest?]) legal.2.1, trivial⟩
    | cons k ks =>
      simp only [modifyLastForest, FiniteLegalForests]
      exact ⟨legal.1, legal.2.1, legal.2.2.modifyLast f keepsLabels
        (fun x selected finite => preserves x (by simpa only [lastForest?] using selected) finite)⟩

theorem labels_modifyLast_forests (f : List Nat → Forests (List Nat) → Forests (List Nat))
    (e : NumericalExpr) :
    labels (modifyLast (fun x => (x.1, f x.1 x.2)) e) = labels e := by
  cases e with
  | nil => simp [modifyLast, labels]
  | cons a hs t =>
    cases t with
    | nil => simp [modifyLast, labels]
    | cons b ks u => simp only [modifyLast, labels, labels_modifyLast_forests f (.cons b ks u)]

theorem special_labels (index depth : Nat) (e : NumericalExpr) :
    labels (special index depth e) = labels e := by
  cases depth with
  | zero =>
    simp only [special]
    exact labels_modifyLast_forests
      (fun _ hs => appendForests (dropLastForest hs) (repeatForest (dropLast (lastForest? hs |>.getD .nil)) index)) e
  | succ depth =>
    simp only [special]
    exact labels_modifyLast_forests (fun _ hs => modifyLastForest (special index depth) hs) e

/-- There is an attached list at the selected last-spine depth. This is
weaker than the actual special-column test; it only excludes creating a
new attachment on a leaf through a malformed call to `special`. -/
def AttachmentAt : Nat → NumericalExpr → Prop
  | 0, e => ∃ a hs, last? e = some (a, hs) ∧ hs ≠ .nil
  | depth + 1, e => ∃ a hs h, last? e = some (a, hs) ∧
      lastForest? hs = some h ∧ AttachmentAt depth h

theorem special_finiteLegal (index depth : Nat) {d : Nat} {context : ParentContext}
    {e : NumericalExpr} (legal : FiniteLegal d context e) (attached : AttachmentAt depth e) :
    FiniteLegal d context (special index depth e) := by
  induction depth generalizing context e with
  | zero =>
    simp only [special]
    apply legal.modifyLast
    intro ctx a hs selected finite
    obtain ⟨b, ks, atLast, nonempty⟩ := attached
    have same : (b, ks) = (a, hs) := Option.some.inj (atLast.symm.trans selected)
    cases same
    have existsLast : ∃ h, lastForest? hs = some h := by
      cases found : lastForest? hs with
      | none => exact False.elim (nonempty ((lastForest_none_iff hs).mp found))
      | some h => exact ⟨h, rfl⟩
    obtain ⟨h, found⟩ := existsLast
    obtain ⟨above, hLegal⟩ := finite.2.2.2.1.last found
    refine ⟨finite.1, finite.2.1, fun _ => finite.2.2.1 nonempty, ?_, trivial⟩
    apply finite.2.2.2.1.dropLast.append
    simp only [found, Option.getD_some]
    exact repeatForest_finiteLegal (fun a member => above a (labels_dropLast_subset h a member)) hLegal.dropLast index
  | succ depth ih =>
    simp only [special]
    apply legal.modifyLast
    intro ctx a hs selected finite
    obtain ⟨b, ks, h, atLast, found, eligible⟩ := attached
    have same : (b, ks) = (a, hs) := Option.some.inj (atLast.symm.trans selected)
    cases same
    have nonempty : hs ≠ .nil := by intro empty; simp [empty, lastForest?] at found
    refine ⟨finite.1, finite.2.1, fun _ => finite.2.2.1 nonempty, ?_, trivial⟩
    apply finite.2.2.2.1.modifyLast (special index depth)
      (fun x a member => by simpa only [special_labels] using member)
    intro x atX xLegal
    have same : h = x := Option.some.inj (found.symm.trans atX)
    subst x
    exact ih xLegal eligible

theorem forestSpine_last (hs : Forests α) :
    forestSpine hs = ((lastForest? hs).map spine).getD [] := by
  cases hs with
  | nil => simp [forestSpine, lastForest?]
  | cons h rest =>
    cases rest with
    | nil => simp [forestSpine, lastForest?, spine]
    | cons k ks => simpa only [forestSpine, lastForest?] using forestSpine_last (.cons k ks)

def lastChild? (e : Expr α) : Option (Expr α) :=
  (last? e).bind fun c => lastForest? c.2

theorem innerSpine_last (e : Expr α) : innerSpine e = ((lastChild? e).map spine).getD [] := by
  cases e with
  | nil => simp [innerSpine, lastChild?, last?]
  | cons a hs t =>
    cases t with
    | nil => simp [innerSpine, lastChild?, last?, forestSpine_last]
    | cons b ks u => simpa only [innerSpine, lastChild?, last?] using innerSpine_last (.cons b ks u)

theorem spine_get_succ (e : Expr α) (depth : Nat) :
    (spine e)[depth + 1]? = (lastChild? e).bind (fun h => (spine h)[depth]?) := by
  change (innerSpine e)[depth]? = (lastChild? e).bind (fun h => (spine h)[depth]?)
  rw [innerSpine_last]
  cases lastChild? e <;> rfl

theorem AttachmentAt.of_spine {depth : Nat} {e stop : NumericalExpr}
    (selected : (spine e)[depth]? = some stop) {a : List Nat} {hs : Forests (List Nat)}
    (atLast : last? stop = some (a, hs)) (nonempty : hs ≠ .nil) : AttachmentAt depth e := by
  induction depth generalizing e with
  | zero =>
    have same : e = stop := by simpa only [spine, List.getElem?_cons_zero, Option.some.injEq] using selected
    subst e
    exact ⟨a, hs, atLast, nonempty⟩
  | succ depth ih =>
    rw [spine_get_succ] at selected
    obtain ⟨h, child, selected⟩ := Option.bind_eq_some_iff.mp selected
    obtain ⟨c, last, forest⟩ := Option.bind_eq_some_iff.mp child
    exact ⟨c.1, c.2, h, last, forest, ih selected⟩

theorem specialColumn_attached {a : List Nat} {hs : Forests (List Nat)}
    (special : specialColumn (a, hs) = true) : hs ≠ .nil := by
  intro empty
  simp [empty, specialColumn, lastForest?] at special

theorem special_spine_finiteLegal (index depth : Nat) {d : Nat} {context : ParentContext}
    {e stop : NumericalExpr} (legal : FiniteLegal d context e)
    (selected : (spine e)[depth]? = some stop) {c : List Nat × Forests (List Nat)}
    (atLast : last? stop = some c) (special : specialColumn c = true) :
    FiniteLegal d context (Source.special index depth e) :=
  special_finiteLegal index depth legal (AttachmentAt.of_spine selected atLast (specialColumn_attached special))

/-- Totality and legality for the actual zero-leaf branch, at every index. -/
theorem expand_zero_finiteLegal (d index : Nat) {context : ParentContext}
    {e : NumericalExpr} (legal : FiniteLegal d context e) {c : List Nat × Forests (List Nat)}
    (atLast : last? e = some c) (zero : zeroColumn c = true) :
    expand? d e index = some (dropLast e) ∧ FiniteLegal d context (dropLast e) := by
  exact ⟨by simp [expand?, atLast, zero], legal.dropLast⟩

/-- This uses the stopping layer selected by the actual algorithm, not
an externally supplied replacement of the fundamental-sequence rule. -/
theorem expand_special_finiteLegal (d index : Nat) {context : ParentContext}
    {e stop : NumericalExpr} (legal : FiniteLegal d context e)
    (selected : (spine e)[(spine e).findIdx stopping]? = some stop)
    {c : List Nat × Forests (List Nat)} (atStop : last? stop = some c)
    (special : specialColumn c = true) :
    ∃ f, expand? d e index = some f ∧ FiniteLegal d context f := by
  cases atLast : last? e with
  | none => exact ⟨.nil, by simp [expand?, atLast], trivial⟩
  | some last =>
    by_cases zero : zeroColumn last = true
    · exact ⟨dropLast e, expand_zero_finiteLegal d index legal atLast zero⟩
    · refine ⟨Source.special index ((spine e).findIdx stopping) e, ?_,
        special_spine_finiteLegal index _ legal selected atStop special⟩
      simp [expand?, atLast, zero, selected, atStop, special]

end BTnSSBMS.Source
