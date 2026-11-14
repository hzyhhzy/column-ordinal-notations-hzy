import BTnSSBMS.ClosedForestTransplant

/-!
A canonical finite numerical transport. It reconstructs each coordinate
as zero, or the represented parent's coordinate plus one. This is an
auxiliary description of existing copies, not a new expansion rule.
The literal activation-and-shift copy is proved equal to it below.
-/
namespace BTnSSBMS.Source

def relocationHead (d : Nat) (source target : ParentContext) (visible : List Nat)
    (a : List Nat) : List Nat :=
  (List.range d).map (Parents.representedValue target visible (Parents.label d source a))

mutual
  def relocate (d : Nat) (source target : ParentContext) (visible : List Nat) :
      NumericalExpr → NumericalExpr
    | .nil => .nil
    | .cons a hs tail =>
      let b := relocationHead d source target visible a
      let nextSource := source ++ [Parents.label d source a]
      let nextTarget := target ++ [Parents.label d target b]
      let nextVisible := visible ++ [target.length]
      .cons b (relocateForests d nextSource nextTarget nextVisible hs)
        (relocate d nextSource nextTarget nextVisible tail)
  def relocateForests (d : Nat) (source target : ParentContext) (visible : List Nat) :
      Forests (List Nat) → Forests (List Nat)
    | .nil => .nil
    | .cons h hs => .cons (relocate d source target visible h) (relocateForests d source target visible hs)
end

theorem relocationHead_width (d : Nat) (source target : ParentContext) (visible a : List Nat) :
    (relocationHead d source target visible a).length = d := by
  simp only [relocationHead, List.length_map, List.length_range]

theorem relocationHead_value (d : Nat) (source target : ParentContext) (visible a : List Nat)
    {j : Nat} (room : j < d) :
    (relocationHead d source target visible a)[j]?.getD 0 =
      Parents.representedValue target visible (Parents.label d source a) j := by
  simp only [relocationHead, List.getElem?_map, List.getElem?_range room, Option.map_some, Option.getD_some]

theorem relocationHead_parents {d : Nat} {source target : ParentContext} {visible : List Nat}
    (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (view : Parents.NumericalView d source target visible) (a : List Nat) (j : Nat) (room : j < d) :
    (Parents.label d target (relocationHead d source target visible a)).parents[j]?.join =
      ((Parents.label d source a).parents[j]?.join).map (Parents.point visible) :=
  Parents.label_parent_transport sourceCoherent sourceValid targetCoherent targetValid (Nat.le_refl d)
    view a _ (fun _ inside => relocationHead_value d source target visible a inside) j room

theorem relocation_view_append {d : Nat} {source target : ParentContext} {visible : List Nat}
    (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (view : Parents.NumericalView d source target visible) (a : List Nat) :
    Parents.NumericalView d (source ++ [Parents.label d source a])
      (target ++ [Parents.label d target (relocationHead d source target visible a)])
      (visible ++ [target.length]) :=
  view.append _ _ (Parents.context_valid_append_label d source sourceValid a)
    (relocationHead_parents sourceCoherent sourceValid targetCoherent targetValid view a)

theorem relocationHead_eq_shift {d : Nat} {source target : ParentContext} {visible history : List Nat}
    {root cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d source target visible history root cap delta phase)
    (a : List Nat) (width : a.length = d)
    (unit : Parents.UnitSteps d (source ++ [Parents.label d source a])) :
    relocationHead d source target visible a =
      shift a (Keys.threshold cap root history (Parents.label d source a)) delta phase := by
  apply List.ext_getElem
  · simp only [relocationHead_width, shift_width, width]
  · intro j left right
    have room : j < d := by simpa only [relocationHead_width] using left
    have value := (relocationHead_value d source target visible a room).trans
      (scope.head_values a width unit j room).symm
    simpa only [List.getElem?_eq_getElem left, List.getElem?_eq_getElem right, Option.getD_some] using value

mutual
  theorem relocate_eq_copied {d : Nat} {source target : ParentContext} {visible history : List Nat}
      {root cap : Nat} {delta : List Nat} {phase : Nat}
      (scope : ShiftView d source target visible history root cap delta phase)
      (e : NumericalExpr) (legal : FiniteLegal d source e) :
      relocate d source target visible e = copied d root cap delta phase source history e := by
    cases e with
    | nil => rfl
    | cons a hs tail =>
      have head := relocationHead_eq_shift scope a legal.1 legal.2.1
      have next := scope.append a legal.1 legal.2.1
      have inside := relocateForests_eq_copied next (a[0]?.getD 0) hs legal.2.2.2.1
      have after := relocate_eq_copied next tail legal.2.2.2.2
      rw [relocate, head, copied_cons d root cap delta phase source history
        (by rw [scope.historyLength]; exact scope.afterRoot), inside, after]

  theorem relocateForests_eq_copied {d : Nat} {source target : ParentContext} {visible history : List Nat}
      {root cap : Nat} {delta : List Nat} {phase : Nat}
      (scope : ShiftView d source target visible history root cap delta phase)
      (owner : Nat) (hs : Forests (List Nat)) (legal : FiniteLegalForests d source owner hs) :
      relocateForests d source target visible hs = copiedForests d root cap delta phase source history hs := by
    cases hs with
    | nil => rfl
    | cons h hs =>
      simp only [relocateForests, copiedForests_cons,
        relocate_eq_copied scope h legal.2.1, relocateForests_eq_copied scope owner hs legal.2.2]
end

theorem transplantedForests_eq_relocate {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context) (positive : 0 < d)
    (position : List Nat)
    (positionUnit : Parents.UnitSteps d (context ++ [Parents.label d context position]))
    {root : Nat} (insideRoot : root < context.length)
    (path : Parents.Ancestor (context ++ [Parents.label d context position]) (d - 1) root context.length)
    (hs : Forests (List Nat))
    (legal : FiniteLegalForests d (context.take (root + 1)) (Parents.reading context 0 root) hs) :
    transplantedForests d context root position hs =
      relocateForests d (context.take (root + 1)) (context ++ [Parents.label d context position])
        (List.range root ++ [context.length]) hs :=
  (relocateForests_eq_copied (transplant_shiftView coherent valid positive position positionUnit insideRoot path)
    (Parents.reading context 0 root) hs legal).symm

end BTnSSBMS.Source
