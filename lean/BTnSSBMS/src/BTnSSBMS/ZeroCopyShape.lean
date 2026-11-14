import BTnSSBMS.BNSplice

/-! With an empty difference vector the frozen zero-class iteration
is literal repetition of the pruned outer template. Its complete first
block, not just its first numerical vector, is independent of the count. -/
namespace BTnSSBMS.Source

theorem holeSite_zero_data {d : Nat} {context : ParentContext} {owner : Option Nat}
    (e : NumericalExpr) {site : HoleSite} (found : holeSite d context owner 0 e = some site) :
    site.context = outerContext d context (dropLast e) ∧ last? e = some (site.terminal, site.attached) := by
  cases e with
  | nil => simp [holeSite] at found
  | cons a hs rest =>
    cases rest with
    | nil =>
      rw [holeSite] at found
      have same := Option.some.inj found
      cases same
      simp only [dropLast, outerContext, last?, and_self]
    | cons b ks tail =>
      rw [holeSite] at found
      have next := holeSite_zero_data (.cons b ks tail) found
      simpa only [dropLast, outerContext, last?] using next

theorem shift_empty (a : List Nat) (threshold phase : Nat) : shift a threshold [] phase = a := by
  simp [shift]
  rw [List.mapIdx_eq_iff]
  intro i
  simp

theorem copied_empty (d root cap phase : Nat) (context : ParentContext) (history : List Nat)
    (e : NumericalExpr) : copied d root cap [] phase context history e = e := by
  simp only [copied, shift_empty, mark_erase, Parents.annotate_erase]

theorem zero_copies_succ (part : MarkedExpr) (count phase : Nat) :
    copies part 0 [] none (count + 1) phase =
      splice 0 (copies part 0 [] none count (phase + 1)) (part.map Prod.fst) := by
  rw [copies, ascendReplace_splice]
  simp only [shift_empty]

theorem takeAbove_splice_zero_high (e replacement : NumericalExpr) (floor : Nat)
    (above : ∀ a ∈ labels e, floor < a[0]?.getD 0)
    (cut : takeAbove floor replacement = .nil) :
    takeAbove floor (splice 0 replacement e) = dropLast e := by
  cases e with
  | nil => simp only [splice, takeAbove, dropLast]
  | cons a hs rest =>
    cases rest with
    | nil => simp only [splice, cut, dropLast]
    | cons b ks tail =>
      rw [splice, takeAbove, if_pos (above a (by simp [labels])), dropLast]
      exact congrArg (Expr.cons a hs) (takeAbove_splice_zero_high (.cons b ks tail) replacement floor
        (fun col member => above col (List.mem_cons_of_mem a member)) cut)

theorem rootBlock_splice_zero_high {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr}
    (nonempty : rest ≠ .nil) (above : ∀ b ∈ labels rest, a[0]?.getD 0 < b[0]?.getD 0)
    (replacement : NumericalExpr) (cut : takeAbove (a[0]?.getD 0) replacement = .nil) :
    rootBlock (splice 0 replacement (.cons a hs rest)) = dropLast (.cons a hs rest) := by
  rw [splice_cons_tail 0 replacement a hs rest nonempty, rootBlock,
    takeAbove_splice_zero_high rest replacement _ above cut]
  cases rest with
  | nil => exact False.elim (nonempty rfl)
  | cons b ks tail => rw [dropLast]

theorem zero_copies_cut {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr}
    {part : MarkedExpr} (erase : part.map Prod.fst = .cons a hs rest)
    (nonempty : rest ≠ .nil) (count phase : Nat) :
    takeAbove (a[0]?.getD 0) (copies part 0 [] none count phase) = .nil := by
  cases count with
  | zero => simp only [copies, takeAbove]
  | succ count =>
    rw [zero_copies_succ, erase, splice_cons_tail 0 _ a hs rest nonempty,
      takeAbove, if_neg (Nat.lt_irrefl _)]

theorem zero_copies_rootBlock {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr}
    {part : MarkedExpr} (erase : part.map Prod.fst = .cons a hs rest)
    (nonempty : rest ≠ .nil) (above : ∀ b ∈ labels rest, a[0]?.getD 0 < b[0]?.getD 0)
    (count phase : Nat) :
    rootBlock (copies part 0 [] none (count + 1) phase) = dropLast (.cons a hs rest) := by
  rw [zero_copies_succ, erase]
  exact rootBlock_splice_zero_high nonempty above _ (zero_copies_cut erase nonempty count (phase + 1))

end BTnSSBMS.Source
