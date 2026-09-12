import OrdinalFormal.LRDStructure

/-!
# Well-foundedness of the actual LRD row comparison

This concerns row labels only, not the full LRD column-graph notation.
Raw polynomial presentations are allowed: comparison factors through trimming,
so distinct trailing-zero presentations cannot create strict descent.
-/

namespace OrdinalFormal.LRDRowWellFounded

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 4096

open LRD Columns

def SameLengthLex (as bs : List Nat) : Prop :=
  as.length = bs.length ∧ List.Lex (fun a b : Nat => a < b) as bs

theorem sameLengthLex_acc (n : Nat) :
    ∀ bs : List Nat, bs.length = n → Acc SameLengthLex bs := by
  induction n with
  | zero =>
      intro bs hb
      have he : bs = [] := by simpa using hb
      subst bs
      refine Acc.intro [] ?_
      intro as ha
      exact False.elim (List.not_lex_nil ha.2)
  | succ n ih =>
      have hcons : ∀ b : Nat, ∀ tail : List Nat, tail.length = n →
          Acc SameLengthLex (b :: tail) := by
        intro b
        induction b using Nat.lt_wfRel.wf.induction with
        | h b ihb =>
            intro tail hlen
            have ht := ih tail hlen
            revert hlen
            induction ht with
            | intro tail ht iht =>
                intro hlen
                refine Acc.intro (b :: tail) ?_
                intro as ha
                cases as with
                | nil => simp [SameLengthLex] at ha
                | cons a rest =>
                    have hl : rest.length = tail.length := by
                      have := ha.1
                      simpa using this
                    rcases List.cons_lex_cons_iff.mp ha.2 with hab | ⟨hab, hrest⟩
                    · exact ihb a hab rest (hl.trans hlen)
                    · subst a
                      exact iht rest ⟨hl, hrest⟩ (hl.trans hlen)
      intro bs hb
      cases bs with
      | nil => simp at hb
      | cons b tail => exact hcons b tail (by simpa using hb)

theorem sameLengthLex_wellFounded : WellFounded SameLengthLex :=
  ⟨fun bs => sameLengthLex_acc bs.length bs rfl⟩

def ShortLex (as bs : List Nat) : Prop :=
  as.length < bs.length ∨ SameLengthLex as bs

theorem shortLex_acc (n : Nat) :
    ∀ bs : List Nat, bs.length = n → Acc ShortLex bs := by
  induction n using Nat.lt_wfRel.wf.induction with
  | h n ihn =>
      intro bs hb
      have ha := sameLengthLex_wellFounded.apply bs
      revert hb
      induction ha with
      | intro bs _ ih =>
          intro hb
          refine Acc.intro bs ?_
          intro as h
          change as.length < bs.length ∨ SameLengthLex as bs at h
          rcases h with h | h
          · exact ihn as.length (hb ▸ h) as rfl
          · exact ih as h (h.1.trans hb)

theorem shortLex_wellFounded : WellFounded ShortLex :=
  ⟨fun bs => shortLex_acc bs.length bs rfl⟩

theorem poly_cmp_to_shortLex {as bs : List Nat}
    (h : Row.cmp (.poly as) (.poly bs) = .lt) :
    ShortLex (trim as).reverse (trim bs).reverse := by
  rcases (LRDStructure.poly_cmp_lt_iff as bs).mp h with h | ⟨hl, hc⟩
  · exact Or.inl (by simpa using h)
  · apply Or.inr
    refine ⟨by simpa using hl, ?_⟩
    have hx := (Comparison.listCompare_lt_iff_lex compare
      (fun _ _ => Nat.compare_eq_eq) _ _).mp hc
    simpa only [Nat.compare_eq_lt] using hx

theorem poly_cmp_wellFounded :
    WellFounded (fun as bs : List Nat => Row.cmp (.poly as) (.poly bs) = .lt) :=
  Subrelation.wf (fun h => poly_cmp_to_shortLex h)
    (InvImage.wf (fun cs => (trim cs).reverse) shortLex_wellFounded)

def RowLt (a b : Row) : Prop := Row.cmp a b = .lt

theorem poly_row_acc (cs : List Nat) : Acc RowLt (.poly cs) := by
  have h := poly_cmp_wellFounded.apply cs
  induction h with
  | intro cs _ ih =>
      refine Acc.intro (Row.poly cs) ?_
      intro a ha
      cases a with
      | limit => simp [RowLt, Row.cmp] at ha
      | poly as => exact ih as ha

theorem row_cmp_wellFounded : WellFounded RowLt := by
  refine ⟨fun a => ?_⟩
  cases a with
  | poly cs => exact poly_row_acc cs
  | limit =>
      refine Acc.intro Row.limit ?_
      intro b hb
      cases b with
      | poly cs => exact poly_row_acc cs
      | limit => simp [RowLt, Row.cmp] at hb

theorem actual_row_cmp_wellFounded :
    WellFounded (fun a b : Row => Row.cmp a b = .lt) := row_cmp_wellFounded

theorem normalRowCmp_wellFounded :
    WellFounded (fun a b : LRDStructure.NormalRow => LRDStructure.normalRowCmp a b = .lt) :=
  InvImage.wf (fun a : LRDStructure.NormalRow => a.val) actual_row_cmp_wellFounded

#print axioms actual_row_cmp_wellFounded
#print axioms normalRowCmp_wellFounded

end OrdinalFormal.LRDRowWellFounded
