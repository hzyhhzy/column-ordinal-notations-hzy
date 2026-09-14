import OrdinalFormal.Columns

/-!
Geometric facts for the actual column implementation. No ordinal interpretation,
comparison law, accessibility, or well-ordering conclusion is assumed here.
-/

set_option maxHeartbeats 500000
set_option maxRecDepth 2048

namespace OrdinalFormal.ExpansionValidity
open Columns
universe u
variable {Row : Type u}

private theorem controlFold_mem (cmp : Row → Row → Ordering)
    (es : Column Row) (a : Entry Row) :
    es.foldl (fun a b => if controlCompare cmp a b == .lt then b else a) a ∈ a :: es := by
  induction es generalizing a with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl_cons]
    split
    · have hm := ih b
      simp only [List.mem_cons] at hm ⊢
      exact hm.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h))
    · have hm := ih a
      simp only [List.mem_cons] at hm ⊢
      exact hm.elim Or.inl (fun h => Or.inr (Or.inr h))

theorem control_mem (cmp : Row → Row → Ordering)
    {c : Column Row} {e : Entry Row} (h : Columns.control cmp c = some e) : e ∈ c := by
  cases c with
  | nil => simp [Columns.control] at h
  | cons a es =>
    simp only [Columns.control, Option.some.injEq] at h
    rw [← h]
    exact controlFold_mem cmp es a

theorem control_valid (cmp : Row → Row → Ordering) {g : Graph Row}
    (hg : Valid g) {e : Entry Row}
    (he : Columns.control cmp (g.getLast?.getD []) = some e) :
    e.root ≤ e.parent ∧ e.parent < g.length - 1 := by
  have hm := control_mem cmp he
  rw [List.getLast?_eq_getElem?] at hm
  exact hg (g.length - 1) e hm

theorem valid_take {g : Graph Row} (hg : Valid g) (n : Nat) : Valid (g.take n) := by
  intro j e he
  rw [List.getElem?_take] at he
  split at he
  · exact hg j e he
  · simp at he

theorem expand_zero_valid (cmp : Row → Row → Ordering) (package : Package Row)
    {g : Graph Row} (hg : Valid g) : Valid (expand cmp package g 0) := by
  rw [expand_zero]
  exact valid_take hg _

theorem move_mono (cut len b : Nat) {i j : Nat} (h : i ≤ j) :
    move cut len b i ≤ move cut len b j := by
  unfold move
  split <;> split <;> omega

theorem move_le (cut len b i : Nat) : move cut len b i ≤ i + b * len := by
  unfold move
  split <;> omega

theorem move_lt_shift (cut len b : Nat) {i j : Nat} (h : i < j) :
    move cut len b i < j + b * len := by
  have hm := move_le cut len b i
  omega

theorem moveEntry_root_bound (cut len b : Nat) {e : Entry Row}
    (h : e.root ≤ e.parent) :
    (moveEntry cut len b e).root ≤ (moveEntry cut len b e).parent :=
  move_mono cut len b h

/-- A moved old edge still points left of its shifted source column. -/
theorem moved_source_bounds (cut len b source : Nat) {e : Entry Row}
    (hroot : e.root ≤ e.parent) (hparent : e.parent < source) :
    (moveEntry cut len b e).root ≤ (moveEntry cut len b e).parent ∧
    (moveEntry cut len b e).parent < source + b * len :=
  ⟨moveEntry_root_bound cut len b hroot, move_lt_shift cut len b hparent⟩

private theorem insert_preserves (cmp : Row → Row → Ordering) (P : Entry Row → Prop)
    (a : Entry Row) (es : Column Row) (ha : P a) (hes : ∀ e ∈ es, P e) :
    ∀ e ∈ insertDescending cmp a es, P e := by
  induction es with
  | nil => simpa [insertDescending] using ha
  | cons b bs ih =>
    simp only [insertDescending]
    split
    · intro e he
      simp only [List.mem_cons] at he
      exact he.elim (fun h => h ▸ ha) (fun h => hes e (List.mem_cons.mpr h))
    · intro e he
      simp only [List.mem_cons] at he
      exact he.elim (fun h => h ▸ hes b (List.mem_cons_self))
        (fun h => ih (fun e he => hes e (List.mem_cons_of_mem _ he)) e h)

private theorem sort_preserves (cmp : Row → Row → Ordering) (P : Entry Row → Prop)
    (es : Column Row) (hes : ∀ e ∈ es, P e) :
    ∀ e ∈ sortDescending cmp es, P e := by
  induction es with
  | nil => simp [sortDescending]
  | cons a as ih =>
    exact insert_preserves cmp P a (sortDescending cmp as)
      (hes a List.mem_cons_self)
      (ih (fun e he => hes e (List.mem_cons_of_mem _ he)))

private theorem dedup_preserves (cmp : Row → Row → Ordering) (P : Entry Row → Prop)
    (es : Column Row) (hes : ∀ e ∈ es, P e) :
    ∀ e ∈ dedupSorted cmp es, P e := by
  induction es with
  | nil => simp [dedupSorted]
  | cons a as ih =>
    have ha := hes a List.mem_cons_self
    have hrest := ih (fun e he => hes e (List.mem_cons_of_mem _ he))
    simp only [dedupSorted]
    generalize hr : dedupSorted cmp as = rest at hrest ⊢
    cases rest with
    | nil => simpa using ha
    | cons b bs =>
      change ∀ e ∈ (if entryCompare cmp a b == .eq then b :: bs else a :: b :: bs), P e
      split
      · exact hrest
      · intro e he
        simp only [List.mem_cons] at he
        exact he.elim (fun h => h ▸ ha) (fun h => hrest e (List.mem_cons.mpr h))

/-- Normalization preserves every entry property closed under decreasing root. -/
theorem normalizeColumn_preserves (cmp : Row → Row → Ordering)
    (P : Entry Row → Prop) (c : Column Row)
    (hc : ∀ e ∈ c, P e)
    (lowerRoot : ∀ e, P e → ∀ q, q ≤ e.root → P {e with root := q}) :
    ∀ e ∈ normalizeColumn cmp c, P e := by
  apply dedup_preserves
  apply sort_preserves
  intro e he
  simp only [List.mem_flatMap, List.mem_map, List.mem_range] at he
  obtain ⟨a, ha, q, hq, he⟩ := he
  subst e
  exact lowerRoot a (hc a ha) q (by omega)

theorem normalizeColumn_bounds (cmp : Row → Row → Ordering)
    (j : Nat) (c : Column Row)
    (hc : ∀ e ∈ c, e.root ≤ e.parent ∧ e.parent < j) :
    ∀ e ∈ normalizeColumn cmp c, e.root ≤ e.parent ∧ e.parent < j := by
  apply normalizeColumn_preserves cmp (fun e => e.root ≤ e.parent ∧ e.parent < j) c hc
  intro e he q hq
  exact ⟨Nat.le_trans hq he.1, he.2⟩

/-- Soundness of sorting, deduplication and root closure: normalization only
weakens a root of an existing entry, preserving its row and parent exactly. -/
theorem mem_normalizeColumn_source (cmp : Row → Row → Ordering)
    (c : Column Row) {e : Entry Row} (he : e ∈ normalizeColumn cmp c) :
    ∃ a ∈ c, e.row = a.row ∧ e.parent = a.parent ∧ e.root ≤ a.root := by
  apply normalizeColumn_preserves cmp
    (fun e => ∃ a ∈ c, e.row = a.row ∧ e.parent = a.parent ∧ e.root ≤ a.root) c
    ?_ ?_ e he
  · intro a ha
    exact ⟨a, ha, rfl, rfl, Nat.le_refl _⟩
  · intro a ha q hq
    obtain ⟨z, hz, hr, hp, hroot⟩ := ha
    exact ⟨z, hz, hr, hp, Nat.le_trans hq hroot⟩

theorem ordinarySeam_bounds (cmp : Row → Row → Ordering)
    (last : Column Row) (e : Entry Row) (len b lastIndex : Nat)
    (hlast : ∀ a ∈ last, a.root ≤ a.parent ∧ a.parent < lastIndex) :
    ∀ a ∈ ordinarySeam cmp last e len b,
      a.root ≤ a.parent ∧ a.parent < lastIndex + b * len := by
  intro a ha
  simp only [ordinarySeam, List.mem_flatMap, List.mem_map,
    List.mem_filter, List.mem_range] at ha
  obtain ⟨z, hz, q, ⟨hq, _⟩, ha⟩ := ha
  subst a
  have hmove := move_mono e.parent len b (hlast z hz).1
  change q ≤ move e.parent len b z.parent ∧
    move e.parent len b z.parent < lastIndex + b * len
  exact ⟨Nat.le_trans (by omega) hmove,
    move_lt_shift e.parent len b (hlast z hz).2⟩

theorem generatedSeam_bounds (package : Package Row) (e : Entry Row)
    (len b : Nat) (hlen : 0 < len) :
    ∀ a ∈ generatedSeam package e len b,
      a.root ≤ a.parent ∧ a.parent < e.parent + (b + 1) * len := by
  intro a ha
  simp only [generatedSeam, List.mem_flatMap, List.mem_map, List.mem_range] at ha
  obtain ⟨row, _, q, hq, ha⟩ := ha
  subst a
  have hmove : move e.parent len b e.parent = e.parent + b * len := by
    simp [move]
  simp only [hmove, Nat.add_mul, Nat.one_mul] at hq ⊢
  constructor <;> omega

/-- Each literal column produced by `block` is geometrically valid at its global
position. This includes copied edges and both kinds of seam before normalization. -/
theorem block_column_bounds (cmp : Row → Row → Ordering) (package : Package Row)
    (g : Graph Row) (e : Entry Row) (b i : Nat) (hg : Valid g)
    (_he : e.parent < g.length - 1)
    (hi : i < g.length - 1 - e.parent) :
    let len := g.length - 1 - e.parent
    let source := (g[e.parent + i]?.getD []).map (moveEntry e.parent len (b + 1))
    ∀ a ∈ normalizeColumn cmp (source ++ if i = 0 then
      ordinarySeam cmp (g.getLast?.getD []) e len b ++ generatedSeam package e len b
      else []),
      a.root ≤ a.parent ∧ a.parent < g.length - 1 + b * len + i := by
  dsimp only
  let len := g.length - 1 - e.parent
  have hlen : 0 < len := by dsimp [len]; omega
  have hsum : e.parent + len = g.length - 1 := by dsimp [len]; omega
  apply normalizeColumn_bounds
  intro a ha
  simp only [List.mem_append] at ha
  cases ha with
  | inl ha =>
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
    have hb := moved_source_bounds e.parent len (b + 1) (e.parent + i)
      (hg (e.parent + i) z hz).1 (hg (e.parent + i) z hz).2
    simp only [Nat.add_mul, Nat.one_mul] at hb
    exact ⟨hb.1, by dsimp [len] at hb hsum; omega⟩
  | inr ha =>
    split at ha
    · rename_i hi0
      subst i
      simp only [List.mem_append] at ha
      cases ha with
      | inl ha =>
        have hl : ∀ z ∈ g.getLast?.getD [], z.root ≤ z.parent ∧ z.parent < g.length - 1 := by
          intro z hz
          rw [List.getLast?_eq_getElem?] at hz
          exact hg _ z hz
        have hb := ordinarySeam_bounds cmp (g.getLast?.getD []) e len b
          (g.length - 1) hl a ha
        simpa using hb
      | inr ha =>
        have hb := generatedSeam_bounds package e len b hlen a ha
        simp only [Nat.add_mul, Nat.one_mul] at hb
        exact ⟨hb.1, by dsimp [len] at hb hsum; omega⟩
    · simp at ha

theorem block_length (cmp : Row → Row → Ordering) (package : Package Row)
    (g : Graph Row) (e : Entry Row) (b : Nat) :
    (block cmp package g e b).length = g.length - 1 - e.parent := by
  simp [block]

theorem block_index_bounds (cmp : Row → Row → Ordering) (package : Package Row)
    (g : Graph Row) (e : Entry Row) (b i : Nat) (hg : Valid g)
    (he : e.parent < g.length - 1) (hi : i < g.length - 1 - e.parent) :
    ∀ a ∈ ((block cmp package g e b)[i]?.getD []),
      a.root ≤ a.parent ∧ a.parent < g.length - 1 + b * (g.length - 1 - e.parent) + i := by
  simpa [block, List.getElem?_map, List.getElem?_range, hi] using
    block_column_bounds cmp package g e b i hg he hi

/-- Coordinate validity for a segment whose first column is at global `offset`. -/
def ValidFrom (offset : Nat) (g : Graph Row) : Prop :=
  ∀ i : Nat, ∀ e : Entry Row, e ∈ (g[i]?.getD []) →
    e.root ≤ e.parent ∧ e.parent < offset + i

theorem validFrom_zero_iff (g : Graph Row) : ValidFrom 0 g ↔ Valid g := by
  simp only [ValidFrom, Valid, Nat.zero_add]

theorem validFrom_nil (offset : Nat) : ValidFrom offset ([] : Graph Row) := by
  intro i e he
  simp at he

theorem validFrom_append (offset : Nat) (a b : Graph Row)
    (ha : ValidFrom offset a) (hb : ValidFrom (offset + a.length) b) :
    ValidFrom offset (a ++ b) := by
  intro i e he
  rw [List.getElem?_append] at he
  split at he
  · exact ha i e he
  · rename_i hi
    have h := hb (i - a.length) e he
    exact ⟨h.1, by omega⟩

theorem block_validFrom (cmp : Row → Row → Ordering) (package : Package Row)
    (g : Graph Row) (e : Entry Row) (b : Nat) (hg : Valid g)
    (he : e.parent < g.length - 1) :
    ValidFrom (g.length - 1 + b * (g.length - 1 - e.parent)) (block cmp package g e b) := by
  intro i a ha
  by_cases hi : i < g.length - 1 - e.parent
  · exact block_index_bounds cmp package g e b i hg he hi a ha
  · rw [List.getElem?_eq_none (by rw [block_length]; omega)] at ha
    simp at ha

theorem blocks_length (cmp : Row → Row → Ordering) (package : Package Row)
    (g : Graph Row) (e : Entry Row) (n : Nat) :
    ((List.range n).flatMap (block cmp package g e)).length =
      n * (g.length - 1 - e.parent) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [List.range_succ, List.flatMap_append, ih, block_length, Nat.add_mul]

theorem blocks_validFrom (cmp : Row → Row → Ordering) (package : Package Row)
    (g : Graph Row) (e : Entry Row) (n : Nat) (hg : Valid g)
    (he : e.parent < g.length - 1) :
    ValidFrom (g.length - 1) ((List.range n).flatMap (block cmp package g e)) := by
  induction n with
  | zero => exact validFrom_nil _
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply validFrom_append _ _ _ ih
    rw [blocks_length]
    exact block_validFrom cmp package g e n hg he

/-- Full preservation for the actual expansion, for arbitrary row comparator and
arbitrary generated row package. No order/semantic/termination premise is used. -/
theorem expand_valid (cmp : Row → Row → Ordering) (package : Package Row)
    (g : Graph Row) (n : Nat) (hg : Valid g) :
    Valid (expand cmp package g n) := by
  unfold expand
  split
  · exact valid_take hg _
  · rename_i e he
    apply (validFrom_zero_iff _).mp
    apply validFrom_append
    · exact (validFrom_zero_iff _).mpr (valid_take hg _)
    · simp only [Nat.zero_add, List.length_take,
        Nat.min_eq_left (Nat.sub_le g.length 1)]
      exact blocks_validFrom cmp package g e n hg (control_valid cmp hg he).2

end OrdinalFormal.ExpansionValidity
