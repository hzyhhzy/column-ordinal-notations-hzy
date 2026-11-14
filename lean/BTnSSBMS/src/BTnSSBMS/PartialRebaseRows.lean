import BTnSSBMS.FixedPrefixRows

/-! Whole-output numerical row transport for the frozen activation copy.
The final theorem constructs the source entry for every real intermediate
SB pair. No whole-block inequality or BMS standardness is concluded here. -/
namespace BTnSSBMS.Encoder

theorem partial_rebase_encode_row {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (unit : Parents.UnitSteps d context) (position : List Nat)
    (positionUnit : Parents.UnitSteps d (context ++ [Parents.label d context position]))
    {cut root : Nat} (positive : 0 < cut) (room : cut < d) (insideRoot : root < context.length)
    (path : Parents.Ancestor (context ++ [Parents.label d context position]) (cut - 1) root context.length)
    (same : (Parents.label d context position).parents[cut]?.join = Parents.parent context cut root)
    (hs : Forests (List Nat)) (tail : NumericalExpr)
    (legal : Source.FiniteLegal d (context.take root) (.cons (context[root]?.getD default).coordinates hs tail))
    {visible nextVisible owners : List Nat} {materials : List (Forests (List Nat))}
    {state next : State d}
    (known : VisibleMaterials d (context.take root) visible owners materials state)
    (oldView : Parents.NumericalView d (context.take root) (BMS.parentTable (d + 2) (matrix state)) visible)
    (newView : Parents.NumericalView d context (BMS.parentTable (d + 2) (matrix next)) nextVisible)
    (contextWidth : ∀ i, i < context.length → (context[i]?.getD default).coordinates.length = d)
    (visiblePrefix : visible <+: nextVisible) (statePrefix : state <+: next)
    (j amount : Nat) (row : j < d)
    (headValue :
      let coordinates := (context[root]?.getD default).coordinates
      let delta := (List.range cut).map (fun k => position[k]?.getD 0 - coordinates[k]?.getD 0)
      vector next nextVisible (Parents.label d context (Source.shift coordinates cut delta 1)) j =
        vector state visible (Parents.label d (context.take root) coordinates) j + amount) :
    let coordinates := (context[root]?.getD default).coordinates
    let delta := (List.range cut).map (fun k => position[k]?.getD 0 - coordinates[k]?.getD 0)
    RowRebaseTrace j state.length amount state next
      (encode d (Parents.annotate d (context.take root) (.cons coordinates hs tail)) visible state)
      (encode d (Parents.annotate d context
        (Source.copied d root cut delta 1 (context.take root) (List.replicate root 0) (.cons coordinates hs tail)))
        nextVisible next) := by
  let coordinates := (context[root]?.getD default).coordinates
  let delta := (List.range cut).map (fun k => position[k]?.getD 0 - coordinates[k]?.getD 0)
  let head := Source.shift coordinates cut delta 1
  have length : (context.take root).length = root := by simp only [List.length_take]; omega
  have divided := coherent.take_succ_label insideRoot
  have forestsLegal := legal.2.2.2.1
  have tailLegal := legal.2.2.2.2
  rw [← divided] at forestsLegal tailLegal
  have scope := Source.partial_rebase_shiftView coherent valid unit position positionUnit
    positive room insideRoot path same legal.1
  have frameSame := partial_rebase_queried_frame coherent valid unit position positionUnit
    positive room insideRoot path same legal.1 oldView visiblePrefix statePrefix
  have keySame := partial_rebase_queryKey coherent valid unit position positionUnit
    positive room insideRoot path same hs legal.1 forestsLegal
  have targetWidth : ∀ i, i < (context ++ [Parents.label d context head]).length →
      ((context ++ [Parents.label d context head])[i]?.getD default).coordinates.length = d := by
    intro i inside
    by_cases old : i < context.length
    · simpa only [List.getElem?_append_left old] using contextWidth i old
    · have last : i = context.length := by
        simp only [List.length_append, List.length_cons, List.length_nil] at inside
        omega
      subst i
      simp only [List.getElem?_concat_length, Option.getD_some, Parents.label]
      exact (Source.shift_width ..).trans legal.1
  have result := prefix_rebase_encode_row d coordinates head hs tail (context.take root) context
    visible nextVisible owners materials state next (by omega)
    (coherent.restrict (List.take_prefix root context)) (valid.restrict (List.take_prefix root context))
    (unit.restrict valid (List.take_prefix root context)) (List.take_prefix root context)
    coherent valid scope.targetUnit
    (by simpa only [coordinates, head, delta, length, ← divided] using scope.view)
    oldView newView targetWidth known visiblePrefix statePrefix frameSame
    (by simpa only [coordinates, head, delta, length, ← divided] using keySame) legal j amount row headValue
  dsimp only [coordinates, head, delta] at result
  simp only [length, ← divided] at result
  rw [Source.relocateForests_eq_copied scope _ hs forestsLegal,
    Source.relocate_eq_copied scope tail tailLegal] at result
  simpa only [Source.copied_at_root, ← divided] using result

theorem Entry.OriginAt.partial_rebase_row {d : Nat} {earlier later : Entry d} {root cut : Nat}
    (origin : earlier.OriginAt later.source later.visible later.owners later.materials later.state root)
    (oldSound : earlier.Sound) (newSound : later.Sound)
    (positive : 0 < cut) (room : cut < d) (insideRoot : root < later.source.length)
    (path : Parents.Ancestor (later.source ++ [Parents.label d later.source later.coordinates])
      (cut - 1) root later.source.length)
    (same : (Parents.label d later.source later.coordinates).parents[cut]?.join =
      Parents.parent later.source cut root) (j amount : Nat) (row : j < d)
    (headValue :
      let delta := (List.range cut).map (fun k => later.coordinates[k]?.getD 0 - earlier.coordinates[k]?.getD 0)
      vector later.state later.visible (Parents.label d later.source (Source.shift earlier.coordinates cut delta 1)) j =
        vector earlier.state earlier.visible (Parents.label d earlier.source earlier.coordinates) j + amount) :
    let delta := (List.range cut).map
      (fun k => later.coordinates[k]?.getD 0 - earlier.coordinates[k]?.getD 0)
    RowRebaseTrace j earlier.state.length amount earlier.state later.state earlier.result
      (encode d (Parents.annotate d later.source
        (Source.copied d root cut delta 1 earlier.source (List.replicate root 0) earlier.remaining))
        later.visible later.state) := by
  have legal : Source.FiniteLegal d (later.source.take root)
      (.cons (later.source[root]?.getD default).coordinates earlier.attachments earlier.tail) := by
    simpa only [Entry.remaining, origin.sourceEq, origin.coordinates] using oldSound.legal
  have known : VisibleMaterials d (later.source.take root) earlier.visible earlier.owners earlier.materials
      earlier.state := by simpa only [origin.sourceEq] using oldSound.materials
  have oldView : Parents.NumericalView d (later.source.take root)
      (BMS.parentTable (d + 2) (matrix earlier.state)) earlier.visible := by
    simpa only [origin.sourceEq] using oldSound.view
  have visiblePrefix : earlier.visible <+: later.visible := by
    rw [origin.visibleEq]
    exact List.take_prefix _ _
  have result := partial_rebase_encode_row newSound.coherent newSound.valid newSound.unit
    later.coordinates newSound.legal.2.1 positive room insideRoot path same earlier.attachments earlier.tail
    legal known oldView newSound.view newSound.width visiblePrefix origin.statePrefix j amount row
    (by simpa only [origin.sourceEq, origin.coordinates] using headValue)
  simpa only [Entry.result, Entry.remaining, origin.sourceEq, origin.coordinates] using result

theorem standard_intermediate_pair_rows {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {a b cut : Nat}
    (rowPositive : 0 < cut) (room : cut < d) (before : a < b) (inside : b < (fromSource d e).length)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) (cut - 1) a b)
    (same : Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) cut a =
      Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) cut b) :
    ∃ earlier later root, earlier ∈ entries d e [] [] [] [] [] ∧
      later ∈ entries d e [] [] [] [] [] ∧ root < later.source.length ∧
      earlier.OriginAt later.source later.visible later.owners later.materials later.state root ∧
      earlier.state.length = a ∧ later.state.length = b ∧
      (let delta := (List.range cut).map
        (fun k => later.coordinates[k]?.getD 0 - earlier.coordinates[k]?.getD 0)
      let shifted := encode d (Parents.annotate d later.source
        (Source.copied d root cut delta 1 earlier.source (List.replicate root 0) earlier.remaining))
        later.visible later.state
      ∀ j, j < d →
        RowRebaseTrace j a
          (if j < cut then Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) j b -
            Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) j a else 0)
          earlier.state later.state earlier.result shifted) := by
  obtain ⟨earlier, later, root, oldMember, newMember, bound, origin, _, oldPosition, newPosition,
      sourcePath, shared⟩ :=
    standard_intermediate_pair_source positive standard rowPositive room before inside path same
  refine ⟨earlier, later, root, oldMember, newMember, bound, origin, oldPosition, newPosition, ?_⟩
  dsimp only
  intro j row
  have oldSound := standard_entries_sound positive standard earlier oldMember
  have newSound := standard_entries_sound positive standard later newMember
  have vectorValue := origin.partial_rebase_vector oldSound newSound rowPositive room bound sourcePath shared.symm j row
  have oldRead := earlier.first_reading_in (entries_execution d e [] [] [] [] [] earlier oldMember).resultPrefix row
  have newRead := later.first_reading_in (entries_execution d e [] [] [] [] [] later newMember).resultPrefix row
  change Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) j earlier.state.length = _ at oldRead
  change Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) j later.state.length = _ at newRead
  rw [oldPosition] at oldRead
  rw [newPosition] at newRead
  let amount := if j < cut then Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) j b -
      Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) j a else 0
  have headValue :
      let delta := (List.range cut).map (fun k => later.coordinates[k]?.getD 0 - earlier.coordinates[k]?.getD 0)
      vector later.state later.visible (Parents.label d later.source (Source.shift earlier.coordinates cut delta 1)) j =
        vector earlier.state earlier.visible (Parents.label d earlier.source earlier.coordinates) j + amount := by
    dsimp only
    rw [vectorValue]
    by_cases low : j < cut
    · have ancestor := path.lower_row (BMS.parentTable_coherent (d + 2) (fromSource d e))
        (by omega : cut - 1 < d + 2) (by omega : j ≤ cut - 1)
      have ordered := ancestor.reading_le (BMS.parentTable_coherent (d + 2) (fromSource d e))
      simp only [low, if_true, amount]
      rw [← oldRead, ← newRead]
      omega
    · simp only [low, if_false, amount, Nat.add_zero]
  simpa only [oldPosition] using origin.partial_rebase_row oldSound newSound rowPositive room bound
    sourcePath shared.symm j amount row headValue

end BTnSSBMS.Encoder
