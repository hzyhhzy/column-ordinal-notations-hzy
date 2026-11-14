import BTnSSBMS.RootedComparison
import BTnSSBMS.ClosingRowEntry

/-!
Initialize the complete insertion comparison from an actual pair of
restored representatives in the standard execution. Saved frames,
numerical offsets and run invariants are derived, not assumed. The
material may be the entire old tail or its exact source-block cutoff.
-/
namespace BTnSSBMS.Encoder

theorem standard_entry_runFacts {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {entry : Entry d}
    (member : entry ∈ entries d e [] [] [] [] []) : RunFacts entry.state :=
  ⟨source_entry_framesOrdered member, source_entry_framesDense member,
   source_entry_framesRealized member, standard_entry_framesAncestral positive standard member⟩

theorem standard_entry_head_runFacts {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {entry : Entry d}
    (member : entry ∈ entries d e [] [] [] [] []) : RunFacts entry.headed := by
  have sound := standard_entries_sound positive standard entry member
  exact (standard_entry_runFacts positive standard member).encode
    (.cons entry.coordinates entry.attachments .nil) entry.source entry.visible
    positive sound.coherent sound.valid sound.view (source_entries_good d e entry member)
    ⟨sound.legal.1, sound.legal.2.1, sound.legal.2.2.1, sound.legal.2.2.2.1, trivial⟩

theorem source_entry_head_good {d : Nat} {e : NumericalExpr} {entry : Entry d}
    (member : entry ∈ entries d e [] [] [] [] []) :
    VisibleGood entry.headed (entry.visible ++ [entry.closing]) :=
  headState_good d _ _ entry.visible entry.state (source_entries_good d e entry member)

/-- Every actual strict closing-ancestor pair supplies a complete comparison
for arbitrary finite legal material at the old restored entry. In particular,
there is no caller-supplied recursive comparison or activation invariant. -/
theorem standard_closing_material_comparison {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {later : Entry d}
    (member : later ∈ entries d e [] [] [] [] []) {position : Nat}
    (self : SelfLatest (encode d (Parents.annotate d [] e) [] []) position)
    (before : position < later.closing)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) d position later.closing) :
    ∃ earlier, earlier ∈ entries d e [] [] [] [] [] ∧ earlier.closing = position ∧
      (let source := earlier.source ++ [Parents.label d earlier.source earlier.coordinates]
       let target := later.source ++ [Parents.label d later.source later.coordinates]
       let moved := List.range earlier.source.length ++ [later.source.length]
       let delta := fun j => Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) j later.closing -
         Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) j position
       ∀ material, Source.FiniteLegal d source material →
         ShiftComparison position delta earlier.headed later.headed
           (encode d (Parents.annotate d source material) (earlier.visible ++ [earlier.closing]) earlier.headed)
           (encode d (Parents.annotate d target (Source.relocate d source target moved material))
             (later.visible ++ [later.closing]) later.headed)) := by
  obtain ⟨_, earlier, extra, _, _, oldMember, _, closes, _, _, relocationView, related, keyAmount, values⟩ :=
    standard_closing_rebased_entry positive standard member self before path
  have oldSound := standard_entries_sound positive standard earlier oldMember
  have newSound := standard_entries_sound positive standard later member
  have oldHeadView := headState_view earlier.state positive oldSound.coherent oldSound.valid oldSound.view
    earlier.coordinates earlier.attachments oldSound.legal.2.2.2.1.separated
  have newHeadView := headState_view later.state positive newSound.coherent newSound.valid newSound.view
    later.coordinates later.attachments newSound.legal.2.2.2.1.separated
  have oldKnown := headState_materials oldSound.materials oldSound.view earlier.coordinates earlier.attachments
    oldSound.legal.1 oldSound.legal.2.2.2.1
  have newKnown := headState_materials newSound.materials newSound.view later.coordinates later.attachments
    newSound.legal.1 newSound.legal.2.2.2.1
  have nonempty := headState_nonempty d (Parents.label d earlier.source earlier.coordinates)
    (Parents.annotateForests d (earlier.source ++ [Parents.label d earlier.source earlier.coordinates]) earlier.attachments)
    earlier.visible earlier.state
  change 0 < earlier.headed.length at nonempty
  refine ⟨earlier, oldMember, closes, ?_⟩
  dsimp only
  intro material legal
  exact encode_rooted_comparison position d material
    (earlier.source ++ [Parents.label d earlier.source earlier.coordinates])
    (later.source ++ [Parents.label d later.source later.coordinates])
    (List.range earlier.source.length ++ [later.source.length])
    (earlier.visible ++ [earlier.closing]) (later.visible ++ [later.closing]) earlier.owners
    (earlier.materials ++ [earlier.attachments]) (extra.map Binding.key) earlier.headed later.headed positive
    (Parents.coherent_append_label oldSound.coherent earlier.coordinates)
    (Parents.context_valid_append_label d earlier.source oldSound.valid earlier.coordinates)
    (Parents.coherent_append_label newSound.coherent later.coordinates)
    (Parents.context_valid_append_label d later.source newSound.valid later.coordinates)
    newSound.legal.2.1 relocationView oldHeadView newHeadView
    (fun i inside => (newKnown.materialContext.legal i inside).1) oldKnown related legal
    (standard_entry_head_runFacts positive standard oldMember)
    (standard_entry_head_runFacts positive standard member)
    (source_entry_head_good oldMember) (source_entry_head_good member) _ keyAmount
    (by rw [← closes]; unfold Entry.closing; omega)
    (by simpa only [List.length_append, List.length_cons, List.length_nil] using values)

end BTnSSBMS.Encoder
