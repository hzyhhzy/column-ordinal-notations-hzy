import BTnSSBMS.Decoding
import Init.Data.Int.Compare

namespace BTnSSBMS
namespace Keys

theorem atomCompare_eq_imp (a b : KeyAtom) (same : atomCompare a b = .eq) : a = b := by
  obtain ⟨activeA, valueA⟩ := a
  obtain ⟨activeB, valueB⟩ := b
  cases activeA <;> cases activeB <;>
    simp_all [atomCompare]

theorem compare_eq_imp (a b : Key) (same : compare a b = .eq) : a = b :=
  Forests.compare_eq_imp (listCompare atomCompare)
    (listCompare_eq_imp atomCompare atomCompare_eq_imp) a b same

/-- The equality test actually used by the encoder cannot confuse different
attachments at the same base. No agreement of thresholds or histories is assumed. -/
theorem equal_comparison_same_attachment (d i j : Nat) (a b : ParentLabel)
    (hs ks : Forests ParentLabel) (ha : HasWidthForests d hs) (hb : HasWidthForests d ks)
    (sameBase : a.coordinates = b.coordinates)
    (sameComparison : compare (ofColumn d i a hs) (ofColumn d j b ks) = .eq) :
    hs.map ParentLabel.coordinates = ks.map ParentLabel.coordinates :=
  same_key_same_attachment d i j a b hs ks ha hb sameBase (compare_eq_imp _ _ sameComparison)

end Keys
end BTnSSBMS
