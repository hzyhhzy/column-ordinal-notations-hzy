import IPDGraphValidity
import OrdinalFormal.ReflectionTransport

/-! Exact block arithmetic for whole-stage splicing. -/

namespace IPD
set_option autoImplicit false

def stageCut (g : Graph) (e : Edge) (b : Nat) : Nat :=
  shift e.parent (g.length-1-e.parent) b e.parent

theorem stageCut_eq (g : Graph) (e : Edge) (b : Nat) :
    stageCut g e b = e.parent + b * (g.length-1-e.parent) := by simp [stageCut,shift]

theorem stageCut_lt {g : Graph} {e : Edge} (he : e.parent < g.length-1) (b : Nat) :
    stageCut g e b < stageWidth g e b := by rw [stageCut_eq,stageWidth]; omega

theorem stage_tail_width {g : Graph} {e : Edge} (he : e.parent < g.length-1) (b : Nat) :
    stageWidth g e b - stageCut g e b = g.length-1-e.parent := by
  rw [stageCut_eq,stageWidth]
  omega

theorem stageWidth_succ {g : Graph} {e : Edge} (he : e.parent < g.length-1) (b : Nat) :
    stageWidth g e (b+1) = stageWidth g e b + (stageWidth g e b-stageCut g e b) := by
  rw [stage_tail_width he]
  simp only [stageWidth,Nat.add_mul,Nat.one_mul]
  omega

theorem shifted_lt_last {g : Graph} {e : Edge} (he : e.parent < g.length-1) (b i : Nat)
    (hi : i < g.length-1) : shift e.parent (g.length-1-e.parent) b i < stageWidth g e b := by
  rw [← shift_last he b]
  exact shift_strictMono _ _ _ hi

theorem shift_block_transition {g : Graph} {e : Edge} (he : e.parent < g.length-1) (b i : Nat) :
    shift e.parent (g.length-1-e.parent) (b+1) i =
      OrdinalFormal.ReflectionTransport.moveColumn (stageWidth g e b) (stageCut g e b)
        (shift e.parent (g.length-1-e.parent) b i) := by
  rw [stageCut_eq]
  simp only [shift,OrdinalFormal.ReflectionTransport.moveColumn,stageWidth,Nat.add_mul,Nat.one_mul]
  by_cases hi : i < e.parent
  · simp only [if_pos hi,if_pos (by omega : i < e.parent + b * (g.length-1-e.parent))]
  · simp only [if_neg hi,if_neg (by omega : ¬ i + b * (g.length-1-e.parent) <
        e.parent + b * (g.length-1-e.parent))]
    omega

theorem stage_zero (g : Graph) (e : Edge) : stage g e 0 = g.take (g.length-1) := by simp [stage]

theorem shift_zero (cut width i : Nat) : shift cut width 0 i = i := by simp [shift]

theorem shifted_source_bounds {g : Graph} {e : Edge} (he : e.parent < g.length-1)
    (b i : Nat) (hi : i < g.length-1-e.parent) :
    e.parent+i < g.length-1 ∧
      stageWidth g e b+i < stageWidth g e (b+1) := by
  rw [stageWidth_succ he,stage_tail_width he]
  omega

end IPD

#print axioms IPD.stageWidth_succ
#print axioms IPD.shift_block_transition
