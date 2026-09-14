import IPDProfileSubstitution
import IPDGraphGeometry

namespace IPD.Layer
set_option autoImplicit false
universe u
variable {X : Type u}

@[simp] theorem rename_id (d : Nat) (a : Layer X d) : rename id d a = a := by
  induction d with
  | zero => rfl
  | succ d ih =>
    have hm : WithTop.map (rename (id : X → X) d) = id := by
      funext h
      cases h with
      | top => rfl
      | coe h => exact congrArg (fun x : Layer X d => (x : WithTop (Layer X d))) (ih h)
    change Tree.rename _ a = a
    rw [hm]
    exact Tree.rename_id a

end IPD.Layer

namespace IPD
set_option autoImplicit false
universe u

@[simp] theorem renameProfile_id {X : Type u} (p : Profile X) : renameProfile id p = p := by
  cases p with
  | mk d a => simp only [renameProfile,Layer.rename_id]

theorem moveEdge_zero (cut width : Nat) (e : Edge) : moveEdge cut width 0 e = e := by
  have hm : shift cut width 0 = id := funext (shift_zero cut width)
  simp only [moveEdge,hm,id_eq,renameProfile_id]

end IPD

#print axioms IPD.Layer.rename_id
#print axioms IPD.moveEdge_zero
