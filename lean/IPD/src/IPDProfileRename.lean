import IPDProfileOrder

/-! Relabel every atomic ROOT/SELF, including atoms nested inside heads.
The level, zero symbols, CAP symbols and ordered arities stay fixed. -/

namespace IPD
set_option autoImplicit false
universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}

namespace Layer

def rename (f : X → Y) : (n : Nat) → Layer X n → Layer Y n
  | 0 => f
  | n+1 => Tree.rename (WithTop.map (rename f n))

theorem rename_strictMono [LinearOrder X] [WellFoundedLT X]
    [LinearOrder Y] [WellFoundedLT Y] (f : X → Y) (hf : StrictMono f) (n : Nat) :
    StrictMono (rename f n) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    change StrictMono (Tree.rename (WithTop.map (rename f n)))
    intro a b hab
    exact Tree.rename_lpo _ (fun _ _ h => ih.withTop_map h) hab

theorem rename_lt_iff [LinearOrder X] [WellFoundedLT X]
    [LinearOrder Y] [WellFoundedLT Y] (f : X → Y) (hf : StrictMono f)
    (n : Nat) (a b : Layer X n) : rename f n a < rename f n b ↔ a < b :=
  (rename_strictMono f hf n).lt_iff_lt

end Layer

def renameProfile (f : X → Y) (p : Profile X) : Profile Y :=
  ⟨p.1, Layer.rename f p.1 p.2⟩

theorem renameProfile_strictMono [LinearOrder X] [WellFoundedLT X]
    [LinearOrder Y] [WellFoundedLT Y] (f : X → Y) (hf : StrictMono f) :
    StrictMono (renameProfile f) := by
  intro a b hab
  cases hab with
  | left a b h => exact .left _ _ h
  | right a h => exact .right _ (Layer.rename_strictMono f hf _ h)

theorem renameProfile_lt_iff [LinearOrder X] [WellFoundedLT X]
    [LinearOrder Y] [WellFoundedLT Y] (f : X → Y) (hf : StrictMono f)
    (a b : Profile X) : renameProfile f a < renameProfile f b ↔ a < b :=
  (renameProfile_strictMono f hf).lt_iff_lt

end IPD

#print axioms IPD.Layer.rename_strictMono
#print axioms IPD.renameProfile_strictMono
#print axioms IPD.renameProfile_lt_iff
