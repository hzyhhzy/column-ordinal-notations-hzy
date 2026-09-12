import OneY.RootIndexed.Representation
import OrdinalFormal.ReflectionTransport

/-!
Lossless type bridge between the fixed upstream natural-layer structures and
the local arbitrary-row structures instantiated at Nat. This module transports
explicit reflection hypotheses; it does not assert an actual semantic backend.
-/

set_option maxHeartbeats 500000
set_option maxRecDepth 2048

namespace OrdinalFormal.NatSemanticTransport
namespace U
export OneY.RootIndexed (Atom TopAtom Diagram Representation Admissible FiniteReflection)
end U
namespace L
export OrdinalFormal.ReflectionTransport (Atom TopAtom Diagram Representation Admissible FiniteReflection)
end L

def atomToUp (e : L.Atom Nat) : U.Atom := ⟨e.layer, e.root, e.parent, e.child⟩
def atomToLocal (e : U.Atom) : L.Atom Nat := ⟨e.layer, e.root, e.parent, e.child⟩
def topToUp (e : L.TopAtom Nat) : U.TopAtom := ⟨e.layer, e.root, e.parent⟩
def topToLocal (e : U.TopAtom) : L.TopAtom Nat := ⟨e.layer, e.root, e.parent⟩

@[simp] theorem atomToLocal_toUp (e : L.Atom Nat) : atomToLocal (atomToUp e) = e := rfl
@[simp] theorem atomToUp_toLocal (e : U.Atom) : atomToUp (atomToLocal e) = e := rfl
@[simp] theorem topToLocal_toUp (e : L.TopAtom Nat) : topToLocal (topToUp e) = e := rfl
@[simp] theorem topToUp_toLocal (e : U.TopAtom) : topToUp (topToLocal e) = e := rfl

def diagramToUp (G : L.Diagram Nat) : U.Diagram where
  size := G.size
  atoms := G.atoms.map atomToUp
  valid := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    exact G.valid a ha

def diagramToLocal (G : U.Diagram) : L.Diagram Nat where
  size := G.size
  atoms := G.atoms.map atomToLocal
  valid := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    exact G.valid a ha

@[simp] theorem diagramToLocal_toUp (G : L.Diagram Nat) :
    diagramToLocal (diagramToUp G) = G := by
  cases G
  simp [diagramToUp, diagramToLocal, List.map_map, Function.comp_def]

@[simp] theorem diagramToUp_toLocal (G : U.Diagram) :
    diagramToUp (diagramToLocal G) = G := by
  cases G
  simp [diagramToUp, diagramToLocal, List.map_map, Function.comp_def]

universe u
variable {α : Type u}

@[simp] theorem atomValid_toUp (e : L.Atom Nat) (n : Nat) :
    (atomToUp e).Valid n ↔ e.Valid n := Iff.rfl
@[simp] theorem atomValid_toLocal (e : U.Atom) (n : Nat) :
    (atomToLocal e).Valid n ↔ e.Valid n := Iff.rfl
@[simp] theorem topValid_toUp (e : L.TopAtom Nat) (n : Nat) :
    (topToUp e).Valid n ↔ e.Valid n := Iff.rfl
@[simp] theorem topValid_toLocal (e : U.TopAtom) (n : Nat) :
    (topToLocal e).Valid n ↔ e.Valid n := Iff.rfl

@[simp] theorem atomHolds_toUp (R : Nat → α → α → α → Prop)
    (f : Nat → α) (e : L.Atom Nat) :
    (atomToUp e).Holds R f ↔ e.Holds R f := Iff.rfl
@[simp] theorem atomHolds_toLocal (R : Nat → α → α → α → Prop)
    (f : Nat → α) (e : U.Atom) :
    (atomToLocal e).Holds R f ↔ e.Holds R f := Iff.rfl
@[simp] theorem topHolds_toUp (R : Nat → α → α → α → Prop)
    (f : Nat → α) (top : α) (e : L.TopAtom Nat) :
    (topToUp e).Holds R f top ↔ e.Holds R f top := Iff.rfl
@[simp] theorem topHolds_toLocal (R : Nat → α → α → α → Prop)
    (f : Nat → α) (top : α) (e : U.TopAtom) :
    (topToLocal e).Holds R f top ↔ e.Holds R f top := Iff.rfl

theorem representation_toUp_iff (lt : α → α → Prop) (D : α → Prop)
    (R : Nat → α → α → α → Prop) (G : L.Diagram Nat) (f : Nat → α) :
    U.Representation lt D R (diagramToUp G) f ↔ L.Representation lt D R G f := by
  constructor
  · intro h
    refine ⟨h.domain, h.ordered, ?_⟩
    intro e he
    exact h.relations (atomToUp e) (List.mem_map.mpr ⟨e, he, rfl⟩)
  · intro h
    refine ⟨h.domain, h.ordered, ?_⟩
    intro e he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    exact h.relations a ha

theorem representation_toLocal_iff (lt : α → α → Prop) (D : α → Prop)
    (R : Nat → α → α → α → Prop) (G : U.Diagram) (f : Nat → α) :
    L.Representation lt D R (diagramToLocal G) f ↔ U.Representation lt D R G f := by
  rw [← representation_toUp_iff, diagramToUp_toLocal]

theorem bounded_iff (lt : α → α → Prop) (n : Nat) (f : Nat → α) (bound : α) :
    OneY.RootIndexed.Bounded lt n f bound ↔
      ReflectionTransport.Bounded lt n f bound := Iff.rfl

theorem lastRepresentation_toUp_iff (lt : α → α → Prop) (D : α → Prop)
    (R : Nat → α → α → α → Prop) (G : L.Diagram Nat) (a : α) :
    OneY.RootIndexed.LastRepresentation lt D R (diagramToUp G) a ↔
      ReflectionTransport.LastRepresentation lt D R G a := by
  constructor
  · rintro ⟨hsize, f, hrep, hlast⟩
    exact ⟨hsize, f, (representation_toUp_iff lt D R G f).mp hrep, hlast⟩
  · rintro ⟨hsize, f, hrep, hlast⟩
    exact ⟨hsize, f, (representation_toUp_iff lt D R G f).mpr hrep, hlast⟩

theorem lastRepresentation_toLocal_iff (lt : α → α → Prop) (D : α → Prop)
    (R : Nat → α → α → α → Prop) (G : U.Diagram) (a : α) :
    ReflectionTransport.LastRepresentation lt D R (diagramToLocal G) a ↔
      OneY.RootIndexed.LastRepresentation lt D R G a := by
  rw [← lastRepresentation_toUp_iff, diagramToUp_toLocal]

@[simp] theorem admissible_toUp (lt : α → α → Prop) (K cut : Nat)
    (theta : α) (f : Nat → α) (d : L.TopAtom Nat) :
    U.Admissible lt K cut theta f (topToUp d) ↔
      L.Admissible Nat.lt lt K cut theta f d := Iff.rfl

@[simp] theorem admissible_toLocal (lt : α → α → Prop) (K cut : Nat)
    (theta : α) (f : Nat → α) (d : U.TopAtom) :
    L.Admissible Nat.lt lt K cut theta f (topToLocal d) ↔
      U.Admissible lt K cut theta f d := Iff.rfl

/-- Transport upstream finite reflection without changing any semantic relation. -/
theorem finiteReflection_toLocal (lt : α → α → Prop) (D : α → Prop)
    (R : Nat → α → α → α → Prop) (h : U.FiniteReflection lt D R) :
    L.FiniteReflection Nat.lt lt D R := by
  intro G cut K theta beta f needs hcut hrep hbeta hbound hcontrol hvalid hadm hholds
  have hv : ∀ d ∈ needs.map topToUp, d.Valid (diagramToUp G).size := by
    intro d hd
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
    exact hvalid a ha
  have ha : ∀ d ∈ needs.map topToUp, U.Admissible lt K cut theta f d := by
    intro d hd
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
    exact hadm a ha
  have hh : ∀ d ∈ needs.map topToUp, d.Holds R f beta := by
    intro d hd
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
    exact hholds a ha
  obtain ⟨g, hg, hfixed, hbelow, hneeds⟩ :=
    h (diagramToUp G) cut K theta beta f (needs.map topToUp)
      hcut ((representation_toUp_iff lt D R G f).mpr hrep)
      hbeta hbound hcontrol hv ha hh
  refine ⟨g, (representation_toUp_iff lt D R G g).mp hg, hfixed, hbelow, ?_⟩
  intro d hd
  exact hneeds (topToUp d) (List.mem_map.mpr ⟨d, hd, rfl⟩)

/-- Reverse transport; the arbitrary-row interface specialized to Nat loses nothing. -/
theorem finiteReflection_toUp (lt : α → α → Prop) (D : α → Prop)
    (R : Nat → α → α → α → Prop) (h : L.FiniteReflection Nat.lt lt D R) :
    U.FiniteReflection lt D R := by
  intro G cut K theta beta f needs hcut hrep hbeta hbound hcontrol hvalid hadm hholds
  have hv : ∀ d ∈ needs.map topToLocal, d.Valid (diagramToLocal G).size := by
    intro d hd
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
    exact hvalid a ha
  have ha : ∀ d ∈ needs.map topToLocal, L.Admissible Nat.lt lt K cut theta f d := by
    intro d hd
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
    exact hadm a ha
  have hh : ∀ d ∈ needs.map topToLocal, d.Holds R f beta := by
    intro d hd
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
    exact hholds a ha
  obtain ⟨g, hg, hfixed, hbelow, hneeds⟩ :=
    h (diagramToLocal G) cut K theta beta f (needs.map topToLocal)
      hcut ((representation_toLocal_iff lt D R G f).mpr hrep)
      hbeta hbound hcontrol hv ha hh
  refine ⟨g, (representation_toLocal_iff lt D R G g).mp hg, hfixed, hbelow, ?_⟩
  intro d hd
  exact hneeds (topToLocal d) (List.mem_map.mpr ⟨d, hd, rfl⟩)

theorem finiteReflection_iff (lt : α → α → Prop) (D : α → Prop)
    (R : Nat → α → α → α → Prop) :
    U.FiniteReflection lt D R ↔ L.FiniteReflection Nat.lt lt D R :=
  ⟨finiteReflection_toLocal lt D R, finiteReflection_toUp lt D R⟩

#print axioms diagramToLocal_toUp
#print axioms representation_toUp_iff
#print axioms representation_toLocal_iff
#print axioms finiteReflection_iff
#print axioms lastRepresentation_toUp_iff

end OrdinalFormal.NatSemanticTransport
