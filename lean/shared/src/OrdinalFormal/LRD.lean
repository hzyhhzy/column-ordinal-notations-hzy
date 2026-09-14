import OrdinalFormal.Columns

namespace OrdinalFormal.LRD

open Columns

/-- Coefficients are little endian: [a₀,a₁,...,a_d]. Trailing zeros are
identified by `normal`; `limit` denotes ω^ω, not an external top. -/
inductive Row where
  | poly (coefficients : List Nat)
  | limit
  deriving Repr, DecidableEq

def trim (cs : List Nat) : List Nat := (cs.reverse.dropWhile (· == 0)).reverse

def Row.normal : Row → Row
  | .poly cs => .poly (trim cs)
  | .limit => .limit

def Row.cmp : Row → Row → Ordering
  | .limit, .limit => .eq
  | .limit, .poly _ => .gt
  | .poly _, .limit => .lt
  | .poly as, .poly bs =>
    let a := trim as
    let b := trim bs
    thenCompare (compare a.length b.length) fun _ => listCompare compare a.reverse b.reverse

/-- Subtract the last monomial copy, and if its exponent is positive replace
it by (t+1) copies of the next smaller monomial. -/
def approximatePoly : List Nat → Nat → List Nat
  | [], _ => []
  | a :: rest, t =>
    if a > 0 then (a - 1) :: rest
    else match rest with
      | [] => []
      | b :: tail =>
        if b > 0 then (t + 1) :: (b - 1) :: tail
        else 0 :: approximatePoly rest t

def Row.approx (a : Row) (t : Nat) : Row :=
  match a with
  | .poly cs => .poly (trim (approximatePoly (trim cs) t))
  | .limit => .poly (List.replicate (t + 1) 0 ++ [1])

def Row.isFinite : Row → Bool
  | .poly cs => (trim cs).length ≤ 1
  | .limit => false

def package (a : Row) (b : Nat) : List Row :=
  if a.isFinite then [] else .poly [] :: (List.range (b + 1)).map a.approx

abbrev Diagram := Graph Row

def seed : Diagram := [[], [⟨.limit, 0, 0⟩]]

def fs (g : Diagram) (n : Nat) : Diagram := expand Row.cmp package g n

def cmp : Diagram → Diagram → Ordering := graphCompare Row.cmp

/-- This domain includes the ordinary finite seed itself; no extra top. -/
inductive Standard : Diagram → Prop
  | seed : Standard seed
  | child {a : Diagram} (h : Standard a) (n : Nat) : Standard (fs a n)

@[simp] theorem fs_zero (g : Diagram) : fs g 0 = g.take (g.length - 1) :=
  expand_zero _ _ _

theorem fs_prefix (g : Diagram) {i j : Nat} (h : i ≤ j) :
    (fs g i).IsPrefix (fs g j) := expand_prefix _ _ _ h

end OrdinalFormal.LRD
