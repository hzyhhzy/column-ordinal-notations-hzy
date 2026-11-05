import LaverLowerBounds.NumericSeedsAndKinds
import LaverLowerBounds.UpperHierarchyEvaluation

set_option autoImplicit false

namespace LaverLowerBounds.NumericBMS
open YesMetaZFC.BMS

/-- Ordinary stack FGH for the numerical BM4 rules: empty is zero, a
nonempty matrix with no last-column parent is a successor, and every other
matrix takes its input-indexed fundamental-sequence term. -/
inductive FastRun : List ValidArray → Nat → Nat → Prop
  | done (x) : FastRun [] x x
  | zero {a rest x y} : a.raw = [] →
      FastRun rest (x + 1) y → FastRun (a :: rest) x y
  | successor {a rest x y} : a.raw ≠ [] → maximalParentRow a.raw = none →
      FastRun (List.replicate (x + 1) (a.expand 0) ++ rest) x y → FastRun (a :: rest) x y
  | limit {a rest x y r} : maximalParentRow a.raw = some r →
      FastRun (a.expand x :: rest) x y → FastRun (a :: rest) x y

def FastEval (a : ValidArray) (x y : Nat) : Prop := FastRun [a] x y

def encodeStack (stack : List ValidArray) : List ParentBMS.Matrix :=
  stack.map (fun a => encode a.raw)

theorem FastRun.to_parent {stack : List ValidArray} {x y : Nat} (h : FastRun stack x y) :
    ParentBMS.FastRun (encodeStack stack) x y := by
  induction h with
  | done x => exact .done x
  | @zero a rest x y ha _ ih =>
    simpa only [encodeStack, List.map_cons, ha, encode, List.length_nil,
      List.range_zero, List.map_nil] using ParentBMS.FastRun.zero ih
  | @successor a rest x y ha hm _ ih =>
    have hne : encode a.raw ≠ [] := by
      intro he
      have : a.raw.length = 0 := by simpa using congrArg List.length he
      exact ha (List.eq_nil_of_length_eq_zero this)
    obtain ⟨s, last, he⟩ := ParentBMS.exists_last hne
    have hz := (encoded_tail_kind he).mpr hm
    subst last
    have hpred : encode (a.expand 0).raw = s := by rw [encode_expand_zero, he]; simp
    change ParentBMS.FastRun (encode a.raw :: encodeStack rest) x y
    rw [he]
    apply ParentBMS.FastRun.successor
    simpa only [encodeStack, List.map_append, List.map_replicate, hpred] using ih
  | @limit a rest x y r hm _ ih =>
    have hne : encode a.raw ≠ [] := by
      intro he
      have hl : a.raw.length = 0 := by simpa using congrArg List.length he
      simp [maximalParentRow, hl] at hm
    obtain ⟨s, last, he⟩ := ParentBMS.exists_last hne
    have hl : last ≠ [] := by
      intro hz
      have := (encoded_tail_kind he).mp hz
      simp_all
    apply ParentBMS.FastRun.limit ⟨s, last, he, hl⟩
    simpa only [encodeStack, List.map_cons, encode_expand] using ih

theorem of_parent_fastRun {pstack : List ParentBMS.Matrix} {x y : Nat}
    (h : ParentBMS.FastRun pstack x y) :
    ∀ stack, encodeStack stack = pstack → FastRun stack x y := by
  induction h with
  | done x =>
    intro stack he
    cases stack with
    | nil => exact .done x
    | cons a rest => simp [encodeStack] at he
  | @zero rest x y _ ih =>
    intro stack he
    cases stack with
    | nil => simp [encodeStack] at he
    | cons a tail =>
      obtain ⟨ha, ht⟩ := List.cons.inj he
      change encode a.raw = [] at ha
      change encodeStack tail = rest at ht
      have hz : a.raw = [] := by
        have : a.raw.length = 0 := by simpa using congrArg List.length ha
        exact List.eq_nil_of_length_eq_zero this
      exact .zero hz (ih tail ht)
  | @successor s rest x y _ ih =>
    intro stack he
    cases stack with
    | nil => simp [encodeStack] at he
    | cons a tail =>
      obtain ⟨ha, ht⟩ := List.cons.inj he
      change encode a.raw = s ++ [[]] at ha
      change encodeStack tail = rest at ht
      have hne := numeric_nonempty ha (by simp)
      have hm := (encoded_tail_kind ha).mp rfl
      apply FastRun.successor hne hm
      apply ih
      have hp : encode (a.expand 0).raw = s := by rw [encode_expand_zero, ha]; simp
      simp only [encodeStack, List.map_append, List.map_replicate, hp]
      exact congrArg (fun t => List.replicate (x + 1) s ++ t) ht
  | @limit s rest x y hs _ ih =>
    intro stack he
    cases stack with
    | nil => simp [encodeStack] at he
    | cons a tail =>
      obtain ⟨ha, ht⟩ := List.cons.inj he
      change encode a.raw = s at ha
      change encodeStack tail = rest at ht
      obtain ⟨front, last, hs, hl⟩ := hs
      have htail : encode a.raw = front ++ [last] := ha.trans hs
      cases hm : maximalParentRow a.raw with
      | none => exact False.elim (hl ((encoded_tail_kind htail).mpr hm))
      | some r =>
        apply FastRun.limit hm
        apply ih
        change encode (a.expand x).raw :: encodeStack tail = _
        rw [encode_expand, ha, ht]

theorem fastEval_iff (a : ValidArray) (x y : Nat) :
    FastEval a x y ↔ ParentBMS.FastEval (encode a.raw) x y :=
  ⟨FastRun.to_parent, fun h => of_parent_fastRun h [a] rfl⟩

def LambdaEval (x y : Nat) : Prop := FastEval (validSeed (x + 1)) x y

def FiniteLevelEval : Nat → Nat → Nat → Prop
  | 0 => LambdaEval
  | n + 1 => fun x y => ParentBMS.RelIter (FiniteLevelEval n) (x + 1) x y

def OmegaEval (x y : Nat) : Prop := FiniteLevelEval (x + 1) x y
def OmegaSuccessorEval (x y : Nat) : Prop := ParentBMS.RelIter OmegaEval (x + 1) x y

theorem lambdaEval_iff (x y : Nat) : LambdaEval x y ↔ ParentBMS.LambdaEval x y := by
  unfold LambdaEval ParentBMS.LambdaEval
  rw [fastEval_iff, raw_validSeed, encode_seed]

theorem relIter_map {R S : Nat → Nat → Prop} (hRS : ∀ a b, R a b → S a b)
    {n x y : Nat} (h : ParentBMS.RelIter R n x y) : ParentBMS.RelIter S n x y := by
  induction h with
  | zero x => exact .zero x
  | step _ hlast ih => exact .step ih (hRS _ _ hlast)

theorem relIter_congr {R S : Nat → Nat → Prop} (hRS : ∀ a b, R a b ↔ S a b)
    (n x y : Nat) : ParentBMS.RelIter R n x y ↔ ParentBMS.RelIter S n x y :=
  ⟨relIter_map (fun a b => (hRS a b).mp), relIter_map (fun a b => (hRS a b).mpr)⟩

theorem finiteLevelEval_iff (n x y : Nat) :
    FiniteLevelEval n x y ↔ ParentBMS.FiniteLevelEval n x y := by
  induction n generalizing x y with
  | zero => exact lambdaEval_iff x y
  | succ n ih => exact relIter_congr ih (x + 1) x y

theorem omegaSuccessorEval_iff (x y : Nat) :
    OmegaSuccessorEval x y ↔ ParentBMS.OmegaSuccessorEval x y :=
  relIter_congr (fun a b => finiteLevelEval_iff (a + 1) a b) (x + 1) x y

theorem omegaSuccessorEval_unique {x y z : Nat}
    (hy : OmegaSuccessorEval x y) (hz : OmegaSuccessorEval x z) : y = z :=
  ParentBMS.omegaSuccessorEval_unique ((omegaSuccessorEval_iff x y).mp hy)
    ((omegaSuccessorEval_iff x z).mp hz)

#print axioms fastEval_iff
#print axioms omegaSuccessorEval_iff

end LaverLowerBounds.NumericBMS
