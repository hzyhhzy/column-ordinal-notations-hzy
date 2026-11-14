import BTnSSBMS.Keys
import Init.Data.List.MapIdx

/-!
Executable strong BT*(-1)Y-nSS v2, with no imposed iteration or size limit.

The mutually recursive walks follow strict subtrees. Copy construction
recurses on the given fundamental-sequence index, never on generated size.
Missing roots on malformed raw input are reported by `none`, not silently
replaced by zero. SourceTotality proves that this never happens on finite-legal
positive-dimensional inputs and hence on the seed-reachable domain. The
stronger block-order invariants remain separate obligations.
-/
namespace BTnSSBMS.Source

def length : Expr α → Nat
  | .nil => 0
  | .cons _ _ t => 1 + length t

def last? : Expr α → Option (α × Forests α)
  | .nil => none
  | .cons a hs .nil => some (a, hs)
  | .cons _ _ t@(.cons ..) => last? t

def lastForest? : Forests α → Option (Expr α)
  | .nil => none
  | .cons h .nil => some h
  | .cons _ hs@(.cons ..) => lastForest? hs

def dropLast : Expr α → Expr α
  | .nil => .nil
  | .cons _ _ .nil => .nil
  | .cons a hs t@(.cons ..) => .cons a hs (dropLast t)

def dropLastForest : Forests α → Forests α
  | .nil => .nil
  | .cons _ .nil => .nil
  | .cons h hs@(.cons ..) => .cons h (dropLastForest hs)

def appendForests : Forests α → Forests α → Forests α
  | .nil, rest => rest
  | .cons h hs, rest => .cons h (appendForests hs rest)

def repeatForest (h : Expr α) : Nat → Forests α
  | 0 => .nil
  | n + 1 => .cons h (repeatForest h n)

def drop : Nat → Expr α → Expr α
  | 0, e => e
  | _, .nil => .nil
  | n + 1, .cons _ _ t => drop n t

def labels : Expr α → List α
  | .nil => []
  | .cons a _ t => a :: labels t

mutual
  def innerSpine : Expr α → List (Expr α)
    | .nil => []
    | .cons _ hs .nil => forestSpine hs
    | .cons _ _ t@(.cons ..) => innerSpine t
  def forestSpine : Forests α → List (Expr α)
    | .nil => []
    | .cons h .nil => h :: innerSpine h
    | .cons _ hs@(.cons ..) => forestSpine hs
end

def spine (e : Expr α) : List (Expr α) := e :: innerSpine e

def zeroColumn (c : List Nat × Forests (List Nat)) : Bool :=
  c.1.all (· == 0) && match c.2 with | .nil => true | _ => false

def specialColumn (c : List Nat × Forests (List Nat)) : Bool :=
  match lastForest? c.2 |>.bind last? with
  | none => false
  | some (a, hs) =>
    a.head? == some (c.1.headD 0 + 1) && (a.drop 1).all (· == 0) &&
      (match hs with | .nil => true | _ => false)

def stopping (e : NumericalExpr) : Bool :=
  match last? e with
  | none => true
  | some c => specialColumn c || match lastForest? c.2 with
      | none => true
      | some .nil => true
      | _ => false

abbrev KeyContext := List (ParentLabel × Key)

def topSearch (d : Nat) (context : KeyContext) (owners : List Nat)
    (key : Key) : Nat → Option Nat
  | 0 => none
  | p + 1 => match context[p]? with
    | none => none
    | some (a, k) =>
      if !owners.contains p && Keys.compare k key == .lt then some p
      else match a.parents[d - 1]?.join with
        | none => none
        | some q => if q < p then topSearch d context owners key (q + 1) else none
termination_by cursor => cursor

mutual
  def fillTop (d : Nat) (context : KeyContext) (owners : List Nat) : ParentExpr → ParentExpr
    | .nil => .nil
    | .cons a hs t =>
      let key := Keys.ofColumn d context.length a hs
      let top := topSearch d context owners key (a.parents[d - 1]?.join |>.map (· + 1) |>.getD 0)
      let a' := { a with parents := a.parents ++ [top] }
      let next := context ++ [(a', key)]
      .cons a' (fillTopForests d next (owners ++ [context.length]) hs) (fillTop d next owners t)
  def fillTopForests (d : Nat) (context : KeyContext) (owners : List Nat) :
      Forests ParentLabel → Forests ParentLabel
    | .nil => .nil
    | .cons h hs => .cons (fillTop d context owners h) (fillTopForests d context owners hs)
end

def parents (d : Nat) (e : NumericalExpr) : ParentExpr :=
  fillTop d [] [] (Parents.annotate d [] e)

abbrev MarkedExpr := Expr (List Nat × Nat)

mutual
  def mark (b root : Nat) (history : List Nat) : ParentExpr → MarkedExpr
    | .nil => .nil
    | .cons a hs t =>
      let i := history.length
      let threshold := if i < root then 0 else if i = root then b else Keys.threshold b root history a
      let next := history ++ [threshold]
      let skip := i < root && match t with | .nil => false | _ => true
      let attached := if skip then hs.map (fun a => (a.coordinates, 0)) else markForests b root next hs
      .cons (a.coordinates, threshold) attached (mark b root next t)
  def markForests (b root : Nat) (history : List Nat) : Forests ParentLabel → Forests (List Nat × Nat)
    | .nil => .nil
    | .cons h hs => .cons (mark b root history h) (markForests b root history hs)
end

def highestParent (offset : Nat) : List (Option Nat) → Option (Nat × Nat)
  | [] => none
  | p :: ps => match highestParent (offset + 1) ps with
    | some hit => some hit
    | none => p.map fun r => (offset, r)

def locateRoot : List (Expr α) → Nat → Option (Nat × Nat)
  | [], _ => none
  | f :: fs, r =>
    if r < length f then some (0, r)
    else (locateRoot fs (r - length f)).map fun (depth, i) => (depth + 1, i)

def modifyLast (f : α × Forests α → α × Forests α) : Expr α → Expr α
  | .nil => .nil
  | .cons a hs .nil => let (b, ks) := f (a, hs); .cons b ks .nil
  | .cons a hs t@(.cons ..) => .cons a hs (modifyLast f t)

def modifyLastForest (f : Expr α → Expr α) : Forests α → Forests α
  | .nil => .nil
  | .cons h .nil => .cons (f h) .nil
  | .cons h hs@(.cons ..) => .cons h (modifyLastForest f hs)

def special (index : Nat) : Nat → NumericalExpr → NumericalExpr
  | 0, e => modifyLast (fun (a, hs) =>
      (a, appendForests (dropLastForest hs) (repeatForest (dropLast (lastForest? hs |>.getD .nil)) index))) e
  | depth + 1, e => modifyLast (fun (a, hs) => (a, modifyLastForest (special index depth) hs)) e

def shift (a : List Nat) (threshold : Nat) (delta : List Nat) (phase : Nat) : List Nat :=
  a.mapIdx fun j v => v + if j < threshold then delta[j]?.getD 0 * phase else 0

mutual
  def ascendReplace (e : MarkedExpr) (tail : NumericalExpr)
      (hole : Option Nat) (delta : List Nat) (phase : Nat) : NumericalExpr :=
    match e with
    | .nil => .nil
    | .cons (a, t) hs rest =>
      let final := match rest with | .nil => true | _ => false
      if final && hole == some 0 then tail
      else
        let inner := if final then hole.map (· - 1) else none
        .cons (shift a t delta phase) (ascendForests hs tail inner delta phase)
          (ascendReplace rest tail hole delta phase)
  def ascendForests (hs : Forests (List Nat × Nat)) (tail : NumericalExpr)
      (hole : Option Nat) (delta : List Nat) (phase : Nat) : Forests (List Nat) :=
    match hs with
    | .nil => .nil
    | .cons h rest =>
      let final := match rest with | .nil => true | _ => false
      .cons (ascendReplace h tail (if final then hole else none) delta phase)
        (ascendForests rest tail hole delta phase)
end

def setFirstForests (hs : Forests (List Nat)) : NumericalExpr → NumericalExpr
  | .nil => .nil
  | .cons a _ rest => .cons a hs rest

def copies (part : MarkedExpr) (hole : Nat) (delta : List Nat)
    (donation : Option (Forests (List Nat × Nat))) : Nat → Nat → NumericalExpr
  | 0, _ => .nil
  | count + 1, phase =>
    let tail := copies part hole delta donation count (phase + 1)
    let result := ascendReplace part tail (some hole) delta phase
    match donation with
    | none => result
    | some hs => setFirstForests (ascendForests hs .nil none delta (phase - 1)) result

def expand? (d : Nat) (e : NumericalExpr) (index : Nat) : Option NumericalExpr := do
  match last? e with
  | none => return .nil
  | some last =>
    if zeroColumn last then return dropLast e
    let sp := spine e
    let tLayer := sp.findIdx stopping
    let stop ← sp[tLayer]?
    let stopColumn ← last? stop
    if specialColumn stopColumn then return special index tLayer e
    let p := parents d e
    let stopP ← (spine p)[tLayer]?
    let stopLabel ← last? stopP
    let (b, root) ← highestParent 0 stopLabel.1.parents
    let (rLayer, ri) ← locateRoot sp root
    let visible := (sp.take (tLayer + 1)).flatMap labels
    let rootCol ← visible[root]?
    let delta := (List.range b).map fun j => stopColumn.1[j]?.getD 0 - rootCol[j]?.getD 0
    let marked := mark b root [] p
    let msp := spine marked
    let rootPart ← msp[rLayer]?
    let tailPart ← msp[tLayer]?
    let tailColumn ← last? tailPart
    let donation := if b = d then some (dropLastForest tailColumn.2) else none
    let result := copies (drop ri rootPart) (tLayer - rLayer) delta donation index 1
    return ascendReplace marked result (some tLayer) delta 0

/-- Finite actual computations, not membership defined by desired invariants.
Root totality is established later in SourceTotality. Universal correspondence
to the frozen external implementation is separate from these path certificates. -/
inductive Reachable (d : Nat) (start : NumericalExpr) : NumericalExpr → Prop where
  | refl : Reachable d start start
  | step {e f} : Reachable d start e → expand? d e n = some f → Reachable d start f

def Standard (d : Nat) (e : NumericalExpr) : Prop := ∃ k, Reachable d (seed d k) e

theorem seed_standard (d k : Nat) : Standard d (seed d k) := ⟨k, .refl⟩

theorem standard_closed (d : Nat) (e f : NumericalExpr) (n : Nat)
    (h : Standard d e) (edge : expand? d e n = some f) : Standard d f := by
  obtain ⟨k, path⟩ := h
  exact ⟨k, .step path edge⟩

def run (d : Nat) (e : NumericalExpr) : List Nat → Option NumericalExpr
  | [] => some e
  | n :: ns => (expand? d e n).bind fun next => run d next ns

theorem run_reachable (d : Nat) (e f : NumericalExpr) (route : List Nat)
    (h : run d e route = some f) : Reachable d e f := by
  have trans {a b c : NumericalExpr} (ab : Reachable d a b) (bc : Reachable d b c) :
      Reachable d a c := by
    induction bc with
    | refl => exact ab
    | step path edge ih => exact .step ih edge
  induction route generalizing e with
  | nil => simp only [run, Option.some.injEq] at h; subst f; exact .refl
  | cons n ns ih =>
    simp only [run, Option.bind_eq_some_iff] at h
    obtain ⟨g, edge, rest⟩ := h
    exact trans (.step .refl edge) (ih g rest)

theorem expand_empty (d index : Nat) : expand? d .nil index = some .nil := by
  simp [expand?, last?]

end BTnSSBMS.Source
