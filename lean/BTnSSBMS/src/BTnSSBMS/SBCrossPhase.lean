import BTnSSBMS.SourceSB

/-!
Numerical barriers for the source SB cross-copy classification.
The barrier is an actual lower-row ancestor, not just an intervening
column in the printed expression. The conclusions use the executable
parent search. They do not assert that every copy seam has this shape.
-/
namespace BTnSSBMS.Parents

/-- A lower-valued ancestor stops the next-row search before it can
reach the parent of an earlier column. -/
theorem parent_distinct_before_barrier {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context)
    {row earlier barrier endpoint : Nat} (room : row + 1 < d)
    (inside : endpoint < context.length) (before : earlier < barrier)
    (strict : barrier ≠ endpoint) (path : Ancestor context row barrier endpoint)
    (lower : reading context (row + 1) barrier < reading context (row + 1) endpoint) :
    parent context (row + 1) earlier ≠ parent context (row + 1) endpoint := by
  intro shared
  obtain ⟨p, selected, retained⟩ := higher_parent_within coherent valid room inside path strict lower
  have oldSelected : parent context (row + 1) earlier = some p := shared.trans selected
  have oldBound := parent_earlier valid oldSelected
  have barrierBound := retained.le valid
  omega

theorem shared_parent_barrier_floor {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context)
    {row earlier barrier endpoint : Nat} (room : row + 1 < d)
    (inside : endpoint < context.length) (before : earlier < barrier)
    (strict : barrier ≠ endpoint) (path : Ancestor context row barrier endpoint)
    (shared : parent context (row + 1) earlier = parent context (row + 1) endpoint) :
    reading context (row + 1) endpoint ≤ reading context (row + 1) barrier := by
  by_cases lower : reading context (row + 1) endpoint ≤ reading context (row + 1) barrier
  · exact lower
  · exact False.elim (parent_distinct_before_barrier coherent valid room inside before strict path
      (by omega) shared)

theorem UnitSteps.shared_parent_reading {d : Nat} {context : ParentContext}
    (unit : UnitSteps d context) {row earlier endpoint : Nat}
    (room : row < d) (oldInside : earlier < context.length) (inside : endpoint < context.length)
    (shared : parent context row earlier = parent context row endpoint) :
    reading context row earlier = reading context row endpoint := by
  rw [unit earlier oldInside row room, unit endpoint inside row room, shared]

/-- Under actual unit increments, a shared-parent earlier column cannot
have a larger next-row coordinate than an intervening ancestor barrier. -/
theorem shared_parent_barrier_floor_left {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context) (unit : UnitSteps d context)
    {row earlier barrier endpoint : Nat} (room : row + 1 < d)
    (inside : endpoint < context.length) (before : earlier < barrier)
    (strict : barrier ≠ endpoint) (path : Ancestor context row barrier endpoint)
    (shared : parent context (row + 1) earlier = parent context (row + 1) endpoint) :
    reading context (row + 1) earlier ≤ reading context (row + 1) barrier := by
  have barrierBound := path.le valid
  rw [unit.shared_parent_reading room (by omega) inside shared]
  exact shared_parent_barrier_floor coherent valid room inside before strict path shared

end BTnSSBMS.Parents

namespace BTnSSBMS.Source

/-- The preceding barrier test in the actual context used by HeadSB.
It excludes an earlier-copy ordinary root whenever the later copy root
has a smaller tested coordinate. No parent pointers are supplied by hand. -/
theorem sb_shared_parent_barrier_floor {d cut root barrier : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (a : List Nat) (unit : Parents.UnitSteps d (context ++ [Parents.label d context a]))
    (positive : 0 < cut) (room : cut < d) (before : root < barrier)
    (inside : barrier < context.length)
    (path : Parents.Ancestor (context ++ [Parents.label d context a]) (cut - 1) barrier context.length)
    (shared : (Parents.label d context a).parents[cut]?.join = Parents.parent context cut root) :
    Parents.reading context cut root ≤ Parents.reading context cut barrier := by
  have rowEq : cut - 1 + 1 = cut := by omega
  have nextCoherent := Parents.coherent_append_label coherent a
  have nextValid := Parents.context_valid_append_label d context valid a
  have nextShared : Parents.parent (context ++ [Parents.label d context a]) cut root =
      Parents.parent (context ++ [Parents.label d context a]) cut context.length := by
    rw [← Parents.parent_prefix_eq (List.prefix_append context [Parents.label d context a]) cut root (by omega),
      Parents.append_label_parent, shared]
  have lower := Parents.shared_parent_barrier_floor_left nextCoherent nextValid unit
    (row := cut - 1) (earlier := root) (barrier := barrier) (endpoint := context.length)
    (by omega) (by simp) before (by omega) path (by simpa only [rowEq] using nextShared)
  simpa only [rowEq,
    ← Parents.reading_prefix (List.prefix_append context [Parents.label d context a]) cut root (by omega),
    ← Parents.reading_prefix (List.prefix_append context [Parents.label d context a]) cut barrier inside] using lower

/-- Once an actual low-valued barrier is available, all earlier roots
are impossible SB partners. Only roots at or after the barrier need a
block comparison. Constructing such barriers at every seam is separate. -/
theorem headSB_of_parent_barrier {d cut barrier : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (history : List NumericalExpr) (a : List Nat) (hs : Forests (List Nat)) (rest : NumericalExpr)
    (inside : barrier < context.length)
    (path : Parents.Ancestor (context ++ [Parents.label d context a]) (cut - 1) barrier context.length)
    (lower : Parents.reading context cut barrier < a[cut]?.getD 0)
    (later : 0 < cut → cut < d → ∀ root, barrier ≤ root → root < context.length →
      Parents.Ancestor (context ++ [Parents.label d context a]) (cut - 1) root context.length →
      (Parents.label d context a).parents[cut]?.join = Parents.parent context cut root →
      ExprLE (rootBlock (.cons a hs rest))
        (rebaseBlock d cut context root a (history[root]?.getD .nil))) :
    HeadSB d cut context history a hs rest := by
  intro positive room root rootInside rootPath shared
  by_cases after : barrier ≤ root
  · exact later positive room root after rootInside rootPath shared
  · have rowEq : cut - 1 + 1 = cut := by omega
    have nextCoherent := Parents.coherent_append_label coherent a
    have nextValid := Parents.context_valid_append_label d context valid a
    have distinct := Parents.parent_distinct_before_barrier nextCoherent nextValid
      (row := cut - 1) (earlier := root) (barrier := barrier) (endpoint := context.length)
      (by omega) (by simp) (by omega) (by omega) path
      (by simpa only [rowEq, Parents.reading_append_label,
        ← Parents.reading_prefix (List.prefix_append context [Parents.label d context a]) cut barrier inside] using lower)
    apply False.elim
    apply distinct
    rw [rowEq, ← Parents.parent_prefix_eq (List.prefix_append context [Parents.label d context a]) cut root rootInside,
      Parents.append_label_parent, shared]

end BTnSSBMS.Source
