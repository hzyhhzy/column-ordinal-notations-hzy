import Lean
import BTnSSBMS.Encoder

/- Closed finite regression equalities against the frozen research encoder.
These are kernel-checked examples, not a universal correspondence theorem. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace BTnSSBMS.Fixtures

-- Source dimension 1; seed[2] followed by [].
def input01 : NumericalExpr := (.cons [0] .nil (.cons [1] (.cons (.cons [2] (.cons .nil .nil) .nil) .nil) .nil))
theorem parents01 : Parents.annotate 1 [] input01 =
  (.cons ⟨[0], [none ]⟩ .nil (.cons ⟨[1], [some 0 ]⟩ (.cons (.cons ⟨[2], [some 1 ]⟩ (.cons .nil .nil) .nil) .nil) .nil)) := by decide_cbv
theorem encoded01 : Encoder.fromSource 1 input01 =
  [[0,0,0],[1,1,1],[2,2,2],[3,2,0],[4,1,1],[5,2,2],[6,2,0],[5,2,0],[2,2,0]] := by decide_cbv

-- Source dimension 1; seed[2] followed by [1].
def input02 : NumericalExpr := (.cons [0] .nil (.cons [1] (.cons (.cons [2] .nil (.cons [3] (.cons .nil .nil) .nil)) .nil) .nil))
theorem parents02 : Parents.annotate 1 [] input02 =
  (.cons ⟨[0], [none ]⟩ .nil (.cons ⟨[1], [some 0 ]⟩ (.cons (.cons ⟨[2], [some 1 ]⟩ .nil (.cons ⟨[3], [some 2 ]⟩ (.cons .nil .nil) .nil)) .nil) .nil)) := by decide_cbv
theorem encoded02 : Encoder.fromSource 1 input02 =
  [[0,0,0],[1,1,1],[2,2,2],[3,2,0],[4,0,0],[5,1,1],[6,2,2],[7,2,0],[6,2,0],[2,2,0]] := by decide_cbv

-- Source dimension 1; seed[2] followed by [2].
def input03 : NumericalExpr := (.cons [0] .nil (.cons [1] (.cons (.cons [2] .nil (.cons [3] (.cons (.cons [4] .nil (.cons [5] (.cons .nil .nil) .nil)) .nil) .nil)) .nil) .nil))
theorem parents03 : Parents.annotate 1 [] input03 =
  (.cons ⟨[0], [none ]⟩ .nil (.cons ⟨[1], [some 0 ]⟩ (.cons (.cons ⟨[2], [some 1 ]⟩ .nil (.cons ⟨[3], [some 2 ]⟩ (.cons (.cons ⟨[4], [some 3 ]⟩ .nil (.cons ⟨[5], [some 4 ]⟩ (.cons .nil .nil) .nil)) .nil) .nil)) .nil) .nil)) := by decide_cbv
theorem encoded03 : Encoder.fromSource 1 input03 =
  [[0,0,0],[1,1,1],[2,2,2],[3,2,0],[4,0,0],[5,1,1],[6,2,2],[7,2,0],[8,0,0],[9,1,1],[10,2,2],[11,2,0],[10,2,0],[6,2,0],[2,2,0]] := by decide_cbv

-- Source dimension 1; seed[2] followed by [2][1].
def input04 : NumericalExpr := (.cons [0] .nil (.cons [1] (.cons (.cons [2] .nil (.cons [3] (.cons (.cons [4] .nil (.cons [5] .nil .nil)) .nil) .nil)) .nil) .nil))
theorem parents04 : Parents.annotate 1 [] input04 =
  (.cons ⟨[0], [none ]⟩ .nil (.cons ⟨[1], [some 0 ]⟩ (.cons (.cons ⟨[2], [some 1 ]⟩ .nil (.cons ⟨[3], [some 2 ]⟩ (.cons (.cons ⟨[4], [some 3 ]⟩ .nil (.cons ⟨[5], [some 4 ]⟩ .nil .nil)) .nil) .nil)) .nil) .nil)) := by decide_cbv
theorem encoded04 : Encoder.fromSource 1 input04 =
  [[0,0,0],[1,1,1],[2,2,2],[3,2,0],[4,0,0],[5,1,1],[6,2,2],[7,2,0],[8,0,0],[9,0,0],[6,2,0],[2,2,0]] := by decide_cbv

-- Source dimension 1; seed[2] followed by [2][2].
def input05 : NumericalExpr := (.cons [0] .nil (.cons [1] (.cons (.cons [2] .nil (.cons [3] (.cons (.cons [4] .nil (.cons [5] .nil (.cons [6] .nil .nil))) .nil) .nil)) .nil) .nil))
theorem parents05 : Parents.annotate 1 [] input05 =
  (.cons ⟨[0], [none ]⟩ .nil (.cons ⟨[1], [some 0 ]⟩ (.cons (.cons ⟨[2], [some 1 ]⟩ .nil (.cons ⟨[3], [some 2 ]⟩ (.cons (.cons ⟨[4], [some 3 ]⟩ .nil (.cons ⟨[5], [some 4 ]⟩ .nil (.cons ⟨[6], [some 5 ]⟩ .nil .nil))) .nil) .nil)) .nil) .nil)) := by decide_cbv
theorem encoded05 : Encoder.fromSource 1 input05 =
  [[0,0,0],[1,1,1],[2,2,2],[3,2,0],[4,0,0],[5,1,1],[6,2,2],[7,2,0],[8,0,0],[9,0,0],[10,0,0],[6,2,0],[2,2,0]] := by decide_cbv

-- Source dimension 1; seed[2] followed by [1][0][1][1][0][1][0][2].
def input06 : NumericalExpr := .nil
theorem parents06 : Parents.annotate 1 [] input06 =
  .nil := by decide_cbv
theorem encoded06 : Encoder.fromSource 1 input06 =
  [] := by decide_cbv

-- Source dimension 2; seed[2] followed by [].
def input07 : NumericalExpr := (.cons [0,0] .nil (.cons [1,1] (.cons (.cons [2,2] (.cons .nil .nil) .nil) .nil) .nil))
theorem parents07 : Parents.annotate 2 [] input07 =
  (.cons ⟨[0,0], [none,none ]⟩ .nil (.cons ⟨[1,1], [some 0,some 0 ]⟩ (.cons (.cons ⟨[2,2], [some 1,some 1 ]⟩ (.cons .nil .nil) .nil) .nil) .nil)) := by decide_cbv
theorem encoded07 : Encoder.fromSource 2 input07 =
  [[0,0,0,0],[1,1,1,1],[2,2,2,2],[3,3,2,0],[4,4,1,1],[5,5,2,2],[6,6,2,0],[5,5,2,0],[2,2,2,0]] := by decide_cbv

-- Source dimension 2; seed[2] followed by [1].
def input08 : NumericalExpr := (.cons [0,0] .nil (.cons [1,1] (.cons (.cons [2,2] .nil (.cons [3,3] (.cons .nil .nil) .nil)) .nil) .nil))
theorem parents08 : Parents.annotate 2 [] input08 =
  (.cons ⟨[0,0], [none,none ]⟩ .nil (.cons ⟨[1,1], [some 0,some 0 ]⟩ (.cons (.cons ⟨[2,2], [some 1,some 1 ]⟩ .nil (.cons ⟨[3,3], [some 2,some 2 ]⟩ (.cons .nil .nil) .nil)) .nil) .nil)) := by decide_cbv
theorem encoded08 : Encoder.fromSource 2 input08 =
  [[0,0,0,0],[1,1,1,1],[2,2,2,2],[3,3,2,0],[4,4,0,0],[5,5,1,1],[6,6,2,2],[7,7,2,0],[6,6,2,0],[2,2,2,0]] := by decide_cbv

-- Source dimension 2; seed[2] followed by [2].
def input09 : NumericalExpr := (.cons [0,0] .nil (.cons [1,1] (.cons (.cons [2,2] .nil (.cons [3,3] (.cons (.cons [4,4] .nil (.cons [5,5] (.cons .nil .nil) .nil)) .nil) .nil)) .nil) .nil))
theorem parents09 : Parents.annotate 2 [] input09 =
  (.cons ⟨[0,0], [none,none ]⟩ .nil (.cons ⟨[1,1], [some 0,some 0 ]⟩ (.cons (.cons ⟨[2,2], [some 1,some 1 ]⟩ .nil (.cons ⟨[3,3], [some 2,some 2 ]⟩ (.cons (.cons ⟨[4,4], [some 3,some 3 ]⟩ .nil (.cons ⟨[5,5], [some 4,some 4 ]⟩ (.cons .nil .nil) .nil)) .nil) .nil)) .nil) .nil)) := by decide_cbv
theorem encoded09 : Encoder.fromSource 2 input09 =
  [[0,0,0,0],[1,1,1,1],[2,2,2,2],[3,3,2,0],[4,4,0,0],[5,5,1,1],[6,6,2,2],[7,7,2,0],[8,8,0,0],[9,9,1,1],[10,10,2,2],[11,11,2,0],[10,10,2,0],[6,6,2,0],[2,2,2,0]] := by decide_cbv

-- Source dimension 2; seed[2] followed by [2][1].
def input10 : NumericalExpr := (.cons [0,0] .nil (.cons [1,1] (.cons (.cons [2,2] .nil (.cons [3,3] (.cons (.cons [4,4] .nil (.cons [5,5] .nil .nil)) .nil) .nil)) .nil) .nil))
theorem parents10 : Parents.annotate 2 [] input10 =
  (.cons ⟨[0,0], [none,none ]⟩ .nil (.cons ⟨[1,1], [some 0,some 0 ]⟩ (.cons (.cons ⟨[2,2], [some 1,some 1 ]⟩ .nil (.cons ⟨[3,3], [some 2,some 2 ]⟩ (.cons (.cons ⟨[4,4], [some 3,some 3 ]⟩ .nil (.cons ⟨[5,5], [some 4,some 4 ]⟩ .nil .nil)) .nil) .nil)) .nil) .nil)) := by decide_cbv
theorem encoded10 : Encoder.fromSource 2 input10 =
  [[0,0,0,0],[1,1,1,1],[2,2,2,2],[3,3,2,0],[4,4,0,0],[5,5,1,1],[6,6,2,2],[7,7,2,0],[8,8,0,0],[9,9,0,0],[6,6,2,0],[2,2,2,0]] := by decide_cbv

-- Source dimension 2; seed[2] followed by [2][2].
def input11 : NumericalExpr := (.cons [0,0] .nil (.cons [1,1] (.cons (.cons [2,2] .nil (.cons [3,3] (.cons (.cons [4,4] .nil (.cons [5,5] .nil (.cons [6,6] .nil .nil))) .nil) .nil)) .nil) .nil))
theorem parents11 : Parents.annotate 2 [] input11 =
  (.cons ⟨[0,0], [none,none ]⟩ .nil (.cons ⟨[1,1], [some 0,some 0 ]⟩ (.cons (.cons ⟨[2,2], [some 1,some 1 ]⟩ .nil (.cons ⟨[3,3], [some 2,some 2 ]⟩ (.cons (.cons ⟨[4,4], [some 3,some 3 ]⟩ .nil (.cons ⟨[5,5], [some 4,some 4 ]⟩ .nil (.cons ⟨[6,6], [some 5,some 5 ]⟩ .nil .nil))) .nil) .nil)) .nil) .nil)) := by decide_cbv
theorem encoded11 : Encoder.fromSource 2 input11 =
  [[0,0,0,0],[1,1,1,1],[2,2,2,2],[3,3,2,0],[4,4,0,0],[5,5,1,1],[6,6,2,2],[7,7,2,0],[8,8,0,0],[9,9,0,0],[10,10,0,0],[6,6,2,0],[2,2,2,0]] := by decide_cbv

-- Source dimension 2; seed[2] followed by [1][0][1][1][0][1][0][2].
def input12 : NumericalExpr := (.cons [0,0] .nil (.cons [1,1] (.cons .nil (.cons .nil .nil)) .nil))
theorem parents12 : Parents.annotate 2 [] input12 =
  (.cons ⟨[0,0], [none,none ]⟩ .nil (.cons ⟨[1,1], [some 0,some 0 ]⟩ (.cons .nil (.cons .nil .nil)) .nil)) := by decide_cbv
theorem encoded12 : Encoder.fromSource 2 input12 =
  [[0,0,0,0],[1,1,1,1],[2,2,2,2],[3,3,2,0],[3,3,2,0],[2,2,2,0]] := by decide_cbv

-- Source dimension 3; seed[2] followed by [].
def input13 : NumericalExpr := (.cons [0,0,0] .nil (.cons [1,1,1] (.cons (.cons [2,2,2] (.cons .nil .nil) .nil) .nil) .nil))
theorem parents13 : Parents.annotate 3 [] input13 =
  (.cons ⟨[0,0,0], [none,none,none ]⟩ .nil (.cons ⟨[1,1,1], [some 0,some 0,some 0 ]⟩ (.cons (.cons ⟨[2,2,2], [some 1,some 1,some 1 ]⟩ (.cons .nil .nil) .nil) .nil) .nil)) := by decide_cbv
theorem encoded13 : Encoder.fromSource 3 input13 =
  [[0,0,0,0,0],[1,1,1,1,1],[2,2,2,2,2],[3,3,3,2,0],[4,4,4,1,1],[5,5,5,2,2],[6,6,6,2,0],[5,5,5,2,0],[2,2,2,2,0]] := by decide_cbv

-- Source dimension 3; seed[2] followed by [1].
def input14 : NumericalExpr := (.cons [0,0,0] .nil (.cons [1,1,1] (.cons (.cons [2,2,2] .nil (.cons [3,3,3] (.cons .nil .nil) .nil)) .nil) .nil))
theorem parents14 : Parents.annotate 3 [] input14 =
  (.cons ⟨[0,0,0], [none,none,none ]⟩ .nil (.cons ⟨[1,1,1], [some 0,some 0,some 0 ]⟩ (.cons (.cons ⟨[2,2,2], [some 1,some 1,some 1 ]⟩ .nil (.cons ⟨[3,3,3], [some 2,some 2,some 2 ]⟩ (.cons .nil .nil) .nil)) .nil) .nil)) := by decide_cbv
theorem encoded14 : Encoder.fromSource 3 input14 =
  [[0,0,0,0,0],[1,1,1,1,1],[2,2,2,2,2],[3,3,3,2,0],[4,4,4,0,0],[5,5,5,1,1],[6,6,6,2,2],[7,7,7,2,0],[6,6,6,2,0],[2,2,2,2,0]] := by decide_cbv

-- Source dimension 3; seed[2] followed by [2].
def input15 : NumericalExpr := (.cons [0,0,0] .nil (.cons [1,1,1] (.cons (.cons [2,2,2] .nil (.cons [3,3,3] (.cons (.cons [4,4,4] .nil (.cons [5,5,5] (.cons .nil .nil) .nil)) .nil) .nil)) .nil) .nil))
theorem parents15 : Parents.annotate 3 [] input15 =
  (.cons ⟨[0,0,0], [none,none,none ]⟩ .nil (.cons ⟨[1,1,1], [some 0,some 0,some 0 ]⟩ (.cons (.cons ⟨[2,2,2], [some 1,some 1,some 1 ]⟩ .nil (.cons ⟨[3,3,3], [some 2,some 2,some 2 ]⟩ (.cons (.cons ⟨[4,4,4], [some 3,some 3,some 3 ]⟩ .nil (.cons ⟨[5,5,5], [some 4,some 4,some 4 ]⟩ (.cons .nil .nil) .nil)) .nil) .nil)) .nil) .nil)) := by decide_cbv
theorem encoded15 : Encoder.fromSource 3 input15 =
  [[0,0,0,0,0],[1,1,1,1,1],[2,2,2,2,2],[3,3,3,2,0],[4,4,4,0,0],[5,5,5,1,1],[6,6,6,2,2],[7,7,7,2,0],[8,8,8,0,0],[9,9,9,1,1],[10,10,10,2,2],[11,11,11,2,0],[10,10,10,2,0],[6,6,6,2,0],[2,2,2,2,0]] := by decide_cbv

-- Source dimension 3; seed[2] followed by [2][1].
def input16 : NumericalExpr := (.cons [0,0,0] .nil (.cons [1,1,1] (.cons (.cons [2,2,2] .nil (.cons [3,3,3] (.cons (.cons [4,4,4] .nil (.cons [5,5,5] .nil .nil)) .nil) .nil)) .nil) .nil))
theorem parents16 : Parents.annotate 3 [] input16 =
  (.cons ⟨[0,0,0], [none,none,none ]⟩ .nil (.cons ⟨[1,1,1], [some 0,some 0,some 0 ]⟩ (.cons (.cons ⟨[2,2,2], [some 1,some 1,some 1 ]⟩ .nil (.cons ⟨[3,3,3], [some 2,some 2,some 2 ]⟩ (.cons (.cons ⟨[4,4,4], [some 3,some 3,some 3 ]⟩ .nil (.cons ⟨[5,5,5], [some 4,some 4,some 4 ]⟩ .nil .nil)) .nil) .nil)) .nil) .nil)) := by decide_cbv
theorem encoded16 : Encoder.fromSource 3 input16 =
  [[0,0,0,0,0],[1,1,1,1,1],[2,2,2,2,2],[3,3,3,2,0],[4,4,4,0,0],[5,5,5,1,1],[6,6,6,2,2],[7,7,7,2,0],[8,8,8,0,0],[9,9,9,0,0],[6,6,6,2,0],[2,2,2,2,0]] := by decide_cbv

-- Source dimension 3; seed[2] followed by [2][2].
def input17 : NumericalExpr := (.cons [0,0,0] .nil (.cons [1,1,1] (.cons (.cons [2,2,2] .nil (.cons [3,3,3] (.cons (.cons [4,4,4] .nil (.cons [5,5,5] .nil (.cons [6,6,6] .nil .nil))) .nil) .nil)) .nil) .nil))
theorem parents17 : Parents.annotate 3 [] input17 =
  (.cons ⟨[0,0,0], [none,none,none ]⟩ .nil (.cons ⟨[1,1,1], [some 0,some 0,some 0 ]⟩ (.cons (.cons ⟨[2,2,2], [some 1,some 1,some 1 ]⟩ .nil (.cons ⟨[3,3,3], [some 2,some 2,some 2 ]⟩ (.cons (.cons ⟨[4,4,4], [some 3,some 3,some 3 ]⟩ .nil (.cons ⟨[5,5,5], [some 4,some 4,some 4 ]⟩ .nil (.cons ⟨[6,6,6], [some 5,some 5,some 5 ]⟩ .nil .nil))) .nil) .nil)) .nil) .nil)) := by decide_cbv
theorem encoded17 : Encoder.fromSource 3 input17 =
  [[0,0,0,0,0],[1,1,1,1,1],[2,2,2,2,2],[3,3,3,2,0],[4,4,4,0,0],[5,5,5,1,1],[6,6,6,2,2],[7,7,7,2,0],[8,8,8,0,0],[9,9,9,0,0],[10,10,10,0,0],[6,6,6,2,0],[2,2,2,2,0]] := by decide_cbv

-- Source dimension 3; seed[2] followed by [1][0][1][1][0][1][0][2].
def input18 : NumericalExpr := (.cons [0,0,0] .nil (.cons [1,1,1] (.cons (.cons [2,1,1] (.cons (.cons [3,1,1] (.cons .nil .nil) .nil) .nil) .nil) .nil) .nil))
theorem parents18 : Parents.annotate 3 [] input18 =
  (.cons ⟨[0,0,0], [none,none,none ]⟩ .nil (.cons ⟨[1,1,1], [some 0,some 0,some 0 ]⟩ (.cons (.cons ⟨[2,1,1], [some 1,some 0,some 0 ]⟩ (.cons (.cons ⟨[3,1,1], [some 2,some 0,some 0 ]⟩ (.cons .nil .nil) .nil) .nil) .nil) .nil) .nil)) := by decide_cbv
theorem encoded18 : Encoder.fromSource 3 input18 =
  [[0,0,0,0,0],[1,1,1,1,1],[2,2,2,2,2],[3,3,3,2,0],[4,1,1,1,1],[5,2,2,2,2],[6,3,3,2,0],[7,1,1,1,1],[8,2,2,2,2],[9,3,3,2,0],[8,2,2,2,0],[5,2,2,2,0],[2,2,2,2,0]] := by decide_cbv

-- Source dimension 5; seed[2] followed by [].
def input19 : NumericalExpr := (.cons [0,0,0,0,0] .nil (.cons [1,1,1,1,1] (.cons (.cons [2,2,2,2,2] (.cons .nil .nil) .nil) .nil) .nil))
theorem parents19 : Parents.annotate 5 [] input19 =
  (.cons ⟨[0,0,0,0,0], [none,none,none,none,none ]⟩ .nil (.cons ⟨[1,1,1,1,1], [some 0,some 0,some 0,some 0,some 0 ]⟩ (.cons (.cons ⟨[2,2,2,2,2], [some 1,some 1,some 1,some 1,some 1 ]⟩ (.cons .nil .nil) .nil) .nil) .nil)) := by decide_cbv
theorem encoded19 : Encoder.fromSource 5 input19 =
  [[0,0,0,0,0,0,0],[1,1,1,1,1,1,1],[2,2,2,2,2,2,2],[3,3,3,3,3,2,0],[4,4,4,4,4,1,1],[5,5,5,5,5,2,2],[6,6,6,6,6,2,0],[5,5,5,5,5,2,0],[2,2,2,2,2,2,0]] := by decide_cbv

-- Source dimension 5; seed[2] followed by [1].
def input20 : NumericalExpr := (.cons [0,0,0,0,0] .nil (.cons [1,1,1,1,1] (.cons (.cons [2,2,2,2,2] .nil (.cons [3,3,3,3,3] (.cons .nil .nil) .nil)) .nil) .nil))
theorem parents20 : Parents.annotate 5 [] input20 =
  (.cons ⟨[0,0,0,0,0], [none,none,none,none,none ]⟩ .nil (.cons ⟨[1,1,1,1,1], [some 0,some 0,some 0,some 0,some 0 ]⟩ (.cons (.cons ⟨[2,2,2,2,2], [some 1,some 1,some 1,some 1,some 1 ]⟩ .nil (.cons ⟨[3,3,3,3,3], [some 2,some 2,some 2,some 2,some 2 ]⟩ (.cons .nil .nil) .nil)) .nil) .nil)) := by decide_cbv
theorem encoded20 : Encoder.fromSource 5 input20 =
  [[0,0,0,0,0,0,0],[1,1,1,1,1,1,1],[2,2,2,2,2,2,2],[3,3,3,3,3,2,0],[4,4,4,4,4,0,0],[5,5,5,5,5,1,1],[6,6,6,6,6,2,2],[7,7,7,7,7,2,0],[6,6,6,6,6,2,0],[2,2,2,2,2,2,0]] := by decide_cbv

-- Source dimension 5; seed[2] followed by [2].
def input21 : NumericalExpr := (.cons [0,0,0,0,0] .nil (.cons [1,1,1,1,1] (.cons (.cons [2,2,2,2,2] .nil (.cons [3,3,3,3,3] (.cons (.cons [4,4,4,4,4] .nil (.cons [5,5,5,5,5] (.cons .nil .nil) .nil)) .nil) .nil)) .nil) .nil))
theorem parents21 : Parents.annotate 5 [] input21 =
  (.cons ⟨[0,0,0,0,0], [none,none,none,none,none ]⟩ .nil (.cons ⟨[1,1,1,1,1], [some 0,some 0,some 0,some 0,some 0 ]⟩ (.cons (.cons ⟨[2,2,2,2,2], [some 1,some 1,some 1,some 1,some 1 ]⟩ .nil (.cons ⟨[3,3,3,3,3], [some 2,some 2,some 2,some 2,some 2 ]⟩ (.cons (.cons ⟨[4,4,4,4,4], [some 3,some 3,some 3,some 3,some 3 ]⟩ .nil (.cons ⟨[5,5,5,5,5], [some 4,some 4,some 4,some 4,some 4 ]⟩ (.cons .nil .nil) .nil)) .nil) .nil)) .nil) .nil)) := by decide_cbv
theorem encoded21 : Encoder.fromSource 5 input21 =
  [[0,0,0,0,0,0,0],[1,1,1,1,1,1,1],[2,2,2,2,2,2,2],[3,3,3,3,3,2,0],[4,4,4,4,4,0,0],[5,5,5,5,5,1,1],[6,6,6,6,6,2,2],[7,7,7,7,7,2,0],[8,8,8,8,8,0,0],[9,9,9,9,9,1,1],[10,10,10,10,10,2,2],[11,11,11,11,11,2,0],[10,10,10,10,10,2,0],[6,6,6,6,6,2,0],[2,2,2,2,2,2,0]] := by decide_cbv

-- Source dimension 5; seed[2] followed by [2][1].
def input22 : NumericalExpr := (.cons [0,0,0,0,0] .nil (.cons [1,1,1,1,1] (.cons (.cons [2,2,2,2,2] .nil (.cons [3,3,3,3,3] (.cons (.cons [4,4,4,4,4] .nil (.cons [5,5,5,5,5] .nil .nil)) .nil) .nil)) .nil) .nil))
theorem parents22 : Parents.annotate 5 [] input22 =
  (.cons ⟨[0,0,0,0,0], [none,none,none,none,none ]⟩ .nil (.cons ⟨[1,1,1,1,1], [some 0,some 0,some 0,some 0,some 0 ]⟩ (.cons (.cons ⟨[2,2,2,2,2], [some 1,some 1,some 1,some 1,some 1 ]⟩ .nil (.cons ⟨[3,3,3,3,3], [some 2,some 2,some 2,some 2,some 2 ]⟩ (.cons (.cons ⟨[4,4,4,4,4], [some 3,some 3,some 3,some 3,some 3 ]⟩ .nil (.cons ⟨[5,5,5,5,5], [some 4,some 4,some 4,some 4,some 4 ]⟩ .nil .nil)) .nil) .nil)) .nil) .nil)) := by decide_cbv
theorem encoded22 : Encoder.fromSource 5 input22 =
  [[0,0,0,0,0,0,0],[1,1,1,1,1,1,1],[2,2,2,2,2,2,2],[3,3,3,3,3,2,0],[4,4,4,4,4,0,0],[5,5,5,5,5,1,1],[6,6,6,6,6,2,2],[7,7,7,7,7,2,0],[8,8,8,8,8,0,0],[9,9,9,9,9,0,0],[6,6,6,6,6,2,0],[2,2,2,2,2,2,0]] := by decide_cbv

-- Source dimension 5; seed[2] followed by [2][2].
def input23 : NumericalExpr := (.cons [0,0,0,0,0] .nil (.cons [1,1,1,1,1] (.cons (.cons [2,2,2,2,2] .nil (.cons [3,3,3,3,3] (.cons (.cons [4,4,4,4,4] .nil (.cons [5,5,5,5,5] .nil (.cons [6,6,6,6,6] .nil .nil))) .nil) .nil)) .nil) .nil))
theorem parents23 : Parents.annotate 5 [] input23 =
  (.cons ⟨[0,0,0,0,0], [none,none,none,none,none ]⟩ .nil (.cons ⟨[1,1,1,1,1], [some 0,some 0,some 0,some 0,some 0 ]⟩ (.cons (.cons ⟨[2,2,2,2,2], [some 1,some 1,some 1,some 1,some 1 ]⟩ .nil (.cons ⟨[3,3,3,3,3], [some 2,some 2,some 2,some 2,some 2 ]⟩ (.cons (.cons ⟨[4,4,4,4,4], [some 3,some 3,some 3,some 3,some 3 ]⟩ .nil (.cons ⟨[5,5,5,5,5], [some 4,some 4,some 4,some 4,some 4 ]⟩ .nil (.cons ⟨[6,6,6,6,6], [some 5,some 5,some 5,some 5,some 5 ]⟩ .nil .nil))) .nil) .nil)) .nil) .nil)) := by decide_cbv
theorem encoded23 : Encoder.fromSource 5 input23 =
  [[0,0,0,0,0,0,0],[1,1,1,1,1,1,1],[2,2,2,2,2,2,2],[3,3,3,3,3,2,0],[4,4,4,4,4,0,0],[5,5,5,5,5,1,1],[6,6,6,6,6,2,2],[7,7,7,7,7,2,0],[8,8,8,8,8,0,0],[9,9,9,9,9,0,0],[10,10,10,10,10,0,0],[6,6,6,6,6,2,0],[2,2,2,2,2,2,0]] := by decide_cbv

-- Source dimension 5; seed[2] followed by [1][0][1][1][0][1][0][2].
def input24 : NumericalExpr := (.cons [0,0,0,0,0] .nil (.cons [1,1,1,1,1] (.cons (.cons [2,2,2,1,1] (.cons (.cons [3,3,3,1,1] (.cons .nil .nil) .nil) .nil) .nil) .nil) .nil))
theorem parents24 : Parents.annotate 5 [] input24 =
  (.cons ⟨[0,0,0,0,0], [none,none,none,none,none ]⟩ .nil (.cons ⟨[1,1,1,1,1], [some 0,some 0,some 0,some 0,some 0 ]⟩ (.cons (.cons ⟨[2,2,2,1,1], [some 1,some 1,some 1,some 0,some 0 ]⟩ (.cons (.cons ⟨[3,3,3,1,1], [some 2,some 2,some 2,some 0,some 0 ]⟩ (.cons .nil .nil) .nil) .nil) .nil) .nil) .nil)) := by decide_cbv
theorem encoded24 : Encoder.fromSource 5 input24 =
  [[0,0,0,0,0,0,0],[1,1,1,1,1,1,1],[2,2,2,2,2,2,2],[3,3,3,3,3,2,0],[4,4,4,1,1,1,1],[5,5,5,2,2,2,2],[6,6,6,3,3,2,0],[7,7,7,1,1,1,1],[8,8,8,2,2,2,2],[9,9,9,3,3,2,0],[8,8,8,2,2,2,0],[5,5,5,2,2,2,0],[2,2,2,2,2,2,0]] := by decide_cbv

end BTnSSBMS.Fixtures
