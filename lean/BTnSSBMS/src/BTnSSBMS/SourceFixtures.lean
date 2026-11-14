import Lean
import BTnSSBMS.SourceFS
import BTnSSBMS.Fixtures

/- Source paths checked by the executable Lean rule. These finite certificates
are not the general standard-domain invariant or an all-input equivalence proof. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace BTnSSBMS.SourceFixtures
open BTnSSBMS.Fixtures

theorem path01 : Source.run 1 (seed 1 2) [] = some input01 := by decide_cbv

theorem reachable01 : Source.Reachable 1 (seed 1 2) input01 :=
  Source.run_reachable 1 (seed 1 2) input01 [] path01

theorem path02 : Source.run 1 (seed 1 2) [1] = some input02 := by decide_cbv

theorem reachable02 : Source.Reachable 1 (seed 1 2) input02 :=
  Source.run_reachable 1 (seed 1 2) input02 [1] path02

theorem path03 : Source.run 1 (seed 1 2) [2] = some input03 := by decide_cbv

theorem reachable03 : Source.Reachable 1 (seed 1 2) input03 :=
  Source.run_reachable 1 (seed 1 2) input03 [2] path03

theorem path04 : Source.run 1 (seed 1 2) [2,1] = some input04 := by decide_cbv

theorem reachable04 : Source.Reachable 1 (seed 1 2) input04 :=
  Source.run_reachable 1 (seed 1 2) input04 [2,1] path04

theorem path05 : Source.run 1 (seed 1 2) [2,2] = some input05 := by decide_cbv

theorem reachable05 : Source.Reachable 1 (seed 1 2) input05 :=
  Source.run_reachable 1 (seed 1 2) input05 [2,2] path05

theorem path06 : Source.run 1 (seed 1 2) [1,0,1,1,0,1,0,2] = some input06 := by decide_cbv

theorem reachable06 : Source.Reachable 1 (seed 1 2) input06 :=
  Source.run_reachable 1 (seed 1 2) input06 [1,0,1,1,0,1,0,2] path06

theorem path07 : Source.run 2 (seed 2 2) [] = some input07 := by decide_cbv

theorem reachable07 : Source.Reachable 2 (seed 2 2) input07 :=
  Source.run_reachable 2 (seed 2 2) input07 [] path07

theorem path08 : Source.run 2 (seed 2 2) [1] = some input08 := by decide_cbv

theorem reachable08 : Source.Reachable 2 (seed 2 2) input08 :=
  Source.run_reachable 2 (seed 2 2) input08 [1] path08

theorem path09 : Source.run 2 (seed 2 2) [2] = some input09 := by decide_cbv

theorem reachable09 : Source.Reachable 2 (seed 2 2) input09 :=
  Source.run_reachable 2 (seed 2 2) input09 [2] path09

theorem path10 : Source.run 2 (seed 2 2) [2,1] = some input10 := by decide_cbv

theorem reachable10 : Source.Reachable 2 (seed 2 2) input10 :=
  Source.run_reachable 2 (seed 2 2) input10 [2,1] path10

theorem path11 : Source.run 2 (seed 2 2) [2,2] = some input11 := by decide_cbv

theorem reachable11 : Source.Reachable 2 (seed 2 2) input11 :=
  Source.run_reachable 2 (seed 2 2) input11 [2,2] path11

theorem path12 : Source.run 2 (seed 2 2) [1,0,1,1,0,1,0,2] = some input12 := by decide_cbv

theorem reachable12 : Source.Reachable 2 (seed 2 2) input12 :=
  Source.run_reachable 2 (seed 2 2) input12 [1,0,1,1,0,1,0,2] path12

theorem path13 : Source.run 3 (seed 3 2) [] = some input13 := by decide_cbv

theorem reachable13 : Source.Reachable 3 (seed 3 2) input13 :=
  Source.run_reachable 3 (seed 3 2) input13 [] path13

theorem path14 : Source.run 3 (seed 3 2) [1] = some input14 := by decide_cbv

theorem reachable14 : Source.Reachable 3 (seed 3 2) input14 :=
  Source.run_reachable 3 (seed 3 2) input14 [1] path14

theorem path15 : Source.run 3 (seed 3 2) [2] = some input15 := by decide_cbv

theorem reachable15 : Source.Reachable 3 (seed 3 2) input15 :=
  Source.run_reachable 3 (seed 3 2) input15 [2] path15

theorem path16 : Source.run 3 (seed 3 2) [2,1] = some input16 := by decide_cbv

theorem reachable16 : Source.Reachable 3 (seed 3 2) input16 :=
  Source.run_reachable 3 (seed 3 2) input16 [2,1] path16

theorem path17 : Source.run 3 (seed 3 2) [2,2] = some input17 := by decide_cbv

theorem reachable17 : Source.Reachable 3 (seed 3 2) input17 :=
  Source.run_reachable 3 (seed 3 2) input17 [2,2] path17

theorem path18 : Source.run 3 (seed 3 2) [1,0,1,1,0,1,0,2] = some input18 := by decide_cbv

theorem reachable18 : Source.Reachable 3 (seed 3 2) input18 :=
  Source.run_reachable 3 (seed 3 2) input18 [1,0,1,1,0,1,0,2] path18

theorem path19 : Source.run 5 (seed 5 2) [] = some input19 := by decide_cbv

theorem reachable19 : Source.Reachable 5 (seed 5 2) input19 :=
  Source.run_reachable 5 (seed 5 2) input19 [] path19

theorem path20 : Source.run 5 (seed 5 2) [1] = some input20 := by decide_cbv

theorem reachable20 : Source.Reachable 5 (seed 5 2) input20 :=
  Source.run_reachable 5 (seed 5 2) input20 [1] path20

theorem path21 : Source.run 5 (seed 5 2) [2] = some input21 := by decide_cbv

theorem reachable21 : Source.Reachable 5 (seed 5 2) input21 :=
  Source.run_reachable 5 (seed 5 2) input21 [2] path21

theorem path22 : Source.run 5 (seed 5 2) [2,1] = some input22 := by decide_cbv

theorem reachable22 : Source.Reachable 5 (seed 5 2) input22 :=
  Source.run_reachable 5 (seed 5 2) input22 [2,1] path22

theorem path23 : Source.run 5 (seed 5 2) [2,2] = some input23 := by decide_cbv

theorem reachable23 : Source.Reachable 5 (seed 5 2) input23 :=
  Source.run_reachable 5 (seed 5 2) input23 [2,2] path23

theorem path24 : Source.run 5 (seed 5 2) [1,0,1,1,0,1,0,2] = some input24 := by decide_cbv

theorem reachable24 : Source.Reachable 5 (seed 5 2) input24 :=
  Source.run_reachable 5 (seed 5 2) input24 [1,0,1,1,0,1,0,2] path24

end BTnSSBMS.SourceFixtures

