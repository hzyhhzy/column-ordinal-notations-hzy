import BTnSSBMS.EncoderOrderScope

/-!
Strict order for the actual complete C-minus output. The mutual proof
keeps real delimiter bounds: a following slot is below every unfinished
forest column, and the owner's close is below a following slot. Neither
bare prefix comparison nor a conditional recursive comparison is assumed.
-/
namespace BTnSSBMS.Encoder

mutual
  theorem encode_delimited_lt (d : Nat) (e f : NumericalExpr)
      (source : ParentContext) (visible : List Nat) (state : State d)
      (positive : 0 < d) (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
      (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
      (ordered : FramesOrdered state) (dense : FramesDense state) (good : VisibleGood state visible)
      (leftLegal : Source.FiniteLegal d source e) (rightLegal : Source.FiniteLegal d source f)
      (floor : Option (Nat × Nat)) (fence : OrderFence source visible state floor)
      (leftAbove : AboveFloor floor e) (rightAbove : AboveFloor floor f)
      (leftExit rightExit : Matrix) (low : ExitBelow (floor.map Prod.snd) leftExit)
      (lower : e.compare (listCompare Ord.compare) f = .lt) :
      matrixCompare (matrix (encode d (Parents.annotate d source e) visible state) ++ leftExit)
        (matrix (encode d (Parents.annotate d source f) visible state) ++ rightExit) = .lt := by
    cases e with
    | nil =>
      cases f with
      | nil => simp [Expr.compare] at lower
      | cons a hs tail =>
        exact empty_before_nonempty state positive coherent valid view fence a hs tail
          (fun s t eq => rightAbove s t eq a (by simp [Source.labels])) leftExit rightExit low
    | cons a hs tail =>
      cases f with
      | nil => simp [Expr.compare] at lower
      | cons b ks rest =>
        cases first : listCompare Ord.compare a b with
        | gt => simp [Expr.compare, first] at lower
        | lt =>
          exact ((encode_first_lt_of_numerical_heads state coherent valid view a b
            leftLegal.1 rightLegal.1 leftLegal.2.1 rightLegal.2.1 first hs ks tail rest).append leftExit rightExit).compare
        | eq =>
          have same : a = b := listCompare_eq_imp Ord.compare
            (fun _ _ h => Nat.compare_eq_eq.mp h) a b first
          subst b
          cases second : hs.compare (listCompare Ord.compare) ks with
          | gt => simp [Expr.compare, first, second] at lower
          | eq =>
            have sameH : hs = ks := Forests.compare_eq_imp (listCompare Ord.compare)
              (fun x y h => listCompare_eq_imp Ord.compare (fun _ _ h => Nat.compare_eq_eq.mp h) x y h)
              hs ks second
            subst ks
            let label := Parents.label d source a
            let attached := Parents.annotateForests d (source ++ [label]) hs
            let next := headState d label attached visible state
            have nextView := headState_view state positive coherent valid view a hs leftLegal.2.2.2.1.separated
            have nextOrder := encode_framesOrdered d (.cons label attached .nil) visible state ordered
            have nextDense := encode_framesDense d (.cons label attached .nil) visible state ordered dense
              (encode_noFallback d _ visible state good)
            have nextGood := headState_good d label attached visible state good
            have nextFence := fence.after_head state positive coherent valid view a hs
              (fun s t eq => leftAbove s t eq a (by simp [Source.labels]))
            have tails : tail.compare (listCompare Ord.compare) rest = .lt := by
              simpa only [Expr.compare, first, second] using lower
            have result := encode_delimited_lt d tail rest (source ++ [label])
              (visible ++ [next.length - 1]) next positive (Parents.coherent_append_label coherent a)
              (Parents.context_valid_append_label d source valid a) nextView nextOrder nextDense nextGood
              leftLegal.2.2.2.2 rightLegal.2.2.2.2 floor nextFence
              (fun s t eq col member => leftAbove s t eq col (by simp only [Source.labels, List.mem_cons]; exact Or.inr member))
              (fun s t eq col member => rightAbove s t eq col (by simp only [Source.labels, List.mem_cons]; exact Or.inr member))
              leftExit rightExit low tails
            simpa only [Parents.annotate, encode_split_head] using result
          | lt =>
            let label := Parents.label d source a
            let ah := Parents.annotateForests d (source ++ [label]) hs
            let ak := Parents.annotateForests d (source ++ [label]) ks
            let keyH := Keys.ofColumn d visible.length label ah
            let keyK := Keys.ofColumn d visible.length label ak
            let frame := frameAt state (representative visible label (d - 1))
            have keyStrict : Keys.compare keyH keyK = .lt := by
              dsimp only [keyH, keyK, label, ah, ak]
              rw [view.length, Keys.ofColumn_annotate_compare coherent valid a hs ks
                leftLegal.2.2.2.1 rightLegal.2.2.2.1]
              exact second
            have frameOrder := queried_frame_ordered ordered (representative visible label (d - 1))
            have frameDense := queried_frame_dense dense (representative visible label (d - 1))
            have frameZero := queried_frame_has_zero state visible good label (d - 1)
            rcases firstHeight_compare_cases frameOrder frameDense frameZero keyH keyK keyStrict with strict | gap
            · exact ((encode_first_lt_of_height d label ah ak _ _ visible state strict).append leftExit rightExit).compare
            · obtain ⟨freshH, freshK, sameGap⟩ := gap
              let below := smaller frame keyH
              let c := (base below).height
              let u := vector state visible label
              let guarded := emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 []
              have belowOrder := smaller_ordered frameOrder keyH
              have belowDense := frameDense_prefix frameDense (smaller_prefix frameOrder keyH)
              have belowZero := fresh_smaller_has_zero frameZero keyH freshH
              have guardOrder := framesOrdered_emit
                (framesOrdered_emit ordered u (c + 1) 1 [] (by simp [FrameOrdered]))
                (fun j => u j + 1) (c + 2) 2 [] (by simp [FrameOrdered])
              have guardDense := framesDense_emit
                (framesDense_emit dense u (c + 1) 1 [] empty_frame_dense)
                (fun j => u j + 1) (c + 2) 2 [] empty_frame_dense
              have guardGood : VisibleGood guarded visible :=
                visibleGood_extends ((emit_extends ..).trans (emit_extends ..)) good
              obtain ⟨extraL, shapeL, lowL⟩ := encode_cons_close_extension d label ah
                (Parents.annotate d (source ++ [label]) tail) visible state positive freshH leftExit
              obtain ⟨extraR, shapeR, _⟩ := encode_cons_close_extension d label ak
                (Parents.annotate d (source ++ [label]) rest) visible state positive freshK rightExit
              have result := encodeForests_delimited_lt d hs ks source a visible state guarded u
                (state.length + 1) c below positive coherent valid view
                (initial_numerical_gate state coherent valid view a c)
                belowOrder belowDense belowZero guardOrder guardDense guardGood
                leftLegal.2.2.2.1 rightLegal.2.2.2.1 extraL extraR lowL second
              change matrixCompare (matrix (encode d (.cons label ah _) visible state) ++ leftExit)
                (matrix (encode d (.cons label ak _) visible state) ++ rightExit) = .lt
              rw [shapeL, shapeR]
              dsimp only [keyH, keyK, frame] at sameGap
              rw [← sameGap]
              exact result

  theorem encodeForests_delimited_lt (d : Nat) (hs ks : Forests (List Nat))
      (source : ParentContext) (coordinates : List Nat) (visible : List Nat)
      (original state : State d) (u : Nat → Nat) (gate c : Nat) (below : List Binding)
      (positive : 0 < d) (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
      (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix original)) visible)
      (scope : NumericalGate d source coordinates visible original state u gate)
      (belowOrder : FrameOrdered below) (belowDense : FrameDense below) (belowZero : HasZero below)
      (ordered : FramesOrdered state) (dense : FramesDense state) (good : VisibleGood state visible)
      (leftLegal : Source.FiniteLegalForests d (source ++ [Parents.label d source coordinates])
        (coordinates[0]?.getD 0) hs)
      (rightLegal : Source.FiniteLegalForests d (source ++ [Parents.label d source coordinates])
        (coordinates[0]?.getD 0) ks)
      (leftExit rightExit : Matrix) (low : ExitBelow (some (u 0 + 1)) leftExit)
      (lower : hs.compare (listCompare Ord.compare) ks = .lt) :
      matrixCompare
        (matrix (encodeForests d (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs)
          visible u c below state) ++ leftExit)
        (matrix (encodeForests d (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) ks)
          visible u c below state) ++ rightExit) = .lt := by
    cases hs with
    | nil =>
      cases ks with
      | nil => simp [Forests.compare] at lower
      | cons k ks =>
        let context := source ++ [Parents.label d source coordinates]
        let slot := emit state (fun j => u j + 2) (c + 2) 0 below
        obtain ⟨added, shape⟩ := matrix_extension
          ((encode_extends d (Parents.annotate d context k) (visible ++ [state.length]) slot).trans
            (encodeForests_extends d (Parents.annotateForests d context ks) visible u c below _))
        change matrixCompare (matrix state ++ leftExit)
          (matrix (encodeForests d (Parents.annotateForests d context ks) visible u c below
            (encode d (Parents.annotate d context k) (visible ++ [state.length]) slot)) ++ rightExit) = .lt
        rw [shape]
        simp only [slot, matrix_emit, List.append_assoc, List.cons_append, List.nil_append,
          matrixCompare, listCompare_common_prefix (listCompare Ord.compare) columnCompare_self]
        cases leftExit with
        | nil => rfl
        | cons head more =>
          obtain ⟨t, eq, width, value⟩ := low
          have equal : u 0 + 1 = t := Option.some.inj eq
          have first : listCompare Ord.compare head (row d (fun j => u j + 2) (c + 2) 0) = .lt := by
            apply columnCompare_lt_of_zero width (by rw [row_width]; omega)
            rw [row_numerical_reading d _ (c + 2) 0 0 positive]
            omega
          simp only [listCompare, first]
    | cons h hs =>
      cases ks with
      | nil => simp [Forests.compare] at lower
      | cons k ks =>
        let context := source ++ [Parents.label d source coordinates]
        let slot := emit state (fun j => u j + 2) (c + 2) 0 below
        let positions := visible ++ [state.length]
        have contextCoherent := Parents.coherent_append_label coherent coordinates
        have contextValid := Parents.context_valid_append_label d source valid coordinates
        have slotView := scope.slot_view valid view (c + 2) below
        have slotOrder := framesOrdered_emit ordered (fun j => u j + 2) (c + 2) 0 below belowOrder
        have slotDense := framesDense_emit dense (fun j => u j + 2) (c + 2) 0 below belowDense
        have slotGood := visibleGood_emit state visible good (fun j => u j + 2) (c + 2) 0 below belowZero
        cases first : h.compare (listCompare Ord.compare) k with
        | gt => simp [Forests.compare, first] at lower
        | eq =>
          have same : h = k := Expr.compare_eq_imp (listCompare Ord.compare)
            (fun x y h => listCompare_eq_imp Ord.compare (fun _ _ h => Nat.compare_eq_eq.mp h) x y h) h k first
          subst k
          let next := encode d (Parents.annotate d context h) positions slot
          obtain ⟨finalVisible, extended, nextView⟩ := encode_numerical_view d h context positions slot
            positive contextCoherent contextValid slotView leftLegal.2.1.separated
          have nextScope := scope.after_forest positive coherent valid view.length (c + 2) below
            (Source.labels h) (encode_extends d _ _ _) extended leftLegal.1 nextView
          have nextOrder := encode_framesOrdered d (Parents.annotate d context h) positions slot slotOrder
          have nextDense := encode_framesDense d (Parents.annotate d context h) positions slot slotOrder slotDense
            (encode_noFallback d _ positions slot slotGood)
          have nextGood : VisibleGood next visible :=
            visibleGood_extends ((emit_extends ..).trans (encode_extends d _ _ _)) good
          have tails : hs.compare (listCompare Ord.compare) ks = .lt := by
            simpa only [Forests.compare, first] using lower
          exact encodeForests_delimited_lt d hs ks source coordinates visible original next u gate c below
            positive coherent valid view nextScope belowOrder belowDense belowZero nextOrder nextDense nextGood
            leftLegal.2.2 rightLegal.2.2 leftExit rightExit low tails
        | lt =>
          obtain ⟨extraL, shapeL, lowL⟩ := encodeForests_extension_low d
            (Parents.annotateForests d context hs) visible u c below
            (encode d (Parents.annotate d context h) positions slot) positive leftExit
            (low.mono (by omega : u 0 + 1 ≤ u 0 + 2))
          obtain ⟨addedR, shapeR⟩ := matrix_extension (encodeForests_extends d
            (Parents.annotateForests d context ks) visible u c below
            (encode d (Parents.annotate d context k) positions slot))
          have slotFence : OrderFence context positions slot
              (some (coordinates[0]?.getD 0, u 0 + 2)) := by
            refine ⟨source.length, by simp [context], ?_, ?_, ?_⟩
            · exact Parents.reading_append_label d source coordinates 0
            · simp only [context, List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel]
              exact .refl _
            · dsimp only [positions, slot]
              rw [← view.length, Parents.point_append_last]
              exact emitted_numerical_value state (fun j => u j + 2) (c + 2) 0 below 0 positive
          have aboveH : AboveFloor (some (coordinates[0]?.getD 0, u 0 + 2)) h := by
            intro s t eq col member
            have same := Option.some.inj eq
            cases same
            exact leftLegal.1 col member
          have aboveK : AboveFloor (some (coordinates[0]?.getD 0, u 0 + 2)) k := by
            intro s t eq col member
            have same := Option.some.inj eq
            cases same
            exact rightLegal.1 col member
          have result := encode_delimited_lt d h k context positions slot positive contextCoherent contextValid
            slotView slotOrder slotDense slotGood leftLegal.2.1 rightLegal.2.1
            (some (coordinates[0]?.getD 0, u 0 + 2)) slotFence aboveH aboveK extraL
            (addedR ++ rightExit) lowL first
          change matrixCompare
            (matrix (encodeForests d (Parents.annotateForests d context hs) visible u c below
              (encode d (Parents.annotate d context h) positions slot)) ++ leftExit)
            (matrix (encodeForests d (Parents.annotateForests d context ks) visible u c below
              (encode d (Parents.annotate d context k) positions slot)) ++ rightExit) = .lt
          rw [shapeL, shapeR, List.append_assoc]
          exact result
end

/-- Complete strict order at a common finite legal entry, including all
fresh-key collisions, forest-prefix exits and restored outer tails. -/
theorem encode_strict_order (d : Nat) (e f : NumericalExpr)
    (source : ParentContext) (visible : List Nat) (state : State d)
    (positive : 0 < d) (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (ordered : FramesOrdered state) (dense : FramesDense state) (good : VisibleGood state visible)
    (leftLegal : Source.FiniteLegal d source e) (rightLegal : Source.FiniteLegal d source f)
    (lower : e.compare (listCompare Ord.compare) f = .lt) :
    matrixCompare (matrix (encode d (Parents.annotate d source e) visible state))
      (matrix (encode d (Parents.annotate d source f) visible state)) = .lt := by
  have result := encode_delimited_lt d e f source visible state positive coherent valid view
    ordered dense good leftLegal rightLegal none (by trivial)
    (by intro s t eq; cases eq) (by intro s t eq; cases eq) [] [] (by trivial) lower
  simpa only [List.append_nil] using result

theorem source_strict_order (d : Nat) (e f : NumericalExpr) (positive : 0 < d)
    (leftLegal : Source.FiniteLegal d [] e) (rightLegal : Source.FiniteLegal d [] f)
    (lower : e.compare (listCompare Ord.compare) f = .lt) :
    matrixCompare (fromSource d e) (fromSource d f) = .lt :=
  encode_strict_order d e f [] [] [] positive (Parents.empty_coherent d) Parents.empty_context_valid
    (Parents.empty_numerical_view d) (by intro col member; simp at member)
    (by intro col member; simp at member) (by intro p member; simp at member) leftLegal rightLegal lower

end BTnSSBMS.Encoder
