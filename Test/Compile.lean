import Lustrean

set_option trace.Lustrean.Elab.Compile true

/--
trace: [Lustrean.Elab.Compile] ✅️ elabExpr
    node inc(x) = o
      where ⏎
        o = (+ x [1, 1])
    ⇒
    some (([node f_0 where
        step := [0, 0] ⇒ f_2,
      node f_1 where
        skip ⇒ f_13,
      node f_2 where
        x_2 := nil ⇒ f_3,
      node f_3 where
        x_3 := x_2 ⇒ f_4,
      node f_4 where
        x_1 := [-∞, ∞] ⇒ f_5,
      node f_5 where
        x_2 := nil ⇒ f_6,
      node f_6 where
        x_2 := (x_1 + [1, 1]) ⇒ f_7,
      node f_7 where
        skip ⇒ f_6
        skip ⇒ f_1
        step := (step + [1, 1]) ⇒ f_8,
      node f_8 where
        x_3 := x_2 ⇒ f_9,
      node f_9 where
        x_1 := [-∞, ∞] ⇒ f_10,
      node f_10 where
        x_2 := nil ⇒ f_11,
      node f_11 where
        x_2 := (x_1 + [1, 1]) ⇒ f_12,
      node f_12 where
        step := (step + [1, 1]) ⇒ f_8
        skip ⇒ f_11
        skip ⇒ f_13,
      node f_13 where
        ],
     [2]))
[Lustrean.Elab.Compile] ✅️ elabExpr
    node plus2(x) = o
      where ⏎
        o.0.x.1.x = x
        o.0.x.1.o = (+ o.0.x.1.x [1, 1])
        o.0.x = o.0.x.1.o
        o.0.o = (+ o.0.x [1, 1])
        o = o.0.o
    ⇒
    some (([node f_0 where
        step := [0, 0] ⇒ f_2,
      node f_1 where
        skip ⇒ f_41,
      node f_2 where
        x_2 := nil ⇒ f_3,
      node f_3 where
        x_3 := nil ⇒ f_4,
      node f_4 where
        x_4 := nil ⇒ f_5,
      node f_5 where
        x_5 := nil ⇒ f_6,
      node f_6 where
        x_6 := nil ⇒ f_7,
      node f_7 where
        x_7 := x_2 ⇒ f_8,
      node f_8 where
        x_8 := x_3 ⇒ f_9,
      node f_9 where
        x_9 := x_4 ⇒ f_10,
      node f_10 where
        x_10 := x_5 ⇒ f_11,
      node f_11 where
        x_11 := x_6 ⇒ f_12,
      node f_12 where
        x_1 := [-∞, ∞] ⇒ f_13,
      node f_13 where
        x_2 := nil ⇒ f_14,
      node f_14 where
        x_3 := nil ⇒ f_15,
      node f_15 where
        x_4 := nil ⇒ f_16,
      node f_16 where
        x_5 := nil ⇒ f_17,
      node f_17 where
        x_6 := nil ⇒ f_18,
      node f_18 where
        x_2 := x_1 ⇒ f_19,
      node f_19 where
        x_3 := (x_2 + [1, 1]) ⇒ f_20,
      node f_20 where
        x_4 := x_3 ⇒ f_21,
      node f_21 where
        x_5 := (x_4 + [1, 1]) ⇒ f_22,
      node f_22 where
        x_6 := x_5 ⇒ f_23,
      node f_23 where
        skip ⇒ f_18
        skip ⇒ f_1
        step := (step + [1, 1]) ⇒ f_24,
      node f_24 where
        x_7 := x_2 ⇒ f_25,
      node f_25 where
        x_8 := x_3 ⇒ f_26,
      node f_26 where
        x_9 := x_4 ⇒ f_27,
      node f_27 where
        x_10 := x_5 ⇒ f_28,
      node f_28 where
        x_11 := x_6 ⇒ f_29,
      node f_29 where
        x_1 := [-∞, ∞] ⇒ f_30,
      node f_30 where
        x_2 := nil ⇒ f_31,
      node f_31 where
        x_3 := nil ⇒ f_32,
      node f_32 where
        x_4 := nil ⇒ f_33,
      node f_33 where
        x_5 := nil ⇒ f_34,
      node f_34 where
        x_6 := nil ⇒ f_35,
      node f_35 where
        x_2 := x_1 ⇒ f_36,
      node f_36 where
        x_3 := (x_2 + [1, 1]) ⇒ f_37,
      node f_37 where
        x_4 := x_3 ⇒ f_38,
      node f_38 where
        x_5 := (x_4 + [1, 1]) ⇒ f_39,
      node f_39 where
        x_6 := x_5 ⇒ f_40,
      node f_40 where
        step := (step + [1, 1]) ⇒ f_24
        skip ⇒ f_35
        skip ⇒ f_41,
      node f_41 where
        ],
     [6]))
-/
#guard_msgs in
lustre
  node inc(x) = o where
    o = x + 1

  node plus2(x) = o where
    o = inc(inc(x))

/--
error: assert failed, got #[[1; +∞], [-∞; +∞], [2; +∞], [-∞; +∞]]
---
trace: [Lustrean.Elab.Compile] ✅️ elabExpr
    node u(x) = o
      where ⏎
        o = (+ (* x x) [3, 3])
      assert
        (≤ o [1, 1])
    ⇒
    some (([node f_0 where
        step := [0, 0] ⇒ f_2,
      node f_1 where
        skip ⇒ f_14,
      node f_2 where
        x_2 := nil ⇒ f_3,
      node f_3 where
        x_3 := x_2 ⇒ f_4,
      node f_4 where
        x_1 := [-∞, ∞] ⇒ f_5,
      node f_5 where
        x_2 := nil ⇒ f_6,
      node f_6 where
        x_2 := ((x_1 * x_1) + [3, 3]) ⇒ f_7,
      node f_7 where
        skip ⇒ f_6
        skip ⇒ f_1
        step := (step + [1, 1]) ⇒ f_8,
      node f_8 where
        x_3 := x_2 ⇒ f_9,
      node f_9 where
        x_1 := [-∞, ∞] ⇒ f_10,
      node f_10 where
        x_2 := nil ⇒ f_11,
      node f_11 where
        x_2 := ((x_1 * x_1) + [3, 3]) ⇒ f_12,
      node f_12 where
        step := (step + [1, 1]) ⇒ f_8
        skip ⇒ f_11
        skip ⇒ f_13,
      node f_13 where
        assert (x_2 ≤ [1, 1]) ⇒ f_14,
      node f_14 where
        ],
     [2]))
-/
#guard_msgs in
lustre
  node u(x) = o where
    o = x * x + 3
  assert
    o ≤ 1

/--
error: assert failed, got #[[1; +∞], [-∞; +∞], [-∞; -1], [-∞; +∞]]
---
trace: [Lustrean.Elab.Compile] ✅️ elabExpr
    node u(x) = o
      where ⏎
        o = (* x x)
      assert
        (≤ [0, 0] o)
    ⇒
    some (([node f_0 where
        step := [0, 0] ⇒ f_2,
      node f_1 where
        skip ⇒ f_14,
      node f_2 where
        x_2 := nil ⇒ f_3,
      node f_3 where
        x_3 := x_2 ⇒ f_4,
      node f_4 where
        x_1 := [-∞, ∞] ⇒ f_5,
      node f_5 where
        x_2 := nil ⇒ f_6,
      node f_6 where
        x_2 := (x_1 * x_1) ⇒ f_7,
      node f_7 where
        skip ⇒ f_6
        skip ⇒ f_1
        step := (step + [1, 1]) ⇒ f_8,
      node f_8 where
        x_3 := x_2 ⇒ f_9,
      node f_9 where
        x_1 := [-∞, ∞] ⇒ f_10,
      node f_10 where
        x_2 := nil ⇒ f_11,
      node f_11 where
        x_2 := (x_1 * x_1) ⇒ f_12,
      node f_12 where
        step := (step + [1, 1]) ⇒ f_8
        skip ⇒ f_11
        skip ⇒ f_13,
      node f_13 where
        assert ([0, 0] ≤ x_2) ⇒ f_14,
      node f_14 where
        ],
     [2]))
[Lustrean.Elab.Compile] ✅️ elabExpr
    node v(x)
      where ⏎
        x2 = (if (≤ [0, 0] x) (* x x) (* x x))
        o = (+ x2 [3, 3])
      assert
        (≤ [3, 3] o)
    ⇒
    some (([node f_0 where
        step := [0, 0] ⇒ f_2,
      node f_1 where
        skip ⇒ f_25,
      node f_2 where
        x_2 := nil ⇒ f_3,
      node f_3 where
        x_3 := nil ⇒ f_4,
      node f_4 where
        x_4 := x_2 ⇒ f_5,
      node f_5 where
        x_5 := x_3 ⇒ f_6,
      node f_6 where
        x_1 := [-∞, ∞] ⇒ f_7,
      node f_7 where
        x_2 := nil ⇒ f_8,
      node f_8 where
        x_3 := nil ⇒ f_9,
      node f_9 where
        guard ([0, 0] ≤ x_1) ⇒ f_10
        guard ([0, 0] > x_1) ⇒ f_11,
      node f_10 where
        x_2 := (x_1 * x_1) ⇒ f_12,
      node f_11 where
        x_2 := (x_1 * x_1) ⇒ f_12,
      node f_12 where
        x_3 := (x_2 + [3, 3]) ⇒ f_13,
      node f_13 where
        skip ⇒ f_9
        skip ⇒ f_1
        step := (step + [1, 1]) ⇒ f_14,
      node f_14 where
        x_4 := x_2 ⇒ f_15,
      node f_15 where
        x_5 := x_3 ⇒ f_16,
      node f_16 where
        x_1 := [-∞, ∞] ⇒ f_17,
      node f_17 where
        x_2 := nil ⇒ f_18,
      node f_18 where
        x_3 := nil ⇒ f_19,
      node f_19 where
        guard ([0, 0] ≤ x_1) ⇒ f_20
        guard ([0, 0] > x_1) ⇒ f_21,
      node f_20 where
        x_2 := (x_1 * x_1) ⇒ f_22,
      node f_21 where
        x_2 := (x_1 * x_1) ⇒ f_22,
      node f_22 where
        x_3 := (x_2 + [3, 3]) ⇒ f_23,
      node f_23 where
        step := (step + [1, 1]) ⇒ f_14
        skip ⇒ f_19
        skip ⇒ f_24,
      node f_24 where
        assert ([3, 3] ≤ x_3) ⇒ f_25,
      node f_25 where
        ],
     []))
-/
#guard_msgs in
lustre
  node u(x) = o where
    -- o = if x ≥ 0 then x * x else x * x
    o = x * x
  assert
    o ≥ 0

  node v(x) where
    x2 = if x ≥ 0 then x * x else x * x
    o = x2 + 3
  assert
    o ≥ 3

/--
error: variable x could be nil
---
trace: [Lustrean.Elab.Compile] ✅️ elabExpr
    node f() = x
      where ⏎
        x = y
        y = x
    ⇒
    some (([node f_0 where
        step := [0, 0] ⇒ f_2,
      node f_1 where
        skip ⇒ f_18,
      node f_2 where
        x_1 := nil ⇒ f_3,
      node f_3 where
        x_2 := nil ⇒ f_4,
      node f_4 where
        x_3 := x_1 ⇒ f_5,
      node f_5 where
        x_4 := x_2 ⇒ f_6,
      node f_6 where
        x_1 := nil ⇒ f_7,
      node f_7 where
        x_2 := nil ⇒ f_8,
      node f_8 where
        x_1 := x_2 ⇒ f_9,
      node f_9 where
        x_2 := x_1 ⇒ f_10,
      node f_10 where
        skip ⇒ f_8
        skip ⇒ f_1
        step := (step + [1, 1]) ⇒ f_11,
      node f_11 where
        x_3 := x_1 ⇒ f_12,
      node f_12 where
        x_4 := x_2 ⇒ f_13,
      node f_13 where
        x_1 := nil ⇒ f_14,
      node f_14 where
        x_2 := nil ⇒ f_15,
      node f_15 where
        x_1 := x_2 ⇒ f_16,
      node f_16 where
        x_2 := x_1 ⇒ f_17,
      node f_17 where
        step := (step + [1, 1]) ⇒ f_11
        skip ⇒ f_15
        skip ⇒ f_18,
      node f_18 where
        ],
     [1]))
-/
#guard_msgs in
lustre
  node f() = x where
    x = y
    y = x

/--
error: variable x could be nil
---
error: variable y could be nil
---
trace: [Lustrean.Elab.Compile] ✅️ elabExpr
    node f(c,z) = x,y
      where ⏎
        x = (if (= c [0, 0]) z y)
        y = (if (= c [0, 0]) x z)
    ⇒
    some (([node f_0 where
        step := [0, 0] ⇒ f_2,
      node f_1 where
        skip ⇒ f_30,
      node f_2 where
        x_3 := nil ⇒ f_3,
      node f_3 where
        x_4 := nil ⇒ f_4,
      node f_4 where
        x_5 := x_3 ⇒ f_5,
      node f_5 where
        x_6 := x_4 ⇒ f_6,
      node f_6 where
        x_1 := [-∞, ∞] ⇒ f_7,
      node f_7 where
        x_2 := [-∞, ∞] ⇒ f_8,
      node f_8 where
        x_3 := nil ⇒ f_9,
      node f_9 where
        x_4 := nil ⇒ f_10,
      node f_10 where
        guard (x_1 = [0, 0]) ⇒ f_11
        guard (x_1 ≠ [0, 0]) ⇒ f_12,
      node f_11 where
        x_3 := x_2 ⇒ f_13,
      node f_12 where
        x_3 := x_4 ⇒ f_13,
      node f_13 where
        guard (x_1 = [0, 0]) ⇒ f_14
        guard (x_1 ≠ [0, 0]) ⇒ f_15,
      node f_14 where
        x_4 := x_3 ⇒ f_16,
      node f_15 where
        x_4 := x_2 ⇒ f_16,
      node f_16 where
        skip ⇒ f_10
        skip ⇒ f_1
        step := (step + [1, 1]) ⇒ f_17,
      node f_17 where
        x_5 := x_3 ⇒ f_18,
      node f_18 where
        x_6 := x_4 ⇒ f_19,
      node f_19 where
        x_1 := [-∞, ∞] ⇒ f_20,
      node f_20 where
        x_2 := [-∞, ∞] ⇒ f_21,
      node f_21 where
        x_3 := nil ⇒ f_22,
      node f_22 where
        x_4 := nil ⇒ f_23,
      node f_23 where
        guard (x_1 = [0, 0]) ⇒ f_24
        guard (x_1 ≠ [0, 0]) ⇒ f_25,
      node f_24 where
        x_3 := x_2 ⇒ f_26,
      node f_25 where
        x_3 := x_4 ⇒ f_26,
      node f_26 where
        guard (x_1 = [0, 0]) ⇒ f_27
        guard (x_1 ≠ [0, 0]) ⇒ f_28,
      node f_27 where
        x_4 := x_3 ⇒ f_29,
      node f_28 where
        x_4 := x_2 ⇒ f_29,
      node f_29 where
        step := (step + [1, 1]) ⇒ f_17
        skip ⇒ f_23
        skip ⇒ f_30,
      node f_30 where
        ],
     [3, 4]))
-/
#guard_msgs in
lustre
  -- this would require a relational domain
  node f(c, z) = x, y where
    x = if c = 0 then z else y
    y = if c = 0 then x else z


/--
error: assert failed, got #[[1; +∞], [-∞; 1], [-∞; -1], [-∞; 1], [-∞; +∞], [-∞; 1], [-∞; +∞], [-∞; 1], [-∞; +∞]]
---
trace: [Lustrean.Elab.Compile] ✅️ elabExpr
    node l() = o
      where ⏎
        up = (if (= @ [0, 0]) [1, 1] (pre 0))
        o = (if (= @ [0, 0]) [0, 0] (pre 1))
        0 = (if (∨ (∧ (= up [1, 1]) (< o [10, 10])) (∧ (= up [0, 0]) (= o [0, 0]))) [1, 1] [0, 0])
        1 = (if (= up [1, 1]) (+ o [1, 1]) (- o [1, 1]))
      assert
        (≤ [0, 0] o)
    ⇒
    some (([node f_0 where
        step := [0, 0] ⇒ f_2,
      node f_1 where
        skip ⇒ f_49,
      node f_2 where
        x_1 := nil ⇒ f_3,
      node f_3 where
        x_2 := nil ⇒ f_4,
      node f_4 where
        x_3 := nil ⇒ f_5,
      node f_5 where
        x_4 := nil ⇒ f_6,
      node f_6 where
        x_5 := x_1 ⇒ f_7,
      node f_7 where
        x_6 := x_2 ⇒ f_8,
      node f_8 where
        x_7 := x_3 ⇒ f_9,
      node f_9 where
        x_8 := x_4 ⇒ f_10,
      node f_10 where
        x_1 := nil ⇒ f_11,
      node f_11 where
        x_2 := nil ⇒ f_12,
      node f_12 where
        x_3 := nil ⇒ f_13,
      node f_13 where
        x_4 := nil ⇒ f_14,
      node f_14 where
        guard (step = [0, 0]) ⇒ f_15
        guard (step ≠ [0, 0]) ⇒ f_16,
      node f_15 where
        x_1 := [1, 1] ⇒ f_17,
      node f_16 where
        x_1 := x_7 ⇒ f_17,
      node f_17 where
        guard (step = [0, 0]) ⇒ f_18
        guard (step ≠ [0, 0]) ⇒ f_19,
      node f_18 where
        x_2 := [0, 0] ⇒ f_20,
      node f_19 where
        x_2 := x_8 ⇒ f_20,
      node f_20 where
        guard (((x_1 = [1, 1]) && (x_2 < [10, 10])) || ((x_1 = [0, 0]) && (x_2 = [0, 0]))) ⇒ f_21
        guard (((x_1 ≠ [1, 1]) || (x_2 ≥ [10, 10])) && ((x_1 ≠ [0, 0]) || (x_2 ≠ [0, 0]))) ⇒ f_22,
      node f_21 where
        x_3 := [1, 1] ⇒ f_23,
      node f_22 where
        x_3 := [0, 0] ⇒ f_23,
      node f_23 where
        guard (x_1 = [1, 1]) ⇒ f_24
        guard (x_1 ≠ [1, 1]) ⇒ f_25,
      node f_24 where
        x_4 := (x_2 + [1, 1]) ⇒ f_26,
      node f_25 where
        x_4 := (x_2 - [1, 1]) ⇒ f_26,
      node f_26 where
        skip ⇒ f_14
        skip ⇒ f_1
        step := (step + [1, 1]) ⇒ f_27,
      node f_27 where
        x_5 := x_1 ⇒ f_28,
      node f_28 where
        x_6 := x_2 ⇒ f_29,
      node f_29 where
        x_7 := x_3 ⇒ f_30,
      node f_30 where
        x_8 := x_4 ⇒ f_31,
      node f_31 where
        x_1 := nil ⇒ f_32,
      node f_32 where
        x_2 := nil ⇒ f_33,
      node f_33 where
        x_3 := nil ⇒ f_34,
      node f_34 where
        x_4 := nil ⇒ f_35,
      node f_35 where
        guard (step = [0, 0]) ⇒ f_36
        guard (step ≠ [0, 0]) ⇒ f_37,
      node f_36 where
        x_1 := [1, 1] ⇒ f_38,
      node f_37 where
        x_1 := x_7 ⇒ f_38,
      node f_38 where
        guard (step = [0, 0]) ⇒ f_39
        guard (step ≠ [0, 0]) ⇒ f_40,
      node f_39 where
        x_2 := [0, 0] ⇒ f_41,
      node f_40 where
        x_2 := x_8 ⇒ f_41,
      node f_41 where
        guard (((x_1 = [1, 1]) && (x_2 < [10, 10])) || ((x_1 = [0, 0]) && (x_2 = [0, 0]))) ⇒ f_42
        guard (((x_1 ≠ [1, 1]) || (x_2 ≥ [10, 10])) && ((x_1 ≠ [0, 0]) || (x_2 ≠ [0, 0]))) ⇒ f_43,
      node f_42 where
        x_3 := [1, 1] ⇒ f_44,
      node f_43 where
        x_3 := [0, 0] ⇒ f_44,
      node f_44 where
        guard (x_1 = [1, 1]) ⇒ f_45
        guard (x_1 ≠ [1, 1]) ⇒ f_46,
      node f_45 where
        x_4 := (x_2 + [1, 1]) ⇒ f_47,
      node f_46 where
        x_4 := (x_2 - [1, 1]) ⇒ f_47,
      node f_47 where
        step := (step + [1, 1]) ⇒ f_27
        skip ⇒ f_35
        skip ⇒ f_48,
      node f_48 where
        assert ([0, 0] ≤ x_2) ⇒ f_49,
      node f_49 where
        ],
     [2]))
-/
#guard_msgs in
lustre
  node l() = o where
    up = 1 fby if (up = 1 ∧ o < 10) ∨ (up = 0 ∧ o = 0) then 1 else 0
    o = 0 fby if up = 1 then o + 1 else o - 1
  assert
    0 ≤ o

/--
trace: [Lustrean.Elab.Compile] ✅️ elabExpr
    node f(x) = o
      guard
        (≤ [0, 0] x)
      where ⏎
        o = (if (< [3, 3] x) [3, 3] x)
      assert
        (≤ [0, 0] o)
        (≤ o [3, 3])
    ⇒
    some (([node f_0 where
        step := [0, 0] ⇒ f_2,
      node f_1 where
        skip ⇒ f_21,
      node f_2 where
        x_2 := nil ⇒ f_3,
      node f_3 where
        x_3 := x_2 ⇒ f_4,
      node f_4 where
        x_1 := [-∞, ∞] ⇒ f_5,
      node f_5 where
        guard ([0, 0] ≤ x_1) ⇒ f_6,
      node f_6 where
        x_2 := nil ⇒ f_7,
      node f_7 where
        guard ([3, 3] < x_1) ⇒ f_8
        guard ([3, 3] ≥ x_1) ⇒ f_9,
      node f_8 where
        x_2 := [3, 3] ⇒ f_10,
      node f_9 where
        x_2 := x_1 ⇒ f_10,
      node f_10 where
        skip ⇒ f_7
        skip ⇒ f_1
        step := (step + [1, 1]) ⇒ f_11,
      node f_11 where
        x_3 := x_2 ⇒ f_12,
      node f_12 where
        x_1 := [-∞, ∞] ⇒ f_13,
      node f_13 where
        guard ([0, 0] ≤ x_1) ⇒ f_14,
      node f_14 where
        x_2 := nil ⇒ f_15,
      node f_15 where
        guard ([3, 3] < x_1) ⇒ f_16
        guard ([3, 3] ≥ x_1) ⇒ f_17,
      node f_16 where
        x_2 := [3, 3] ⇒ f_18,
      node f_17 where
        x_2 := x_1 ⇒ f_18,
      node f_18 where
        step := (step + [1, 1]) ⇒ f_11
        skip ⇒ f_15
        skip ⇒ f_19,
      node f_19 where
        assert ([0, 0] ≤ x_2) ⇒ f_20,
      node f_20 where
        assert (x_2 ≤ [3, 3]) ⇒ f_21,
      node f_21 where
        ],
     [2]))
[Lustrean.Elab.Compile] ✅️ elabExpr
    node g(x) = o
      guard
        (≤ [0, 0] x)
      where ⏎
        y = (if (= @ [0, 0]) x (pre 0))
        o = (if (< [3, 3] y) [3, 3] y)
        0 = (+ y [1, 1])
      assert
        (≤ [0, 0] o)
        (≤ o [3, 3])
    ⇒
    some (([node f_0 where
        step := [0, 0] ⇒ f_2,
      node f_1 where
        skip ⇒ f_39,
      node f_2 where
        x_2 := nil ⇒ f_3,
      node f_3 where
        x_3 := nil ⇒ f_4,
      node f_4 where
        x_4 := nil ⇒ f_5,
      node f_5 where
        x_5 := x_2 ⇒ f_6,
      node f_6 where
        x_6 := x_3 ⇒ f_7,
      node f_7 where
        x_7 := x_4 ⇒ f_8,
      node f_8 where
        x_1 := [-∞, ∞] ⇒ f_9,
      node f_9 where
        guard ([0, 0] ≤ x_1) ⇒ f_10,
      node f_10 where
        x_2 := nil ⇒ f_11,
      node f_11 where
        x_3 := nil ⇒ f_12,
      node f_12 where
        x_4 := nil ⇒ f_13,
      node f_13 where
        guard (step = [0, 0]) ⇒ f_14
        guard (step ≠ [0, 0]) ⇒ f_15,
      node f_14 where
        x_2 := x_1 ⇒ f_16,
      node f_15 where
        x_2 := x_7 ⇒ f_16,
      node f_16 where
        guard ([3, 3] < x_2) ⇒ f_17
        guard ([3, 3] ≥ x_2) ⇒ f_18,
      node f_17 where
        x_3 := [3, 3] ⇒ f_19,
      node f_18 where
        x_3 := x_2 ⇒ f_19,
      node f_19 where
        x_4 := (x_2 + [1, 1]) ⇒ f_20,
      node f_20 where
        skip ⇒ f_13
        skip ⇒ f_1
        step := (step + [1, 1]) ⇒ f_21,
      node f_21 where
        x_5 := x_2 ⇒ f_22,
      node f_22 where
        x_6 := x_3 ⇒ f_23,
      node f_23 where
        x_7 := x_4 ⇒ f_24,
      node f_24 where
        x_1 := [-∞, ∞] ⇒ f_25,
      node f_25 where
        guard ([0, 0] ≤ x_1) ⇒ f_26,
      node f_26 where
        x_2 := nil ⇒ f_27,
      node f_27 where
        x_3 := nil ⇒ f_28,
      node f_28 where
        x_4 := nil ⇒ f_29,
      node f_29 where
        guard (step = [0, 0]) ⇒ f_30
        guard (step ≠ [0, 0]) ⇒ f_31,
      node f_30 where
        x_2 := x_1 ⇒ f_32,
      node f_31 where
        x_2 := x_7 ⇒ f_32,
      node f_32 where
        guard ([3, 3] < x_2) ⇒ f_33
        guard ([3, 3] ≥ x_2) ⇒ f_34,
      node f_33 where
        x_3 := [3, 3] ⇒ f_35,
      node f_34 where
        x_3 := x_2 ⇒ f_35,
      node f_35 where
        x_4 := (x_2 + [1, 1]) ⇒ f_36,
      node f_36 where
        step := (step + [1, 1]) ⇒ f_21
        skip ⇒ f_29
        skip ⇒ f_37,
      node f_37 where
        assert ([0, 0] ≤ x_3) ⇒ f_38,
      node f_38 where
        assert (x_3 ≤ [3, 3]) ⇒ f_39,
      node f_39 where
        ],
     [3]))
-/
#guard_msgs in
lustre
  node f(x) = o
    guard
      x ≥ 0
    where
      o = if x > 3 then 3 else x
    assert
      0 ≤ o
      o ≤ 3

  node g(x) = o
    guard
      x ≥ 0
    where
      y = x fby y + 1
      o = if y > 3 then 3 else y
    assert
      o ≥ 0
      o ≤ 3

/--
error: variable o could be nil
---
error: variable o could be nil
---
error: assert failed, got #[[1; +∞], [5; +∞], [0; 3], [0; 3]]
---
error: assert failed, got #[[1; +∞], [5; 5], [3; 3], [5; 5], [3; 3], [6; 6], [5; 5], [3; 3], [5; 5], [3; 3], [6; 6]]
---
error: assert failed, got #[[1; +∞], [5; 5], [3; 3], [5; 5], [3; 3], [6; 6], [5; 5], [3; 3], [5; 5], [3; 3], [6; 6]]
---
trace: [Lustrean.Elab.Compile] ✅️ elabExpr
    node f() = o,o
      where ⏎
        o = o
    ⇒
    some (([node f_0 where
        step := [0, 0] ⇒ f_2,
      node f_1 where
        skip ⇒ f_11,
      node f_2 where
        x_1 := nil ⇒ f_3,
      node f_3 where
        x_2 := x_1 ⇒ f_4,
      node f_4 where
        x_1 := nil ⇒ f_5,
      node f_5 where
        x_1 := x_1 ⇒ f_6,
      node f_6 where
        skip ⇒ f_5
        skip ⇒ f_1
        step := (step + [1, 1]) ⇒ f_7,
      node f_7 where
        x_2 := x_1 ⇒ f_8,
      node f_8 where
        x_1 := nil ⇒ f_9,
      node f_9 where
        x_1 := x_1 ⇒ f_10,
      node f_10 where
        step := (step + [1, 1]) ⇒ f_7
        skip ⇒ f_9
        skip ⇒ f_11,
      node f_11 where
        ],
     [1, 1]))
[Lustrean.Elab.Compile] ✅️ elabExpr
    node u(x) = o
      where ⏎
        o = (if (= @ [0, 0]) [0, 0] (pre 0))
        0 = x
    ⇒
    some (([node f_0 where
        step := [0, 0] ⇒ f_2,
      node f_1 where
        skip ⇒ f_24,
      node f_2 where
        x_2 := nil ⇒ f_3,
      node f_3 where
        x_3 := nil ⇒ f_4,
      node f_4 where
        x_4 := x_2 ⇒ f_5,
      node f_5 where
        x_5 := x_3 ⇒ f_6,
      node f_6 where
        x_1 := [-∞, ∞] ⇒ f_7,
      node f_7 where
        x_2 := nil ⇒ f_8,
      node f_8 where
        x_3 := nil ⇒ f_9,
      node f_9 where
        guard (step = [0, 0]) ⇒ f_10
        guard (step ≠ [0, 0]) ⇒ f_11,
      node f_10 where
        x_2 := [0, 0] ⇒ f_12,
      node f_11 where
        x_2 := x_5 ⇒ f_12,
      node f_12 where
        x_3 := x_1 ⇒ f_13,
      node f_13 where
        skip ⇒ f_9
        skip ⇒ f_1
        step := (step + [1, 1]) ⇒ f_14,
      node f_14 where
        x_4 := x_2 ⇒ f_15,
      node f_15 where
        x_5 := x_3 ⇒ f_16,
      node f_16 where
        x_1 := [-∞, ∞] ⇒ f_17,
      node f_17 where
        x_2 := nil ⇒ f_18,
      node f_18 where
        x_3 := nil ⇒ f_19,
      node f_19 where
        guard (step = [0, 0]) ⇒ f_20
        guard (step ≠ [0, 0]) ⇒ f_21,
      node f_20 where
        x_2 := [0, 0] ⇒ f_22,
      node f_21 where
        x_2 := x_5 ⇒ f_22,
      node f_22 where
        x_3 := x_1 ⇒ f_23,
      node f_23 where
        step := (step + [1, 1]) ⇒ f_14
        skip ⇒ f_19
        skip ⇒ f_24,
      node f_24 where
        ],
     [2]))
[Lustrean.Elab.Compile] ✅️ elabExpr
    node f(x) = o
      guard
        (≤ [0, 0] x)
      where ⏎
        o = (if (< [3, 3] x) [3, 3] x)
      assert
        (≤ [0, 0] x)
        (≤ x [4, 4])
    ⇒
    some (([node f_0 where
        step := [0, 0] ⇒ f_2,
      node f_1 where
        skip ⇒ f_21,
      node f_2 where
        x_2 := nil ⇒ f_3,
      node f_3 where
        x_3 := x_2 ⇒ f_4,
      node f_4 where
        x_1 := [-∞, ∞] ⇒ f_5,
      node f_5 where
        guard ([0, 0] ≤ x_1) ⇒ f_6,
      node f_6 where
        x_2 := nil ⇒ f_7,
      node f_7 where
        guard ([3, 3] < x_1) ⇒ f_8
        guard ([3, 3] ≥ x_1) ⇒ f_9,
      node f_8 where
        x_2 := [3, 3] ⇒ f_10,
      node f_9 where
        x_2 := x_1 ⇒ f_10,
      node f_10 where
        skip ⇒ f_7
        skip ⇒ f_1
        step := (step + [1, 1]) ⇒ f_11,
      node f_11 where
        x_3 := x_2 ⇒ f_12,
      node f_12 where
        x_1 := [-∞, ∞] ⇒ f_13,
      node f_13 where
        guard ([0, 0] ≤ x_1) ⇒ f_14,
      node f_14 where
        x_2 := nil ⇒ f_15,
      node f_15 where
        guard ([3, 3] < x_1) ⇒ f_16
        guard ([3, 3] ≥ x_1) ⇒ f_17,
      node f_16 where
        x_2 := [3, 3] ⇒ f_18,
      node f_17 where
        x_2 := x_1 ⇒ f_18,
      node f_18 where
        step := (step + [1, 1]) ⇒ f_11
        skip ⇒ f_15
        skip ⇒ f_19,
      node f_19 where
        assert ([0, 0] ≤ x_1) ⇒ f_20,
      node f_20 where
        assert (x_1 ≤ [4, 4]) ⇒ f_21,
      node f_21 where
        ],
     [2]))
[Lustrean.Elab.Compile] ✅️ elabExpr
    node g() = o
      where ⏎
        o.0.x = [5, 5]
        o.0.o = (if (< [3, 3] o.0.x) [3, 3] o.0.x)
        o.1.x = [5, 5]
        o.1.o = (if (< [3, 3] o.1.x) [3, 3] o.1.x)
        o = (+ o.0.o o.1.o)
      assert
        (≤ [0, 0] o.0.x)
        (≤ [0, 0] o.0.x)
        (≤ o.0.x [4, 4])
        (≤ [0, 0] o.1.x)
        (≤ [0, 0] o.1.x)
        (≤ o.1.x [4, 4])
    ⇒
    some (([node f_0 where
        step := [0, 0] ⇒ f_2,
      node f_1 where
        skip ⇒ f_53,
      node f_2 where
        x_1 := nil ⇒ f_3,
      node f_3 where
        x_2 := nil ⇒ f_4,
      node f_4 where
        x_3 := nil ⇒ f_5,
      node f_5 where
        x_4 := nil ⇒ f_6,
      node f_6 where
        x_5 := nil ⇒ f_7,
      node f_7 where
        x_6 := x_1 ⇒ f_8,
      node f_8 where
        x_7 := x_2 ⇒ f_9,
      node f_9 where
        x_8 := x_3 ⇒ f_10,
      node f_10 where
        x_9 := x_4 ⇒ f_11,
      node f_11 where
        x_10 := x_5 ⇒ f_12,
      node f_12 where
        x_1 := nil ⇒ f_13,
      node f_13 where
        x_2 := nil ⇒ f_14,
      node f_14 where
        x_3 := nil ⇒ f_15,
      node f_15 where
        x_4 := nil ⇒ f_16,
      node f_16 where
        x_5 := nil ⇒ f_17,
      node f_17 where
        x_1 := [5, 5] ⇒ f_18,
      node f_18 where
        guard ([3, 3] < x_1) ⇒ f_19
        guard ([3, 3] ≥ x_1) ⇒ f_20,
      node f_19 where
        x_2 := [3, 3] ⇒ f_21,
      node f_20 where
        x_2 := x_1 ⇒ f_21,
      node f_21 where
        x_3 := [5, 5] ⇒ f_22,
      node f_22 where
        guard ([3, 3] < x_3) ⇒ f_23
        guard ([3, 3] ≥ x_3) ⇒ f_24,
      node f_23 where
        x_4 := [3, 3] ⇒ f_25,
      node f_24 where
        x_4 := x_3 ⇒ f_25,
      node f_25 where
        x_5 := (x_2 + x_4) ⇒ f_26,
      node f_26 where
        skip ⇒ f_17
        skip ⇒ f_1
        step := (step + [1, 1]) ⇒ f_27,
      node f_27 where
        x_6 := x_1 ⇒ f_28,
      node f_28 where
        x_7 := x_2 ⇒ f_29,
      node f_29 where
        x_8 := x_3 ⇒ f_30,
      node f_30 where
        x_9 := x_4 ⇒ f_31,
      node f_31 where
        x_10 := x_5 ⇒ f_32,
      node f_32 where
        x_1 := nil ⇒ f_33,
      node f_33 where
        x_2 := nil ⇒ f_34,
      node f_34 where
        x_3 := nil ⇒ f_35,
      node f_35 where
        x_4 := nil ⇒ f_36,
      node f_36 where
        x_5 := nil ⇒ f_37,
      node f_37 where
        x_1 := [5, 5] ⇒ f_38,
      node f_38 where
        guard ([3, 3] < x_1) ⇒ f_39
        guard ([3, 3] ≥ x_1) ⇒ f_40,
      node f_39 where
        x_2 := [3, 3] ⇒ f_41,
      node f_40 where
        x_2 := x_1 ⇒ f_41,
      node f_41 where
        x_3 := [5, 5] ⇒ f_42,
      node f_42 where
        guard ([3, 3] < x_3) ⇒ f_43
        guard ([3, 3] ≥ x_3) ⇒ f_44,
      node f_43 where
        x_4 := [3, 3] ⇒ f_45,
      node f_44 where
        x_4 := x_3 ⇒ f_45,
      node f_45 where
        x_5 := (x_2 + x_4) ⇒ f_46,
      node f_46 where
        step := (step + [1, 1]) ⇒ f_27
        skip ⇒ f_37
        skip ⇒ f_47,
      node f_47 where
        assert ([0, 0] ≤ x_1) ⇒ f_48,
      node f_48 where
        assert ([0, 0] ≤ x_1) ⇒ f_49,
      node f_49 where
        assert (x_1 ≤ [4, 4]) ⇒ f_50,
      node f_50 where
        assert ([0, 0] ≤ x_3) ⇒ f_51,
      node f_51 where
        assert ([0, 0] ≤ x_3) ⇒ f_52,
      node f_52 where
        assert (x_3 ≤ [4, 4]) ⇒ f_53,
      node f_53 where
        ],
     [5]))
-/
#guard_msgs in
lustre
  node f() = o, o where
    o = o

  node u(x) = o where
    o = 0 fby x

  -- shadowing
  node f(x) = o
    guard
      x ≥ 0
    where
      o = if x > 3 then 3 else x
    assert
      0 ≤ x
      x ≤ 4

  node g() = o where
    o = f(5) + f(5)

/--
trace: [Lustrean.Elab.Compile] ✅️ elabExpr
    node a() = o
      where ⏎
        o = (if (= @ [0, 0]) [0, 0] (pre 0))
        0 = (+ [1, 1] o)
      assert
        (≤ [0, 0] o)
    ⇒
    some (([node f_0 where
        step := [0, 0] ⇒ f_2,
      node f_1 where
        skip ⇒ f_23,
      node f_2 where
        x_1 := nil ⇒ f_3,
      node f_3 where
        x_2 := nil ⇒ f_4,
      node f_4 where
        x_3 := x_1 ⇒ f_5,
      node f_5 where
        x_4 := x_2 ⇒ f_6,
      node f_6 where
        x_1 := nil ⇒ f_7,
      node f_7 where
        x_2 := nil ⇒ f_8,
      node f_8 where
        guard (step = [0, 0]) ⇒ f_9
        guard (step ≠ [0, 0]) ⇒ f_10,
      node f_9 where
        x_1 := [0, 0] ⇒ f_11,
      node f_10 where
        x_1 := x_4 ⇒ f_11,
      node f_11 where
        x_2 := ([1, 1] + x_1) ⇒ f_12,
      node f_12 where
        skip ⇒ f_8
        skip ⇒ f_1
        step := (step + [1, 1]) ⇒ f_13,
      node f_13 where
        x_3 := x_1 ⇒ f_14,
      node f_14 where
        x_4 := x_2 ⇒ f_15,
      node f_15 where
        x_1 := nil ⇒ f_16,
      node f_16 where
        x_2 := nil ⇒ f_17,
      node f_17 where
        guard (step = [0, 0]) ⇒ f_18
        guard (step ≠ [0, 0]) ⇒ f_19,
      node f_18 where
        x_1 := [0, 0] ⇒ f_20,
      node f_19 where
        x_1 := x_4 ⇒ f_20,
      node f_20 where
        x_2 := ([1, 1] + x_1) ⇒ f_21,
      node f_21 where
        step := (step + [1, 1]) ⇒ f_13
        skip ⇒ f_17
        skip ⇒ f_22,
      node f_22 where
        assert ([0, 0] ≤ x_1) ⇒ f_23,
      node f_23 where
        ],
     [1]))
-/
#guard_msgs in
lustre
  node a() = o where
    o = 0 fby 1 + o
  assert
    o ≥ 0

/--
trace: [Lustrean.Elab.Compile] ✅️ elabExpr
    node h() = o,i
      where ⏎
        o = (if (= @ [0, 0]) [0, 0] (pre 1))
        i = (if (= o [5, 5]) 2 [0, 0])
        0 = (+ i [1, 1])
        1 = (if (= @ [0, 0]) [1, 1] (pre 0))
        2 = (if (∨ (< [0, 0] [0, 0]) (< [0, 0] [0, 0])) [1, 1] [2, 2])
    ⇒
    some (([node f_0 where
        step := [0, 0] ⇒ f_2,
      node f_1 where
        skip ⇒ f_55,
      node f_2 where
        x_1 := nil ⇒ f_3,
      node f_3 where
        x_2 := nil ⇒ f_4,
      node f_4 where
        x_3 := nil ⇒ f_5,
      node f_5 where
        x_4 := nil ⇒ f_6,
      node f_6 where
        x_5 := nil ⇒ f_7,
      node f_7 where
        x_6 := x_1 ⇒ f_8,
      node f_8 where
        x_7 := x_2 ⇒ f_9,
      node f_9 where
        x_8 := x_3 ⇒ f_10,
      node f_10 where
        x_9 := x_4 ⇒ f_11,
      node f_11 where
        x_10 := x_5 ⇒ f_12,
      node f_12 where
        x_1 := nil ⇒ f_13,
      node f_13 where
        x_2 := nil ⇒ f_14,
      node f_14 where
        x_3 := nil ⇒ f_15,
      node f_15 where
        x_4 := nil ⇒ f_16,
      node f_16 where
        x_5 := nil ⇒ f_17,
      node f_17 where
        guard (step = [0, 0]) ⇒ f_18
        guard (step ≠ [0, 0]) ⇒ f_19,
      node f_18 where
        x_1 := [0, 0] ⇒ f_20,
      node f_19 where
        x_1 := x_9 ⇒ f_20,
      node f_20 where
        guard (x_1 = [5, 5]) ⇒ f_21
        guard (x_1 ≠ [5, 5]) ⇒ f_22,
      node f_21 where
        x_2 := x_5 ⇒ f_23,
      node f_22 where
        x_2 := [0, 0] ⇒ f_23,
      node f_23 where
        x_3 := (x_2 + [1, 1]) ⇒ f_24,
      node f_24 where
        guard (step = [0, 0]) ⇒ f_25
        guard (step ≠ [0, 0]) ⇒ f_26,
      node f_25 where
        x_4 := [1, 1] ⇒ f_27,
      node f_26 where
        x_4 := x_8 ⇒ f_27,
      node f_27 where
        guard (([0, 0] < [0, 0]) || ([0, 0] < [0, 0])) ⇒ f_28
        guard (([0, 0] ≥ [0, 0]) && ([0, 0] ≥ [0, 0])) ⇒ f_29,
      node f_28 where
        x_5 := [1, 1] ⇒ f_30,
      node f_29 where
        x_5 := [2, 2] ⇒ f_30,
      node f_30 where
        skip ⇒ f_17
        skip ⇒ f_1
        step := (step + [1, 1]) ⇒ f_31,
      node f_31 where
        x_6 := x_1 ⇒ f_32,
      node f_32 where
        x_7 := x_2 ⇒ f_33,
      node f_33 where
        x_8 := x_3 ⇒ f_34,
      node f_34 where
        x_9 := x_4 ⇒ f_35,
      node f_35 where
        x_10 := x_5 ⇒ f_36,
      node f_36 where
        x_1 := nil ⇒ f_37,
      node f_37 where
        x_2 := nil ⇒ f_38,
      node f_38 where
        x_3 := nil ⇒ f_39,
      node f_39 where
        x_4 := nil ⇒ f_40,
      node f_40 where
        x_5 := nil ⇒ f_41,
      node f_41 where
        guard (step = [0, 0]) ⇒ f_42
        guard (step ≠ [0, 0]) ⇒ f_43,
      node f_42 where
        x_1 := [0, 0] ⇒ f_44,
      node f_43 where
        x_1 := x_9 ⇒ f_44,
      node f_44 where
        guard (x_1 = [5, 5]) ⇒ f_45
        guard (x_1 ≠ [5, 5]) ⇒ f_46,
      node f_45 where
        x_2 := x_5 ⇒ f_47,
      node f_46 where
        x_2 := [0, 0] ⇒ f_47,
      node f_47 where
        x_3 := (x_2 + [1, 1]) ⇒ f_48,
      node f_48 where
        guard (step = [0, 0]) ⇒ f_49
        guard (step ≠ [0, 0]) ⇒ f_50,
      node f_49 where
        x_4 := [1, 1] ⇒ f_51,
      node f_50 where
        x_4 := x_8 ⇒ f_51,
      node f_51 where
        guard (([0, 0] < [0, 0]) || ([0, 0] < [0, 0])) ⇒ f_52
        guard (([0, 0] ≥ [0, 0]) && ([0, 0] ≥ [0, 0])) ⇒ f_53,
      node f_52 where
        x_5 := [1, 1] ⇒ f_54,
      node f_53 where
        x_5 := [2, 2] ⇒ f_54,
      node f_54 where
        step := (step + [1, 1]) ⇒ f_31
        skip ⇒ f_41
        skip ⇒ f_55,
      node f_55 where
        ],
     [1, 2]))
-/
#guard_msgs in
lustre
  node h() = o, i where
    o = 0 fby 1 fby i+1
    i =
      if o = 5 then
        if 0 ≠ 0 then 1 else 2
      else
        0
/--
trace: [Lustrean.Elab.Compile] ✅️ elabExpr
    node f()
      where ⏎
        ⏎
    ⇒
    some (([node f_0 where
        step := [0, 0] ⇒ f_2,
      node f_1 where
        skip ⇒ f_4,
      node f_2 where
        skip ⇒ f_2
        skip ⇒ f_1
        step := (step + [1, 1]) ⇒ f_3,
      node f_3 where
        step := (step + [1, 1]) ⇒ f_3
        skip ⇒ f_3
        skip ⇒ f_4,
      node f_4 where
        ],
     []))
-/
#guard_msgs in
lustre
  node f() where
