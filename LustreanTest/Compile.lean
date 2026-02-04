import Lustrean

set_option trace.Lustrean.Elab.Compile true

/--
trace: [Lustrean.Elab.Compile] ✅️ elabExpr
    node inc(x) = o
      where ⏎
        o = (x + [1, 1])
    ⇒
    node f_0 where
      step := 0 ⇒ f_2
    node f_1 where
      skip ⇒ f_11
    node f_2 where
      x₂ := nil ⇒ f_3
    node f_3 where
      x₃ := x₂ ⇒ f_4
    node f_4 where
      x₁ := [-∞, ∞] ⇒ f_5
    node f_5 where
      x₂ := (x₁ + 1) ⇒ f_6
    node f_6 where
      skip ⇒ f_5
      skip ⇒ f_1
      step := (step + 1) ⇒ f_7
    node f_7 where
      x₃ := x₂ ⇒ f_8
    node f_8 where
      x₁ := [-∞, ∞] ⇒ f_9
    node f_9 where
      x₂ := (x₁ + 1) ⇒ f_10
    node f_10 where
      step := (step + 1) ⇒ f_7
      skip ⇒ f_9
      skip ⇒ f_11
    node f_11 where
      ⏎
[Lustrean.Elab.Compile] ✅️ elabExpr
    node plus2(x) = o
      where ⏎
        o.0.x.1.x = x
        o.0.x.1.o = (o.0.x.1.x + [1, 1])
        o.0.x = o.0.x.1.o
        o.0.o = (o.0.x + [1, 1])
        o = o.0.o
    ⇒
    node f_0 where
      step := 0 ⇒ f_2
    node f_1 where
      skip ⇒ f_31
    node f_2 where
      x₂ := nil ⇒ f_3
    node f_3 where
      x₃ := nil ⇒ f_4
    node f_4 where
      x₄ := nil ⇒ f_5
    node f_5 where
      x₅ := nil ⇒ f_6
    node f_6 where
      x₆ := nil ⇒ f_7
    node f_7 where
      x₇ := x₂ ⇒ f_8
    node f_8 where
      x₈ := x₃ ⇒ f_9
    node f_9 where
      x₉ := x₄ ⇒ f_10
    node f_10 where
      x₁₀ := x₅ ⇒ f_11
    node f_11 where
      x₁₁ := x₆ ⇒ f_12
    node f_12 where
      x₁ := [-∞, ∞] ⇒ f_13
    node f_13 where
      x₂ := x₁ ⇒ f_14
    node f_14 where
      x₃ := (x₂ + 1) ⇒ f_15
    node f_15 where
      x₄ := x₃ ⇒ f_16
    node f_16 where
      x₅ := (x₄ + 1) ⇒ f_17
    node f_17 where
      x₆ := x₅ ⇒ f_18
    node f_18 where
      skip ⇒ f_13
      skip ⇒ f_1
      step := (step + 1) ⇒ f_19
    node f_19 where
      x₇ := x₂ ⇒ f_20
    node f_20 where
      x₈ := x₃ ⇒ f_21
    node f_21 where
      x₉ := x₄ ⇒ f_22
    node f_22 where
      x₁₀ := x₅ ⇒ f_23
    node f_23 where
      x₁₁ := x₆ ⇒ f_24
    node f_24 where
      x₁ := [-∞, ∞] ⇒ f_25
    node f_25 where
      x₂ := x₁ ⇒ f_26
    node f_26 where
      x₃ := (x₂ + 1) ⇒ f_27
    node f_27 where
      x₄ := x₃ ⇒ f_28
    node f_28 where
      x₅ := (x₄ + 1) ⇒ f_29
    node f_29 where
      x₆ := x₅ ⇒ f_30
    node f_30 where
      step := (step + 1) ⇒ f_19
      skip ⇒ f_25
      skip ⇒ f_31
    node f_31 where
-/
#guard_msgs in
lustre
  node inc(x) = o where
    o = x + 1

  node plus2(x) = o where
    o = inc(inc(x))

/--
error: assert failed under #[[1; +∞], [-∞; +∞], [2; +∞], [-∞; +∞]]
---
trace: [Lustrean.Elab.Compile] ✅️ elabExpr
    node u(x) = o
      where ⏎
        o = ((x * x) + [3, 3])
      assert
        (o ≤ [1, 1])
    ⇒
    node f_0 where
      step := 0 ⇒ f_2
    node f_1 where
      skip ⇒ f_12
    node f_2 where
      x₂ := nil ⇒ f_3
    node f_3 where
      x₃ := x₂ ⇒ f_4
    node f_4 where
      x₁ := [-∞, ∞] ⇒ f_5
    node f_5 where
      x₂ := ((x₁ * x₁) + 3) ⇒ f_6
    node f_6 where
      skip ⇒ f_5
      skip ⇒ f_1
      step := (step + 1) ⇒ f_7
    node f_7 where
      x₃ := x₂ ⇒ f_8
    node f_8 where
      x₁ := [-∞, ∞] ⇒ f_9
    node f_9 where
      x₂ := ((x₁ * x₁) + 3) ⇒ f_10
    node f_10 where
      step := (step + 1) ⇒ f_7
      skip ⇒ f_9
      skip ⇒ f_11
    node f_11 where
      assert (x₂ ≤ 1) ⇒ f_12
    node f_12 where
-/
#guard_msgs in
lustre
  node u(x) = o where
    o = x * x + 3
  assert
    o ≤ 1

/--
error: assert failed under #[[1; +∞], [-∞; +∞], [-∞; -1], [-∞; +∞]]
---
trace: [Lustrean.Elab.Compile] ✅️ elabExpr
    node u(x) = o
      where ⏎
        o = (x * x)
      assert
        ([0, 0] ≤ o)
    ⇒
    node f_0 where
      step := 0 ⇒ f_2
    node f_1 where
      skip ⇒ f_12
    node f_2 where
      x₂ := nil ⇒ f_3
    node f_3 where
      x₃ := x₂ ⇒ f_4
    node f_4 where
      x₁ := [-∞, ∞] ⇒ f_5
    node f_5 where
      x₂ := (x₁ * x₁) ⇒ f_6
    node f_6 where
      skip ⇒ f_5
      skip ⇒ f_1
      step := (step + 1) ⇒ f_7
    node f_7 where
      x₃ := x₂ ⇒ f_8
    node f_8 where
      x₁ := [-∞, ∞] ⇒ f_9
    node f_9 where
      x₂ := (x₁ * x₁) ⇒ f_10
    node f_10 where
      step := (step + 1) ⇒ f_7
      skip ⇒ f_9
      skip ⇒ f_11
    node f_11 where
      assert (0 ≤ x₂) ⇒ f_12
    node f_12 where
      ⏎
[Lustrean.Elab.Compile] ✅️ elabExpr
    node v(x)
      where ⏎
        x2 = (if ([0, 0] ≤ x) then (x * x) else (x * x))
        o = (x2 + [3, 3])
      assert
        ([3, 3] ≤ o)
    ⇒
    node f_0 where
      step := 0 ⇒ f_2
    node f_1 where
      skip ⇒ f_21
    node f_2 where
      x₂ := nil ⇒ f_3
    node f_3 where
      x₃ := nil ⇒ f_4
    node f_4 where
      x₄ := x₂ ⇒ f_5
    node f_5 where
      x₅ := x₃ ⇒ f_6
    node f_6 where
      x₁ := [-∞, ∞] ⇒ f_7
    node f_7 where
      guard (0 ≤ x₁) ⇒ f_8
      guard (0 > x₁) ⇒ f_9
    node f_8 where
      x₂ := (x₁ * x₁) ⇒ f_10
    node f_9 where
      x₂ := (x₁ * x₁) ⇒ f_10
    node f_10 where
      x₃ := (x₂ + 3) ⇒ f_11
    node f_11 where
      skip ⇒ f_7
      skip ⇒ f_1
      step := (step + 1) ⇒ f_12
    node f_12 where
      x₄ := x₂ ⇒ f_13
    node f_13 where
      x₅ := x₃ ⇒ f_14
    node f_14 where
      x₁ := [-∞, ∞] ⇒ f_15
    node f_15 where
      guard (0 ≤ x₁) ⇒ f_16
      guard (0 > x₁) ⇒ f_17
    node f_16 where
      x₂ := (x₁ * x₁) ⇒ f_18
    node f_17 where
      x₂ := (x₁ * x₁) ⇒ f_18
    node f_18 where
      x₃ := (x₂ + 3) ⇒ f_19
    node f_19 where
      step := (step + 1) ⇒ f_12
      skip ⇒ f_15
      skip ⇒ f_20
    node f_20 where
      assert (3 ≤ x₃) ⇒ f_21
    node f_21 where
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
    node f_0 where
      step := 0 ⇒ f_2
    node f_1 where
      skip ⇒ f_14
    node f_2 where
      x₁ := nil ⇒ f_3
    node f_3 where
      x₂ := nil ⇒ f_4
    node f_4 where
      x₃ := x₁ ⇒ f_5
    node f_5 where
      x₄ := x₂ ⇒ f_6
    node f_6 where
      x₁ := x₂ ⇒ f_7
    node f_7 where
      x₂ := x₁ ⇒ f_8
    node f_8 where
      skip ⇒ f_6
      skip ⇒ f_1
      step := (step + 1) ⇒ f_9
    node f_9 where
      x₃ := x₁ ⇒ f_10
    node f_10 where
      x₄ := x₂ ⇒ f_11
    node f_11 where
      x₁ := x₂ ⇒ f_12
    node f_12 where
      x₂ := x₁ ⇒ f_13
    node f_13 where
      step := (step + 1) ⇒ f_9
      skip ⇒ f_11
      skip ⇒ f_14
    node f_14 where
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
        x = (if (c = [0, 0]) then z else y)
        y = (if (c = [0, 0]) then x else z)
    ⇒
    node f_0 where
      step := 0 ⇒ f_2
    node f_1 where
      skip ⇒ f_26
    node f_2 where
      x₃ := nil ⇒ f_3
    node f_3 where
      x₄ := nil ⇒ f_4
    node f_4 where
      x₅ := x₃ ⇒ f_5
    node f_5 where
      x₆ := x₄ ⇒ f_6
    node f_6 where
      x₁ := [-∞, ∞] ⇒ f_7
    node f_7 where
      x₂ := [-∞, ∞] ⇒ f_8
    node f_8 where
      guard (x₁ = 0) ⇒ f_9
      guard (x₁ ≠ 0) ⇒ f_10
    node f_9 where
      x₃ := x₂ ⇒ f_11
    node f_10 where
      x₃ := x₄ ⇒ f_11
    node f_11 where
      guard (x₁ = 0) ⇒ f_12
      guard (x₁ ≠ 0) ⇒ f_13
    node f_12 where
      x₄ := x₃ ⇒ f_14
    node f_13 where
      x₄ := x₂ ⇒ f_14
    node f_14 where
      skip ⇒ f_8
      skip ⇒ f_1
      step := (step + 1) ⇒ f_15
    node f_15 where
      x₅ := x₃ ⇒ f_16
    node f_16 where
      x₆ := x₄ ⇒ f_17
    node f_17 where
      x₁ := [-∞, ∞] ⇒ f_18
    node f_18 where
      x₂ := [-∞, ∞] ⇒ f_19
    node f_19 where
      guard (x₁ = 0) ⇒ f_20
      guard (x₁ ≠ 0) ⇒ f_21
    node f_20 where
      x₃ := x₂ ⇒ f_22
    node f_21 where
      x₃ := x₄ ⇒ f_22
    node f_22 where
      guard (x₁ = 0) ⇒ f_23
      guard (x₁ ≠ 0) ⇒ f_24
    node f_23 where
      x₄ := x₃ ⇒ f_25
    node f_24 where
      x₄ := x₂ ⇒ f_25
    node f_25 where
      step := (step + 1) ⇒ f_15
      skip ⇒ f_19
      skip ⇒ f_26
    node f_26 where
-/
#guard_msgs in
lustre
  -- this would require a relational domain
  node f(c, z) = x, y where
    x = if c = 0 then z else y
    y = if c = 0 then x else z


/--
error: assert failed under #[[1; +∞], [-∞; 1], [-∞; -1], [-∞; 1], [-∞; +∞], [-∞; 1], [-∞; +∞], [-∞; 1], [-∞; +∞]]
---
trace: [Lustrean.Elab.Compile] ✅️ elabExpr
    node l() = o
      where ⏎
        up = (if (step = [0, 0]) then [1, 1] else (pre x_0))
        o = (if (step = [0, 0]) then [0, 0] else (pre x_1))
        x_0 = (if (((up = [1, 1]) ∧ (o < [10, 10])) ∨ ((up = [0, 0]) ∧ (o = [0, 0]))) then [1, 1] else [0, 0])
        x_1 = (if (up = [1, 1]) then (o + [1, 1]) else (o - [1, 1]))
      assert
        ([0, 0] ≤ o)
    ⇒
    node f_0 where
      step := 0 ⇒ f_2
    node f_1 where
      skip ⇒ f_41
    node f_2 where
      x₁ := nil ⇒ f_3
    node f_3 where
      x₂ := nil ⇒ f_4
    node f_4 where
      x₃ := nil ⇒ f_5
    node f_5 where
      x₄ := nil ⇒ f_6
    node f_6 where
      x₅ := x₁ ⇒ f_7
    node f_7 where
      x₆ := x₂ ⇒ f_8
    node f_8 where
      x₇ := x₃ ⇒ f_9
    node f_9 where
      x₈ := x₄ ⇒ f_10
    node f_10 where
      guard (step = 0) ⇒ f_11
      guard (step ≠ 0) ⇒ f_12
    node f_11 where
      x₁ := 1 ⇒ f_13
    node f_12 where
      x₁ := x₇ ⇒ f_13
    node f_13 where
      guard (step = 0) ⇒ f_14
      guard (step ≠ 0) ⇒ f_15
    node f_14 where
      x₂ := 0 ⇒ f_16
    node f_15 where
      x₂ := x₈ ⇒ f_16
    node f_16 where
      guard (((x₁ = 1) && (x₂ < 10)) || ((x₁ = 0) && (x₂ = 0))) ⇒ f_17
      guard (((x₁ ≠ 1) || (x₂ ≥ 10)) && ((x₁ ≠ 0) || (x₂ ≠ 0))) ⇒ f_18
    node f_17 where
      x₃ := 1 ⇒ f_19
    node f_18 where
      x₃ := 0 ⇒ f_19
    node f_19 where
      guard (x₁ = 1) ⇒ f_20
      guard (x₁ ≠ 1) ⇒ f_21
    node f_20 where
      x₄ := (x₂ + 1) ⇒ f_22
    node f_21 where
      x₄ := (x₂ - 1) ⇒ f_22
    node f_22 where
      skip ⇒ f_10
      skip ⇒ f_1
      step := (step + 1) ⇒ f_23
    node f_23 where
      x₅ := x₁ ⇒ f_24
    node f_24 where
      x₆ := x₂ ⇒ f_25
    node f_25 where
      x₇ := x₃ ⇒ f_26
    node f_26 where
      x₈ := x₄ ⇒ f_27
    node f_27 where
      guard (step = 0) ⇒ f_28
      guard (step ≠ 0) ⇒ f_29
    node f_28 where
      x₁ := 1 ⇒ f_30
    node f_29 where
      x₁ := x₇ ⇒ f_30
    node f_30 where
      guard (step = 0) ⇒ f_31
      guard (step ≠ 0) ⇒ f_32
    node f_31 where
      x₂ := 0 ⇒ f_33
    node f_32 where
      x₂ := x₈ ⇒ f_33
    node f_33 where
      guard (((x₁ = 1) && (x₂ < 10)) || ((x₁ = 0) && (x₂ = 0))) ⇒ f_34
      guard (((x₁ ≠ 1) || (x₂ ≥ 10)) && ((x₁ ≠ 0) || (x₂ ≠ 0))) ⇒ f_35
    node f_34 where
      x₃ := 1 ⇒ f_36
    node f_35 where
      x₃ := 0 ⇒ f_36
    node f_36 where
      guard (x₁ = 1) ⇒ f_37
      guard (x₁ ≠ 1) ⇒ f_38
    node f_37 where
      x₄ := (x₂ + 1) ⇒ f_39
    node f_38 where
      x₄ := (x₂ - 1) ⇒ f_39
    node f_39 where
      step := (step + 1) ⇒ f_23
      skip ⇒ f_27
      skip ⇒ f_40
    node f_40 where
      assert (0 ≤ x₂) ⇒ f_41
    node f_41 where
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
        ([0, 0] ≤ x)
      where ⏎
        o = (if ([3, 3] < x) then [3, 3] else x)
      assert
        ([0, 0] ≤ o)
        (o ≤ [3, 3])
    ⇒
    node f_0 where
      step := 0 ⇒ f_2
    node f_1 where
      skip ⇒ f_19
    node f_2 where
      x₂ := nil ⇒ f_3
    node f_3 where
      x₃ := x₂ ⇒ f_4
    node f_4 where
      x₁ := [-∞, ∞] ⇒ f_5
    node f_5 where
      guard (0 ≤ x₁) ⇒ f_6
    node f_6 where
      guard (3 < x₁) ⇒ f_7
      guard (3 ≥ x₁) ⇒ f_8
    node f_7 where
      x₂ := 3 ⇒ f_9
    node f_8 where
      x₂ := x₁ ⇒ f_9
    node f_9 where
      skip ⇒ f_6
      skip ⇒ f_1
      step := (step + 1) ⇒ f_10
    node f_10 where
      x₃ := x₂ ⇒ f_11
    node f_11 where
      x₁ := [-∞, ∞] ⇒ f_12
    node f_12 where
      guard (0 ≤ x₁) ⇒ f_13
    node f_13 where
      guard (3 < x₁) ⇒ f_14
      guard (3 ≥ x₁) ⇒ f_15
    node f_14 where
      x₂ := 3 ⇒ f_16
    node f_15 where
      x₂ := x₁ ⇒ f_16
    node f_16 where
      step := (step + 1) ⇒ f_10
      skip ⇒ f_13
      skip ⇒ f_17
    node f_17 where
      assert (0 ≤ x₂) ⇒ f_18
    node f_18 where
      assert (x₂ ≤ 3) ⇒ f_19
    node f_19 where
      ⏎
[Lustrean.Elab.Compile] ✅️ elabExpr
    node g(x) = o
      guard
        ([0, 0] ≤ x)
      where ⏎
        y = (if (step = [0, 0]) then x else (pre x_0))
        o = (if ([3, 3] < y) then [3, 3] else y)
        x_0 = (y + [1, 1])
      assert
        ([0, 0] ≤ o)
        (o ≤ [3, 3])
    ⇒
    node f_0 where
      step := 0 ⇒ f_2
    node f_1 where
      skip ⇒ f_33
    node f_2 where
      x₂ := nil ⇒ f_3
    node f_3 where
      x₃ := nil ⇒ f_4
    node f_4 where
      x₄ := nil ⇒ f_5
    node f_5 where
      x₅ := x₂ ⇒ f_6
    node f_6 where
      x₆ := x₃ ⇒ f_7
    node f_7 where
      x₇ := x₄ ⇒ f_8
    node f_8 where
      x₁ := [-∞, ∞] ⇒ f_9
    node f_9 where
      guard (0 ≤ x₁) ⇒ f_10
    node f_10 where
      guard (step = 0) ⇒ f_11
      guard (step ≠ 0) ⇒ f_12
    node f_11 where
      x₂ := x₁ ⇒ f_13
    node f_12 where
      x₂ := x₇ ⇒ f_13
    node f_13 where
      guard (3 < x₂) ⇒ f_14
      guard (3 ≥ x₂) ⇒ f_15
    node f_14 where
      x₃ := 3 ⇒ f_16
    node f_15 where
      x₃ := x₂ ⇒ f_16
    node f_16 where
      x₄ := (x₂ + 1) ⇒ f_17
    node f_17 where
      skip ⇒ f_10
      skip ⇒ f_1
      step := (step + 1) ⇒ f_18
    node f_18 where
      x₅ := x₂ ⇒ f_19
    node f_19 where
      x₆ := x₃ ⇒ f_20
    node f_20 where
      x₇ := x₄ ⇒ f_21
    node f_21 where
      x₁ := [-∞, ∞] ⇒ f_22
    node f_22 where
      guard (0 ≤ x₁) ⇒ f_23
    node f_23 where
      guard (step = 0) ⇒ f_24
      guard (step ≠ 0) ⇒ f_25
    node f_24 where
      x₂ := x₁ ⇒ f_26
    node f_25 where
      x₂ := x₇ ⇒ f_26
    node f_26 where
      guard (3 < x₂) ⇒ f_27
      guard (3 ≥ x₂) ⇒ f_28
    node f_27 where
      x₃ := 3 ⇒ f_29
    node f_28 where
      x₃ := x₂ ⇒ f_29
    node f_29 where
      x₄ := (x₂ + 1) ⇒ f_30
    node f_30 where
      step := (step + 1) ⇒ f_18
      skip ⇒ f_23
      skip ⇒ f_31
    node f_31 where
      assert (0 ≤ x₃) ⇒ f_32
    node f_32 where
      assert (x₃ ≤ 3) ⇒ f_33
    node f_33 where
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
error: assert failed under #[[1; +∞], [5; +∞], [0; 3], [0; 3]]
---
error: assert failed under #[[1; +∞], [5; 5], [3; 3], [5; 5], [3; 3], [6; 6], [5; 5], [3; 3], [5; 5], [3; 3], [6; 6]]
---
error: assert failed under #[[1; +∞], [5; 5], [3; 3], [5; 5], [3; 3], [6; 6], [5; 5], [3; 3], [5; 5], [3; 3], [6; 6]]
---
trace: [Lustrean.Elab.Compile] ✅️ elabExpr
    node f() = o,o
      where ⏎
        o = o
    ⇒
    node f_0 where
      step := 0 ⇒ f_2
    node f_1 where
      skip ⇒ f_9
    node f_2 where
      x₁ := nil ⇒ f_3
    node f_3 where
      x₂ := x₁ ⇒ f_4
    node f_4 where
      x₁ := x₁ ⇒ f_5
    node f_5 where
      skip ⇒ f_4
      skip ⇒ f_1
      step := (step + 1) ⇒ f_6
    node f_6 where
      x₂ := x₁ ⇒ f_7
    node f_7 where
      x₁ := x₁ ⇒ f_8
    node f_8 where
      step := (step + 1) ⇒ f_6
      skip ⇒ f_7
      skip ⇒ f_9
    node f_9 where
      ⏎
[Lustrean.Elab.Compile] ✅️ elabExpr
    node u(x) = o
      where ⏎
        o = (if (step = [0, 0]) then [0, 0] else (pre x_0))
        x_0 = x
    ⇒
    node f_0 where
      step := 0 ⇒ f_2
    node f_1 where
      skip ⇒ f_20
    node f_2 where
      x₂ := nil ⇒ f_3
    node f_3 where
      x₃ := nil ⇒ f_4
    node f_4 where
      x₄ := x₂ ⇒ f_5
    node f_5 where
      x₅ := x₃ ⇒ f_6
    node f_6 where
      x₁ := [-∞, ∞] ⇒ f_7
    node f_7 where
      guard (step = 0) ⇒ f_8
      guard (step ≠ 0) ⇒ f_9
    node f_8 where
      x₂ := 0 ⇒ f_10
    node f_9 where
      x₂ := x₅ ⇒ f_10
    node f_10 where
      x₃ := x₁ ⇒ f_11
    node f_11 where
      skip ⇒ f_7
      skip ⇒ f_1
      step := (step + 1) ⇒ f_12
    node f_12 where
      x₄ := x₂ ⇒ f_13
    node f_13 where
      x₅ := x₃ ⇒ f_14
    node f_14 where
      x₁ := [-∞, ∞] ⇒ f_15
    node f_15 where
      guard (step = 0) ⇒ f_16
      guard (step ≠ 0) ⇒ f_17
    node f_16 where
      x₂ := 0 ⇒ f_18
    node f_17 where
      x₂ := x₅ ⇒ f_18
    node f_18 where
      x₃ := x₁ ⇒ f_19
    node f_19 where
      step := (step + 1) ⇒ f_12
      skip ⇒ f_15
      skip ⇒ f_20
    node f_20 where
      ⏎
[Lustrean.Elab.Compile] ✅️ elabExpr
    node f(x) = o
      guard
        ([0, 0] ≤ x)
      where ⏎
        o = (if ([3, 3] < x) then [3, 3] else x)
      assert
        ([0, 0] ≤ x)
        (x ≤ [4, 4])
    ⇒
    node f_0 where
      step := 0 ⇒ f_2
    node f_1 where
      skip ⇒ f_19
    node f_2 where
      x₂ := nil ⇒ f_3
    node f_3 where
      x₃ := x₂ ⇒ f_4
    node f_4 where
      x₁ := [-∞, ∞] ⇒ f_5
    node f_5 where
      guard (0 ≤ x₁) ⇒ f_6
    node f_6 where
      guard (3 < x₁) ⇒ f_7
      guard (3 ≥ x₁) ⇒ f_8
    node f_7 where
      x₂ := 3 ⇒ f_9
    node f_8 where
      x₂ := x₁ ⇒ f_9
    node f_9 where
      skip ⇒ f_6
      skip ⇒ f_1
      step := (step + 1) ⇒ f_10
    node f_10 where
      x₃ := x₂ ⇒ f_11
    node f_11 where
      x₁ := [-∞, ∞] ⇒ f_12
    node f_12 where
      guard (0 ≤ x₁) ⇒ f_13
    node f_13 where
      guard (3 < x₁) ⇒ f_14
      guard (3 ≥ x₁) ⇒ f_15
    node f_14 where
      x₂ := 3 ⇒ f_16
    node f_15 where
      x₂ := x₁ ⇒ f_16
    node f_16 where
      step := (step + 1) ⇒ f_10
      skip ⇒ f_13
      skip ⇒ f_17
    node f_17 where
      assert (0 ≤ x₁) ⇒ f_18
    node f_18 where
      assert (x₁ ≤ 4) ⇒ f_19
    node f_19 where
      ⏎
[Lustrean.Elab.Compile] ✅️ elabExpr
    node g() = o
      where ⏎
        o.0.x = [5, 5]
        o.0.o = (if ([3, 3] < o.0.x) then [3, 3] else o.0.x)
        o.1.x = [5, 5]
        o.1.o = (if ([3, 3] < o.1.x) then [3, 3] else o.1.x)
        o = (o.0.o + o.1.o)
      assert
        ([0, 0] ≤ o.0.x)
        ([0, 0] ≤ o.0.x)
        (o.0.x ≤ [4, 4])
        ([0, 0] ≤ o.1.x)
        ([0, 0] ≤ o.1.x)
        (o.1.x ≤ [4, 4])
    ⇒
    node f_0 where
      step := 0 ⇒ f_2
    node f_1 where
      skip ⇒ f_43
    node f_2 where
      x₁ := nil ⇒ f_3
    node f_3 where
      x₂ := nil ⇒ f_4
    node f_4 where
      x₃ := nil ⇒ f_5
    node f_5 where
      x₄ := nil ⇒ f_6
    node f_6 where
      x₅ := nil ⇒ f_7
    node f_7 where
      x₆ := x₁ ⇒ f_8
    node f_8 where
      x₇ := x₂ ⇒ f_9
    node f_9 where
      x₈ := x₃ ⇒ f_10
    node f_10 where
      x₉ := x₄ ⇒ f_11
    node f_11 where
      x₁₀ := x₅ ⇒ f_12
    node f_12 where
      x₁ := 5 ⇒ f_13
    node f_13 where
      guard (3 < x₁) ⇒ f_14
      guard (3 ≥ x₁) ⇒ f_15
    node f_14 where
      x₂ := 3 ⇒ f_16
    node f_15 where
      x₂ := x₁ ⇒ f_16
    node f_16 where
      x₃ := 5 ⇒ f_17
    node f_17 where
      guard (3 < x₃) ⇒ f_18
      guard (3 ≥ x₃) ⇒ f_19
    node f_18 where
      x₄ := 3 ⇒ f_20
    node f_19 where
      x₄ := x₃ ⇒ f_20
    node f_20 where
      x₅ := (x₂ + x₄) ⇒ f_21
    node f_21 where
      skip ⇒ f_12
      skip ⇒ f_1
      step := (step + 1) ⇒ f_22
    node f_22 where
      x₆ := x₁ ⇒ f_23
    node f_23 where
      x₇ := x₂ ⇒ f_24
    node f_24 where
      x₈ := x₃ ⇒ f_25
    node f_25 where
      x₉ := x₄ ⇒ f_26
    node f_26 where
      x₁₀ := x₅ ⇒ f_27
    node f_27 where
      x₁ := 5 ⇒ f_28
    node f_28 where
      guard (3 < x₁) ⇒ f_29
      guard (3 ≥ x₁) ⇒ f_30
    node f_29 where
      x₂ := 3 ⇒ f_31
    node f_30 where
      x₂ := x₁ ⇒ f_31
    node f_31 where
      x₃ := 5 ⇒ f_32
    node f_32 where
      guard (3 < x₃) ⇒ f_33
      guard (3 ≥ x₃) ⇒ f_34
    node f_33 where
      x₄ := 3 ⇒ f_35
    node f_34 where
      x₄ := x₃ ⇒ f_35
    node f_35 where
      x₅ := (x₂ + x₄) ⇒ f_36
    node f_36 where
      step := (step + 1) ⇒ f_22
      skip ⇒ f_27
      skip ⇒ f_37
    node f_37 where
      assert (0 ≤ x₁) ⇒ f_38
    node f_38 where
      assert (0 ≤ x₁) ⇒ f_39
    node f_39 where
      assert (x₁ ≤ 4) ⇒ f_40
    node f_40 where
      assert (0 ≤ x₃) ⇒ f_41
    node f_41 where
      assert (0 ≤ x₃) ⇒ f_42
    node f_42 where
      assert (x₃ ≤ 4) ⇒ f_43
    node f_43 where
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
        o = (if (step = [0, 0]) then [0, 0] else (pre x_0))
        x_0 = ([1, 1] + o)
      assert
        ([0, 0] ≤ o)
    ⇒
    node f_0 where
      step := 0 ⇒ f_2
    node f_1 where
      skip ⇒ f_19
    node f_2 where
      x₁ := nil ⇒ f_3
    node f_3 where
      x₂ := nil ⇒ f_4
    node f_4 where
      x₃ := x₁ ⇒ f_5
    node f_5 where
      x₄ := x₂ ⇒ f_6
    node f_6 where
      guard (step = 0) ⇒ f_7
      guard (step ≠ 0) ⇒ f_8
    node f_7 where
      x₁ := 0 ⇒ f_9
    node f_8 where
      x₁ := x₄ ⇒ f_9
    node f_9 where
      x₂ := (1 + x₁) ⇒ f_10
    node f_10 where
      skip ⇒ f_6
      skip ⇒ f_1
      step := (step + 1) ⇒ f_11
    node f_11 where
      x₃ := x₁ ⇒ f_12
    node f_12 where
      x₄ := x₂ ⇒ f_13
    node f_13 where
      guard (step = 0) ⇒ f_14
      guard (step ≠ 0) ⇒ f_15
    node f_14 where
      x₁ := 0 ⇒ f_16
    node f_15 where
      x₁ := x₄ ⇒ f_16
    node f_16 where
      x₂ := (1 + x₁) ⇒ f_17
    node f_17 where
      step := (step + 1) ⇒ f_11
      skip ⇒ f_13
      skip ⇒ f_18
    node f_18 where
      assert (0 ≤ x₁) ⇒ f_19
    node f_19 where
-/
#guard_msgs in
lustre
  node a() = o where
    o = 0 fby 1 + o
  assert
    o ≥ 0

/--
trace: [Lustrean.Elab.Compile] ✅️ elabExpr
    node f()
      where ⏎
        ⏎
    ⇒
    node f_0 where
      step := 0 ⇒ f_2
    node f_1 where
      skip ⇒ f_4
    node f_2 where
      skip ⇒ f_2
      skip ⇒ f_1
      step := (step + 1) ⇒ f_3
    node f_3 where
      step := (step + 1) ⇒ f_3
      skip ⇒ f_3
      skip ⇒ f_4
    node f_4 where
-/
#guard_msgs in
lustre
  node f() where