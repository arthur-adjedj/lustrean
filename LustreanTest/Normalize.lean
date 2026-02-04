import Lustrean

set_option trace.Lustrean.Elab.Normalize true

/--
trace: [Lustrean.Elab.Normalize] ✅️ elabExpr
    node inc(x) = o
      where ⏎
        o = (x + [1, 1])
    ⇒
    some (node inc(x) = o
      where ⏎
        o = (x + [1, 1]))
[Lustrean.Elab.Normalize] ✅️ elabExpr
    node plus2(x) = o
      where ⏎
        o.0.x.1.x = x
        o.0.x.1.o = (o.0.x.1.x + [1, 1])
        o.0.x = o.0.x.1.o
        o.0.o = (o.0.x + [1, 1])
        o = o.0.o
    ⇒
    some (node plus2(x) = o
      where ⏎
        o.0.x.1.x = x
        o.0.x.1.o = (o.0.x.1.x + [1, 1])
        o.0.x = o.0.x.1.o
        o.0.o = (o.0.x + [1, 1])
        o = o.0.o)
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
trace: [Lustrean.Elab.Normalize] ✅️ elabExpr
    node u(x) = o
      where ⏎
        o = ((x * x) + [3, 3])
      assert
        (o ≤ [1, 1])
    ⇒
    some (node u(x) = o
      where ⏎
        o = ((x * x) + [3, 3])
      assert
        (o ≤ [1, 1]))
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
trace: [Lustrean.Elab.Normalize] ✅️ elabExpr
    node u(x) = o
      where ⏎
        o = (x * x)
      assert
        ([0, 0] ≤ o)
    ⇒
    some (node u(x) = o
      where ⏎
        o = (x * x)
      assert
        ([0, 0] ≤ o))
[Lustrean.Elab.Normalize] ✅️ elabExpr
    node v(x)
      where ⏎
        x2 = (if ([0, 0] ≤ x) then (x * x) else (x * x))
        o = (x2 + [3, 3])
      assert
        ([3, 3] ≤ o)
    ⇒
    some (node v(x)
      where ⏎
        x2 = (if ([0, 0] ≤ x) then (x * x) else (x * x))
        o = (x2 + [3, 3])
      assert
        ([3, 3] ≤ o))
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
trace: [Lustrean.Elab.Normalize] ✅️ elabExpr
    node f() = x
      where ⏎
        x = y
        y = x
    ⇒
    some (node f() = x
      where ⏎
        x = y
        y = x)
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
trace: [Lustrean.Elab.Normalize] ✅️ elabExpr
    node f(c,z) = x,y
      where ⏎
        x = (if (c = [0, 0]) then z else y)
        y = (if (c = [0, 0]) then x else z)
    ⇒
    some (node f(c,z) = x,y
      where ⏎
        x = (if (c = [0, 0]) then z else y)
        y = (if (c = [0, 0]) then x else z))
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
trace: [Lustrean.Elab.Normalize] ✅️ elabExpr
    node l() = o
      where ⏎
        up = ([1, 1] fby (if (((up = [1, 1]) ∧ (o < [10, 10])) ∨ ((up = [0, 0]) ∧ (o = [0, 0]))) then [1, 1] else [0, 0]))
        o = ([0, 0] fby (if (up = [1, 1]) then (o + [1, 1]) else (o - [1, 1])))
      assert
        ([0, 0] ≤ o)
    ⇒
    some (node l() = o
      where ⏎
        up = (if (step = [0, 0]) then [1, 1] else (pre x_0))
        o = (if (step = [0, 0]) then [0, 0] else (pre x_1))
        x_0 = (if (((up = [1, 1]) ∧ (o < [10, 10])) ∨ ((up = [0, 0]) ∧ (o = [0, 0]))) then [1, 1] else [0, 0])
        x_1 = (if (up = [1, 1]) then (o + [1, 1]) else (o - [1, 1]))
      assert
        ([0, 0] ≤ o))
-/
#guard_msgs in
lustre
  node l() = o where
    up = 1 fby if (up = 1 ∧ o < 10) ∨ (up = 0 ∧ o = 0) then 1 else 0
    o = 0 fby if up = 1 then o + 1 else o - 1
  assert
    0 ≤ o

/--
trace: [Lustrean.Elab.Normalize] ✅️ elabExpr
    node f(x) = o
      guard
        ([0, 0] ≤ x)
      where ⏎
        o = (if ([3, 3] < x) then [3, 3] else x)
      assert
        ([0, 0] ≤ o)
        (o ≤ [3, 3])
    ⇒
    some (node f(x) = o
      guard
        ([0, 0] ≤ x)
      where ⏎
        o = (if ([3, 3] < x) then [3, 3] else x)
      assert
        ([0, 0] ≤ o)
        (o ≤ [3, 3]))
[Lustrean.Elab.Normalize] ✅️ elabExpr
    node g(x) = o
      guard
        ([0, 0] ≤ x)
      where ⏎
        y = (x fby (y + [1, 1]))
        o = (if ([3, 3] < y) then [3, 3] else y)
      assert
        ([0, 0] ≤ o)
        (o ≤ [3, 3])
    ⇒
    some (node g(x) = o
      guard
        ([0, 0] ≤ x)
      where ⏎
        y = (if (step = [0, 0]) then x else (pre x_0))
        o = (if ([3, 3] < y) then [3, 3] else y)
        x_0 = (y + [1, 1])
      assert
        ([0, 0] ≤ o)
        (o ≤ [3, 3]))
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
trace: [Lustrean.Elab.Normalize] ✅️ elabExpr
    node f() = o,o
      where ⏎
        o = o
    ⇒
    some (node f() = o,o
      where ⏎
        o = o)
[Lustrean.Elab.Normalize] ✅️ elabExpr
    node u(x) = o
      where ⏎
        o = ([0, 0] fby x)
    ⇒
    some (node u(x) = o
      where ⏎
        o = (if (step = [0, 0]) then [0, 0] else (pre x_0))
        x_0 = x)
[Lustrean.Elab.Normalize] ✅️ elabExpr
    node f(x) = o
      guard
        ([0, 0] ≤ x)
      where ⏎
        o = (if ([3, 3] < x) then [3, 3] else x)
      assert
        ([0, 0] ≤ x)
        (x ≤ [4, 4])
    ⇒
    some (node f(x) = o
      guard
        ([0, 0] ≤ x)
      where ⏎
        o = (if ([3, 3] < x) then [3, 3] else x)
      assert
        ([0, 0] ≤ x)
        (x ≤ [4, 4]))
[Lustrean.Elab.Normalize] ✅️ elabExpr
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
    some (node g() = o
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
        (o.1.x ≤ [4, 4]))
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
trace: [Lustrean.Elab.Normalize] ✅️ elabExpr
    node a() = o
      where ⏎
        o = ([0, 0] fby ([1, 1] + o))
      assert
        ([0, 0] ≤ o)
    ⇒
    some (node a() = o
      where ⏎
        o = (if (step = [0, 0]) then [0, 0] else (pre x_0))
        x_0 = ([1, 1] + o)
      assert
        ([0, 0] ≤ o))
-/
#guard_msgs in
lustre
  node a() = o where
    o = 0 fby 1 + o
  assert
    o ≥ 0

/--
trace: [Lustrean.Elab.Normalize] ✅️ elabExpr
    node h() = o,i
      where ⏎
        o = ([0, 0] fby ([1, 1] fby (i + [1, 1])))
        i = (if (o = [5, 5]) then (if (([0, 0] < [0, 0]) ∨ ([0, 0] < [0, 0])) then [1, 1] else [2, 2]) else [0, 0])
    ⇒
    some (node h() = o,i
      where ⏎
        o = (if (step = [0, 0]) then [0, 0] else (pre x_1))
        i = (if (o = [5, 5]) then x_2 else [0, 0])
        x_0 = (i + [1, 1])
        x_1 = (if (step = [0, 0]) then [1, 1] else (pre x_0))
        x_2 = (if (([0, 0] < [0, 0]) ∨ ([0, 0] < [0, 0])) then [1, 1] else [2, 2]))
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
trace: [Lustrean.Elab.Normalize] ✅️ elabExpr
    node f()
      where ⏎
        ⏎
    ⇒
    some (node f()
      where ⏎
        )
-/
#guard_msgs in
lustre
  node f() where



/- This test ensures that `pre x` and ` a fby x` does not introduce a new bvar in `Normalize` when `x` is itself a bvar-/

/--
error: variable y could be nil
---
trace: [Lustrean.Elab.Normalize] ✅️ elabExpr
    node f() = x,y
      where ⏎
        x = ([0, 0] fby x)
        y = (pre x)
    ⇒
    some (node f() = x,y
      where ⏎
        x = (if (step = [0, 0]) then [0, 0] else (pre x))
        y = (pre x))
-/
#guard_msgs in
lustre
  node f() = x,y where
    x = 0 fby x
    y = pre x