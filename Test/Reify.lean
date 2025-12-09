import Lustrean

set_option trace.Lustrean.Elab.Reify true

/--
trace: [Lustrean.Elab.Reify] ✅️ elabNode
    node inc(x) = o where o = x + [1, 1]
    ⇒
    node inc(x) = o
      where ⏎
        o = x + 1
  [Lustrean.Elab.Reify] ✅️ elabExpr
      x + [1, 1]
      ⇒
      some (x + 1)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        x
        ⇒
        some (x)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        [1, 1]
        ⇒
        some (1)
[Lustrean.Elab.Reify] ✅️ elabNode
    node plus2(x) = o where o = inc(inc(x))
    ⇒
    node plus2(x) = o
      where ⏎
        o = inc(inc(x))
  [Lustrean.Elab.Reify] ✅️ elabExpr
      inc(inc(x))
      ⇒
      some (inc(inc(x)))
    [Lustrean.Elab.Reify] ✅️ elabExpr
        inc(x)
        ⇒
        some (inc(x))
      [Lustrean.Elab.Reify] ✅️ elabExpr
          x
          ⇒
          some (x)
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
trace: [Lustrean.Elab.Reify] ✅️ elabNode
    node u(x) = o where o = x * x + [3, 3] assert o ≤ [1, 1]
    ⇒
    node u(x) = o
      where ⏎
        o = x * x + 3
      assert
        o ≤ 1
  [Lustrean.Elab.Reify] ✅️ elabExpr
      x * x + [3, 3]
      ⇒
      some (x * x + 3)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        x * x
        ⇒
        some (x * x)
      [Lustrean.Elab.Reify] ✅️ elabExpr
          x
          ⇒
          some (x)
      [Lustrean.Elab.Reify] ✅️ elabExpr
          x
          ⇒
          some (x)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        [3, 3]
        ⇒
        some (3)
  [Lustrean.Elab.Reify] ✅️ elabBoolExpr
      o ≤ [1, 1]
      ⇒
      some (o ≤ 1)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        o
        ⇒
        some (o)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        [1, 1]
        ⇒
        some (1)
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
trace: [Lustrean.Elab.Reify] ✅️ elabNode
    node u(x) = o where
      -- o = if x ≥ 0 then x * x else x * x
      o = x * x assert[0, 0] ≤ o
    ⇒
    node u(x) = o
      where ⏎
        o = x * x
      assert
        0 ≤ o
  [Lustrean.Elab.Reify] ✅️ elabExpr
      x * x
      ⇒
      some (x * x)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        x
        ⇒
        some (x)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        x
        ⇒
        some (x)
  [Lustrean.Elab.Reify] ✅️ elabBoolExpr
      [0, 0] ≤ o
      ⇒
      some (0 ≤ o)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        [0, 0]
        ⇒
        some (0)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        o
        ⇒
        some (o)
[Lustrean.Elab.Reify] ✅️ elabNode
    node v(x) where x2 = if [0, 0] ≤ x then x * x else x * x o = x2 + [3, 3] assert[3, 3] ≤ o
    ⇒
    node v(x)
      where ⏎
        x2 = if 0 ≤ x then x * x else x * x
        o = x2 + 3
      assert
        3 ≤ o
  [Lustrean.Elab.Reify] ✅️ elabExpr
       if [0, 0] ≤ x then x * x else x * x
      ⇒
      some (if 0 ≤ x then x * x else x * x)
    [Lustrean.Elab.Reify] ✅️ elabBoolExpr
        [0, 0] ≤ x
        ⇒
        some (0 ≤ x)
      [Lustrean.Elab.Reify] ✅️ elabExpr
          [0, 0]
          ⇒
          some (0)
      [Lustrean.Elab.Reify] ✅️ elabExpr
          x
          ⇒
          some (x)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        x * x
        ⇒
        some (x * x)
      [Lustrean.Elab.Reify] ✅️ elabExpr
          x
          ⇒
          some (x)
      [Lustrean.Elab.Reify] ✅️ elabExpr
          x
          ⇒
          some (x)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        x * x
        ⇒
        some (x * x)
      [Lustrean.Elab.Reify] ✅️ elabExpr
          x
          ⇒
          some (x)
      [Lustrean.Elab.Reify] ✅️ elabExpr
          x
          ⇒
          some (x)
  [Lustrean.Elab.Reify] ✅️ elabExpr
      x2 + [3, 3]
      ⇒
      some (x2 + 3)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        x2
        ⇒
        some (x2)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        [3, 3]
        ⇒
        some (3)
  [Lustrean.Elab.Reify] ✅️ elabBoolExpr
      [3, 3] ≤ o
      ⇒
      some (3 ≤ o)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        [3, 3]
        ⇒
        some (3)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        o
        ⇒
        some (o)
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
trace: [Lustrean.Elab.Reify] ✅️ elabNode
    node f() = x where x = y y = x
    ⇒
    node f() = x
      where ⏎
        x = y
        y = x
  [Lustrean.Elab.Reify] ✅️ elabExpr
      y
      ⇒
      some (y)
  [Lustrean.Elab.Reify] ✅️ elabExpr
      x
      ⇒
      some (x)
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
trace: [Lustrean.Elab.Reify] ✅️ elabNode
    node f(c, z) = x, y where x = if c = [0, 0] then z else y y = if c = [0, 0] then x else z
    ⇒
    node f(c,z) = x,y
      where ⏎
        x = if c = 0 then z else y
        y = if c = 0 then x else z
  [Lustrean.Elab.Reify] ✅️ elabExpr
       if c = [0, 0] then z else y
      ⇒
      some (if c = 0 then z else y)
    [Lustrean.Elab.Reify] ✅️ elabBoolExpr
        c = [0, 0]
        ⇒
        some (c = 0)
      [Lustrean.Elab.Reify] ✅️ elabExpr
          c
          ⇒
          some (c)
      [Lustrean.Elab.Reify] ✅️ elabExpr
          [0, 0]
          ⇒
          some (0)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        z
        ⇒
        some (z)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        y
        ⇒
        some (y)
  [Lustrean.Elab.Reify] ✅️ elabExpr
       if c = [0, 0] then x else z
      ⇒
      some (if c = 0 then x else z)
    [Lustrean.Elab.Reify] ✅️ elabBoolExpr
        c = [0, 0]
        ⇒
        some (c = 0)
      [Lustrean.Elab.Reify] ✅️ elabExpr
          c
          ⇒
          some (c)
      [Lustrean.Elab.Reify] ✅️ elabExpr
          [0, 0]
          ⇒
          some (0)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        x
        ⇒
        some (x)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        z
        ⇒
        some (z)
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
trace: [Lustrean.Elab.Reify] ✅️ elabNode
    node l() = o where
      up =
        [1,
            1] fby if up = [1, 1] ∧ o < [10, 10] ∨ up = [0, 0] ∧ o = [0, 0] then [1, 1] else
            [0, 0]o = [0, 0] fby if up = [1, 1] then o + [1, 1] else o - [1, 1] assert[0, 0] ≤ o
    ⇒
    node l() = o
      where ⏎
        up = 1 fby if up = 1 ∧ o < 10 ∨ up = 0 ∧ o = 0 then 1 else 0
        o = 0 fby if up = 1 then o + 1 else o - 1
      assert
        0 ≤ o
  [Lustrean.Elab.Reify] ✅️ elabExpr
      [1, 1] fby if up = [1, 1] ∧ o < [10, 10] ∨ up = [0, 0] ∧ o = [0, 0] then [1, 1] else [0, 0]
      ⇒
      some (1 fby if up = 1 ∧ o < 10 ∨ up = 0 ∧ o = 0 then 1 else 0)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        [1, 1]
        ⇒
        some (1)
    [Lustrean.Elab.Reify] ✅️ elabExpr
         if up = [1, 1] ∧ o < [10, 10] ∨ up = [0, 0] ∧ o = [0, 0] then [1, 1] else [0, 0]
        ⇒
        some (if up = 1 ∧ o < 10 ∨ up = 0 ∧ o = 0 then 1 else 0)
      [Lustrean.Elab.Reify] ✅️ elabBoolExpr
          up = [1, 1] ∧ o < [10, 10] ∨ up = [0, 0] ∧ o = [0, 0]
          ⇒
          some (up = 1 ∧ o < 10 ∨ up = 0 ∧ o = 0)
        [Lustrean.Elab.Reify] ✅️ elabBoolExpr
            up = [1, 1] ∧ o < [10, 10]
            ⇒
            some (up = 1 ∧ o < 10)
          [Lustrean.Elab.Reify] ✅️ elabBoolExpr
              up = [1, 1]
              ⇒
              some (up = 1)
            [Lustrean.Elab.Reify] ✅️ elabExpr
                up
                ⇒
                some (up)
            [Lustrean.Elab.Reify] ✅️ elabExpr
                [1, 1]
                ⇒
                some (1)
          [Lustrean.Elab.Reify] ✅️ elabBoolExpr
              o < [10, 10]
              ⇒
              some (o < 10)
            [Lustrean.Elab.Reify] ✅️ elabExpr
                o
                ⇒
                some (o)
            [Lustrean.Elab.Reify] ✅️ elabExpr
                [10, 10]
                ⇒
                some (10)
        [Lustrean.Elab.Reify] ✅️ elabBoolExpr
            up = [0, 0] ∧ o = [0, 0]
            ⇒
            some (up = 0 ∧ o = 0)
          [Lustrean.Elab.Reify] ✅️ elabBoolExpr
              up = [0, 0]
              ⇒
              some (up = 0)
            [Lustrean.Elab.Reify] ✅️ elabExpr
                up
                ⇒
                some (up)
            [Lustrean.Elab.Reify] ✅️ elabExpr
                [0, 0]
                ⇒
                some (0)
          [Lustrean.Elab.Reify] ✅️ elabBoolExpr
              o = [0, 0]
              ⇒
              some (o = 0)
            [Lustrean.Elab.Reify] ✅️ elabExpr
                o
                ⇒
                some (o)
            [Lustrean.Elab.Reify] ✅️ elabExpr
                [0, 0]
                ⇒
                some (0)
      [Lustrean.Elab.Reify] ✅️ elabExpr
          [1, 1]
          ⇒
          some (1)
      [Lustrean.Elab.Reify] ✅️ elabExpr
          [0, 0]
          ⇒
          some (0)
  [Lustrean.Elab.Reify] ✅️ elabExpr
      [0, 0] fby if up = [1, 1] then o + [1, 1] else o - [1, 1]
      ⇒
      some (0 fby if up = 1 then o + 1 else o - 1)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        [0, 0]
        ⇒
        some (0)
    [Lustrean.Elab.Reify] ✅️ elabExpr
         if up = [1, 1] then o + [1, 1] else o - [1, 1]
        ⇒
        some (if up = 1 then o + 1 else o - 1)
      [Lustrean.Elab.Reify] ✅️ elabBoolExpr
          up = [1, 1]
          ⇒
          some (up = 1)
        [Lustrean.Elab.Reify] ✅️ elabExpr
            up
            ⇒
            some (up)
        [Lustrean.Elab.Reify] ✅️ elabExpr
            [1, 1]
            ⇒
            some (1)
      [Lustrean.Elab.Reify] ✅️ elabExpr
          o + [1, 1]
          ⇒
          some (o + 1)
        [Lustrean.Elab.Reify] ✅️ elabExpr
            o
            ⇒
            some (o)
        [Lustrean.Elab.Reify] ✅️ elabExpr
            [1, 1]
            ⇒
            some (1)
      [Lustrean.Elab.Reify] ✅️ elabExpr
          o - [1, 1]
          ⇒
          some (o - 1)
        [Lustrean.Elab.Reify] ✅️ elabExpr
            o
            ⇒
            some (o)
        [Lustrean.Elab.Reify] ✅️ elabExpr
            [1, 1]
            ⇒
            some (1)
  [Lustrean.Elab.Reify] ✅️ elabBoolExpr
      [0, 0] ≤ o
      ⇒
      some (0 ≤ o)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        [0, 0]
        ⇒
        some (0)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        o
        ⇒
        some (o)
-/
#guard_msgs in
lustre
  node l() = o where
    up = 1 fby if (up = 1 ∧ o < 10) ∨ (up = 0 ∧ o = 0) then 1 else 0
    o = 0 fby if up = 1 then o + 1 else o - 1
  assert
    0 ≤ o

/--
trace: [Lustrean.Elab.Reify] ✅️ elabNode
    node f(x) = o guard[0, 0] ≤ x where o = if [3, 3] < x then [3, 3] else x assert[0, 0] ≤ o o ≤ [3, 3]
    ⇒
    node f(x) = o
      guard
        0 ≤ x
      where ⏎
        o = if 3 < x then 3 else x
      assert
        0 ≤ o
        o ≤ 3
  [Lustrean.Elab.Reify] ✅️ elabExpr
       if [3, 3] < x then [3, 3] else x
      ⇒
      some (if 3 < x then 3 else x)
    [Lustrean.Elab.Reify] ✅️ elabBoolExpr
        [3, 3] < x
        ⇒
        some (3 < x)
      [Lustrean.Elab.Reify] ✅️ elabExpr
          [3, 3]
          ⇒
          some (3)
      [Lustrean.Elab.Reify] ✅️ elabExpr
          x
          ⇒
          some (x)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        [3, 3]
        ⇒
        some (3)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        x
        ⇒
        some (x)
  [Lustrean.Elab.Reify] ✅️ elabBoolExpr
      [0, 0] ≤ x
      ⇒
      some (0 ≤ x)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        [0, 0]
        ⇒
        some (0)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        x
        ⇒
        some (x)
  [Lustrean.Elab.Reify] ✅️ elabBoolExpr
      [0, 0] ≤ o
      ⇒
      some (0 ≤ o)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        [0, 0]
        ⇒
        some (0)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        o
        ⇒
        some (o)
  [Lustrean.Elab.Reify] ✅️ elabBoolExpr
      o ≤ [3, 3]
      ⇒
      some (o ≤ 3)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        o
        ⇒
        some (o)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        [3, 3]
        ⇒
        some (3)
[Lustrean.Elab.Reify] ✅️ elabNode
    node g(x) = o guard[0, 0] ≤ x where
      y = x fby y + [1, 1]o = if [3, 3] < y then [3, 3] else y assert[0, 0] ≤ o o ≤ [3, 3]
    ⇒
    node g(x) = o
      guard
        0 ≤ x
      where ⏎
        y = x fby y + 1
        o = if 3 < y then 3 else y
      assert
        0 ≤ o
        o ≤ 3
  [Lustrean.Elab.Reify] ✅️ elabExpr
      x fby y + [1, 1]
      ⇒
      some (x fby y + 1)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        x
        ⇒
        some (x)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        y + [1, 1]
        ⇒
        some (y + 1)
      [Lustrean.Elab.Reify] ✅️ elabExpr
          y
          ⇒
          some (y)
      [Lustrean.Elab.Reify] ✅️ elabExpr
          [1, 1]
          ⇒
          some (1)
  [Lustrean.Elab.Reify] ✅️ elabExpr
       if [3, 3] < y then [3, 3] else y
      ⇒
      some (if 3 < y then 3 else y)
    [Lustrean.Elab.Reify] ✅️ elabBoolExpr
        [3, 3] < y
        ⇒
        some (3 < y)
      [Lustrean.Elab.Reify] ✅️ elabExpr
          [3, 3]
          ⇒
          some (3)
      [Lustrean.Elab.Reify] ✅️ elabExpr
          y
          ⇒
          some (y)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        [3, 3]
        ⇒
        some (3)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        y
        ⇒
        some (y)
  [Lustrean.Elab.Reify] ✅️ elabBoolExpr
      [0, 0] ≤ x
      ⇒
      some (0 ≤ x)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        [0, 0]
        ⇒
        some (0)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        x
        ⇒
        some (x)
  [Lustrean.Elab.Reify] ✅️ elabBoolExpr
      [0, 0] ≤ o
      ⇒
      some (0 ≤ o)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        [0, 0]
        ⇒
        some (0)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        o
        ⇒
        some (o)
  [Lustrean.Elab.Reify] ✅️ elabBoolExpr
      o ≤ [3, 3]
      ⇒
      some (o ≤ 3)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        o
        ⇒
        some (o)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        [3, 3]
        ⇒
        some (3)
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
trace: [Lustrean.Elab.Reify] ✅️ elabNode
    node f() = o, o where o = o
    ⇒
    node f() = o,o
      where ⏎
        o = o
  [Lustrean.Elab.Reify] ✅️ elabExpr
      o
      ⇒
      some (o)
[Lustrean.Elab.Reify] ✅️ elabNode
    node u(x) = o where o = [0, 0] fby x
    ⇒
    node u(x) = o
      where ⏎
        o = 0 fby x
  [Lustrean.Elab.Reify] ✅️ elabExpr
      [0, 0] fby x
      ⇒
      some (0 fby x)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        [0, 0]
        ⇒
        some (0)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        x
        ⇒
        some (x)
[Lustrean.Elab.Reify] ✅️ elabNode
    node f(x) = o guard[0, 0] ≤ x where o = if [3, 3] < x then [3, 3] else x assert[0, 0] ≤ x x ≤ [4, 4]
    ⇒
    node f(x) = o
      guard
        0 ≤ x
      where ⏎
        o = if 3 < x then 3 else x
      assert
        0 ≤ x
        x ≤ 4
  [Lustrean.Elab.Reify] ✅️ elabExpr
       if [3, 3] < x then [3, 3] else x
      ⇒
      some (if 3 < x then 3 else x)
    [Lustrean.Elab.Reify] ✅️ elabBoolExpr
        [3, 3] < x
        ⇒
        some (3 < x)
      [Lustrean.Elab.Reify] ✅️ elabExpr
          [3, 3]
          ⇒
          some (3)
      [Lustrean.Elab.Reify] ✅️ elabExpr
          x
          ⇒
          some (x)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        [3, 3]
        ⇒
        some (3)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        x
        ⇒
        some (x)
  [Lustrean.Elab.Reify] ✅️ elabBoolExpr
      [0, 0] ≤ x
      ⇒
      some (0 ≤ x)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        [0, 0]
        ⇒
        some (0)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        x
        ⇒
        some (x)
  [Lustrean.Elab.Reify] ✅️ elabBoolExpr
      [0, 0] ≤ x
      ⇒
      some (0 ≤ x)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        [0, 0]
        ⇒
        some (0)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        x
        ⇒
        some (x)
  [Lustrean.Elab.Reify] ✅️ elabBoolExpr
      x ≤ [4, 4]
      ⇒
      some (x ≤ 4)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        x
        ⇒
        some (x)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        [4, 4]
        ⇒
        some (4)
[Lustrean.Elab.Reify] ✅️ elabNode
    node g() = o where o = f([5, 5]) + f([5, 5])
    ⇒
    node g() = o
      where ⏎
        o = f(5) + f(5)
  [Lustrean.Elab.Reify] ✅️ elabExpr
      f([5, 5]) + f([5, 5])
      ⇒
      some (f(5) + f(5))
    [Lustrean.Elab.Reify] ✅️ elabExpr
        f([5, 5])
        ⇒
        some (f(5))
      [Lustrean.Elab.Reify] ✅️ elabExpr
          [5, 5]
          ⇒
          some (5)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        f([5, 5])
        ⇒
        some (f(5))
      [Lustrean.Elab.Reify] ✅️ elabExpr
          [5, 5]
          ⇒
          some (5)
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
trace: [Lustrean.Elab.Reify] ✅️ elabNode
    node a() = o where o = [0, 0] fby [1, 1] + o assert[0, 0] ≤ o
    ⇒
    node a() = o
      where ⏎
        o = 0 fby 1 + o
      assert
        0 ≤ o
  [Lustrean.Elab.Reify] ✅️ elabExpr
      [0, 0] fby [1, 1] + o
      ⇒
      some (0 fby 1 + o)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        [0, 0]
        ⇒
        some (0)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        [1, 1] + o
        ⇒
        some (1 + o)
      [Lustrean.Elab.Reify] ✅️ elabExpr
          [1, 1]
          ⇒
          some (1)
      [Lustrean.Elab.Reify] ✅️ elabExpr
          o
          ⇒
          some (o)
  [Lustrean.Elab.Reify] ✅️ elabBoolExpr
      [0, 0] ≤ o
      ⇒
      some (0 ≤ o)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        [0, 0]
        ⇒
        some (0)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        o
        ⇒
        some (o)
-/
#guard_msgs in
lustre
  node a() = o where
    o = 0 fby 1 + o
  assert
    o ≥ 0

/--
trace: [Lustrean.Elab.Reify] ✅️ elabNode
    node h() = o, i where
      o =
        [0, 0] fby
          [1, 1] fby
            i + [1, 1]i = if o = [5, 5] then if [0, 0] < [0, 0] ∨ [0, 0] < [0, 0] then [1, 1] else [2, 2] else [0, 0]
    ⇒
    node h() = o,i
      where ⏎
        o = 0 fby 1 fby i + 1
        i = if o = 5 then if 0 < 0 ∨ 0 < 0 then 1 else 2 else 0
  [Lustrean.Elab.Reify] ✅️ elabExpr
      [0, 0] fby [1, 1] fby i + [1, 1]
      ⇒
      some (0 fby 1 fby i + 1)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        [0, 0]
        ⇒
        some (0)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        [1, 1] fby i + [1, 1]
        ⇒
        some (1 fby i + 1)
      [Lustrean.Elab.Reify] ✅️ elabExpr
          [1, 1]
          ⇒
          some (1)
      [Lustrean.Elab.Reify] ✅️ elabExpr
          i + [1, 1]
          ⇒
          some (i + 1)
        [Lustrean.Elab.Reify] ✅️ elabExpr
            i
            ⇒
            some (i)
        [Lustrean.Elab.Reify] ✅️ elabExpr
            [1, 1]
            ⇒
            some (1)
  [Lustrean.Elab.Reify] ✅️ elabExpr
       if o = [5, 5] then if [0, 0] < [0, 0] ∨ [0, 0] < [0, 0] then [1, 1] else [2, 2] else [0, 0]
      ⇒
      some (if o = 5 then if 0 < 0 ∨ 0 < 0 then 1 else 2 else 0)
    [Lustrean.Elab.Reify] ✅️ elabBoolExpr
        o = [5, 5]
        ⇒
        some (o = 5)
      [Lustrean.Elab.Reify] ✅️ elabExpr
          o
          ⇒
          some (o)
      [Lustrean.Elab.Reify] ✅️ elabExpr
          [5, 5]
          ⇒
          some (5)
    [Lustrean.Elab.Reify] ✅️ elabExpr
         if [0, 0] < [0, 0] ∨ [0, 0] < [0, 0] then [1, 1] else [2, 2]
        ⇒
        some (if 0 < 0 ∨ 0 < 0 then 1 else 2)
      [Lustrean.Elab.Reify] ✅️ elabBoolExpr
          [0, 0] < [0, 0] ∨ [0, 0] < [0, 0]
          ⇒
          some (0 < 0 ∨ 0 < 0)
        [Lustrean.Elab.Reify] ✅️ elabBoolExpr
            [0, 0] < [0, 0]
            ⇒
            some (0 < 0)
          [Lustrean.Elab.Reify] ✅️ elabExpr
              [0, 0]
              ⇒
              some (0)
          [Lustrean.Elab.Reify] ✅️ elabExpr
              [0, 0]
              ⇒
              some (0)
        [Lustrean.Elab.Reify] ✅️ elabBoolExpr
            [0, 0] < [0, 0]
            ⇒
            some (0 < 0)
          [Lustrean.Elab.Reify] ✅️ elabExpr
              [0, 0]
              ⇒
              some (0)
          [Lustrean.Elab.Reify] ✅️ elabExpr
              [0, 0]
              ⇒
              some (0)
      [Lustrean.Elab.Reify] ✅️ elabExpr
          [1, 1]
          ⇒
          some (1)
      [Lustrean.Elab.Reify] ✅️ elabExpr
          [2, 2]
          ⇒
          some (2)
    [Lustrean.Elab.Reify] ✅️ elabExpr
        [0, 0]
        ⇒
        some (0)
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
trace: [Lustrean.Elab.Reify] ✅️ elabNode
    node f() where
    ⇒
    node f()
      where
-/
#guard_msgs in
lustre
  node f() where
