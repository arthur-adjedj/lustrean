import Lustrean

lustre (domain := Sign)
  node f(x) = y
  where   y = if x ≥ 0 then x + 1 else x - 1
  assert  y ≠ 0
