import Lustrean.Domain
import Lustrean.Interpreter
import Lustrean.Elaboration

-- lustre
--   node e₁(x) = o
--     guard
--       x ≥ 0
--     where
--       o = 3 + x * [2, ∞]
--     assert
--       o ≠ 0

--   node e₂(x) = o where
--     v = e₁(x)
--     o = v + v

--   node e₃(x) = o where
--     v = e₂(x)
--     o = v + v

--   node e₄(x) = o
--     guard
--       x ≥ 0
--     where
--       o = v + v
--       v = e₃(x)
--     assert
--       o ≥ 0

--   -- node main() = o where
--   --   o = e₄(5)


-- lustre
--   node a() = o₁, o₂ where
--     o₁ = 3
--     o₂ = 5

--   node b() = o₁ where
--     o₁, o₂ = a()