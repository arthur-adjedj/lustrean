import Lustrean.Domain.Sign

open Lustrean.Sign.Notation

/-- info: [>0]-/
#guard_msgs in #eval [>0] + [≥0]

/-- info: [<0]-/
#guard_msgs in #eval [<0] + [≤0]

/-- info: [=0]-/
#guard_msgs in #eval [<0] * [=0]

/-- info: [⊥]-/
#guard_msgs in #eval [<0] / [=0]

-- We keep 0 because if we take e ∈ γ[<0] and e' ∈ γ[≥0]
-- where e' > e.natAbs then e / e' = 0, since we are
-- performing division on integers
/-- info: [≤0]-/
#guard_msgs in #eval [<0] / [≥0]