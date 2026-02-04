namespace Int
variable (n m o : Int)

theorem min_max_absorb : min n (max n m) = n := by
  apply Int.min_eq_left
  apply Int.le_max_left

theorem max_min_absorb : max n (min n m) = n := by
  apply Int.max_eq_left
  apply Int.min_le_left
end Int