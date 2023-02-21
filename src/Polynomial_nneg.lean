import data.real.basic

example (x : ℝ) (h : 0 ≤ x) : 0 ≤ x ^ 3 - x ^ 2 + 1 :=
begin
  by_cases x_vs_one : x ≤ 1,
  {
    convert_to 0 ≤ x ^ 3 + 1 - x ^ 2,
    { rw sub_add_eq_add_sub },
    have x_cub : 0 ≤ x ^ 3 := pow_nonneg h 3,
    have x_sqr : x ^ 2 ≤ 1 := (sq_le_one_iff h).mpr x_vs_one,
    have one_sub_x_sqr : 0 ≤ 1 - x ^ 2 := sub_nonneg.mpr x_sqr,
    rw ←add_sub,
    exact add_nonneg x_cub one_sub_x_sqr,
  },
  {
    convert_to 0 ≤ x ^ 2 * (x - 1) + 1,
    { ring },
    nlinarith,
  },
end
