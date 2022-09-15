import algebra.group.basic


lemma right_inverse_eq_left_inverse {T : Type} [monoid T]
  {a b c : T} (inv_right : a * b = 1) (inv_left : c * a = 1) :
  b = c :=
calc b = 1 * b : (one_mul b).symm
... = (c * a) * b : by rw inv_left
... = c * (a * b) : mul_assoc c a b
... = c * 1 : by rw inv_right
... = c : mul_one c


lemma right_inverse_unique {T : Type} [group T]
  {a b c : T} (inv_ab : a * b = 1) (inv_ac : a * c = 1) :
  b = c :=
calc b = 1 * b : (one_mul b).symm
... = (a⁻¹ * a) * b : by rw mul_left_inv
... = a⁻¹ * (a * b) : mul_assoc a⁻¹ a b
... = a⁻¹ * 1 : by rw inv_ab
... = a⁻¹ * (a * c) : by rw inv_ac
... = (a⁻¹ * a) * c : (mul_assoc a⁻¹ a c).symm
... = 1 * c : by rw mul_left_inv
... = c : one_mul c

lemma right_inverse_unique_aux {T : Type} [group T]
  {a b : T} (inv_ab : a * b = 1) :
  b = a⁻¹ :=
calc b = 1 * b : (one_mul b).symm
... = (a⁻¹ * a) * b : by rw mul_left_inv
... = a⁻¹ * (a * b) : mul_assoc a⁻¹ a b
... = a⁻¹ * 1 : by rw inv_ab
... = a⁻¹ : mul_one a⁻¹

lemma right_inverse_unique' {T : Type} [group T]
  {a b c : T} (inv_ab : a * b = 1) (inv_ac : a * c = 1) :
  b = c :=
begin
  rw right_inverse_unique_aux inv_ab,
  rw right_inverse_unique_aux inv_ac,
end
