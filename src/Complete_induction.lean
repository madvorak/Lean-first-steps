import data.nat.basic
open nat


private lemma induction_strong_version (P : ℕ → Prop) (n : ℕ) : 
  (∀ x : ℕ, (∀ y : ℕ, y < x → (P y)) → (P x))  →  (∀ z : ℕ, z < n → (P z)) 
  :=
begin
  intro ass,
  induction n with m ih,

    -- base case --
    intros z z_neg,
    exfalso,
    exact nat.not_lt_zero z z_neg,

    -- induction step --
    intros z z_le_m,
    rw lt_succ_iff at z_le_m,
    cases eq_or_lt_of_le z_le_m with z_eq_m z_lt_m,

      -- case of z = m
      specialize ass m,
      rw z_eq_m,
      exact ass ih,

      -- case of z < m
      exact ih z z_lt_m,
end


theorem induction_complete (P : ℕ → Prop) : 
  (∀ x : ℕ, (∀ y : ℕ, y < x → (P y)) → (P x))  →  (∀ n : ℕ, P n) 
  :=
begin
  intro assum,
  intro n,
  exact induction_strong_version P (n+1) assum n (lt_succ_self n),
end