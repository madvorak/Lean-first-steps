import data.real.basic
import tactic

-- based on Lean Tutorial / 05_sequence_limits.lean
-- https://github.com/leanprover-community/tutorials

def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, abs (u n - l) ≤ ε



-- Arithmetic of limits: sum law
-- If [`u` tends to `a`] and [`v` tends `b`], then [`u+v` tends to `a+b`].
example (u v : ℕ → ℝ) (a b : ℝ) (hu : seq_limit u a) (hv : seq_limit v b) :
  seq_limit (u + v) (a + b) 
  :=
begin
  intro ε,
  intro epp,
  have ephp : ε/2 > 0,
    linarith,
  specialize hu (ε/2) ephp,
  specialize hv (ε/2) ephp,

  cases hu with Nᵤ limit_u,
  cases hv with Nᵥ limit_v,
  have prop_u : max Nᵤ Nᵥ ≥ Nᵤ,
   exact le_max_left Nᵤ Nᵥ,
  have prop_v : max Nᵤ Nᵥ ≥ Nᵥ,
   exact le_max_right Nᵤ Nᵥ,

  use max Nᵤ Nᵥ,
  intro n,
  specialize limit_u n,
  specialize limit_v n,
  intro ass,

  have n_large_u : n ≥ Nᵤ,
    linarith,
  have n_large_v : n ≥ Nᵥ,
    linarith,
  specialize limit_u n_large_u,
  specialize limit_v n_large_v,

  apply abs_le'.2,
  cases (abs_le'.1 limit_u),
  cases (abs_le'.1 limit_v),
  split,

  calc (u + v) n - (a + b) = (u n) + (v n) - (a + b)   : by refl
  ...                      = ((u n) - a) + ((v n) - b) : by ring
  ...                      ≤ (ε / 2) + ((v n) - b)     : by linarith
  ...                      ≤ (ε / 2) + (ε / 2)         : by linarith
  ...                      = ε                         : by ring,

  calc -((u + v) n - (a + b)) = - ((u n) + (v n) - (a + b))   : by refl
  ...                         = - (((u n) - a) + ((v n) - b)) : by ring
  ...                         = -((u n) - a) + (-((v n) - b)) : by ring
  ...                         ≤ (ε / 2) + (-((v n) - b))      : by linarith
  ...                         ≤ (ε / 2) + (ε / 2)             : by linarith
  ...                         = ε                             : by ring,
end


-- Squeeze theorem (a.k.a. Sandwich rule, Two policemen and a drunk, ...)
-- If [`u` approches `l`] and [`v` approches `l`], then [`w` such that `u ≤ w ≤ v` approaches `l` as well].
example (u v w : ℕ → ℝ) (l : ℝ) (hu : seq_limit u l) (hv : seq_limit v l)
        (below : ∀ n, u n ≤ w n) (above : ∀ n, w n ≤ v n) :
  seq_limit v l 
  :=
begin
  intros ε epp,
  specialize hu ε epp,
  specialize hv ε epp,

  cases hu with Nᵤ limit_u,
  cases hv with Nᵥ limit_v,
  use max Nᵤ Nᵥ,

  intros n n_large,
  have nNu : n ≥ Nᵤ,
  {
    have smallNu := le_max_left Nᵤ Nᵥ,
    linarith,
  },
  have nNv : n ≥ Nᵥ,
  {
    have smallNv := le_max_right Nᵤ Nᵥ,
    linarith,
  },
  specialize limit_u n nNu,
  specialize limit_v n nNv,

  apply abs_le.2,
  cases abs_le.1 limit_u,
  cases abs_le.1 limit_v,
  split,

  specialize below n,
  linarith,

  specialize above n,
  linarith,

  exact ordered_add_comm_monoid.to_covariant_class_left ℝ,
end
