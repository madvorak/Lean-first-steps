import data.real.basic
import data.real.sqrt
import tactic


def seq_limit (s : ℕ → ℝ) (a : ℝ) : Prop :=
∀ ε : ℝ, ε > 0 → ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → |s n - a| ≤ ε

-- Arithmetic of limits – the sum law:
-- If [`u` approaches `a`] and [`v` approaches `b`] then [`u + v` approaches `a + b`].
example (u v : ℕ → ℝ) (a b : ℝ) (hu : seq_limit u a) (hv : seq_limit v b) :
  seq_limit (u + v) (a + b) :=
begin
  intros ε ep_pos,
  cases hu (ε / 2) (half_pos ep_pos) with Nᵤ ha,
  cases hv (ε / 2) (half_pos ep_pos) with Nᵥ hb,
  use max Nᵤ Nᵥ,
  intros n n_large,
  change max Nᵤ Nᵥ ≤ n at n_large,
  rw max_le_iff at n_large,
  specialize ha n n_large.left,
  specialize hb n n_large.right,

  change |(u n + v n) - (a + b)| ≤ ε,
  rw abs_le at *,
  split;
  linarith,
end

-- Arithmetic of limits – the product law:
-- If [`u` approaches `a`] and [`v` approaches `b`] then [`u * v` approaches `a * b`].
example (u v : ℕ → ℝ) (a b : ℝ) (hu : seq_limit u a) (hv : seq_limit v b) :
  seq_limit (u * v) (a * b) :=
begin
  intros ε ep_pos,

  have ep_third_pos : ε / 3 > 0,
  {
    linarith,
  },
  have ep_third_nneg : ε / 3 ≥ 0,
  {
    exact le_of_lt ep_third_pos,
  },
  have sqrt_ep_third_pos : 0 < real.sqrt (ε / 3),
  {
    rw real.sqrt_pos,
    exact ep_third_pos,
  },
  have ep_u_pos : min (ε / (3 * (|b| + 1))) (real.sqrt (ε / 3)) > 0,
  {
    apply lt_min,
    {
      have denom_pos : 0 < (3 * (|b| + 1)),
      {
        have : |b| ≥ 0, exact abs_nonneg b,
        have : |b| + 1 > 0, linarith,
        linarith,
      },
      exact div_pos ep_pos denom_pos,
    },
    {
      exact sqrt_ep_third_pos,
    },
  },
  have ep_v_pos : min (ε / (3 * (|a| + 1))) (real.sqrt (ε / 3)) > 0,
  {
    apply lt_min,
    {
      have denom_pos : 0 < (3 * (|a| + 1)),
      {
        have : |a| ≥ 0, exact abs_nonneg a,
        have : |a| + 1 > 0, linarith,
        linarith,
      },
      exact div_pos ep_pos denom_pos,
    },
    {
      exact sqrt_ep_third_pos,
    },
  },
  cases hu (min (ε / (3 * (|b| + 1))) (real.sqrt (ε / 3))) ep_u_pos with Nᵤ ha,
  cases hv (min (ε / (3 * (|a| + 1))) (real.sqrt (ε / 3))) ep_v_pos with Nᵥ hb,
  use max Nᵤ Nᵥ,
  intros n n_large,
  specialize ha n (le_of_max_le_left  n_large),
  specialize hb n (le_of_max_le_right n_large),
  have trick :
    (u n * v n) - a * b = (u n - a) * b + (v n - b) * a + (u n - a) * (v n - b),
  {
    ring,
  },
  change |(u n * v n) - a * b| ≤ ε,
  rw trick,

  have fst_summand : |(u n - a) * b| ≤ ε / 3,
  {
    rw abs_mul,
    have ha' : |u n - a| ≤ (ε / (3 * (|b| + 1))), calc |u n - a|
          ≤ min (ε / (3 * (|b| + 1))) (real.sqrt (ε / 3)) : ha
      ... ≤ (ε / (3 * (|b| + 1))) : min_le_left _ _,
    have foo : |b| ≤ (|b| + 1), linarith,
    have bar : |b| ≥ 0, exact abs_nonneg b,
    have baz : |b| + 1 > 0, linarith,
    have qux : (|b| / (|b| + 1)) ≤ 1,
    {
      rw div_le_one baz,
      exact foo,
    },
    calc |u n - a| * |b| 
        ≤ (ε / (3 * (|b| + 1))) * |b| : mul_le_mul_of_nonneg_right ha' (abs_nonneg _)
    ... = ((ε / 3) / (|b| + 1)) * |b| : by rw div_div
    ... = (ε / 3) * (|b| / (|b| + 1)) : mul_comm_div _ _ _
    ... ≤ (ε / 3) * 1 : mul_le_mul_of_nonneg_left qux ep_third_nneg
    ... = ε / 3 : mul_one _,
  },
  have snd_summand : |(v n - b) * a| ≤ ε / 3,
  {
    rw abs_mul,
    have hb' : |v n - b| ≤ (ε / (3 * (|a| + 1))), calc |v n - b|
          ≤ min (ε / (3 * (|a| + 1))) (real.sqrt (ε / 3)) : hb
      ... ≤ (ε / (3 * (|a| + 1))) : min_le_left _ _,
    have foo : |a| ≤ (|a| + 1), linarith,
    have bar : |a| ≥ 0, exact abs_nonneg a,
    have baz : |a| + 1 > 0, linarith,
    have qux : (|a| / (|a| + 1)) ≤ 1,
    {
      rw div_le_one baz,
      exact foo,
    },
    calc |v n - b| * |a| 
        ≤ (ε / (3 * (|a| + 1))) * |a| : mul_le_mul_of_nonneg_right hb' (abs_nonneg _)
    ... = ((ε / 3) / (|a| + 1)) * |a| : by rw div_div
    ... = (ε / 3) * (|a| / (|a| + 1)) : mul_comm_div _ _ _
    ... ≤ (ε / 3) * 1 : mul_le_mul_of_nonneg_left qux ep_third_nneg
    ... = ε / 3 : mul_one _,
  },
  have last_summand : |(u n - a) * (v n - b)| ≤ ε / 3,
  {
    rw abs_mul,
    have ha'' : |u n - a| ≤ (real.sqrt (ε / 3)), calc |u n - a|
          ≤ min (ε / (3 * (|b| + 1))) (real.sqrt (ε / 3)) : ha
      ... ≤ (real.sqrt (ε / 3)) : min_le_right _ _,
    have hb'' : |v n - b| ≤ (real.sqrt (ε / 3)), calc |v n - b|
          ≤ min (ε / (3 * (|a| + 1))) (real.sqrt (ε / 3)) : hb
      ... ≤ (real.sqrt (ε / 3)) : min_le_right _ _,
    calc |u n - a| * |v n - b|
        ≤ real.sqrt (ε / 3) * |v n - b|         : mul_le_mul_of_nonneg_right ha'' (abs_nonneg _)
    ... ≤ real.sqrt (ε / 3) * real.sqrt (ε / 3) : mul_le_mul_of_nonneg_left hb'' (real.sqrt_nonneg _)
    ... = ε / 3 : real.mul_self_sqrt ep_third_nneg,
  },
  calc | (u n - a) * b  +  (v n - b) * a  +  (u n - a) * (v n - b)|
      ≤ |(u n - a) * b  +  (v n - b) * a| + |(u n - a) * (v n - b)| : abs_add _ _
  ... ≤ |(u n - a) * b| + |(v n - b) * a| + |(u n - a) * (v n - b)| : add_le_add (abs_add _ _) (le_of_eq rfl)
  ... ≤ ε / 3 + ε / 3 + ε / 3 : add_le_add (add_le_add fst_summand snd_summand) last_summand
  ... = ε : by ring,
end


def fun_limit (f : ℝ → ℝ) : ℝ → ℝ → Prop :=
  λ x, λ ℓ, ∀ ε : ℝ, ∃ δ : ℝ, (ε > 0) → 
    ((δ > 0) ∧ (∀ a : ℝ, ((a ≠ x) ∧ (abs (x - a) < δ)) → (abs (ℓ - f a) < ε)))

def is_continuous_at (f : ℝ → ℝ) : ℝ → Prop :=
  λ x, fun_limit f x (f x)

def is_continuous_function (f : ℝ → ℝ) : Prop :=
  ∀ x, is_continuous_at f x

def has_derivative_exactly (f : ℝ → ℝ) : ℝ → ℝ → Prop :=
  λ x, λ s, fun_limit (λ h : ℝ, (f (x + h) - (f x)) / h) 0 s

example : fun_limit (λ x : ℝ, 3*x) 10 30 :=
begin
  unfold fun_limit,
  intro ε,
  use (ε / 3),
  intro epp,
  split,
  {
    linarith,
  },
  intro a,
  intro assumptions,
  cases assumptions with un important,
  have absol₃ : abs (3 : ℝ) = (3 : ℝ),
  {
    simp,
    linarith,
  },
  calc abs (30 - 3 * a) = abs (3 * (10 - a))     : by ring_nf
  ...                   = (abs 3) * abs (10 - a) : by rw abs_mul
  ...                   = 3 * abs (10 - a)       : by rw absol₃
  ...                   < 3 * ε / 3              : by linarith
  ...                   = ε                      : by ring
end

example : has_derivative_exactly (λ x, x*x) 100 200 :=
begin
  unfold has_derivative_exactly,
  unfold fun_limit,
  intro ε,
  use ε,
  intro epp,
  split,
  {
    exact epp,
  },
  intro h,
  intro assum,
  cases assum with h_not_zero h_near_zero,
  have absm_h_small : abs (- h) < ε,
  {
    rw zero_sub at h_near_zero,
    exact h_near_zero,
  },
  have crap : h = 0 → 200 + h = 0, 
  {
    contrapose!,
    intro foo,
    exact h_not_zero,
  },
  calc abs (200 - ((100 + h) * (100 + h) - 100 * 100) / h) 
       = abs (200 - (100 * 100 + 200 * h + h * h - 100 * 100) / h) : by ring_nf
  ...  = abs (200 - (200 * h + h * h) / h)                         : by ring_nf
  ...  = abs (200 - (h * (200 + h)) / h)                           : by ring_nf
  ...  = abs (200 - (200 + h))                                     : by rw mul_div_cancel_left_of_imp crap
  ...  = abs (- h)                                                 : by ring_nf
  ...  < ε                                                         : absm_h_small,
end
