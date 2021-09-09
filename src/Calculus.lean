import data.real.basic
import tactic


def has_limit_exactly (f : ℝ → ℝ) : ℝ → ℝ → Prop :=
  λ x, λ ℓ, ∀ ε : ℝ, ∃ δ : ℝ, (ε > 0) → 
    ((δ > 0) ∧ (∀ a : ℝ, ((a ≠ x) ∧ (abs (x - a) < δ)) → (abs (ℓ - f a) < ε)))

def is_continuous_at (f : ℝ → ℝ) : ℝ → Prop :=
  λ x, has_limit_exactly f x (f x)

def is_continuous_function (f : ℝ → ℝ) : Prop :=
  ∀ x, is_continuous_at f x

def has_derivative_exactly (f : ℝ → ℝ) : ℝ → ℝ → Prop :=
  λ x, λ s, has_limit_exactly (λ h : ℝ, (f (x + h) - (f x)) / h) 0 s


example : has_limit_exactly (λ x : ℝ, 3*x) 10 30 :=
begin
  unfold has_limit_exactly,
  intro ε,
  use (ε / 3),
  intro epp,
  split,
    linarith,

    intro a,
    intro assumptions,
    cases assumptions with un important,
    have absol₃ : abs (3 : ℝ) = (3 : ℝ),
    {
      rw abs,
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
  unfold has_limit_exactly,
  intro ε,
  use ε,
  --use (ε / 999),
  intro epp,
  split,
    linarith,

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

example (k q : ℝ) : is_continuous_function (λ x : ℝ, k*x + q) :=
begin
  intro x,
  intro ε,
  use (ε / (1 + abs k)),
  intro epp,
  split,
    sorry,
    
    intro a,
    intro assumts,
    cases assumts with a_not_x a_near_x,
    ring_nf,
    ring_nf,
    calc abs ((x - a) * k) = abs (x - a) * abs k           : by rw abs_mul
    ...                    < abs k * ε / (1 + abs k)       : by sorry
    ...                    ≤ (1 + abs k) * ε / (1 + abs k) : by sorry
    ...                    = ε                             : by rw mul_div_cancel_left_of_imp sorry,
end