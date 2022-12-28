import tactic
import data.nat.prime
import data.set.finite

open nat

private def generate_naturals_satisfying_down (pred : ℕ → Prop) [decidable_pred pred] : ℕ → list ℕ
| 0     := []
| (n+1) := if pred n
           then n :: generate_naturals_satisfying_down n
           else      generate_naturals_satisfying_down n

def generate_naturals_satisfying_under (pred : ℕ → Prop) [decidable_pred pred] (z : ℕ) : list ℕ :=
list.reverse (generate_naturals_satisfying_down pred z)

def generate_primes_under (z : ℕ) : list ℕ :=
generate_naturals_satisfying_under nat.prime z

#eval generate_primes_under 40

lemma generated_exactly_naturals_satisfying_under (pred : ℕ → Prop) [decidable_pred pred] (z : ℕ) :
  ∀ n : ℕ,  n ∈ generate_naturals_satisfying_under pred z  ↔  n < z  ∧  pred n  :=
begin
  unfold generate_naturals_satisfying_under,
  induction z with y ih,
  {
    intro n,
    unfold generate_naturals_satisfying_down,
    simp,
  },
  intro n,
  specialize ih n,
  rw list.mem_reverse at *,
  split,
  {
    intro ass,
    unfold generate_naturals_satisfying_down at ass,
    by_cases n = y,
    {
      rename h n_eq_y,
      rw n_eq_y at *,
      have y_not_in : y ∉ generate_naturals_satisfying_down pred y,
      {
        by_contradiction,
        have hyp := (ih.1 h).left,
        exact (ne_of_lt hyp) rfl,
      },
      split_ifs at ass,
      {
        split,
        {
          exact lt_add_one y,
        },
        {
          exact h,
        },
      },
      {
        exfalso,
        exact y_not_in ass,
      }
    },
    {
      rename h n_neq_y,
      have n_in : n ∈ generate_naturals_satisfying_down pred y,
      {
        split_ifs at ass,
        {
          cases ass,
          {
            exfalso,
            exact n_neq_y ass,
          },
          {
            exact ass,
          }
        },
        {
          exact ass,
        }
      },
      have hyp := ih.1 n_in,
      split,
      {
        exact nat.lt.step hyp.left,
      },
      {
        exact hyp.right,
      },
    },
  },
  {
    rintro ⟨ n_small, n_prime ⟩,
    by_cases n < y,
    {
      rename h n_lt_y,
      have hyp := ih.2 (and.intro n_lt_y n_prime),
      unfold generate_naturals_satisfying_down,
      split_ifs,
      {
        exact list.mem_cons_of_mem y hyp,
      },
      {
        exact hyp,
      },
    },
    {
      have n_eq_y := nat.eq_of_lt_succ_of_not_lt n_small h,
      clear h,
      rw n_eq_y at *,
      unfold generate_naturals_satisfying_down,
      split_ifs,
      exact list.mem_cons_self y _,
    }
  },
end

theorem generated_exactly_primes_under (z : ℕ) :
  ∀ n : ℕ,  n ∈ generate_primes_under z  ↔  n < z  ∧  nat.prime n  :=
generated_exactly_naturals_satisfying_under nat.prime z


private def is_prime_aux (n : ℕ) (k : ℕ) : ℕ → bool
| zero     := tt
| (succ d) := if (k - d) ∣ n
              then ff
              else is_prime_aux d

-- It is not really fast, but why?
def is_prime_fast (n : ℕ) : bool :=
if n > 1
then is_prime_aux n (nat.sqrt n) (nat.sqrt n - 1)
else ff

def generate_primes_under_fast (z : ℕ) : list ℕ :=
generate_naturals_satisfying_under (λ x, is_prime_fast x) z

#eval generate_primes_under_fast 40

#eval list.length $ generate_primes_under 100000
#eval list.length $ generate_primes_under_fast 100000
