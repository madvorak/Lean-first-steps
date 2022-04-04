import tactic
import data.nat.prime
import data.set.finite

open nat

/-
@[derive decidable]
def is_prime (n : ℕ) : Prop :=
∀ a : ℕ, ((1 < a) ∧ (a < n)) → (a ∣ n)
-/

/-def generate_primes_under : ℕ → list ℕ
| 0     := []
| (n+1) := (generate_primes_under (n)) ++ (if nat.prime n then [n] else [])

#eval generate_primes_under 12345-/

/-def generate_primes_from_a_to_b (a b : ℕ) : list ℕ :=
if a > b then [] else (
  if nat.prime a then a :: (generate_primes_from_a_to_b (a+1) b)
  else (generate_primes_from_a_to_b (a+1) b)
)-/

private def generate_primes_down : ℕ → list ℕ
| 0     := []
| (n+1) := if nat.prime n then n :: (generate_primes_down (n))
                          else      (generate_primes_down (n))

def generate_primes_under (z : ℕ) : list ℕ :=
list.reverse (generate_primes_down z)

#eval generate_primes_under 20


theorem generated_primes_under (z : ℕ) :
  ∀ n : ℕ,  n ∈ generate_primes_under z  ↔  n < z  ∧  nat.prime n  :=
begin
  unfold generate_primes_under,
  induction z with y ih,
  {
    intro n,
    unfold generate_primes_down,
    simp,
  },
  intro n,
  specialize ih n,
  rw list.mem_reverse at *,
  split,
  {
    intro ass,
    unfold generate_primes_down at ass,
    by_cases n = y,
    {
      rename h n_eq_y,
      rw n_eq_y at *,
      have y_not_in : y ∉ generate_primes_down y,
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
      have n_in : n ∈ generate_primes_down y,
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
      unfold generate_primes_down,
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
      unfold generate_primes_down,
      split_ifs,
      exact list.mem_cons_self y _,
    }
  },
end


/-private def is_prime_aux (n d : ℕ) : bool :=
if d * d ≥ n then tt
else if d ∣ n then ff
     else is_prime_aux n (d + 1)-/

private def is_prime_aux (n : ℕ) : ℕ → bool
| zero     := tt
| (succ d) := if d = 1 
              then tt
              else if d ∣ n 
                   then ff
                   else is_prime_aux d

def is_prime_fast (n : ℕ) : bool :=
if n > 1
then is_prime_aux n (nat.sqrt n + 1)
else ff

-- TODO in order to be really fast, test potential divisors from 2 up (not down)
private def generate_primes_down_fast : ℕ → list ℕ
| 0     := []
| (n+1) := if is_prime_fast n 
           then n :: (generate_primes_down_fast (n))
           else      (generate_primes_down_fast (n))

def generate_primes_under_fast (z : ℕ) : list ℕ :=
list.reverse (generate_primes_down_fast z)

#eval generate_primes_under_fast 20

#eval list.length $ generate_primes_under 10000
#eval list.length $ generate_primes_under_fast 10000


theorem infinitely_many_primes :
  ∀ z : ℕ, ∃ p : ℕ,  p > z  ∧  nat.prime p  :=
begin
  intro z,
  by_contradiction contra,
  push_neg at contra,
  let x := z.factorial + 1,
  /-by_cases nat.prime x,
  {
    have x_gt_z : x > z,
    {
      have big_fak := nat.self_le_factorial z,
      linarith,
    },
    exact contra x x_gt_z h,
  },-/

  have two_le_x : 2 ≤ x,
  {
    change 2 ≤ z.factorial + 1,
    have pos_fak := nat.factorial_pos z,
    linarith,
  },
  rcases exists_prime_and_dvd two_le_x with ⟨ q, prime_q, q_dvd_x ⟩,

  by_cases q > z;
  rename h hqz,
  {
    exact contra q hqz prime_q,
  },
  {
    by_cases q = 0,
    {
      finish,
    },
    have q_dvd_zfak : q ∣ z.factorial, 
    {
      apply nat.dvd_factorial,
      {
        rw pos_iff_ne_zero,
        exact h,
      },
      push_neg at hqz,
      exact hqz,
    },
    have dvd_difference := nat.dvd_sub' q_dvd_x q_dvd_zfak,
    change q ∣ z.factorial + 1 - z.factorial at dvd_difference,
    rw nat.add_sub_cancel_left at dvd_difference,
    rw nat.dvd_one at dvd_difference,
    exact prime.ne_one prime_q dvd_difference,
  },
end
