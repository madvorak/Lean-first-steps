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

/-
The remaining part of this file doesn't work with the updated mathlib.

lemma equivalent_defs_primes : ↑is_prime_fast = nat.prime :=
begin
  ext1,
  norm_num,
  split,
  {
    sorry,
  },
  {
    unfold_coes,
    unfold is_prime_fast,
    intro ass,
    simp,
    split,
    {
      exact prime.one_lt ass,
    },
    have indu : ∀ k : ℕ, is_prime_aux x (sqrt x) k = tt,
    {
      intro k,
      induction k with m ih;
      unfold is_prime_aux,
      split_ifs,
      {
        have hope_contra := ass.right (sqrt x - m) h,
        cases hope_contra,
        {
          sorry,
        },
        {
          sorry,
        },
      },
      {
        exact ih,
      }
    },
    exact indu (sqrt x - 1),
  },
end

theorem generated_exactly_primes_under_fast (z : ℕ) :
  ∀ n : ℕ,  n ∈ generate_primes_under_fast z  ↔  n < z  ∧  nat.prime n  :=
begin
  intro n,
  unfold generate_primes_under_fast,
  unfold_coes,
  convert generated_exactly_naturals_satisfying_under (λ (x : ℕ), is_prime_fast x = tt) z n,
  exact (congr_fun equivalent_defs_primes n).symm,
end


lemma always_higher_prime :
  ∀ z : ℕ, ∃ p : ℕ,  p > z  ∧  nat.prime p  :=
begin
  intro z,
  by_contradiction contra,
  push_neg at contra,
  let x := z.factorial + 1,

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

theorem infinite_set_of_primes : set.infinite nat.prime :=
begin
  intro finit,
  unfold set.finite at finit,
  cases finit,
  let all_primes := finit.elems.val,
  sorry,
end
-/