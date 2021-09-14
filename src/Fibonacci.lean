import data.nat.basic
import tactic
import Complete_induction


def fibo : ℕ → ℕ
| 0 := 0
| 1 := 1
| (n+2) := (fibo (n+1)) + (fibo n)

#eval fibo 33


def ff : ℕ → (ℕ × ℕ)
| 0 := (0, 1)
| (n+1) := let a := (ff n) in (a.2, a.1 + a.2)

def fibo_fast : ℕ → ℕ
| 0 := 0
| (n+1) := (ff n).2

#eval fibo_fast 33



private lemma fibo_ff_aux : ∀ n : ℕ, (ff n) = (fibo n, fibo n.succ)
  :=
begin
  apply induction_complete,
  intro n,
  by_cases n < 2,
    intro _,
    by_cases n = 0,

      -- case n = 0
      rw h,
      refl,

      -- case n = 1
      have n_eq_1: n = 1, 
        omega,
      rw n_eq_1,
      refl,

    -- case n ≥ 2
    push_neg at h,
    intro ass,
    have n_as_succ_succ: ∃ m : ℕ, n = m.succ.succ,
    {
      use n - 2,
      omega,
    },
    cases n_as_succ_succ with m rel,
    rw rel,
    unfold fibo,
    have unfolding_ff: (ff m.succ.succ) = ((ff m.succ).2, (ff m.succ).1 + (ff m.succ).2),
      refl,
    rw unfolding_ff,

    have m_succ_le_n: m.succ < n,
      rw rel,
      exact lt_add_one m.succ,
    have h₁ := ass m.succ m_succ_le_n,

    rw h₁,
    simp,
    split,
      refl,

      unfold fibo,
      rw add_comm,
end


lemma fibo_eq : ∀ n : ℕ, fibo n = fibo_fast n 
  :=
begin
  intro n,
  cases n,
    refl,

    unfold fibo_fast,
    rw fibo_ff_aux,
end
