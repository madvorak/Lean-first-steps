import data.nat.basic
import tactic


def fibo : ℕ → ℕ
| 0 := 0
| 1 := 1
| (n+2) := (fibo (n+1)) + (fibo n)

#eval fibo 5


def ff : ℕ → (ℕ × ℕ)
| 0 := (0, 1)
| (n+1) := let a := (ff n) in (a.2, a.1 + a.2)

def fibo_fast : ℕ → ℕ
| 0 := 0
| (n+1) := (ff n).2

#eval fibo_fast 5



private lemma fibo_ff_aux (n : ℕ) : (ff n) = (fibo n, fibo n.succ)
  :=
begin
  induction n with n ih,
    refl,

    unfold fibo,
    have unfolding_ff: (ff n.succ) = ((ff n).2, (ff n).1 + (ff n).2),
      refl,
    rw unfolding_ff,
    rw ih,
    simp,
    apply add_comm,
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
