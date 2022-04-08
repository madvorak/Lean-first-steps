import tactic
import field_theory.finite.basic


structure public_key :=
(n : ℕ)
(n_pos : n > 0)
(e : ℕ)

structure full_key :=
(pub : public_key)
(d : ℕ)


def encrypt (key : public_key) (message : fin key.n) : fin key.n :=
fin.mk (message.val ^ key.e % key.n) (nat.mod_lt _ key.n_pos)

def decrypt (key : full_key) (message : fin key.pub.n) : fin key.pub.n :=
fin.mk (message.val ^ key.d % key.pub.n) (nat.mod_lt _ key.pub.n_pos)

-- equivalent of `int.mod_def` for natural numbers
lemma unmodulo (a m : ℕ) : (a % m) = a - m * (a / m) :=
eq_sub_of_add_eq'' (nat.mod_add_div a m)

lemma mod_pow_mod (a m : ℤ) (n : ℕ) : ((a % m) ^ n) % m = (a ^ n) % m :=
begin
  rw int.mod_def a m,
  induction n with n ih,
  {
    rw pow_zero,
    rw pow_zero,
  },
  rw pow_succ,
  rw mul_sub_right_distrib,
  rw int.sub_mod,
  rw mul_assoc,
  rw int.mul_mod_right,
  rw sub_zero,
  rw int.mod_mod,
  convert_to a * ((a - m * (a / m)) ^ n % m) % m = a ^ n.succ % m,
  {
    rw int.mul_mod,
    rw int.mul_mod a,
    rw int.mod_mod,
  },
  rw ih,
  rw pow_succ,
  rw int.mul_mod,
  rw int.mod_mod,
  rw int.mul_mod a,
end

theorem RSA_works (key_pair : full_key) : ∀ message : fin key_pair.pub.n,
  decrypt key_pair (encrypt key_pair.pub message) = message :=
begin
  intro m,
  unfold decrypt,
  unfold encrypt,
  norm_num,
  have mpm := mod_pow_mod (↑m ^ key_pair.pub.e) key_pair.pub.n key_pair.d,
  /-
  convert_to @fin.mk (key_pair.pub.n)
          ((↑m ^ key_pair.pub.e) ^ ↑key_pair.d % key_pair.pub.n)
          (nat.mod_lt _ key_pair.pub.n_pos)
          = m,
  {
    convert mpm;
    sorry,
  },
  rw ← pow_mul,
  sorry,
  -/
  sorry,
end

/-
def encrypt' (key : public_key) (message : ℤ) : ℤ :=
message ^ key.e % key.n

def decrypt' (key : full_key) (message : ℤ) : ℤ :=
message ^ key.d % key.pub.n

open_locale nat

theorem RSA_works' (key_pair : full_key) :
  ∀ message : ℕ,  0 ≤ message  →  message < key_pair.pub.n  →
    decrypt' key_pair (encrypt' key_pair.pub message) = message :=
begin
  intros m non_neg non_over,
  unfold decrypt',
  unfold encrypt',
  rw mod_pow_mod,
  rw ← pow_mul,
  have cheaty : (key_pair.pub.e * key_pair.d) % (φ ↑key_pair.pub.n) = 1, sorry,
  have kopr : m.coprime ↑key_pair.pub.n, sorry,
  have fermat := nat.modeq.pow_totient kopr,
  rw unmodulo at cheaty,
  have cheaty' : 
    key_pair.pub.e * key_pair.d = 
    1 + ↑(key_pair.pub.n).totient * (key_pair.pub.e * key_pair.d / ↑(key_pair.pub.n).totient),
  {
    -- ??? follows from `cheaty` ???
    sorry,
  },
  rw cheaty',
  rw pow_add,
  rw pow_mul,
  --rw fermat,
  sorry,
end
-/