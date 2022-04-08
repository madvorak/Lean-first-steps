import tactic
import field_theory.finite.basic

open_locale nat


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
  have mpm := mod_pow_mod (m ^ key_pair.pub.e) key_pair.pub.n key_pair.d,
/-
  have maybe_can : (↑m ^ key_pair.pub.e % ↑key_pair.pub.n) ^ key_pair.d % ↑key_pair.pub.n = ↑m,
  {
    rw mpm,
    rw ← pow_mul,
    have cheaty : (key_pair.pub.e * key_pair.d) % (φ ↑key_pair.pub.n) = 1, sorry,
    have fermat := nat.modeq.pow_totient sorry;
    sorry,
  }, swap, exact coe_to_lift,
-/
  have cannot : (↑m ^ key_pair.pub.e % key_pair.pub.n) ^ key_pair.d % key_pair.pub.n = ↑m,
  {
    sorry,
  },
  finish, -- uncommenting `maybe_can` above breaks this `finish` and I have no idea why
end
