import data.matrix.notation

def chain {α : Type*} {n : ℕ}
  (f : (fin n) → (α → α)) :
  α → α :=
(list.of_fn f).reverse.foldl (∘) id

def g : (fin 4) → (ℤ → ℤ) :=
![(λ a, a + 1),
  (λ a, a / 2),
  (λ a, a * a),
  (λ a, a * a)]

#eval chain g 9
