-- for simplicity, you can imagine that `T : Type` means `T` is a set
-- and that `S : set T` means `S ⊆ T`


-- we define when a function ` f : X → Y ` is surjective
def surjectiv {X : Type} {Y : Type} (f : X → Y) := ∀ y : Y, ∃ x : X, f x = y


-- we state the Cantor's theorem as a non-existence of a surjective function from a set to its powerset
theorem Cantor_diag {T : Type} : ¬ ∃ g : T → (set T), surjectiv g :=
-- here comes the proof
begin
  intro ass,                              -- gives ` ass : ∃ (g : T → set T), surjectiv g `
                                          -- and tranforms the goal into ` false `
                                          -- because `intro` first unwraps `¬Q` into `Q → false`
                                          -- (definition of negation in Lean), then it saves `Q` into `ass`

  cases ass with g surj,                  -- gives ` g : T → set T ` and ` surj : surjectiv g `
  specialize surj (λ t : T, ¬ (g t t)),   -- gives ` surj: ∃ (x : T), g x = λ (t : T), ¬g t t `
  cases surj with x surje,                -- gives ` x : T ` (fixes the element provided by the existential quantifier) 
                                          -- and ` surje: g x = λ (t : T), ¬g t t ` as open formula

  -- since `set T` is defined as `T → Prop`,
  -- we can treat `surje` as a claim about equality between two sets
  -- (you can imagine `Prop` as if it was `Bool`)
  -- the first set is defined by the now-fixed term ` g x `
  -- the second set is defined by the lambda expression ` λ (t : T), ¬g t t `
  -- i.e., the set of values (of the type `T`) that are not contained in their `g`-image

  have paradox: g x x = ¬ (g x x),        -- now we claim equality of these two concrete terms
    exact congr_fun surje x,              -- which is obtained by plugging `x` into `surje`
                                          -- i.e., by asking whether `x ∈ (g x)` and dtto for the second set (assumed to be equal)
                                          -- in set theory, we would say { A=B implies z∈A ↔ z∈B }
                                          -- here, in type theory, sets are modelled by functions, and so,
                                          -- we call `congr_fun` which implements the rule { A=B implies (A z) ↔ (B z) } 
                                          -- for `A,B : T → Prop` in our pseudo-code formula above
  exact false_of_a_eq_not_a paradox,      -- we finish by calling a technical lemma that concludes `false` from `p = ¬p`

  -- finally, the interactive windows now displays "goals accomplished"; we are done
end
