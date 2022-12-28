import tactic



def reversed {α : Type} : list α → list α
| []        := []
| (x :: xs) := (reversed xs) ++ [x]



lemma reverse_preserves_length {α : Type} (l : list α) : 
  l.length = (reversed l).length  :=
begin
  induction l with head tail hyp,
  {
    apply list.length_eq_zero.2,
    refl,
  },
  unfold reversed,
  rw list.length_cons,
  rw list.length_append,
  rw list.length_singleton head,
  rw hyp,
end


private lemma reverse_end {α : Type} (lizt : list α) (ende : α) :
  reversed (lizt ++ [ende]) = ende :: (reversed lizt)  :=
begin
  induction lizt with lihead litail ih,
  {
    simp [reversed],
  },
  unfold reversed,
  simp,
  unfold reversed,
  rw ih,
  refl,
end

lemma reverse_is_dual_operation {α : Type} (l : list α) :
  l = reversed (reversed l)  :=
begin
  induction l with head tail hyp;
  unfold reversed,
  {
    rw reverse_end (reversed tail) head,
    rw ← hyp,
  },
end
