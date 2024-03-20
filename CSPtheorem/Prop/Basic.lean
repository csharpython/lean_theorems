import Lean
theorem symm (h:a=b) : b=a := by rw[h]

@[simp]theorem not_not_not_iff (P:Prop) : ¬¬¬P↔¬P := ⟨λh i↦h λj↦j i,λh a↦a h⟩
theorem iff_not (P Q:Prop)(h:P ↔ Q) : ¬P↔¬Q := ⟨λa q↦a (h.mpr q),λa p↦a (h.mp p)⟩

theorem add_comm (P Q:Prop) : P∧Q↔Q∧P := ⟨λh↦⟨h.right,h.left⟩,λh↦⟨h.right,h.left⟩⟩
@[simp]theorem and_self_iff (P:Prop) : P∧P↔P := ⟨λh↦h.left,λh↦⟨h,h⟩⟩
@[simp]theorem and_true_iff (P:Prop) : P∧True↔P := ⟨λh↦h.left,λh↦⟨h,trivial⟩⟩
@[simp]theorem and_not_self_iff (P:Prop) : (P∧¬P)↔False := ⟨λh↦False.elim (h.right h.left),False.elim⟩

@[simp]theorem true_or_iff (P:Prop) : True∨P↔True := ⟨λ_↦trivial,λh↦Or.inl h⟩
theorem or_comm (P Q:Prop) : P∨Q↔Q∨P := ⟨λh↦Or.elim h Or.inr Or.inl,λh↦Or.elim h Or.inr Or.inl⟩
