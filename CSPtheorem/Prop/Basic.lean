import Lean
theorem symm (h:a=b) : b=a := by rw[h]

theorem not_not_not_iff (P:Prop) : ¬¬¬P↔¬P := ⟨λh i↦h λj↦j i,λh a↦a h⟩

theorem and_self_iff (P:Prop) : P∧P↔P := ⟨λh↦h.left,λh↦⟨h,h⟩⟩

theorem true_or_iff (P:Prop) : true∨P↔true := ⟨λ_↦rfl,λh↦Or.inl h⟩
theorem or_comm (P Q:Prop) : P∨Q↔Q∨P := ⟨λh↦Or.elim h Or.inr Or.inl,λh↦Or.elim h Or.inr Or.inl⟩
