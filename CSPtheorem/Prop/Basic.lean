import Lean
theorem symm (h:a=b) : b=a := by rw[h]
theorem true' : True := trivial

@[simp]theorem true_iff_iff (P:Prop) : (True↔P)↔P := ⟨λh↦h.mp true',λh↦⟨λ_↦h,λ_↦true'⟩⟩
theorem iff_comm (P Q:Prop) : (P↔Q)↔(Q↔P):= ⟨λh↦⟨h.mpr,h.mp⟩,λh↦⟨h.mpr,h.mp⟩⟩

@[simp]theorem not_not_iff (P:Prop) : ¬¬P↔P := ⟨λa↦Or.elim (Classical.em _) (λp↦p) λp↦False.elim (a p),λp h↦h p⟩
theorem iff_not (P Q:Prop)(h:P ↔ Q) : ¬P↔¬Q := by rw[h];exact Iff.rfl

theorem add_comm (P Q:Prop) : P∧Q↔Q∧P := ⟨λh↦⟨h.right,h.left⟩,λh↦⟨h.right,h.left⟩⟩
@[simp]theorem and_self_iff (P:Prop) : P∧P↔P := ⟨λh↦h.left,λh↦⟨h,h⟩⟩
@[simp]theorem and_true_iff (P:Prop) : P∧True↔P := ⟨λh↦h.left,λh↦⟨h,true'⟩⟩
@[simp]theorem and_not_self_iff (P:Prop) : (P∧¬P)↔False := ⟨λh↦False.elim (h.right h.left),False.elim⟩
@[simp]theorem and_false_iff (P:Prop) : (P∧False)↔False := ⟨λh↦False.elim h.right,False.elim⟩

@[simp]theorem true_or_iff (P:Prop) : True∨P↔True := ⟨λ_↦true',λh↦Or.inl h⟩
theorem or_comm (P Q:Prop) : P∨Q↔Q∨P := ⟨λh↦Or.elim h Or.inr Or.inl,λh↦Or.elim h Or.inr Or.inl⟩
