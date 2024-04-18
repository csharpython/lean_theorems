import Lean
theorem symm (h:a=b) : b=a := by rw[h]
theorem by_cases (P Q:Prop) : (P→Q)→(¬P→Q)→Q := Or.elim (Classical.em _)

@[simp]theorem true_iff_iff (P:Prop) : (True↔P)↔P := ⟨λh↦h.mp trivial,λh↦⟨λ_↦h,λ_↦trivial⟩⟩
theorem not_not(P:Prop) : P→¬¬P := λp n↦n p
theorem not_not_iff (P:Prop) : ¬¬P↔P := ⟨λa↦by_cases P _ (λp↦p) λp↦False.elim (a p),not_not _⟩
@[simp]theorem not_not_not_iff (P:Prop) : ¬¬¬P↔¬P := ⟨λa p↦a λn↦n p,not_not _⟩
theorem iff_not (P Q:Prop)(h:P ↔ Q) : ¬P↔¬Q := by rw[h]

theorem imp_of_not_or (P Q:Prop) : (¬P∨Q)→P→Q := λh p↦Or.elim h (λi↦False.elim (i p)) λq↦q
theorem not_imp (P Q:Prop) : (P→Q)↔(¬P∨Q) := ⟨λh↦by_cases P _ (λp↦Or.inr (h p)) λp↦Or.inl p,imp_of_not_or _ _⟩

theorem add_comm (P Q:Prop) : P∧Q↔Q∧P := ⟨λh↦⟨h.right,h.left⟩,λh↦⟨h.right,h.left⟩⟩
@[simp]theorem and_true_iff (P:Prop) : P∧True↔P := ⟨λh↦h.left,λh↦⟨h,trivial⟩⟩
@[simp]theorem and_false_iff (P:Prop) : (P∧False)↔False := ⟨λh↦False.elim h.right,False.elim⟩

@[simp]theorem true_or_iff (P:Prop) : True∨P↔True := ⟨λ_↦trivial,λh↦Or.inl h⟩
theorem not_eq_not_self(P:Prop) : P≠¬P := λh↦(λi↦Eq.mp h i i) (Eq.mpr h λi↦Eq.mp h i i)

theorem eq_or_ne : a=b ∨ a≠b := Classical.em _
