import data.real.basic tactic.ring tactic.tidy

/- Definitions -/

definition double (n : ℕ) : ℕ := n + n

#check double

#check double ∘ double

definition quadruple : ℕ → ℕ := double ∘ double

--- --- --- --- --- --- --- --- --- --- --- --- --- ---

lemma transitive_imply (P Q R : Prop)
(P_imp_Q : P → Q)
(Q_imp_R : Q → R) :
  P → R :=
begin
  intro P_is_true,
  apply Q_imp_R,
  apply P_imp_Q,
  assumption,
end

lemma transitive_imply' (P Q R : Prop)
(P_imp_Q : P → Q)
(Q_imp_R : Q → R) :
  P → R := Q_imp_R ∘ P_imp_Q