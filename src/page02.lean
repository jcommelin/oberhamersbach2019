/- The Curry-Howard correspondence -/
/- a.k.a. propositions-as-types    -/
/- a.k.a. proofs-as-programs       -/

variables (X Y : Type) (f : X → Y)

variables (P Q : Prop) (hypothesis : P → Q)

#check ∀ x : X, P

variable (P' : X → Prop)

--- --- --- --- --- --- --- --- --- --- --- --- --- ---

variables (G : X → Type) (hG : ∀ x, group (G x))

#check Π x, G x

--- --- --- --- --- --- --- --- --- --- --- --- --- ---

lemma universal : (∀ x, P' x) = (Π x, P' x) :=
begin
  apply eq.refl,
end

lemma subsets_are_just_props :
  { x | P' x } = P' := rfl