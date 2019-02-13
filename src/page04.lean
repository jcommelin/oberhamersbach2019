import data.nat.prime help

open nat

theorem Euclid (n : ℕ) : ∃ p ≥ n, prime p :=
begin
  let N := n.fact + 1,
  let p := min_fac N,
  use_this p,
  have p_is_prime : prime p,
    apply min_fac_prime,
    apply ne_of_gt,
    show 1 < N,
    apply succ_lt_succ,
    apply fact_pos,
  split,
  swap,
    assumption,
  show n ≤ p,
  by_contradiction contra_hyp,
  have old_fact := p_is_prime.not_dvd_one,
  suffices : p ∣ 1,
    contradiction,
  have pdvd₁ : p ∣ n.fact + 1 := min_fac_dvd N,
  have pdvd₂ : p ∣ n.fact,
    apply dvd_fact,
      apply min_fac_pos,
      apply le_of_not_ge,
      assumption,
  have tada := nat.dvd_add_iff_right pdvd₂,
  rewrite ←tada at pdvd₁,
  assumption,
end