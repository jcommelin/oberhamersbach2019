import data.nat.prime help

open nat

theorem Euclid (n : ℕ) : ∃ p ≥ n, prime p :=
begin
  let N := n.fact + 1,
  let p := min_fac N,
  use_this p,
  have p_is_prime : prime p,
    apply min_fac_prime,
    have key_fact := fact_pos n,
    have now : N > 1 := succ_lt_succ key_fact,
    apply ne_of_gt,
    assumption,
  split,
  swap,
    assumption,
  by_contradiction contra_hyp,
  have key_fact : p ∣ n.fact,
    apply dvd_fact,
      apply p_is_prime.pos,
      apply le_of_not_ge,
      assumption,
  have old_fact : p ∣ n.fact + 1 := min_fac_dvd N,
  have oops : p ∣ 1,
    have tada := dvd_add_iff_right_of_left,
    rewrite ←tada at old_fact,
    assumption',
  have := p_is_prime.not_dvd_one,
  contradiction,
end