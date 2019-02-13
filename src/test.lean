import help data.nat.prime

open nat

theorem Euclid (n : ℕ) : ∃ p ≥ n, prime p :=
begin
  let N := n.fact + 1,
  let p := min_fac N,
  use_this p,
  have p_is_prime : prime p := min_fac_prime _,
  split,
    by_contradiction,
    have key_fact : p ∣ n.fact := dvd_fact _ _,
    have oops : p ∣ 1,
  all_goals { auto },
end