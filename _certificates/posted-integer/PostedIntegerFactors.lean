import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar

/-! Prime factorization of the integer supplied by Dominic Dabish.
The large primes are certified by multiplicative-order tests and repeated squaring.
Tristan Lecourtois also posted the numeral. This file certifies its arithmetic.
https://x.com/tristanlecourt/status/2125763116017610869 -/

namespace PostedInteger

set_option maxRecDepth 8192

def x : ℕ := 8193746205841170392658200302327406197

private theorem prime_7 : Nat.Prime 7 := by decide

private theorem prime_2 : Nat.Prime 2 := by decide

private theorem prime_3 : Nat.Prime 3 := by decide

private theorem prime_23 : Nat.Prime 23 := by decide

private theorem prime_167 : Nat.Prime 167 := by decide

private theorem prime_161323 : Nat.Prime 161323 := by
  apply lucas_primality 161323 (3 : ZMod 161323)
  · change (3 : ZMod 161323) ^ 161322 = 1
    reduce_mod_char
  · intro q hq hdiv
    change q ∣ 2 * (3 * (7 * (23 * 167))) at hdiv
    simp only [hq.dvd_mul,
      Nat.dvd_prime_two_le prime_2 hq.two_le, Nat.dvd_prime_two_le prime_3 hq.two_le,
      Nat.dvd_prime_two_le prime_7 hq.two_le, Nat.dvd_prime_two_le prime_23 hq.two_le,
      Nat.dvd_prime_two_le prime_167 hq.two_le] at hdiv
    rcases hdiv with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 161323) ^ 80661 ≠ 1
      reduce_mod_char <;> decide
    · change (3 : ZMod 161323) ^ 53774 ≠ 1
      reduce_mod_char <;> decide
    · change (3 : ZMod 161323) ^ 23046 ≠ 1
      reduce_mod_char <;> decide
    · change (3 : ZMod 161323) ^ 7014 ≠ 1
      reduce_mod_char <;> decide
    · change (3 : ZMod 161323) ^ 966 ≠ 1
      reduce_mod_char <;> decide

private theorem prime_733 : Nat.Prime 733 := by decide

private theorem prime_5 : Nat.Prime 5 := by decide

private theorem prime_11 : Nat.Prime 11 := by decide

private theorem prime_2027 : Nat.Prime 2027 := by decide

private theorem prime_10256621 : Nat.Prime 10256621 := by
  apply lucas_primality 10256621 (2 : ZMod 10256621)
  · change (2 : ZMod 10256621) ^ 10256620 = 1
    reduce_mod_char
  · intro q hq hdiv
    change q ∣ 2 * (2 * (5 * (11 * (23 * 2027)))) at hdiv
    simp only [hq.dvd_mul,
      Nat.dvd_prime_two_le prime_2 hq.two_le, Nat.dvd_prime_two_le prime_5 hq.two_le,
      Nat.dvd_prime_two_le prime_11 hq.two_le, Nat.dvd_prime_two_le prime_23 hq.two_le,
      Nat.dvd_prime_two_le prime_2027 hq.two_le, or_self_left] at hdiv
    rcases hdiv with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10256621) ^ 5128310 ≠ 1
      reduce_mod_char <;> decide
    · change (2 : ZMod 10256621) ^ 2051324 ≠ 1
      reduce_mod_char <;> decide
    · change (2 : ZMod 10256621) ^ 932420 ≠ 1
      reduce_mod_char <;> decide
    · change (2 : ZMod 10256621) ^ 445940 ≠ 1
      reduce_mod_char <;> decide
    · change (2 : ZMod 10256621) ^ 5060 ≠ 1
      reduce_mod_char <;> decide

private theorem prime_240579302177 : Nat.Prime 240579302177 := by
  apply lucas_primality 240579302177 (3 : ZMod 240579302177)
  · change (3 : ZMod 240579302177) ^ 240579302176 = 1
    reduce_mod_char
  · intro q hq hdiv
    change q ∣ 2 * (2 * (2 * (2 * (2 * (733 * 10256621))))) at hdiv
    simp only [hq.dvd_mul,
      Nat.dvd_prime_two_le prime_2 hq.two_le, Nat.dvd_prime_two_le prime_733 hq.two_le,
      Nat.dvd_prime_two_le prime_10256621 hq.two_le, or_self_left] at hdiv
    rcases hdiv with rfl | rfl | rfl
    · change (3 : ZMod 240579302177) ^ 120289651088 ≠ 1
      reduce_mod_char <;> decide
    · change (3 : ZMod 240579302177) ^ 328211872 ≠ 1
      reduce_mod_char <;> decide
    · change (3 : ZMod 240579302177) ^ 23456 ≠ 1
      reduce_mod_char <;> decide

private theorem prime_77621949530200343 : Nat.Prime 77621949530200343 := by
  apply lucas_primality 77621949530200343 (5 : ZMod 77621949530200343)
  · change (5 : ZMod 77621949530200343) ^ 77621949530200342 = 1
    reduce_mod_char
  · intro q hq hdiv
    change q ∣ 2 * (161323 * 240579302177) at hdiv
    simp only [hq.dvd_mul,
      Nat.dvd_prime_two_le prime_2 hq.two_le, Nat.dvd_prime_two_le prime_161323 hq.two_le,
      Nat.dvd_prime_two_le prime_240579302177 hq.two_le] at hdiv
    rcases hdiv with rfl | rfl | rfl
    · change (5 : ZMod 77621949530200343) ^ 38810974765100171 ≠ 1
      reduce_mod_char <;> decide
    · change (5 : ZMod 77621949530200343) ^ 481158604354 ≠ 1
      reduce_mod_char <;> decide
    · change (5 : ZMod 77621949530200343) ^ 322646 ≠ 1
      reduce_mod_char <;> decide

private theorem prime_4057 : Nat.Prime 4057 := by decide

private theorem prime_36781 : Nat.Prime 36781 := by decide

private theorem prime_29 : Nat.Prime 29 := by decide

private theorem prime_2251 : Nat.Prime 2251 := by decide

private theorem prime_25264539697 : Nat.Prime 25264539697 := by
  apply lucas_primality 25264539697 (5 : ZMod 25264539697)
  · change (5 : ZMod 25264539697) ^ 25264539696 = 1
    reduce_mod_char
  · intro q hq hdiv
    change q ∣ 2 * (2 * (2 * (2 * (3 * (11 * (29 * (733 * 2251))))))) at hdiv
    simp only [hq.dvd_mul,
      Nat.dvd_prime_two_le prime_2 hq.two_le, Nat.dvd_prime_two_le prime_3 hq.two_le,
      Nat.dvd_prime_two_le prime_11 hq.two_le, Nat.dvd_prime_two_le prime_29 hq.two_le,
      Nat.dvd_prime_two_le prime_733 hq.two_le, Nat.dvd_prime_two_le prime_2251 hq.two_le,
      or_self_left] at hdiv
    rcases hdiv with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 25264539697) ^ 12632269848 ≠ 1
      reduce_mod_char <;> decide
    · change (5 : ZMod 25264539697) ^ 8421513232 ≠ 1
      reduce_mod_char <;> decide
    · change (5 : ZMod 25264539697) ^ 2296776336 ≠ 1
      reduce_mod_char <;> decide
    · change (5 : ZMod 25264539697) ^ 871191024 ≠ 1
      reduce_mod_char <;> decide
    · change (5 : ZMod 25264539697) ^ 34467312 ≠ 1
      reduce_mod_char <;> decide
    · change (5 : ZMod 25264539697) ^ 11223696 ≠ 1
      reduce_mod_char <;> decide

private theorem prime_15079950701413453397 : Nat.Prime 15079950701413453397 := by
  apply lucas_primality 15079950701413453397 (2 : ZMod 15079950701413453397)
  · change (2 : ZMod 15079950701413453397) ^ 15079950701413453396 = 1
    reduce_mod_char
  · intro q hq hdiv
    change q ∣ 2 * (2 * (4057 * (36781 * 25264539697))) at hdiv
    simp only [hq.dvd_mul,
      Nat.dvd_prime_two_le prime_2 hq.two_le, Nat.dvd_prime_two_le prime_4057 hq.two_le,
      Nat.dvd_prime_two_le prime_36781 hq.two_le, Nat.dvd_prime_two_le prime_25264539697 hq.two_le,
      or_self_left] at hdiv
    rcases hdiv with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15079950701413453397) ^ 7539975350706726698 ≠ 1
      reduce_mod_char <;> decide
    · change (2 : ZMod 15079950701413453397) ^ 3717020138381428 ≠ 1
      reduce_mod_char <;> decide
    · change (2 : ZMod 15079950701413453397) ^ 409992950202916 ≠ 1
      reduce_mod_char <;> decide
    · change (2 : ZMod 15079950701413453397) ^ 596882068 ≠ 1
      reduce_mod_char <;> decide

/-- The nontrivial gcd returned by elliptic-curve factorization of x/7. -/
theorem ecm_gcd : Nat.gcd (x / 7) 552969141749355614110441482007206431 =
    77621949530200343 := by decide

/-- Complete prime factorization, with primality certified for every factor. -/
theorem full_factorization :
    x = 7 * 77621949530200343 * 15079950701413453397 ∧
    Nat.Prime 7 ∧ Nat.Prime 77621949530200343 ∧ Nat.Prime 15079950701413453397 :=
  ⟨rfl, prime_7, prime_77621949530200343, prime_15079950701413453397⟩

end PostedInteger

#print axioms PostedInteger.full_factorization
