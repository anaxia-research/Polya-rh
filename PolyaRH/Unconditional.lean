import PolyaRH.Main
import OAI.NumberTheory.DirichletL.Nonvanishing

/-!
# The unconditional statements

OpenAI's Lean library proves that no Dirichlet `L`-function vanishes on `re s > 7/8`
(`OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`, from
https://github.com/openai/math, Apache License 2.0). That theorem is the hypothesis
`SevenEighths`, so Theorems 2 and 5 hold with no hypothesis.
-/

open Finset

namespace PolyaRH

/-- The half-plane `re s > 7/8`, from OpenAI's formal proof. -/
theorem sevenEighths : SevenEighths := by
  intro q _ χ hχ z hz
  exact OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re χ hz
    (fun h => hχ h.1)

/-- **Corollary 4.** `|∑_{n ≤ T} χ(n)| ≤ C √q log log q` for every primitive Dirichlet character
`χ` modulo `q ≥ 3`, with an absolute constant `C`. -/
theorem polya_vinogradov :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      3 ≤ q → ∀ T : ℕ,
        ‖∑ n ∈ Ioc 0 T, (χ n : ℂ)‖ ≤ C * Real.sqrt q * Real.log (Real.log q) :=
  polya_vinogradov_of_sevenEighths sevenEighths

/-- **Theorem 5**, unconditionally. -/
theorem character_sum_range :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → 3 ≤ q →
      ∀ x : ℕ, 2 ≤ x →
        ‖∑ n ∈ Ioc 0 x, (χ n : ℂ)‖ ≤
          C * x * (Real.log (Real.log q) / Real.log x + 1 / Real.log q) :=
  character_sum_range_of_sevenEighths sevenEighths

end PolyaRH
