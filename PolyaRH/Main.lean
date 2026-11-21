import Vinogradov.PV.Range

/-!
# The Pólya–Vinogradov inequality with `log log q` from a zero-free half-plane

The theorems of the paper with their hypotheses as explicit arguments: the half-plane
`SevenEighths` (Theorems 2 and 5 of the paper) or the generalized Riemann hypothesis
`GRH` (Corollary 3). The unconditional versions are in `PolyaRH.Unconditional`.

* `polya_vinogradov_of_GRH`: for every primitive character `χ` modulo `q ≥ 3` and every `T`,
  `‖∑_{n ≤ T} χ(n)‖ ≤ C √q log log q`, with an absolute constant `C`
  (Montgomery and Vaughan, 1977).
* `character_sum_range_of_GRH`: for every nonprincipal `χ` modulo `q ≥ 3` and every `x ≥ 2`,
  `‖∑_{n ≤ x} χ(n)‖ ≤ C x (log log q / log x + 1 / log q)`.
-/

open Finset

namespace PolyaRH

/-- **Theorem 2.** If no `L(s, ξ)` with `ξ` nonprincipal vanishes on `re s > 7/8`, then
`|∑_{n ≤ T} χ(n)| ≤ C √q log log q` for every primitive Dirichlet character `χ` modulo `q ≥ 3`. -/
theorem polya_vinogradov_of_sevenEighths (h : SevenEighths) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      3 ≤ q → ∀ T : ℕ,
        ‖∑ n ∈ Ioc 0 T, (χ n : ℂ)‖ ≤ C * Real.sqrt q * Real.log (Real.log q) := by
  haveI : HalfPlane := ⟨h⟩
  exact Vinogradov.PV.polya_vinogradov_loglog

/-- **Theorem 5** under the half-plane `re s > 7/8`. -/
theorem character_sum_range_of_sevenEighths (h : SevenEighths) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → 3 ≤ q →
      ∀ x : ℕ, 2 ≤ x →
        ‖∑ n ∈ Ioc 0 x, (χ n : ℂ)‖ ≤
          C * x * (Real.log (Real.log q) / Real.log x + 1 / Real.log q) := by
  haveI : HalfPlane := ⟨h⟩
  exact Vinogradov.PV.character_sum_range

/-- **Corollary 3** (Montgomery–Vaughan). Under GRH, `|∑_{n ≤ T} χ(n)| ≤ C √q log log q` for every primitive Dirichlet
character `χ` modulo `q ≥ 3`. -/
theorem polya_vinogradov_of_GRH (h : GRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      3 ≤ q → ∀ T : ℕ,
        ‖∑ n ∈ Ioc 0 T, (χ n : ℂ)‖ ≤ C * Real.sqrt q * Real.log (Real.log q) := by
  exact polya_vinogradov_of_sevenEighths (sevenEighths_of_GRH h)

/-- **Theorem 5** under GRH: `|∑_{n ≤ x} χ(n)| ≤ C x (log log q / log x + 1 / log q)` for every
nonprincipal Dirichlet character `χ` modulo `q ≥ 3` and every `x ≥ 2`. -/
theorem character_sum_range_of_GRH (h : GRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → 3 ≤ q →
      ∀ x : ℕ, 2 ≤ x →
        ‖∑ n ∈ Ioc 0 x, (χ n : ℂ)‖ ≤
          C * x * (Real.log (Real.log q) / Real.log x + 1 / Real.log q) := by
  exact character_sum_range_of_sevenEighths (sevenEighths_of_GRH h)

end PolyaRH
