import Mathlib

/-!
# The generalized Riemann hypothesis as an explicit hypothesis

`GRH` is the statement that no Dirichlet `L`-function vanishes in the half-plane `re s > 1/2`,
apart from the pole of `L(s, 1)` at `s = 1`. It is stated with Mathlib's own
`DirichletCharacter.LFunction`, in the same form as the hypothesis `EveryCharacter` of the
closure files of `anaxia-research/Openproblemsforfieldsmedal1` (`Closure/`), so a proof of that
statement can be passed to the theorems of this library directly.

The proof of the Pólya–Vinogradov bound needs much less than `GRH`: only the half-plane
`re s > 7/8` for nonprincipal characters, `SevenEighths`. The class `HalfPlane` carries that
statement through the files that use it, and its only use is `Vinogradov.zeroFree`. `GRH` gives an
instance (`halfPlane_of_GRH`), and so does OpenAI's Lean proof of the half-plane
(`PolyaRH.Unconditional`).
-/

namespace PolyaRH

/-- **The generalized Riemann hypothesis for Dirichlet `L`-functions**, in half-plane form. -/
def GRH : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), 1 / 2 < s.re →
    ¬ (χ = 1 ∧ s = 1) → DirichletCharacter.LFunction χ s ≠ 0

/-- No `L(s, χ)` with `χ` nonprincipal vanishes on `re s > 7/8`. -/
def SevenEighths : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    ∀ z : ℂ, 7 / 8 < z.re → DirichletCharacter.LFunction χ z ≠ 0

/-- `GRH` implies `SevenEighths`. -/
theorem sevenEighths_of_GRH (h : GRH) : SevenEighths := by
  intro q _ χ hχ z hz
  exact h q χ z (by linarith) (fun h' => hχ h'.1)

/-- The half-plane `SevenEighths`, as a class so that it passes through the library implicitly. -/
class HalfPlane : Prop where
  zeroFree : SevenEighths

end PolyaRH

namespace Vinogradov

/-- The half-plane `re s > 7/8`, read off the class `HalfPlane`. This is the only place where the
zeros of `L`-functions enter the proof. -/
theorem zeroFree [h : PolyaRH.HalfPlane] :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ z : ℂ, 7 / 8 < z.re → DirichletCharacter.LFunction χ z ≠ 0 :=
  h.zeroFree

end Vinogradov
