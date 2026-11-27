import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusScaling

/-! Exact finite-field sextic-twist conjugacy for native centered-cubic Frobenius. -/

namespace ManuscriptAudit.CubicFrobeniusSexticTwists

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open CubicPointScaling CubicFrobeniusScaling

noncomputable section

variable {E : Type*} [Field E] [Fintype E]

/-- Relative scalar for the Frobenius of two centered twists when q=6k+1. -/
def parameter (A B : E) (k : ℕ) : E := (B / A) ^ k

theorem parameter_pow_six {A B : E} (hA : A ≠ 0) (hB : B ≠ 0)
    {k : ℕ} (hq : Fintype.card E = 6 * k + 1) :
    parameter A B k ^ 6 = 1 := by
  have hk : Fintype.card E - 1 = k * 6 := by omega
  rw [parameter, ← pow_mul, ← hk]
  exact FiniteField.pow_card_sub_one_eq_one (B / A) (div_ne_zero hB hA)

/-- The computed diagonal correction has one cube rotation and one ordinate sign. -/
theorem rotation_sign {A B z : E} (hA : A ≠ 0) (hB : B ≠ 0) (hz : IsPrimitiveRoot z 3)
    {k : ℕ} (hq : Fintype.card E = 6 * k + 1) :
    ∃ j : Fin 3, z ^ j.val = parameter A B k ^ 2 ∧
      (parameter A B k ^ 3 = 1 ∨ parameter A B k ^ 3 = -1) := by
  have h₆ := parameter_pow_six hA hB hq
  have h₂ : (parameter A B k ^ 2) ^ 3 = 1 := by rw [← pow_mul]; exact h₆
  have h₃ : (parameter A B k ^ 3) ^ 2 = (1 : E) ^ 2 := by rw [← pow_mul, one_pow]; exact h₆
  obtain ⟨j, hj, he⟩ := hz.eq_pow_of_pow_eq_one h₂
  exact ⟨⟨j, hj⟩, he, ordinate_eq_of_two_squares h₃⟩

variable (E) (L : Type*) [Field L] [Algebra E L] [IsAlgClosed L] [DecidableEq L]

abbrev Geometric (A : E) := (Curve (algebraMap E L A)).Point

abbrev arithmeticFrobenius (A : E) : AddMonoid.End (Geometric E L A) :=
  nativeMap E L (FiniteField.frobeniusAlgHom E L) A

/-- The actual Frobenius on one twist differs by the explicit computed finite-field scalar. -/
theorem exists_conjugacy {A B : E} (hA : A ≠ 0) (hB : B ≠ 0)
    {k : ℕ} (hq : Fintype.card E = 6 * k + 1)
    (hΔA : (shortCubic (0 : L) (algebraMap E L A)).Δ ≠ 0)
    (hΔB : (shortCubic (0 : L) (algebraMap E L B)).Δ ≠ 0) :
    let v := algebraMap E L (parameter A B k)
    ∃ (hv : v ≠ 0) (hV : v ^ 6 * algebraMap E L A = algebraMap E L A)
      (e : Geometric E L A ≃+ Geometric E L B), ∀ P,
      arithmeticFrobenius E L B (e P) =
        e (scale hv hV hΔA (arithmeticFrobenius E L A P)) := by
  let i := algebraMap E L
  let g := FiniteField.frobeniusAlgHom E L
  let v := i (parameter A B k)
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (i (B / A)) (by decide : 0 < (6 : ℕ))
  have hu₀ : u ≠ 0 := by
    intro he
    have hd := (map_ne_zero i).mpr (div_ne_zero hB hA)
    exact hd (by simpa [he] using hu.symm)
  have hAB : u ^ 6 * i A = i B := by rw [hu, ← map_mul, div_mul_cancel₀ _ hA]
  have hv₆ : v ^ 6 = 1 := by
    simpa only [v, map_pow, map_one] using congrArg i (parameter_pow_six hA hB hq)
  have hv : v ≠ 0 := by
    intro he
    rw [he, zero_pow (by decide : (6 : ℕ) ≠ 0)] at hv₆
    exact zero_ne_one hv₆
  have hV : v ^ 6 * i A = i A := by rw [hv₆, one_mul]
  have hg : g u = u * v := by
    change u ^ Fintype.card E = _
    rw [hq, pow_add, pow_mul, pow_one, hu, mul_comm]
    simp only [v, parameter, map_pow]
  let e := scaleEquiv hu₀ hAB hΔA hΔB
  exact ⟨hv, hV, e, fun P => nativeMap_scale g hu₀ hv hAB hV hΔA hΔB hg P⟩

end
end ManuscriptAudit.CubicFrobeniusSexticTwists

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicFrobeniusSexticTwists.parameter_pow_six,
      ``ManuscriptAudit.CubicFrobeniusSexticTwists.rotation_sign,
      ``ManuscriptAudit.CubicFrobeniusSexticTwists.exists_conjugacy] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
