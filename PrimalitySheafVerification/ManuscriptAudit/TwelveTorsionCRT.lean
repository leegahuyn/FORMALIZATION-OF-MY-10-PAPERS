import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.TorsionFrobeniusModule

/-! The natural Chinese-remainder decomposition of actual twelve-torsion. -/

namespace ManuscriptAudit.TwelveTorsionCRT

open TorsionFrobeniusModule

noncomputable section

variable (G : Type*) [AddCommGroup G]

private def decompose (P : Torsion 12 G) : Torsion 4 G × Torsion 3 G :=
  (⟨(9 : ℕ) • P.val, by
      have h : (12 : ℕ) • P.val = 0 := P.property
      change (4 : ℕ) • ((9 : ℕ) • P.val) = 0
      rw [← mul_nsmul, show (4 : ℕ) * 9 = 3 * 12 by decide, mul_nsmul, h, nsmul_zero]⟩,
   ⟨(4 : ℕ) • P.val, by
      change (3 : ℕ) • ((4 : ℕ) • P.val) = 0
      rw [← mul_nsmul]
      exact P.property⟩)

private def recompose (P : Torsion 4 G × Torsion 3 G) : Torsion 12 G :=
  ⟨P.1.val + P.2.val, by
    have h₄ : (4 : ℕ) • P.1.val = 0 := P.1.property
    have h₃ : (3 : ℕ) • P.2.val = 0 := P.2.property
    change (12 : ℕ) • (P.1.val + P.2.val) = 0
    rw [nsmul_add]
    have h₁ : (12 : ℕ) • P.1.val = 0 := by
      rw [show (12 : ℕ) = 3 * 4 by decide, mul_nsmul, h₄, nsmul_zero]
    have h₂ : (12 : ℕ) • P.2.val = 0 := by
      rw [show (12 : ℕ) = 4 * 3 by decide, mul_nsmul, h₃, nsmul_zero]
    rw [h₁, h₂, zero_add]⟩

/-- On a native additive group the projections are multiplication by nine and four. -/
def equivalence : Torsion 12 G ≃+ Torsion 4 G × Torsion 3 G where
  toFun := decompose G
  invFun := recompose G
  left_inv P := by
    apply Subtype.ext
    have hp : (12 : ℕ) • P.val = 0 := P.property
    change (9 : ℕ) • P.val + (4 : ℕ) • P.val = P.val
    rw [← add_nsmul, show (9 : ℕ) + 4 = 12 + 1 by decide, add_nsmul, hp, one_nsmul, zero_add]
  right_inv P := by
    have h₄ : (4 : ℕ) • P.1.val = 0 := P.1.property
    have h₃ : (3 : ℕ) • P.2.val = 0 := P.2.property
    apply Prod.ext
    · apply Subtype.ext
      change (9 : ℕ) • (P.1.val + P.2.val) = P.1.val
      rw [nsmul_add]
      have h₁ : (9 : ℕ) • P.1.val = P.1.val := by
        rw [show (9 : ℕ) = 2 * 4 + 1 by decide, add_nsmul, mul_nsmul, h₄, nsmul_zero,
          one_nsmul, zero_add]
      have h₂ : (9 : ℕ) • P.2.val = 0 := by
        rw [show (9 : ℕ) = 3 * 3 by decide, mul_nsmul, h₃, nsmul_zero]
      rw [h₁, h₂, add_zero]
    · apply Subtype.ext
      change (4 : ℕ) • (P.1.val + P.2.val) = P.2.val
      rw [nsmul_add, h₄, show (4 : ℕ) = 3 + 1 by decide, add_nsmul, h₃, one_nsmul, zero_add, zero_add]
  map_add' P Q := by
    apply Prod.ext
    · apply Subtype.ext
      change (9 : ℕ) • (P.val + Q.val) = (9 : ℕ) • P.val + (9 : ℕ) • Q.val
      rw [nsmul_add]
    · apply Subtype.ext
      change (4 : ℕ) • (P.val + Q.val) = (4 : ℕ) • P.val + (4 : ℕ) • Q.val
      rw [nsmul_add]

theorem components (P : Torsion 12 G) :
    ((equivalence G P).1.val = (9 : ℕ) • P.val) ∧
      ((equivalence G P).2.val = (4 : ℕ) • P.val) :=
  ⟨rfl, rfl⟩

/-- The decomposition commutes with the actual map of torsion induced by any group homomorphism. -/
theorem natural {H : Type*} [AddCommGroup H] (f : G →+ H) (P : Torsion 12 G) :
    equivalence H (mapAdd 12 f P) =
      (mapAdd 4 f (equivalence G P).1, mapAdd 3 f (equivalence G P).2) := by
  apply Prod.ext
  · apply Subtype.ext
    change (9 : ℕ) • f P.val = f ((9 : ℕ) • P.val)
    rw [map_nsmul]
  · apply Subtype.ext
    change (4 : ℕ) • f P.val = f ((4 : ℕ) • P.val)
    rw [map_nsmul]

end
end ManuscriptAudit.TwelveTorsionCRT

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.TwelveTorsionCRT.natural
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
