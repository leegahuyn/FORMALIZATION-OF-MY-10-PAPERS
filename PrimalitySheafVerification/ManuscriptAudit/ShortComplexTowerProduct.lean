import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AbelianCountableProductShortExact
import PrimalitySheafVerification.ManuscriptAudit.ComplexTowerDifference

/-! Consecutive differences form an endomorphism of the actual product
of a countable tower of short complexes. -/

namespace ManuscriptAudit.ShortComplexTowerProduct

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open AbelianCountableProductShortExact
open ComplexTowerDifference (difference difference_π)

noncomputable section

variable {C : Type*} [Category C] [Abelian C] [HasLimitsOfShape (Discrete ℕ) C]

private theorem difference_natural
    (A B : ℕ → C) (a : ∀ n, A (n+1) ⟶ A n) (b : ∀ n, B (n+1) ⟶ B n)
    (g : ∀ n, A n ⟶ B n)
    (hg : ∀ n, a n ≫ g n = g (n+1) ≫ b n) :
    difference A a ≫ mapProduct g = mapProduct g ≫ difference B b := by
  apply Pi.hom_ext
  intro n
  calc
    _ = Pi.π A n ≫ g n - Pi.π A (n+1) ≫ a n ≫ g n := by
      rw [Category.assoc, mapProduct_π, ← Category.assoc, difference_π,
        sub_comp, Category.assoc]
    _ = Pi.π A n ≫ g n - Pi.π A (n+1) ≫ g (n+1) ≫ b n := by rw [hg]
    _ = _ := by
      rw [Category.assoc, difference_π, comp_sub, mapProduct_π,
        ← Category.assoc, mapProduct_π, Category.assoc]

variable (S : ℕ → ShortComplex C) (s : ∀ n, S (n+1) ⟶ S n)

/-- The endomorphism whose three coordinates are the corresponding
identity minus consecutive shift. -/
def consecutive : product S ⟶ product S where
  τ₁ := difference (leftTerms S) (fun n ↦ (s n).τ₁)
  τ₂ := difference (middleTerms S) (fun n ↦ (s n).τ₂)
  τ₃ := difference (rightTerms S) (fun n ↦ (s n).τ₃)
  comm₁₂ := difference_natural (leftTerms S) (middleTerms S)
    (fun n ↦ (s n).τ₁) (fun n ↦ (s n).τ₂) (fun n ↦ (S n).f)
    (fun n ↦ (s n).comm₁₂)
  comm₂₃ := difference_natural (middleTerms S) (rightTerms S)
    (fun n ↦ (s n).τ₂) (fun n ↦ (s n).τ₃) (fun n ↦ (S n).g)
    (fun n ↦ (s n).comm₂₃)

variable {T : ShortComplex C} (r : ∀ n, T ⟶ S n)

/-- A compatible family of row maps gives one map into the literal product. -/
def toProduct : T ⟶ product S where
  τ₁ := Pi.lift (fun n ↦ (r n).τ₁)
  τ₂ := Pi.lift (fun n ↦ (r n).τ₂)
  τ₃ := Pi.lift (fun n ↦ (r n).τ₃)
  comm₁₂ := by
    apply Pi.hom_ext
    intro n
    change (Pi.lift (fun k ↦ (r k).τ₁) ≫ mapProduct (fun k ↦ (S k).f)) ≫
      Pi.π (middleTerms S) n = (T.f ≫ Pi.lift (fun k ↦ (r k).τ₂)) ≫
        Pi.π (middleTerms S) n
    rw [Category.assoc, mapProduct_π, ← Category.assoc, Pi.lift_π,
      Category.assoc T.f, Pi.lift_π, (r n).comm₁₂]
  comm₂₃ := by
    apply Pi.hom_ext
    intro n
    change (Pi.lift (fun k ↦ (r k).τ₂) ≫ mapProduct (fun k ↦ (S k).g)) ≫
      Pi.π (rightTerms S) n = (T.g ≫ Pi.lift (fun k ↦ (r k).τ₃)) ≫
        Pi.π (rightTerms S) n
    rw [Category.assoc, mapProduct_π, ← Category.assoc, Pi.lift_π,
      Category.assoc T.g, Pi.lift_π, (r n).comm₂₃]

theorem lift_comp_difference_zero (A : ℕ → C) (a : ∀ n, A (n+1) ⟶ A n)
    {X : C} (q : ∀ n, X ⟶ A n) (h : ∀ n, q (n+1) ≫ a n = q n) :
    Pi.lift q ≫ difference A a = 0 := by
  apply Pi.hom_ext
  intro n
  rw [Category.assoc, difference_π, comp_sub, Pi.lift_π, ← Category.assoc,
    Pi.lift_π, h, sub_self, zero_comp]

end
end ManuscriptAudit.ShortComplexTowerProduct

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ShortComplexTowerProduct.consecutive,
      ``ManuscriptAudit.ShortComplexTowerProduct.toProduct,
      ``ManuscriptAudit.ShortComplexTowerProduct.lift_comp_difference_zero] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
