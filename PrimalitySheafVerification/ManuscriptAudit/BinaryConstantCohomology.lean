import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Finiteness.Basic

/-! The actual cohomology of a constant mod-two sheaf is killed by two in
every degree, giving its canonical binary coefficient action. -/

namespace ManuscriptAudit.BinaryConstantCohomology

open CategoryTheory CategoryTheory.Abelian

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u w

variable {D : Type u} [Category.{0} D] (J : GrothendieckTopology D)
variable [HasSheafify J AddCommGrpCat.{0}] [HasExt.{w} (Sheaf J AddCommGrpCat.{0})]

private abbrev G := AddCommGrpCat.{0}
private abbrev M := AddCommGrpCat.of (ZMod 2)
abbrev constantBinary := (constantSheaf J G).obj M

private theorem double_id_zero : (2 : ℕ) • 𝟙 (constantBinary J) = 0 := by
  let P := (Functor.const Dᵒᵖ).obj M
  let L := presheafToSheaf J G
  letI : L.Additive := L.additive_of_preserves_binary_products
  have h : (2 : ℕ) • 𝟙 P = 0 := by
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.ext
    intro a
    change (2 : ℕ) • a = (0 : ZMod 2)
    have hcast : ((2 : ℕ) : ZMod 2) = 0 := by decide
    rw [← Nat.cast_smul_eq_nsmul (R := ZMod 2), hcast, zero_smul]
  have he := congrArg L.map h
  rw [Functor.map_nsmul, L.map_id, Functor.map_zero] at he
  exact he

/-- Actual native cohomological classes with constant mod-two coefficients
are annihilated by two in every degree. -/
theorem double_eq_zero (n : ℕ) (x : Sheaf.H (constantBinary J) n) :
    (2 : ℕ) • x = 0 := by
  let H := Sheaf.functorH J n
  have h := congrArg H.map (double_id_zero J)
  rw [Functor.map_nsmul, H.map_id, Functor.map_zero] at h
  have he := ConcreteCategory.congr_hom h x
  change (2 : ℕ) • x = 0 at he
  exact he

/-- The coefficient action on the actual cohomology group. -/
def coefficientModule (n : ℕ) : Module (ZMod 2) (Sheaf.H (constantBinary J) n) :=
  AddCommGroup.zmodModule (double_eq_zero J n)

/-- A four-element actual mod-two cohomology group has coefficient-field dimension two. -/
theorem finrank_eq_two_of_card_four (n : ℕ) [Finite (Sheaf.H (constantBinary J) n)]
    (h : Nat.card (Sheaf.H (constantBinary J) n) = 4) :
    letI := coefficientModule J n
    Module.finrank (ZMod 2) (Sheaf.H (constantBinary J) n) = 2 := by
  classical
  letI := coefficientModule J n
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  let V := Sheaf.H (constantBinary J) n
  let b := Module.finBasis (ZMod 2) V
  have hC : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
    calc
      Nat.card V = Nat.card (Fin (Module.finrank (ZMod 2) V) → ZMod 2) :=
        Nat.card_congr b.equivFun.toEquiv
      _ = _ := by
        rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  exact (Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ))) (hC.symm.trans h)

end
end ManuscriptAudit.BinaryConstantCohomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.BinaryConstantCohomology.double_eq_zero,
      ``ManuscriptAudit.BinaryConstantCohomology.finrank_eq_two_of_card_four] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
