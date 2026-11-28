import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NativeAdicScalarAction
import PrimalitySheafVerification.ManuscriptAudit.ProetaleInverseImage

/-! The continuous pro-étale coefficient direct image inherits the literal
adic scalar action, and the native diagonal is linear in every degree. -/

namespace ManuscriptAudit.ProetaleAdicDirectImageScalar

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ProetaleBaseChange (directImage)
open ProetaleContinuousDirectImageMaps (functionsOver diagonal)
open ProetaleContinuousCoefficientNaturality (diagonal_natural)
open NativeAdicScalarAction (scalarMap adicModule multiply multiply_continuous)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {Y X : Scheme.{0}} (i : Y ⟶ X) (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev F := directImage i AddCommGrpCat.{1}

private instance : (F i).IsRightAdjoint := (ProetaleInverseImage.adjunction i).isRightAdjoint
private instance : (F i).Additive := (F i).additive_of_preserves_binary_products

abbrev scalar (a : ℤ_[ℓ]) : functionsOver ℤ_[ℓ] i ⟶ functionsOver ℤ_[ℓ] i :=
  (F i).map (scalarMap Y ℓ a)

/-- Scalar multiplication on the target is induced by the actual native
coefficient endomorphism on the source scheme. -/
def imageModule (d : ℕ) : Module ℤ_[ℓ] (Sheaf.H (functionsOver ℤ_[ℓ] i) d) where
  smul a := Sheaf.H.map (scalar i ℓ a) d
  one_smul x := by
    change Sheaf.H.map ((F i).map (scalarMap Y ℓ 1)) d x = x
    rw [NativeAdicScalarAction.scalarMap_one, (F i).map_id, Sheaf.H.map_id_apply]
  mul_smul a b x := by
    change Sheaf.H.map ((F i).map (scalarMap Y ℓ (a*b))) d x =
      Sheaf.H.map (scalar i ℓ a) d (Sheaf.H.map (scalar i ℓ b) d x)
    rw [NativeAdicScalarAction.scalarMap_mul, (F i).map_comp, Sheaf.H.map_comp_apply] <;> rfl
  smul_zero a := map_zero (Sheaf.H.map (scalar i ℓ a) d)
  smul_add a := map_add (Sheaf.H.map (scalar i ℓ a) d)
  add_smul a b x := by
    change Sheaf.H.map ((F i).map (scalarMap Y ℓ (a+b))) d x =
      Sheaf.H.map (scalar i ℓ a) d x + Sheaf.H.map (scalar i ℓ b) d x
    rw [NativeAdicScalarAction.scalarMap_add, (F i).map_add, Sheaf.H.map_add_apply] <;> rfl
  zero_smul x := by
    change Sheaf.H.map ((F i).map (scalarMap Y ℓ 0)) d x = 0
    rw [NativeAdicScalarAction.scalarMap_zero, (F i).map_zero]
    simp [Sheaf.H.map_apply]

local instance (d : ℕ) : Module ℤ_[ℓ] (X.EllAdicCohomology ℓ d) := adicModule X ℓ d
local instance (d : ℕ) : Module ℤ_[ℓ] (Sheaf.H (functionsOver ℤ_[ℓ] i) d) := imageModule i ℓ d

theorem diagonal_map_smul (d : ℕ) (a : ℤ_[ℓ]) (x : X.EllAdicCohomology ℓ d) :
    Sheaf.H.map (diagonal ℤ_[ℓ] i) d (a • x) =
      a • Sheaf.H.map (diagonal ℤ_[ℓ] i) d x := by
  change Sheaf.H.map (diagonal ℤ_[ℓ] i) d (Sheaf.H.map (scalarMap X ℓ a) d x) =
    Sheaf.H.map (scalar i ℓ a) d (Sheaf.H.map (diagonal ℤ_[ℓ] i) d x)
  rw [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply]
  exact congrArg (fun f ↦ Sheaf.H.map f d x)
    (diagonal_natural (multiply ℓ a) (multiply_continuous ℓ a) i)

end
end ManuscriptAudit.ProetaleAdicDirectImageScalar

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAdicDirectImageScalar.imageModule,
      ``ManuscriptAudit.ProetaleAdicDirectImageScalar.diagonal_map_smul] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
