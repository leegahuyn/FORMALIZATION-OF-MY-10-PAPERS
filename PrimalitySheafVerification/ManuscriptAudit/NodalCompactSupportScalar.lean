import Lean.Util.CollectAxioms
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import PrimalitySheafVerification.ManuscriptAudit.NodalCompactSupportHOne
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleCohomologyPresheaf

/-! Actual compactly supported nodal cohomology carries its native finite coefficient action. -/

namespace ManuscriptAudit.NodalCompactSupportScalar

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open OpenEtaleExtension
open NodalProjectiveClosure (affineNode affineOpen projectiveNode)
open NodalCompactSupportHOne (nodalHc)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

private abbrev A := AddCommGrpCat.{0}

variable (K : Type) [Field K]
variable (ℓ : ℕ)

abbrev coefficient := AddCommGrpCat.of (ZMod ℓ)

private theorem map_annihilated_id {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] (X : C)
    (h : ℓ • 𝟙 X = 0) : ℓ • 𝟙 (F.obj X) = 0 := by
  calc
    ℓ • 𝟙 (F.obj X) = F.map (ℓ • 𝟙 X) := by rw [F.map_nsmul, F.map_id]
    _ = 0 := by rw [h, F.map_zero]

private theorem coefficient_annihilated : ℓ • 𝟙 (coefficient ℓ) = 0 := by
  ext x
  change ℓ • x = (0 : ZMod ℓ)
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

private theorem constant_additive (X : Scheme.{0}) :
    (constantSheaf X.smallEtaleTopology A).Additive := by
  let J := X.smallEtaleTopology
  let T : X.Etale := ⊤_ X.Etale
  let a := constantSheafAdj J A (terminalIsTerminal (C := X.Etale))
  letI : ((sheafSections J A).obj (op T)).Additive := ⟨by intros; rfl⟩
  exact a.left_adjoint_additive

private theorem annihilates_elements {V : AddCommGrpCat.{0}}
    (h : ℓ • 𝟙 V = 0) (x : V) : ℓ • x = 0 := by
  exact congrArg (fun f : V ⟶ V ↦ f.hom x) h

/-- The coefficient order annihilates ordinary cohomology with those constant coefficients. -/
theorem ordinary_annihilated (X : Scheme.{0}) (n : ℕ)
    (x : Sheaf.H ((constantSheaf X.smallEtaleTopology A).obj (coefficient ℓ)) n) :
    ℓ • x = 0 := by
  let F := constantSheaf X.smallEtaleTopology A
  letI : F.Additive := constant_additive X
  have hF := map_annihilated_id ℓ F (coefficient ℓ) (coefficient_annihilated ℓ)
  have hH := map_annihilated_id ℓ (Sheaf.functorH X.smallEtaleTopology n) _ hF
  exact annihilates_elements ℓ hH x

/-- The canonical ZMod action on ordinary cohomology with those constant coefficients. -/
def ordinaryModule (X : Scheme.{0}) (n : ℕ) :
    Module (ZMod ℓ) (Sheaf.H ((constantSheaf X.smallEtaleTopology A).obj (coefficient ℓ)) n) :=
  AddCommGroup.zmodModule (ordinary_annihilated ℓ X n)

set_option maxHeartbeats 1200000 in
/-- The coefficient order annihilates cohomology after extension by zero along any open. -/
theorem extension_annihilated {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
    (n : ℕ) (x : Sheaf.H ((extensionByZero j A).obj
      ((constantSheaf U.smallEtaleTopology A).obj (coefficient ℓ))) n) : ℓ • x = 0 := by
  let F := constantSheaf U.smallEtaleTopology A
  let E := extensionByZero j A
  letI : F.Additive := constant_additive U
  letI : E.Additive := extensionByZero_additive j
  have hF := map_annihilated_id ℓ F (coefficient ℓ) (coefficient_annihilated ℓ)
  have hE := map_annihilated_id ℓ E (F.obj (coefficient ℓ)) hF
  have hH := map_annihilated_id ℓ (Sheaf.functorH X.smallEtaleTopology n)
    (E.obj (F.obj (coefficient ℓ))) hE
  exact annihilates_elements ℓ hH x

/-- The canonical ZMod action on extension-by-zero cohomology. -/
def extensionModule {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    Module (ZMod ℓ) (Sheaf.H ((extensionByZero j A).obj
      ((constantSheaf U.smallEtaleTopology A).obj (coefficient ℓ))) n) :=
  AddCommGroup.zmodModule (extension_annihilated ℓ j n)

/-- The coefficient order annihilates the actual abelian compact nodal groups. -/
theorem compact_annihilated (n : ℕ) (x : nodalHc K (coefficient ℓ) n) : ℓ • x = 0 :=
  extension_annihilated ℓ (affineOpen K) n x

/-- The canonical ZMod action on actual compact nodal cohomology. -/
def compactModule (n : ℕ) : Module (ZMod ℓ) (nodalHc K (coefficient ℓ) n) :=
  extensionModule ℓ (affineOpen K) n

end
end ManuscriptAudit.NodalCompactSupportScalar

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalCompactSupportScalar.ordinaryModule,
      ``ManuscriptAudit.NodalCompactSupportScalar.extensionModule,
      ``ManuscriptAudit.NodalCompactSupportScalar.compact_annihilated,
      ``ManuscriptAudit.NodalCompactSupportScalar.compactModule] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
