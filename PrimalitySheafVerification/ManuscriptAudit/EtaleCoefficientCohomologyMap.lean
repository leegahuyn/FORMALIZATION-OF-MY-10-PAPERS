import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleCoefficientHOne
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-! The actual coefficient-lift map exists in every degree,
commutes with literal connecting homomorphisms, and is surjective
in degree zero because lift is full. -/

namespace ManuscriptAudit.EtaleCoefficientCohomologyMap

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open EtaleCoefficientUniverseLift (lift constantIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{0})

private abbrev A := AddCommGrpCat.{0}
private abbrev B := AddCommGrpCat.{1}
private abbrev C := Sheaf X.smallEtaleTopology A
private abbrev D := Sheaf X.smallEtaleTopology B

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

private theorem highGrothendieck : IsGrothendieckAbelian.{1} (D X) := by
  letI : EssentiallySmall.{1} X.Etale :=
    EssentiallySmall.mk' (AsSmall.equiv : X.Etale ≌ AsSmall.{0} X.Etale)
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall X.smallEtaleTopology B

attribute [local instance] highGrothendieck

local instance highExt : HasExt.{1} (D X) := IsGrothendieckAbelian.hasExt (D X)

private abbrev Z₀ := (constantSheaf X.smallEtaleTopology A).obj (AddCommGrpCat.of (ULift.{0} ℤ))
private abbrev Z₁ := (constantSheaf X.smallEtaleTopology B).obj (AddCommGrpCat.of (ULift.{1} ℤ))

private def zEquiv : ULift.{1} (ULift.{0} ℤ) ≃+ ULift.{1} ℤ where
  toFun x := ⟨x.down.down⟩
  invFun x := ⟨⟨x.down⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

private def integerIso : (lift X).obj (Z₀ X) ≅ Z₁ X :=
  (constantIso X).app (AddCommGrpCat.of (ULift.{0} ℤ)) ≪≫
    (constantSheaf X.smallEtaleTopology B).mapIso zEquiv.toAddCommGrpIso

/-- The actual cohomology arrow for the exact étale coefficient lift. -/
def comparison (F : C X) (n : ℕ) : Sheaf.H F n →+ Sheaf.H ((lift X).obj F) n :=
  ((Ext.mk₀ (integerIso X).inv).precomp ((lift X).obj F) (zero_add n)).comp
    ((lift X).mapExtAddHom (Z₀ X) F n)

set_option maxHeartbeats 3400000 in
/-- The coefficient lift commutes with the actual boundary maps. -/
theorem comparison_boundary {S : ShortComplex (C X)} (hS : S.ShortExact) (n : ℕ)
    (e : Sheaf.H S.X₃ n) :
    comparison X S.X₁ (n+1) (e.comp hS.extClass rfl) =
      (comparison X S.X₃ n e).comp (hS.map_of_exact (lift X)).extClass rfl := by
  change (Ext.mk₀ (integerIso X).inv).comp
      ((e.comp hS.extClass rfl).mapExactFunctor (lift X)) (zero_add (n+1)) =
    ((Ext.mk₀ (integerIso X).inv).comp (e.mapExactFunctor (lift X)) (zero_add n)).comp
      (hS.map_of_exact (lift X)).extClass rfl
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass, Ext.comp_assoc] <;> simp

set_option maxHeartbeats 3100000 in
/-- Every actual degree-zero class in the lifted coefficient sheaf
is the coefficient lift of a degree-zero class in the small sheaf. -/
theorem comparison_zero_surjective (F : C X) :
    Function.Surjective (comparison X F 0) := by
  intro z
  obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective (Z₁ X) ((lift X).obj F)).surjective z
  obtain ⟨f, hf⟩ := (lift X).map_surjective ((integerIso X).hom ≫ g)
  refine ⟨Ext.mk₀ f, ?_⟩
  change (Ext.mk₀ (integerIso X).inv).comp
    ((Ext.mk₀ f).mapExactFunctor (lift X)) (zero_add 0) = _
  rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, hf, Iso.inv_hom_id_assoc]

end
end ManuscriptAudit.EtaleCoefficientCohomologyMap

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleCoefficientCohomologyMap.comparison_boundary,
      ``ManuscriptAudit.EtaleCoefficientCohomologyMap.comparison_zero_surjective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
