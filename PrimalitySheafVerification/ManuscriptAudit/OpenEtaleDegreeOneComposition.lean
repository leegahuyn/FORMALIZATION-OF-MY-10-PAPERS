import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleDegreeOneCoefficients
import PrimalitySheafVerification.ManuscriptAudit.NestedOpenEtaleHOneNaturality

/-! Composition of actual degree-one pullback with coefficient maps. -/

namespace ManuscriptAudit.OpenEtaleDegreeOneComposition

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open OpenEtaleExtension OpenEtaleDegreeOnePullback OpenEtaleDegreeOneCoefficients
open NestedOpenEtaleHOneNaturality

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

universe u

private abbrev A := AddCommGrpCat.{u}
private abbrev C (X : Scheme.{u}) := Sheaf X.smallEtaleTopology A.{u}
private abbrev R {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] := restriction j A.{u}

variable {V U X : Scheme.{u}}
variable (i : V ⟶ U) [IsOpenImmersion i]
variable (j : U ⟶ X) [IsOpenImmersion j]

local instance : PreservesFiniteLimits (R j) := (restriction_exact j).1

local instance : (R j).PreservesInjectiveObjects := by
  let E := extensionByZero j A.{u}
  letI : PreservesFiniteLimits E := (extensionByZero_exact j).1
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (abelianExtensionByZeroAdjunction j)

/-- The canonical H¹ map commutes with each genuine coefficient map. -/
theorem pullback_coeff {F G : C X} (a : F ⟶ G) (c : Sheaf.H F 1) :
    Sheaf.H.map ((R j).map a) 1 (pullback j F c) =
      pullback j G (Sheaf.H.map a 1 c) := by
  let m := Injective.ι F
  let n := Injective.ι G
  let b := Injective.factorThru (a ≫ n) m
  exact pullbackHOne_coeff j m n a b (Injective.comp_factorThru (a ≫ n) m) c

/-- The canonical H¹ map respects ordinary composition of the actual opens. -/
theorem pullback_comp (F : C X) (c : Sheaf.H F 1) :
    Sheaf.H.map ((restrictionCompIso i j).hom.app F) 1
        (pullback i ((R j).obj F) (pullback j F c)) =
      pullback (i ≫ j) F c := by
  let m := Injective.ι F
  let g := (R j).map m
  letI : Mono g := inferInstanceAs (Mono ((R j).map m))
  letI : Injective ((R j).obj (Injective.under F)) := inferInstance
  have h := pullback_eq i g (pullback j F c)
  rw [h]
  exact pullbackHOne_comp i j m c

/-- Pullback followed by a specified morphism of the restricted coefficients. -/
def pullbackWith {F : C X} {G : C U} (a : (R j).obj F ⟶ G) :
    Sheaf.H F 1 →+ Sheaf.H G 1 :=
  (Sheaf.H.map a 1).comp (pullback j F)

/-- Composition transports the coefficient map by the actual comparison
of restrictions. -/
theorem pullbackWith_comp {F : C X} {G : C U} {H : C V}
    (a : (R j).obj F ⟶ G) (b : (R i).obj G ⟶ H) (c : Sheaf.H F 1) :
    pullbackWith i b (pullbackWith j a c) =
      pullbackWith (i ≫ j)
        ((restrictionCompIso i j).inv.app F ≫ (R i).map a ≫ b) c := by
  let e := restrictionCompIso i j
  let d := (R i).map a ≫ b
  let w := pullback i ((R j).obj F) (pullback j F c)
  change Sheaf.H.map b 1 (pullback i G (Sheaf.H.map a 1 (pullback j F c))) =
    Sheaf.H.map (e.inv.app F ≫ d) 1 (pullback (i ≫ j) F c)
  rw [← pullback_coeff i a, ← Sheaf.H.map_comp_apply, ← pullback_comp i j,
    ← Sheaf.H.map_comp_apply]
  change Sheaf.H.map d 1 w = Sheaf.H.map (e.hom.app F ≫ e.inv.app F ≫ d) 1 w
  simp

end

end ManuscriptAudit.OpenEtaleDegreeOneComposition

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.OpenEtaleDegreeOneComposition.pullback_coeff,
      ``ManuscriptAudit.OpenEtaleDegreeOneComposition.pullback_comp,
      ``ManuscriptAudit.OpenEtaleDegreeOneComposition.pullbackWith_comp] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
