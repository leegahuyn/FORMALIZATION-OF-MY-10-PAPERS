import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NestedOpenEtaleCokernelNaturality
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleDegreeOnePullback

/-! Actual degree-one small étale pullback is compatible with composition
of genuine open immersions, including semilinear automorphisms. -/

namespace ManuscriptAudit.NestedOpenEtaleHOneNaturality

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open OpenEtaleExtension EtaleTwoOpenHOne OpenEtaleHOneByRepresentatives
open EtaleHOneCokernelNaturality OpenEtaleDegreeOnePullback SheafH1Descent
open NestedOpenEtaleCokernelNaturality NestedOpenEtaleSectionNaturality

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

universe u
variable {V U X : Scheme.{u}}
variable (i : V ⟶ U) [IsOpenImmersion i] (j : U ⟶ X) [IsOpenImmersion j]

private abbrev A := AddCommGrpCat.{u}
private abbrev C (Y : Scheme.{u}) := Sheaf Y.smallEtaleTopology A.{u}
private abbrev T (Y : Scheme.{u}) := identityObject Y
private abbrev t (Y : Scheme.{u}) := MorphismProperty.Over.mkIdTerminal @Etale Y
private abbrev R {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f] := restriction f A.{u}
private abbrev e : R j ⋙ R i ≅ R (i ≫ j) := restrictionCompIso i j

local instance : PreservesFiniteLimits (R i) := (restriction_exact i).1
local instance : PreservesFiniteLimits (R j) := (restriction_exact j).1
local instance : PreservesFiniteLimits (R (i ≫ j)) := (restriction_exact (i ≫ j)).1
local instance : PreservesFiniteColimits (R i) := (restriction_exact i).2
local instance : PreservesFiniteColimits (R j) := (restriction_exact j).2
local instance : PreservesFiniteColimits (R (i ≫ j)) := (restriction_exact (i ≫ j)).2
local instance : (R i).Additive := restriction_additive i
local instance : (R j).Additive := restriction_additive j
local instance : (R (i ≫ j)).Additive := restriction_additive (i ≫ j)

local instance : (R j).PreservesInjectiveObjects := by
  let E := extensionByZero j A.{u}
  letI : PreservesFiniteLimits E := (extensionByZero_exact j).1
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (abelianExtensionByZeroAdjunction j)

variable {F I : C X} (m : F ⟶ I) [Mono m] [Injective I]

private theorem openArrow_nested :
    nestedObjectArrow i j ≫ openArrow j = openArrow (i ≫ j) := by
  apply MorphismProperty.Over.Hom.ext
  rfl

private theorem sections_restrict_twice (z : (cokernel m).obj.obj (op (T X))) :
    (cokernel m).obj.map (nestedObjectArrow i j).op ((cokernel m).obj.map (openArrow j).op z) =
      (cokernel m).obj.map (openArrow (i ≫ j)).op z := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, openArrow_nested]

private abbrev compare (m : F ⟶ I) :=
  (compareCokernels i j m).hom

private theorem connecting_compared
    (z : (cokernel ((R i).map ((R j).map m))).obj.obj (op (T V))) :
    Sheaf.H.map ((e i j).hom.app F) 1
      (connectingSection ((R i).map ((R j).map m)) (t V) z) =
    connectingSection ((R (i ≫ j)).map m) (t V) ((compare i j m).hom.app (op (T V)) z) :=
  connectingSection_map ((R i).map ((R j).map m)) ((R (i ≫ j)).map m)
    ((e i j).hom.app F) ((e i j).hom.app I) ((e i j).hom.naturality m) z

/-- The actual nested pullback of a true small étale H¹ class agrees
with pullback to the actual composite open. -/
theorem pullbackHOne_comp (c : Sheaf.H F 1) :
    Sheaf.H.map ((e i j).hom.app F) 1
        (pullbackHOne ((R j).map m) i (pullbackHOne m j c)) =
      pullbackHOne m (i ≫ j) c := by
  obtain ⟨x, rfl⟩ := connectingSection_surjective m (t X) c
  let y := (cokernel m).obj.map (openArrow j).op x
  let w := cokernelSectionEquiv j m y
  let z := cokernelSectionEquiv i ((R j).map m)
    ((cokernel ((R j).map m)).obj.map (openArrow i).op w)
  have h₁ : pullbackHOne m j (connectingSection m (t X) x) =
      connectingSection ((R j).map m) (t U) w :=
    pullbackHOne_connecting m j x
  have h₂ : pullbackHOne ((R j).map m) i (connectingSection ((R j).map m) (t U) w) =
      connectingSection ((R i).map ((R j).map m)) (t V) z :=
    pullbackHOne_connecting ((R j).map m) i w
  have h₃ : (compare i j m).hom.app (op (T V)) z =
      cokernelSectionEquiv (i ≫ j) m ((cokernel m).obj.map (openArrow (i ≫ j)).op x) :=
    (cokernelSections_nested i j m y).trans
      (congrArg (cokernelSectionEquiv (i ≫ j) m) (sections_restrict_twice i j m x))
  rw [h₁, h₂, connecting_compared, h₃, pullbackHOne_connecting]

end

end ManuscriptAudit.NestedOpenEtaleHOneNaturality

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NestedOpenEtaleHOneNaturality.pullbackHOne_comp
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
