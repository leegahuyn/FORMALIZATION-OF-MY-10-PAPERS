import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NestedOpenEtaleSectionNaturality
import PrimalitySheafVerification.ManuscriptAudit.PreservedCokernelComposition

/-! The actual sections of the restricted cokernel sheaf commute
with restricting to two successive open immersions. -/

namespace ManuscriptAudit.NestedOpenEtaleCokernelNaturality

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open EtaleTwoOpenHOne OpenEtaleExtension OpenEtaleHOneByRepresentatives
open NestedOpenEtaleSectionNaturality PreservedCokernelComposition

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {V U X : Scheme.{u}}
variable (i : V ⟶ U) [IsOpenImmersion i] (j : U ⟶ X) [IsOpenImmersion j]

private abbrev A := AddCommGrpCat.{u}
private abbrev C (Y : Scheme.{u}) := Sheaf Y.smallEtaleTopology A.{u}
private abbrev T (Y : Scheme.{u}) := identityObject Y
private abbrev R {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f] :=
  restriction f A.{u}
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

private def restrictGlobal (F : C U) (x : F.obj.obj (op (T U))) :
    ((R i).obj F).obj.obj (op (T V)) :=
  sectionEquiv i F (F.obj.map (openArrow i).op x)

private theorem restrictGlobal_natural {F G : C U} (f : F ⟶ G) (x : F.obj.obj (op (T U))) :
    restrictGlobal i G (f.hom.app (op (T U)) x) =
      ((R i).map f).hom.app (op (T V)) (restrictGlobal i F x) := by
  unfold restrictGlobal
  rw [← NatTrans.naturality_apply, sectionEquiv_natural]

variable {F I : C X} (m : F ⟶ I) [Mono m]

/-- The actual composition comparison for the cokernel sheaves. -/
abbrev compareCokernels :=
  inducedCokernelIso (R j) (R i) (R (i ≫ j)) (e i j) m

/-- The native cokernel sections give the same representative when
restricted in two steps or along the composite immersion. -/
theorem cokernelSections_nested (x : (cokernel m).obj.obj (op (Scheme.Etale.mk j))) :
    (compareCokernels i j m).hom.hom.app (op (T V))
      (cokernelSectionEquiv i ((R j).map m)
        ((cokernel ((R j).map m)).obj.map (openArrow i).op (cokernelSectionEquiv j m x))) =
    cokernelSectionEquiv (i ≫ j) m
      ((cokernel m).obj.map (nestedObjectArrow i j).op x) := by
  let t := op (T V)
  let q := PreservesCokernel.iso (R j) m
  let q' := PreservesCokernel.iso (R i) ((R j).map m)
  let q'' := PreservesCokernel.iso (R (i ≫ j)) m
  let k := compareCokernels i j m
  let v := sectionEquiv j (cokernel m) x
  let w := restrictGlobal i ((R j).obj (cokernel m)) v
  have hNatural := restrictGlobal_natural i q.hom v
  have hNested := sectionEquiv_nested i j (cokernel m) x
  have hComp := congrArg (fun f : (R i).obj ((R j).obj (cokernel m)) ⟶
      cokernel ((R (i ≫ j)).map m) => f.hom.app t w)
    (cokernelComparisons_compose (R j) (R i) (R (i ≫ j)) (e i j) m)
  simp only [Sheaf.comp_hom, NatTrans.comp_app, ConcreteCategory.comp_apply] at hComp
  change k.hom.hom.app t
      (q'.hom.hom.app t (restrictGlobal i _ (q.hom.hom.app (op (T U)) v))) =
    q''.hom.hom.app t (sectionEquiv (i ≫ j) (cokernel m)
      ((cokernel m).obj.map (nestedObjectArrow i j).op x))
  rw [hNatural]
  exact hComp.trans (congrArg (fun y => q''.hom.hom.app t y) hNested)

end

end ManuscriptAudit.NestedOpenEtaleCokernelNaturality

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NestedOpenEtaleCokernelNaturality.cokernelSections_nested
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
