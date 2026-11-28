import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleRestrictRepresentative
import PrimalitySheafVerification.ManuscriptAudit.ConnectingExtNaturality
import PrimalitySheafVerification.ManuscriptAudit.SheafH1Descent
import PrimalitySheafVerification.ManuscriptAudit.KummerAffineCohomology

/-! Derived degree-one restriction on the actual affine small étale basis.
Its connecting-section formula is compatible with literal local representatives. -/

namespace ManuscriptAudit.AffineEtaleDerivedRestriction

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AffineEtaleTensorOverlap AffineEtaleOpenRestriction AffineEtaleOpenBaseChange
open AffineEtaleCechRestriction AffineEtaleRestrictionNaturality
open AffineEtaleRestrictedUnits AffineEtaleRestrictedResolution AffineEtaleRestrictRepresentative
open KummerUnitsSheaf SheafH1Descent

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] KummerCohomologySequence.affineSiteHasExt

variable (A S : Type) [CommRing A] [CommRing S] [Algebra A S]

private abbrev X (R : Type) [CommRing R] := Spec (CommRingCat.of R)
private abbrev J (R : Type) [CommRing R] := Scheme.AffineEtale.topology (X R)
private abbrev C (R : Type) [CommRing R] := Sheaf (J R) AddCommGrpCat.{0}
private abbrev Z (R : Type) [CommRing R] :=
  (constantSheaf (J R) AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift.{0} ℤ))
private abbrev G (R : Type) [CommRing R] := coordinateUnitSheaf (X R)
private abbrev terminal (R : Type) [CommRing R] :=
  KummerAffineCohomology.affineTerminal_isTerminal (CommRingCat.of R)
private abbrev j := Spec.map (CommRingCat.ofHom (algebraMap A S))
variable [IsOpenImmersion (j A S)]
private abbrev R := affineRestriction (j A S)

local instance : PreservesFiniteLimits (R A S) := (affineRestriction_exact (j A S)).1
local instance : PreservesFiniteColimits (R A S) := (affineRestriction_exact (j A S)).2
local instance : (R A S).Additive := (R A S).additive_of_preserves_binary_products

private def sectionHom (B : Type) [CommRing B] (F : C B)
    (x : F.obj.obj (op (baseObject B))) : Z B ⟶ F :=
  Ext.homEquiv₀ ((Sheaf.H.equiv₀ F (terminal B)).symm x)

private theorem mk₀_sectionHom (B : Type) [CommRing B] (F : C B)
    (x : F.obj.obj (op (baseObject B))) :
    Ext.mk₀ (sectionHom B F x) = (Sheaf.H.equiv₀ F (terminal B)).symm x :=
  Ext.mk₀_homEquiv₀_apply _

private theorem sectionHom_map (B : Type) [CommRing B]
    {F G : C B} (f : F ⟶ G) (x : F.obj.obj (op (baseObject B))) :
    sectionHom B G (f.hom.app (op (baseObject B)) x) = sectionHom B F x ≫ f := by
  apply (Ext.mk₀_bijective (Z B) G).injective
  rw [mk₀_sectionHom, ← Ext.mk₀_comp_mk₀, mk₀_sectionHom]
  exact (Sheaf.H.equiv₀_symm_naturality (terminal B) f x).symm

private def generator (B : Type) [CommRing B] : (Z B).obj.obj (op (baseObject B)) :=
  Sheaf.H.equiv₀ (Z B) (terminal B) (Ext.mk₀ (𝟙 (Z B)))

private theorem sectionHom_generator (B : Type) [CommRing B] :
    sectionHom B (Z B) (generator B) = 𝟙 _ := by
  apply (Ext.mk₀_bijective (Z B) (Z B)).injective
  rw [mk₀_sectionHom, generator, AddEquiv.symm_apply_apply]

private theorem sectionHom_eval (B : Type) [CommRing B] (F : C B)
    (x : F.obj.obj (op (baseObject B))) :
    (sectionHom B F x).hom.app (op (baseObject B)) (generator B) = x := by
  apply (Sheaf.H.equiv₀ F (terminal B)).symm.injective
  rw [← mk₀_sectionHom, sectionHom_map, sectionHom_generator, Category.id_comp, mk₀_sectionHom]

/-- The constant-object map is determined by the actual pullback of the
integer generator to the affine open. -/
def restrictionConstant : Z S ⟶ (R A S).obj (Z A) :=
  sectionHom S _ ((restrictSection (j A S) (Z A) (baseMap A S)).hom (generator A))

/-- The native derived restriction map on degree-one affine unit cohomology. -/
def restrictHOne : Sheaf.H (G A) 1 →+ Sheaf.H (G S) 1 :=
  ((Ext.mk₀ (restrictionConstant A S)).precomp _ (zero_add 1)).comp
    (((Ext.mk₀ (restrictionUnitsIso (j A S)).hom).postcomp _ (add_zero 1)).comp
      ((R A S).mapExtAddHom (Z A) (G A) 1))

private abbrev seq {D : Type*} [Category* D] [Abelian D] {F I : D} (i : F ⟶ I) :=
  ShortComplex.mk i (cokernel.π i) (cokernel.condition i)

private theorem short_exact {D : Type*} [Category* D] [Abelian D]
    {F I : D} (i : F ⟶ I) [Mono i] : (seq i).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i)
  mono_f := inferInstance
  epi_g := inferInstance

variable {I : C A} (i : G A ⟶ I) [Mono i]
variable (x : (cokernel i).obj.obj (op (baseObject A)))

private theorem restrictionConstant_section :
    sectionHom S (cokernel (restrictedInjection (j A S) i)) (restrictGlobal A S i x) =
      restrictionConstant A S ≫ (R A S).map (sectionHom A (cokernel i) x) ≫
        (restrictedCokernelIso (j A S) i).hom := by
  let f := sectionHom A (cokernel i) x
  let q := restrictedCokernelIso (j A S) i
  let b := baseMap A S
  have hm := restrictSection_sheafMap (j A S) f b
  have hp := congrArg (fun k : (Z A).obj.obj (op (baseObject A)) ⟶
      ((R A S).obj (cokernel i)).obj.obj (op (baseObject S)) => k.hom (generator A)) hm
  simp only [ConcreteCategory.comp_apply] at hp
  have hx : f.hom.app (op (baseObject A)) (generator A) = x := sectionHom_eval A _ x
  rw [hx] at hp
  unfold restrictGlobal restrictionConstant
  change sectionHom S _ (q.hom.hom.app (op (baseObject S))
      ((restrictSection (j A S) (cokernel i) b).hom x)) = _
  rw [sectionHom_map, hp, sectionHom_map, Category.assoc]

set_option maxHeartbeats 800000 in
/-- Actual derived restriction takes a true connecting representative to
the connecting representative of the genuinely restricted global section. -/
theorem restrictHOne_connecting :
    restrictHOne A S (connectingSection i (terminal A) x) =
      connectingSection (restrictedInjection (j A S) i) (terminal S) (restrictGlobal A S i x) := by
  let k := restrictedInjection (j A S) i
  let q := restrictedSequenceComparison (j A S) i
  have h := ConnectingExtNaturality.map_connecting (R A S) (short_exact i) (short_exact k) q
    (restrictionConstant A S) (sectionHom A (cokernel i) x)
  change (Ext.mk₀ (restrictionConstant A S)).comp
      ((((Ext.mk₀ (sectionHom A (cokernel i) x)).comp (short_exact i).extClass (zero_add 1)).
        mapExactFunctor (R A S)).comp (Ext.mk₀ (restrictionUnitsIso (j A S)).hom)
          (add_zero 1)) (zero_add 1) =
    (Ext.mk₀ (restrictionConstant A S ≫ (R A S).map (sectionHom A (cokernel i) x) ≫
      (restrictedCokernelIso (j A S) i).hom)).comp (short_exact k).extClass (zero_add 1) at h
  rw [← restrictionConstant_section A S i x, mk₀_sectionHom, mk₀_sectionHom] at h
  exact h

end

end ManuscriptAudit.AffineEtaleDerivedRestriction

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineEtaleDerivedRestriction.restrictHOne_connecting
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
