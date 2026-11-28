import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleTerminalSectionHom
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleDegreeOneCoefficients
import PrimalitySheafVerification.ManuscriptAudit.ConnectingExtNaturality

/-! The canonical full small-étale pullback in degree one is literally
the exact-functor Ext map with the actual constant coefficients. -/

namespace ManuscriptAudit.OpenEtaleDegreeOneExt

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open TerminalCohomologySectionHom OpenEtaleTerminalSectionHom OpenEtaleExtension
open OpenEtaleDegreeOneCoefficients OpenEtaleDegreeOnePullback OpenEtaleHOneByRepresentatives
open SheafH1Descent EtaleTwoOpenHOne

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

universe u
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

private abbrev A := AddCommGrpCat.{u}
private abbrev J (Y : Scheme.{u}) := Y.smallEtaleTopology
private abbrev R := restriction j A.{u}
private abbrev T (Y : Scheme.{u}) := identityObject Y
private abbrev t (Y : Scheme.{u}) := MorphismProperty.Over.mkIdTerminal @Etale Y
private abbrev C (Y : Scheme.{u}) := Sheaf (J Y) A.{u}
private abbrev Z (Y : Scheme.{u}) := integerSheaf (J Y)

local instance : PreservesFiniteLimits (R j) := (restriction_exact j).1
local instance : PreservesFiniteColimits (R j) := (restriction_exact j).2
local instance : (R j).Additive := restriction_additive j

/-- Actual pullback through the exact full small-site restriction functor. -/
def extPullback (F : C X) : Sheaf.H F 1 →+ Sheaf.H ((R j).obj F) 1 :=
  ((Ext.mk₀ (constantIntegerIso j).hom).precomp _ (zero_add 1)).comp
    ((R j).mapExtAddHom (Z X) F 1)

private abbrev seq {D : Type*} [Category* D] [Abelian D] {F I : D} (m : F ⟶ I) :=
  ShortComplex.mk m (cokernel.π m) (cokernel.condition m)

private theorem short_exact {D : Type*} [Category* D] [Abelian D] {F I : D} (m : F ⟶ I) [Mono m] :
    (seq m).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel m)
  mono_f := inferInstance
  epi_g := inferInstance

private theorem connecting_formula {Y : Scheme.{u}} {F I : C Y} (m : F ⟶ I) [Mono m]
    (x : (cokernel m).obj.obj (op (T Y))) :
    connectingSection m (t Y) x =
      (Ext.mk₀ (sectionHom (J Y) (t Y) (cokernel m) x)).comp (short_exact m).extClass (zero_add 1) := by
  exact congrArg (fun z : Ext (Z Y) (cokernel m) 0 =>
    z.comp (short_exact m).extClass (zero_add 1)) (mk₀_sectionHom (J Y) (t Y) (cokernel m) x).symm

variable {F I : C X} (m : F ⟶ I) [Mono m]
private abbrev m' := (R j).map m
private abbrev q := (PreservesCokernel.iso (R j) m).hom

private def sequenceMap : (seq m).map (R j) ⟶ seq (m' j m) where
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := q j m
  comm₁₂ := by simp
  comm₂₃ := by
    rw [Category.id_comp]
    exact (PreservesCokernel.π_iso_hom (R j) m).symm

private theorem extPullback_class (s : Z X ⟶ cokernel m) :
    extPullback j F ((Ext.mk₀ s).comp (short_exact m).extClass (zero_add 1)) =
      (Ext.mk₀ ((constantIntegerIso j).hom ≫ (R j).map s ≫ q j m)).comp
        (short_exact (m' j m)).extClass (zero_add 1) := by
  have h := ConnectingExtNaturality.map_connecting (C := C X) (D := C U) (R j)
    (S := seq m) (T := seq (m' j m)) (short_exact m) (short_exact (m' j m))
    (sequenceMap j m) (constantIntegerIso j).hom s
  simpa only [sequenceMap, Ext.comp_mk₀_id] using h

private theorem extPullback_connecting (x : (cokernel m).obj.obj (op (T X))) :
    extPullback j F (connectingSection m (t X) x) =
      connectingSection (m' j m) (t U)
        (cokernelSectionEquiv j m ((cokernel m).obj.map (openArrow j).op x)) := by
  let x' := cokernelSectionEquiv j m ((cokernel m).obj.map (openArrow j).op x)
  let s := sectionHom (J X) (t X) (cokernel m) x
  have hs : (constantIntegerIso j).hom ≫ (R j).map s ≫ q j m =
      sectionHom (J U) (t U) (cokernel (m' j m)) x' := by
    rw [← Category.assoc, ← sectionHom_restrict j (cokernel m) x,
      ← sectionHom_map (J U) (t U) ((R j).obj (cokernel m)) (q j m)] <;> rfl
  rw [connecting_formula, extPullback_class, hs, ← connecting_formula]

/-- The actual exact-functor pullback agrees with the canonical native
degree-one pullback calculated on injective representatives. -/
theorem extPullback_eq (c : Sheaf.H F 1) :
    extPullback j F c = pullback j F c := by
  let i := Injective.ι F
  obtain ⟨x, rfl⟩ := connectingSection_surjective i (t X) c
  rw [pullback_eq j i _, pullbackHOne_connecting, extPullback_connecting]

end

end ManuscriptAudit.OpenEtaleDegreeOneExt

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.OpenEtaleDegreeOneExt.extPullback_eq
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
