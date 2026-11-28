import Lean.Util.CollectAxioms
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import PrimalitySheafVerification.ManuscriptAudit.EtalePresheafHOneTransport
import PrimalitySheafVerification.ManuscriptAudit.SheafH1ConnectingExact

/-! Native degree-one comparison between evaluating ambient étale
cohomology on an open and taking cohomology on the actual open site.
Both sides are compared on sections of the same restricted cokernel. -/

namespace ManuscriptAudit.OpenEtaleHOneByRepresentatives

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open OpenEtaleExtension EtalePresheafHOneRepresentatives EtalePresheafHOneTransport
open SheafH1Descent SheafH1ConnectingExact

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

universe u
private abbrev A := AddCommGrpCat.{u}
private abbrev C (Y : Scheme.{u}) := Sheaf Y.smallEtaleTopology A.{u}

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

private abbrev R := restriction j A.{u}
private abbrev O := Scheme.Etale.mk j
private abbrev T := Scheme.Etale.mk (𝟙 U)
private abbrev terminal := MorphismProperty.Over.mkIdTerminal @Etale U

local instance : PreservesFiniteLimits (R j) := (restriction_exact j).1
local instance : PreservesFiniteColimits (R j) := (restriction_exact j).2
local instance : (R j).Additive := restriction_additive j
local instance : (R j).PreservesInjectiveObjects := by
  let E := extensionByZero j A.{u}
  letI : PreservesFiniteLimits E := (extensionByZero_exact j).1
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (abelianExtensionByZeroAdjunction j)

private def objectIso : (etalePostcompose j).obj (T (U := U)) ≅ O j :=
  MorphismProperty.Over.isoMk (Iso.refl U) (by rfl)

/-- Actual sections over an open in the ambient site and on the open site. -/
def sectionEquiv (F : C X) :
    F.obj.obj (op (O j)) ≃+ ((R j).obj F).obj.obj (op (T (U := U))) :=
  (F.obj.mapIso (objectIso j).op).addCommGroupIsoToAddEquiv

theorem sectionEquiv_natural {F I : C X} (g : F ⟶ I)
    (x : F.obj.obj (op (O j))) :
    sectionEquiv j I (g.hom.app (op (O j)) x) =
      ((R j).map g).hom.app (op (T (U := U))) (sectionEquiv j F x) := by
  exact (NatTrans.naturality_apply g.hom (objectIso j).hom.op x).symm

variable {F I : C X} (i : F ⟶ I) [Mono i]

private abbrev i' := (R j).map i
private abbrev Q := cokernel i
private abbrev Q' := cokernel (i' j i)

private def clearCokernel : (R j).obj (Q i) ≅ Q' j i :=
  PreservesCokernel.iso (R j) i

/-- The actual cokernel section comparison from exact open restriction. -/
def cokernelSectionEquiv :
    (Q i).obj.obj (op (O j)) ≃+ (Q' j i).obj.obj (op (T (U := U))) := by
  let E := (sheafSections U.smallEtaleTopology A.{u}).obj (op (T (U := U)))
  exact (sectionEquiv j (Q i)).trans ((E.mapIso (clearCokernel j i)).addCommGroupIsoToAddEquiv)

private theorem cokernelSectionEquiv_π (z : I.obj.obj (op (O j))) :
    cokernelSectionEquiv j i ((cokernel.π i).hom.app (op (O j)) z) =
      (cokernel.π (i' j i)).hom.app (op (T (U := U))) (sectionEquiv j I z) := by
  change (clearCokernel j i).hom.hom.app (op (T (U := U)))
      (sectionEquiv j (Q i) ((cokernel.π i).hom.app (op (O j)) z)) = _
  rw [sectionEquiv_natural]
  have h := PreservesCokernel.π_iso_hom (R j) i
  exact congrArg (fun f : (R j).obj I ⟶ Q' j i =>
    f.hom.app (op (T (U := U))) (sectionEquiv j I z)) h

private def openConnecting :
    (Q' j i).obj.obj (op (T (U := U))) →+ Sheaf.H ((R j).obj F) 1 := by
  let S := ShortComplex.mk (i' j i) (cokernel.π (i' j i)) (cokernel.condition (i' j i))
  have h : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (i' j i))
      mono_f := inferInstance, epi_g := inferInstance }
  exact (h.extClass.postcomp _ (zero_add 1)).comp
    (Sheaf.H.equiv₀ (Q' j i) (terminal (U := U))).symm.toAddMonoidHom

private theorem openConnecting_apply (x : (Q' j i).obj.obj (op (T (U := U)))) :
    openConnecting j i x = connectingSection (i' j i) (terminal (U := U)) x := rfl

private theorem same_kernel :
    (connectingAt i (O j)).ker =
      ((openConnecting j i).comp (cokernelSectionEquiv j i).toAddMonoidHom).ker := by
  ext x
  change connectingAt i (O j) x = 0 ↔ openConnecting j i (cokernelSectionEquiv j i x) = 0
  rw [connectingAt_eq_zero_iff, openConnecting_apply, connectingSection_eq_zero_iff]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨sectionEquiv j I z, (cokernelSectionEquiv_π j i z).symm.trans (congrArg _ hz)⟩
  · rintro ⟨z, hz⟩
    obtain ⟨z', rfl⟩ := (sectionEquiv j I).surjective z
    exact ⟨z', (cokernelSectionEquiv j i).injective ((cokernelSectionEquiv_π j i z').trans hz)⟩

variable [Injective I]

private def openRepresentatives :
    (Q i).obj.obj (op (O j)) →+ Sheaf.H ((R j).obj F) 1 :=
  (openConnecting j i).comp (cokernelSectionEquiv j i).toAddMonoidHom

private theorem openRepresentatives_surjective : Function.Surjective (openRepresentatives j i) := by
  change Function.Surjective (openConnecting j i ∘ cokernelSectionEquiv j i)
  apply Function.Surjective.comp ?_ (cokernelSectionEquiv j i).surjective
  intro a
  obtain ⟨s, hs⟩ := connectingSection_surjective (i' j i) (terminal (U := U)) a
  exact ⟨s, (openConnecting_apply j i s).trans hs⟩

private theorem openRepresentatives_zero (x : (Q i).obj.obj (op (O j))) :
    connectingAt i (O j) x = 0 ↔ openRepresentatives j i x = 0 := by
  change x ∈ (connectingAt i (O j)).ker ↔ x ∈ (openRepresentatives j i).ker
  rw [same_kernel j i] <;> rfl

/-- A native comparison for degree one with an explicit formula on genuine
cokernel-section representatives. -/
def degreeOneEquiv : F.H' 1 (O j) ≃+ Sheaf.H ((R j).obj F) 1 :=
  transport i (O j) (openRepresentatives j i) (openRepresentatives_surjective j i)
    (openRepresentatives_zero j i)

theorem degreeOneEquiv_connecting (x : (Q i).obj.obj (op (O j))) :
    degreeOneEquiv j i (connectingAt i (O j) x) =
      connectingSection (i' j i) (terminal (U := U)) (cokernelSectionEquiv j i x) :=
  (transport_connecting i (O j) (openRepresentatives j i) (openRepresentatives_surjective j i)
    (openRepresentatives_zero j i) x).trans (openConnecting_apply j i _)

end

end ManuscriptAudit.OpenEtaleHOneByRepresentatives

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.OpenEtaleHOneByRepresentatives.degreeOneEquiv_connecting
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
