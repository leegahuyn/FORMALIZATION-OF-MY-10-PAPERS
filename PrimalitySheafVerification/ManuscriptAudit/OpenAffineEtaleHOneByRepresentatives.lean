import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NestedAffineEtaleRestriction
import PrimalitySheafVerification.ManuscriptAudit.EtalePresheafHOneTransport
import PrimalitySheafVerification.ManuscriptAudit.KummerAffineCohomology

/-! Direct degree-one comparison between an actual ambient étale open
and its affine small étale basis, on the identical cokernel sections. -/

namespace ManuscriptAudit.OpenAffineEtaleHOneByRepresentatives

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open NestedAffineEtaleRestriction EtalePresheafHOneRepresentatives EtalePresheafHOneTransport
open AffineEtaleTensorOverlap OpenEtaleHOneByRepresentatives
open SheafH1Descent SheafH1ConnectingExact KummerUnitsSheaf

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt
  KummerCohomologySequence.affineSiteHasExt

variable {R : Type} [CommRing R] {X : Scheme.{0}}
variable (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]

private abbrev C := Sheaf X.smallEtaleTopology AddCommGrpCat.{0}
private abbrev T := baseObject R
private abbrev t := KummerAffineCohomology.affineTerminal_isTerminal (CommRingCat.of R)
private abbrev U := Scheme.Etale.mk j
private abbrev A := restrictToAffine j

local instance : PreservesFiniteLimits (A j) := (restrictToAffine_exact j).1
local instance : PreservesFiniteColimits (A j) := (restrictToAffine_exact j).2
local instance : (A j).Additive := (A j).additive_of_preserves_binary_products
local instance : (A j).PreservesInjectiveObjects := restrictToAffine_preservesInjectiveObjects j

private theorem affineSection_natural {F G : C (X := X)} (g : F ⟶ G)
    (x : F.obj.obj (op (U j))) :
    affineSectionEquiv j G (g.hom.app (op (U j)) x) =
      ((A j).map g).hom.app (op (T (R := R))) (affineSectionEquiv j F x) :=
  sectionEquiv_natural j g x

variable {F I : C (X := X)} (i : F ⟶ I) [Mono i]

private abbrev i' := (A j).map i
private abbrev Q := cokernel i
private abbrev Q' := cokernel (i' j i)

private def compareCokernel : (A j).obj (Q i) ≅ Q' j i := PreservesCokernel.iso (A j) i

/-- Actual global cokernel sections evaluated on the affine basis. -/
def affineCokernelSections :
    (Q i).obj.obj (op (U j)) ≃+ (Q' j i).obj.obj (op (T (R := R))) := by
  let E := (sheafSections (Scheme.AffineEtale.topology (Spec (CommRingCat.of R)))
    AddCommGrpCat.{0}).obj (op (T (R := R)))
  exact (affineSectionEquiv j (Q i)).trans ((E.mapIso (compareCokernel j i)).addCommGroupIsoToAddEquiv)

private theorem sections_π (z : I.obj.obj (op (U j))) :
    affineCokernelSections j i ((cokernel.π i).hom.app (op (U j)) z) =
      (cokernel.π (i' j i)).hom.app (op (T (R := R))) (affineSectionEquiv j I z) := by
  change (compareCokernel j i).hom.hom.app (op (T (R := R)))
    (affineSectionEquiv j (Q i) ((cokernel.π i).hom.app (op (U j)) z)) = _
  rw [affineSection_natural]
  exact congrArg (fun f : (A j).obj I ⟶ Q' j i => f.hom.app (op (T (R := R)))
    (affineSectionEquiv j I z)) (PreservesCokernel.π_iso_hom (A j) i)

private def rightConnecting :
    (Q' j i).obj.obj (op (T (R := R))) →+ Sheaf.H ((A j).obj F) 1 := by
  let S := ShortComplex.mk (i' j i) (cokernel.π (i' j i)) (cokernel.condition (i' j i))
  have h : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (i' j i))
      mono_f := inferInstance, epi_g := inferInstance }
  exact (h.extClass.postcomp _ (zero_add 1)).comp
    (Sheaf.H.equiv₀ (Q' j i) (t (R := R))).symm.toAddMonoidHom

private theorem rightConnecting_apply (x : (Q' j i).obj.obj (op (T (R := R)))) :
    rightConnecting j i x = connectingSection (i' j i) (t (R := R)) x := rfl

private def onRepresentatives : (Q i).obj.obj (op (U j)) →+ Sheaf.H ((A j).obj F) 1 :=
  (rightConnecting j i).comp (affineCokernelSections j i).toAddMonoidHom

private theorem onRepresentatives_zero (x : (Q i).obj.obj (op (U j))) :
    connectingAt i (U j) x = 0 ↔ onRepresentatives j i x = 0 := by
  change connectingAt i (U j) x = 0 ↔ rightConnecting j i (affineCokernelSections j i x) = 0
  rw [connectingAt_eq_zero_iff, rightConnecting_apply, connectingSection_eq_zero_iff]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨affineSectionEquiv j I z, (sections_π j i z).symm.trans (congrArg _ hz)⟩
  · rintro ⟨z, hz⟩
    obtain ⟨z', rfl⟩ := (affineSectionEquiv j I).surjective z
    exact ⟨z', (affineCokernelSections j i).injective ((sections_π j i z').trans hz)⟩

variable [Injective I]

private theorem onRepresentatives_surjective : Function.Surjective (onRepresentatives j i) := by
  change Function.Surjective (rightConnecting j i ∘ affineCokernelSections j i)
  apply Function.Surjective.comp ?_ (affineCokernelSections j i).surjective
  intro c
  obtain ⟨x, hx⟩ := connectingSection_surjective (i' j i) (t (R := R)) c
  exact ⟨x, (rightConnecting_apply j i x).trans hx⟩

/-- The actual ambient degree-one cohomology group on an affine open is
the degree-one cohomology of the restricted sheaf on its affine basis. -/
def affineDegreeOneEquiv : F.H' 1 (U j) ≃+ Sheaf.H ((A j).obj F) 1 :=
  transport i (U j) (onRepresentatives j i) (onRepresentatives_surjective j i)
    (onRepresentatives_zero j i)

theorem affineDegreeOneEquiv_connecting (x : (Q i).obj.obj (op (U j))) :
    affineDegreeOneEquiv j i (connectingAt i (U j) x) =
      connectingSection (i' j i) (t (R := R)) (affineCokernelSections j i x) :=
  (transport_connecting i (U j) (onRepresentatives j i) (onRepresentatives_surjective j i)
    (onRepresentatives_zero j i) x).trans (rightConnecting_apply j i _)

end

end ManuscriptAudit.OpenAffineEtaleHOneByRepresentatives

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.OpenAffineEtaleHOneByRepresentatives.affineDegreeOneEquiv_connecting
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
