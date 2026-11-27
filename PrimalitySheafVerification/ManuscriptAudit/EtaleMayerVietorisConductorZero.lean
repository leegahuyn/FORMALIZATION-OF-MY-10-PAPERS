import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleMayerVietorisLocalSection
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleCohomologyPresheaf

/-! When all first-chart classes come from a quotient supported off the overlap, their overlap restriction is zero. -/

namespace ManuscriptAudit.EtaleMayerVietoris

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open EtaleOpenIntersection OpenEtaleExtension OpenEtaleExtendShortExact SheafPresheafHOneBoundary

noncomputable section

universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt
attribute [local instance] OpenEtaleExtension.restriction_additive

private abbrev G := AddCommGrpCat.{u}
private abbrev ÉtaleSheaf (X : Scheme.{u}) := Sheaf X.smallEtaleTopology G.{u}

private theorem boundary_surjective {X : Scheme.{u}} (S : ShortComplex (ÉtaleSheaf X))
    (hS : S.ShortExact) (W : X.Etale) (hMiddle : Subsingleton (S.X₂.H' 1 W)) :
    Function.Surjective (boundaryOfSection X.smallEtaleTopology S hS W) := by
  let J := X.smallEtaleTopology
  let Z := (freeYoneda J).obj W
  intro x
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ (X := Z) hS x (hMiddle.elim _ _)
    (show 0 + 1 = 1 from rfl)
  obtain ⟨f, hf⟩ := (Ext.mk₀_bijective Z S.X₃).surjective z
  let s := sectionEquiv J S.X₃ W f
  have hs : sectionHom J S.X₃ W s = f := (sectionEquiv J S.X₃ W).symm_apply_apply f
  refine ⟨s, ?_⟩
  change (Ext.mk₀ (sectionHom J S.X₃ W s)).comp hS.extClass rfl = x
  rw [hs, hf]
  exact hz

/-- A native short exact sequence on U whose quotient has no sections on U∩V and
whose middle sheaf has trivial H¹ forces the first overlap restriction to vanish. -/
theorem first_leg_zero_of_overlap_quotient_zero {U V X : Scheme.{u}}
    (j : U ⟶ X) (k : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (F : ÉtaleSheaf X) (S : ShortComplex (ÉtaleSheaf U)) (hS : S.ShortExact)
    (e : S.X₁ ≅ (restriction j G.{u}).obj F)
    (hMiddle : Subsingleton (Sheaf.H S.X₂ 1))
    (hOverlap : Subsingleton (S.X₃.obj.obj (op (Scheme.Etale.mk (pullback.fst j k))))) :
    (((F.cohomologyPresheaf 1).map (fstLeg j k).op).hom) = 0 := by
  let J := X.smallEtaleTopology
  let T := extended j S F e
  let hT : T.ShortExact := extended_shortExact j S F e hS
  let φ := restrictedExtensionIso j S F e hS
  let A := Scheme.Etale.mk j
  let D := intersection j k
  let W := Scheme.Etale.mk (pullback.fst j k)
  let a : D ⟶ A := fstLeg j k
  let eOpen := openCohomologyPresheafEquiv j T.X₂ 1
  let eMiddle := ((Sheaf.functorH U.smallEtaleTopology 1).mapIso
    (asIso φ.hom.τ₂)).addCommGroupIsoToAddEquiv
  have hA : Subsingleton (T.X₂.H' 1 A) :=
    ⟨fun x y ↦ eOpen.injective (eMiddle.symm.injective (hMiddle.elim _ _))⟩
  let eOverlap := (((sheafSections U.smallEtaleTopology G.{u}).obj (op W)).mapIso
    (asIso φ.hom.τ₃)).addCommGroupIsoToAddEquiv
  have hD : Subsingleton (T.X₃.obj.obj (op D)) :=
    ⟨fun x y ↦ eOverlap.symm.injective (hOverlap.elim _ _)⟩
  apply AddMonoidHom.ext
  intro x
  let c : T.X₁.H' 1 A := x
  change (T.X₁.cohomologyPresheaf 1).map a.op c = 0
  obtain ⟨s, hs⟩ := boundary_surjective T hT A hA c
  rw [← hs, boundaryOfSection_restrict]
  exact boundaryOfSection_zero_of_lift J T hT D _ 0 (hD.elim _ _)

end
end ManuscriptAudit.EtaleMayerVietoris

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.EtaleMayerVietoris.first_leg_zero_of_overlap_quotient_zero
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
