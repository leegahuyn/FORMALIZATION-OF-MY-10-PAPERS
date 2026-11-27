import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleMayerVietorisCompatiblePair
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtendShortExact
import PrimalitySheafVerification.ManuscriptAudit.SheafPresheafHOneBoundary

/-! A section without a trace lift on one open, but with a lift on the
overlap, produces a nonzero ordinary ambient class. -/

namespace ManuscriptAudit.EtaleMayerVietoris

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open EtaleOpenIntersection EtaleTwoOpenHOne OpenEtaleExtension
open OpenEtaleExtendShortExact SheafPresheafHOneBoundary

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt
attribute [local instance] OpenEtaleExtension.restriction_additive

universe u

private abbrev G := AddCommGrpCat.{u}
private abbrev ÉtaleSheaf (X : Scheme.{u}) := Sheaf X.smallEtaleTopology G.{u}

/-- A section of the quotient has an actual local section in its fiber. -/
def SectionHasLift {X : Scheme.{u}} (S : ShortComplex (ÉtaleSheaf X))
    (W : X.Etale) (s : S.X₃.obj.obj (op W)) : Prop :=
  ∃ t : S.X₂.obj.obj (op W), S.g.hom.app (op W) t = s

/-- Transport of liftability along an actual isomorphism of short complexes. -/
theorem sectionHasLift_iso {X : Scheme.{u}}
    {S T : ShortComplex (ÉtaleSheaf X)} (e : S ≅ T) (W : X.Etale)
    (s : S.X₃.obj.obj (op W)) :
    SectionHasLift T W (e.hom.τ₃.hom.app (op W) s) ↔ SectionHasLift S W s := by
  let A := (sheafSections X.smallEtaleTopology G.{u}).obj (op W)
  let i₂ := A.mapIso (asIso e.hom.τ₂)
  let i₃ := A.mapIso (asIso e.hom.τ₃)
  have hc (t : S.X₂.obj.obj (op W)) :
      T.g.hom.app (op W) (i₂.hom t) = i₃.hom (S.g.hom.app (op W) t) := by
    change ((A.map e.hom.τ₂) ≫ A.map T.g) t = (A.map S.g ≫ A.map e.hom.τ₃) t
    rw [← A.map_comp, ← A.map_comp, e.hom.comm₂₃]
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨t, rfl⟩ := i₂.addCommGroupIsoToAddEquiv.surjective z
    refine ⟨t, i₃.addCommGroupIsoToAddEquiv.injective ?_⟩
    change i₃.hom (S.g.hom.app (op W) t) = i₃.hom s
    rw [← hc]
    exact hz
  · rintro ⟨t, ht⟩
    exact ⟨i₂.hom t, by rw [hc, ht] <;> rfl⟩

variable {U V X : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ X)
variable [IsOpenImmersion j] [IsOpenImmersion k]

/-- The terminal object of the open identifies with its actual ambient chart. -/
def postcomposeTerminalIso :
    (etalePostcompose j).obj (identityObject U) ≅ Scheme.Etale.mk j :=
  MorphismProperty.Over.isoMk (Iso.refl U) (by rfl)

private abbrev innerOverlap := Scheme.Etale.mk (pullback.fst j k)

/-- The actual represented overlap restriction agrees with open postcomposition. -/
theorem postcompose_overlap_arrow :
    (etalePostcompose j).map (openArrow (pullback.fst j k)) ≫ (postcomposeTerminalIso j).hom =
      fstLeg j k := by
  apply MorphismProperty.Over.Hom.ext
  change pullback.fst j k ≫ 𝟙 U = pullback.fst j k
  rw [Category.comp_id]

/-- A nonliftable section on U that lifts on U∩V detects nonzero ambient
H¹, when the kernel of the short exact sequence extends to X. -/
theorem existsHOne_first_not_second_of_local_section_lift
    (hCover : Set.range j ∪ Set.range k = Set.univ)
    (F : ÉtaleSheaf X) (S : ShortComplex (ÉtaleSheaf U)) (hS : S.ShortExact)
    (e : S.X₁ ≅ (restriction j G.{u}).obj F)
    (s : S.X₃.obj.obj (op (identityObject U)))
    (h₀ : ¬ SectionHasLift S (identityObject U) s)
    (h₁ : SectionHasLift S (innerOverlap j k)
      (S.X₃.obj.map (openArrow (pullback.fst j k)).op s)) :
    ∃ z : F.H' 1 (identityObject X),
      (F.cohomologyPresheaf 1).map (openArrow j).op z ≠ 0 ∧
      (F.cohomologyPresheaf 1).map (openArrow k).op z = 0 := by
  let T := extended j S F e
  let hT : T.ShortExact := extended_shortExact j S F e hS
  let φ := restrictedExtensionIso j S F e hS
  let W := innerOverlap j k
  let A := (etalePostcompose j).obj (identityObject U)
  let D := intersection j k
  let b : W ⟶ identityObject U := openArrow (pullback.fst j k)
  let r : D ⟶ A := (etalePostcompose j).map b
  let t : T.X₃.obj.obj (op A) := φ.hom.τ₃.hom.app (op (identityObject U)) s
  have hn : ¬ SectionHasLift T A t := by
    change ¬ SectionHasLift (T.map (restriction j G.{u})) (identityObject U)
      (φ.hom.τ₃.hom.app (op (identityObject U)) s)
    exact fun hs => h₀ ((sectionHasLift_iso φ (identityObject U) s).mp hs)
  have hr : SectionHasLift T D (T.X₃.obj.map r.op t) := by
    have hs : T.X₃.obj.map r.op t =
        φ.hom.τ₃.hom.app (op W) (S.X₃.obj.map b.op s) := by
      exact ConcreteCategory.congr_hom (φ.hom.τ₃.hom.naturality b.op).symm s
    rw [hs]
    change SectionHasLift (T.map (restriction j G.{u})) W
      (φ.hom.τ₃.hom.app (op W) (S.X₃.obj.map b.op s))
    exact (sectionHasLift_iso φ W (S.X₃.obj.map b.op s)).mpr h₁
  let J := X.smallEtaleTopology
  let c₀ : F.H' 1 A := boundaryOfSection J T hT A t
  have hnz : c₀ ≠ 0 :=
    fun h => hn ((boundaryOfSection_eq_zero_iff J T hT A t).mp h)
  have hz : (F.cohomologyPresheaf 1).map r.op c₀ = 0 := by
    change (T.X₁.cohomologyPresheaf 1).map r.op (boundaryOfSection J T hT A t) = 0
    rw [boundaryOfSection_restrict]
    exact (boundaryOfSection_eq_zero_iff J T hT D _).mpr hr
  let q := postcomposeTerminalIso j
  let c := (F.cohomologyPresheaf 1).map q.inv.op c₀
  have hc : c ≠ 0 := by
    let i := (F.cohomologyPresheaf 1).mapIso q.op.symm
    intro h
    apply hnz
    apply i.addCommGroupIsoToAddEquiv.injective
    change i.hom c₀ = i.hom 0
    rw [map_zero]
    exact h
  have hArrow : fstLeg j k ≫ q.inv = r := by
    rw [← postcompose_overlap_arrow j k, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hc0 : (F.cohomologyPresheaf 1).map (fstLeg j k).op c = 0 := by
    have hOp : q.inv.op ≫ (fstLeg j k).op = r.op := by rw [← op_comp, hArrow]
    change (F.cohomologyPresheaf 1).map (fstLeg j k).op
      ((F.cohomologyPresheaf 1).map q.inv.op c₀) = 0
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, hOp]
    exact hz
  have hPair : (F.cohomologyPresheaf 1).map (fstLeg j k).op c =
      (F.cohomologyPresheaf 1).map (sndLeg j k).op 0 := by
    rw [hc0, map_zero]
  obtain ⟨z, hz₁, hz₂⟩ := existsHOne_of_compatible_pair j k F hCover c 0 hPair
  exact ⟨z, fun h => hc (hz₁.symm.trans h), hz₂⟩

/-- A nonliftable section on a chart that lifts on the overlap produces a
nonzero ambient cohomology class. -/
theorem HOne_nontrivial_of_local_section_lift
    (hCover : Set.range j ∪ Set.range k = Set.univ)
    (F : ÉtaleSheaf X) (S : ShortComplex (ÉtaleSheaf U)) (hS : S.ShortExact)
    (e : S.X₁ ≅ (restriction j G.{u}).obj F)
    (s : S.X₃.obj.obj (op (identityObject U)))
    (h₀ : ¬ SectionHasLift S (identityObject U) s)
    (h₁ : SectionHasLift S (innerOverlap j k)
      (S.X₃.obj.map (openArrow (pullback.fst j k)).op s)) :
    Nontrivial (Sheaf.H F 1) := by
  obtain ⟨z, hz, _⟩ := existsHOne_first_not_second_of_local_section_lift j k hCover F S hS e s h₀ h₁
  have h : z ≠ 0 := fun h => hz (by rw [h, map_zero])
  let i := (terminalCohomologyIso F 1).addCommGroupIsoToAddEquiv
  exact ⟨⟨i z, 0, fun h' => h (i.injective (h'.trans (map_zero i).symm))⟩⟩

end
end ManuscriptAudit.EtaleMayerVietoris

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleMayerVietoris.existsHOne_first_not_second_of_local_section_lift,
      ``ManuscriptAudit.EtaleMayerVietoris.HOne_nontrivial_of_local_section_lift] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"

