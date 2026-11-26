import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtension

/-!
# Étale stalk of extension by zero at a point of the open

Pulling a pointed étale neighborhood back to the open gives a refinement.
The resulting cofinal comparison of stalks and the fully faithful Kan
extension unit identify the ambient stalk with the original stalk.
-/

namespace ManuscriptAudit.OpenEtaleExtension

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U)

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev openPoint := Scheme.pointSmallEtale s
private abbrev ambientPoint := Scheme.pointSmallEtale (s ≫ j)

private def postcomposePoint {W : U.Etale}
    (t : (openPoint s).fiber.obj W) :
    (ambientPoint j s).fiber.obj ((etalePostcompose j).obj W) :=
  Over.homMk t.left (by
    have h : t.left ≫ W.hom = s := Over.w t
    change t.left ≫ (W.hom ≫ j) = s ≫ j
    rw [← Category.assoc, h])

private def pointedPostcompose :
    (openPoint s).fiber.Elements ⥤ (ambientPoint j s).fiber.Elements where
  obj W := ⟨(etalePostcompose j).obj W.1, postcomposePoint j s W.2⟩
  map {W V} f := ⟨(etalePostcompose j).map f.val, by
    apply CostructuredArrow.hom_ext
    change W.2.left ≫ f.val.left = V.2.left
    exact congrArg (fun t => t.left) f.property⟩

private def pointedPostcomposeFullyFaithful : (pointedPostcompose j s).FullyFaithful where
  preimage {W V} f :=
    let e := postcomposeFullyFaithful j
    let g := e.preimage f.val
    ⟨g, by
      have hg := congrArg (fun a => a.left) (e.map_preimage f.val)
      change g.left = f.val.left at hg
      apply CostructuredArrow.hom_ext
      change W.2.left ≫ g.left = V.2.left
      rw [hg]
      exact congrArg (fun t => t.left) f.property⟩
  map_preimage f := Subtype.ext ((postcomposeFullyFaithful j).map_preimage f.val)
  preimage_map f := Subtype.ext ((postcomposeFullyFaithful j).preimage_map f.val)

private theorem pointedPostcompose_initial : (pointedPostcompose j s).Initial := by
  letI := (pointedPostcomposeFullyFaithful j s).full
  letI := (pointedPostcomposeFullyFaithful j s).faithful
  apply Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful
  intro W
  let V := (MorphismProperty.Over.pullback @Etale ⊤ j).obj W.1
  have ht : W.2.left ≫ W.1.hom = s ≫ j := Over.w W.2
  let a : Spec (.of Ω) ⟶ V.left := pullback.lift W.2.left s ht
  let v : (openPoint s).fiber.obj V := Over.homMk a (pullback.lift_snd _ _ _)
  let q : (etalePostcompose j).obj V ⟶ W.1 :=
    MorphismProperty.Over.homMk (pullback.fst W.1.hom j) pullback.condition
  refine ⟨⟨V, v⟩, ⟨⟨q, ?_⟩⟩⟩
  apply CostructuredArrow.hom_ext
  change a ≫ pullback.fst W.1.hom j = W.2.left
  exact pullback.lift_fst _ _ _

private def presheafFiberComparison (P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (ambientPoint j s).presheafFiber.obj P ≅
      (openPoint s).presheafFiber.obj ((etalePostcompose j).op ⋙ P) := by
  letI := pointedPostcompose_initial j s
  let R := (CategoryOfElements.π (ambientPoint j s).fiber).op ⋙ P
  change colimit R ≅ colimit ((pointedPostcompose j s).op ⋙ R)
  exact (Functor.Final.colimitIso (pointedPostcompose j s).op R).symm

/-- Cofinal comparison of presheaf stalks along the open immersion. -/
def presheafFiberComparisonNatIso :
    (ambientPoint j s).presheafFiber (A := AddCommGrpCat.{u}) ≅
      (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj (etalePostcompose j).op ⋙
        (openPoint s).presheafFiber := by
  letI := pointedPostcompose_initial j s
  let I := (pointedPostcompose j s).op
  let π := (CategoryOfElements.π (ambientPoint j s).fiber).op
  refine (NatIso.ofComponents (fun P => (presheafFiberComparison j s P).symm) ?_).symm
  intro P Q f
  change colim.map (Functor.whiskerLeft I (Functor.whiskerLeft π f)) ≫ colimit.pre (π ⋙ Q) I =
    colimit.pre (π ⋙ P) I ≫ colim.map (Functor.whiskerLeft π f)
  exact (colimit.pre_map (Functor.whiskerLeft π f) I).symm

/-- Stalk comparison inside the open, naturally in the sheaf being restricted. -/
def restrictionStalkNatIso :
    restriction j AddCommGrpCat.{u} ⋙ (openPoint s).sheafFiber ≅
      (ambientPoint j s).sheafFiber :=
  (Functor.isoWhiskerLeft (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (presheafFiberComparisonNatIso j s)).symm

/-- Stalk comparison inside the open, naturally in the sheaf being extended. -/
def extensionByZeroStalkNatIso :
    extensionByZero j AddCommGrpCat.{u} ⋙ (ambientPoint j s).sheafFiber ≅
      (openPoint s).sheafFiber := by
  let C := AddCommGrpCat.{u}
  let G := (etalePostcompose j).op
  letI := (postcomposeFullyFaithful j).full
  letI := (postcomposeFullyFaithful j).faithful
  letI := hasLeftKanExtension j C
  letI := hasPointwiseLeftKanExtension j C
  let incl := sheafToPresheaf U.smallEtaleTopology C
  let a := (ambientPoint j s).presheafToSheafCompSheafFiberIso C
  let b := presheafFiberComparisonNatIso j s
  let c := asIso (G.lanUnit (H := C))
  exact Functor.isoWhiskerLeft incl (Functor.isoWhiskerLeft G.lan a) ≪≫
    Functor.isoWhiskerLeft incl (Functor.isoWhiskerLeft G.lan b) ≪≫
    Functor.isoWhiskerLeft incl (Functor.isoWhiskerRight c.symm (openPoint s).presheafFiber) ≪≫
    Functor.isoWhiskerLeft incl (Functor.leftUnitor _)

/-- At a geometric point of the open, the actual extension by zero has
the same stalk as the original sheaf. -/
def extensionByZeroStalkIso (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) :
    (ambientPoint j s).sheafFiber.obj
      ((extensionByZero j AddCommGrpCat.{u}).obj F) ≅ (openPoint s).sheafFiber.obj F := by
  let C := AddCommGrpCat.{u}
  let G := (etalePostcompose j).op
  letI := (postcomposeFullyFaithful j).full
  letI := (postcomposeFullyFaithful j).faithful
  letI := hasLeftKanExtension j C
  letI := hasPointwiseLeftKanExtension j C F.obj
  let P := G.lan.obj F.obj
  let e : F.obj ≅ G ⋙ P := asIso (G.lanUnit.app F.obj)
  change (ambientPoint j s).sheafFiber.obj ((presheafToSheaf X.smallEtaleTopology C).obj P) ≅
    (openPoint s).presheafFiber.obj F.obj
  exact ((ambientPoint j s).presheafToSheafCompSheafFiberIso C).app P ≪≫
    presheafFiberComparison j s P ≪≫ ((openPoint s).presheafFiber.mapIso e).symm

end

end ManuscriptAudit.OpenEtaleExtension

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.OpenEtaleExtension.extensionByZeroStalkIso,
      ``ManuscriptAudit.OpenEtaleExtension.restrictionStalkNatIso,
      ``ManuscriptAudit.OpenEtaleExtension.extensionByZeroStalkNatIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
