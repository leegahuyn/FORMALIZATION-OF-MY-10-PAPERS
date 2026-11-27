import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.Point.Conservative
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleDisjointSections

/-! Epimorphisms lift locally on the actual small étale site. -/

namespace ManuscriptAudit.EtaleEpiLocalSurjectivity

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section
universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- A map of actual abelian small-étale sheaves is locally surjective if it is epi. -/
theorem of_epi {X : Scheme.{u}} {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (f : F ⟶ G) [Epi f] : Sheaf.IsLocallySurjective f := by
  let geometricPoint (x : X) : Spec (.of (SeparableClosure (X.residueField x))) ⟶ X :=
    (Scheme.SpecToEquivOfField (SeparableClosure (X.residueField x)) X).2
      ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) _)⟩
  let P := ObjectProperty.ofObj (fun x : X ↦ Scheme.pointSmallEtale (geometricPoint x))
  have hP : P.IsConservativeFamilyOfPoints :=
    Scheme.isConservativeFamilyOfPoints_pointSmallEtale' X
  apply hP.jointly_reflect_isLocallySurjective f.hom
  intro Φ
  let T := Φ.obj.sheafFiber (A := AddCommGrpCat.{u})
  change Function.Surjective (T.map f)
  exact (AddCommGrpCat.epi_iff_surjective _).mp (T.map_epi f)

/-- The empty étale object has a unique section for every additive sheaf. -/
theorem subsingleton_sections_of_empty {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (U : X.Etale) [IsEmpty U.left] :
    Subsingleton (F.obj.obj (Opposite.op U)) :=
  SmallEtaleDisjointSections.sections_subsingleton_of_isEmpty F U

end
end ManuscriptAudit.EtaleEpiLocalSurjectivity

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleEpiLocalSurjectivity.of_epi,
      ``ManuscriptAudit.EtaleEpiLocalSurjectivity.subsingleton_sections_of_empty] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
