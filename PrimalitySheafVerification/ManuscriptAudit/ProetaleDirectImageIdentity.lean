import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleBaseChange

/-! The actual native direct image along the identity preserves epimorphisms. -/

namespace ManuscriptAudit.ProetaleDirectImageIdentity

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleBaseChange

noncomputable section
universe u v

variable (X : Scheme.{u})

private def baseChangeIso : baseChange (𝟙 X) ≅ 𝟭 X.ProEt := by
  refine NatIso.ofComponents (fun U ↦ ?_) ?_
  · let f := pullback.fst U.hom (𝟙 X)
    letI : IsIso f := inferInstanceAs (IsIso (pullback.fst U.hom (𝟙 X)))
    refine MorphismProperty.Over.isoMk (asIso f) ?_
    change f ≫ U.hom = pullback.snd U.hom (𝟙 X)
    simpa only [f, Category.comp_id] using pullback.condition (f := U.hom) (g := 𝟙 X)
  · intro U V h
    apply MorphismProperty.Over.Hom.ext
    change ((baseChange (𝟙 X)).map h).left ≫ pullback.fst V.hom (𝟙 X) =
      pullback.fst U.hom (𝟙 X) ≫ h.left
    simp only [baseChange, MorphismProperty.Over.pullback_map_left, pullback.lift_fst]

private abbrev A := AddCommGrpCat.{v}
private abbrev C := Sheaf (Scheme.ProEt.topology X) A.{v}

private def imageIso : directImage (𝟙 X) A.{v} ≅ 𝟭 (C.{u,v} X) := by
  let e : (baseChange (𝟙 X)).op ≅ (𝟭 X.ProEt).op := (NatIso.op (baseChangeIso X)).symm
  refine NatIso.ofComponents (fun M ↦
    (fullyFaithfulSheafToPresheaf (Scheme.ProEt.topology X) A.{v}).preimageIso
      (Functor.isoWhiskerRight e M.obj)) ?_
  intro F G a
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext D
  exact (a.hom.naturality (e.hom.app D)).symm

theorem map_epi {F G : C.{u,v} X} (a : F ⟶ G) [Epi a] :
    Epi ((directImage (𝟙 X) A.{v}).map a) := by
  let e := imageIso X
  apply (epi_comp_iff_of_isIso _ (e.hom.app G)).mp
  rw [e.hom.naturality a]
  exact inferInstanceAs (Epi (e.hom.app F ≫ a))

end
end ManuscriptAudit.ProetaleDirectImageIdentity

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleDirectImageIdentity.map_epi
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
