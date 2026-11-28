import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.PullbackCarrier
import PrimalitySheafVerification.ManuscriptAudit.SplitClosedProetaleDirectImage

/-! The closed-support complement is quasi-compact on all actual affine
charts as soon as the base complement is quasi-compact. -/

namespace ManuscriptAudit.SplitClosedProetaleComplement

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open SplitClosedProetaleDirectImage

noncomputable section
universe u

variable {S T : Scheme.{u}} (i : S ⟶ T) [IsClosedImmersion i]

def baseComplement : T.Opens :=
  ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- A geometric point belongs to the closed fiber exactly when its base
image lies on the actual closed immersion. -/
theorem complement_eq_preimage (U : T.ProEt) :
    complement i U = U.hom ⁻¹ᵁ baseComplement i := by
  ext x
  change (x ∉ Set.range (pullback.fst U.hom i)) ↔ (U.hom x ∉ Set.range i)
  apply not_congr
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨pullback.snd U.hom i z, ?_⟩
    exact (congrArg (fun f : pullback U.hom i ⟶ T ↦ f z)
      (pullback.condition (f := U.hom) (g := i))).symm
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz, _⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := U.hom) (g := i) x y hy.symm
    exact ⟨z, hz⟩

theorem chart_quasiCompact (h : QuasiCompact (baseComplement i).ι) (U : T.ProEt) :
    QuasiCompact (complement i U).ι := by
  rw [complement_eq_preimage]
  exact MorphismProperty.of_isPullback (P := @QuasiCompact)
    (isPullback_morphismRestrict U.hom (baseComplement i)) h

theorem baseComplement_quasiCompact [NoetherianSpace T] :
    QuasiCompact (baseComplement i).ι := by
  letI : NoetherianSpace (baseComplement i) :=
    inferInstanceAs (NoetherianSpace (↥((baseComplement i : T.Opens) : Set T)))
  exact ⟨fun _ _ _ ↦ NoetherianSpace.isCompact _⟩

/-- For a split closed immersion into a Noetherian topological space, the
actual pro-étale direct image takes epimorphisms to epimorphisms. -/
theorem map_epi [IsAffine S] [NoetherianSpace T] (r : T ⟶ S) (hir : i ≫ r = 𝟙 S)
    {F G : Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u+1}} (α : F ⟶ G) [Epi α] :
    Epi ((ProetaleBaseChange.directImage i AddCommGrpCat.{u+1}).map α) :=
  SplitClosedProetaleDirectImage.map_epi i r hir
    (fun U _ ↦ chart_quasiCompact i (baseComplement_quasiCompact i) U) α

end
end ManuscriptAudit.SplitClosedProetaleComplement

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SplitClosedProetaleComplement.map_epi
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
