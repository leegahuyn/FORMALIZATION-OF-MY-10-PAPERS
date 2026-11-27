import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleCohomologyIso
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenLocalLifts
import PrimalitySheafVerification.ManuscriptAudit.ProetaleConstantRestriction
import PrimalitySheafVerification.ManuscriptAudit.TwoOpenCokernelLift
import PrimalitySheafVerification.ManuscriptAudit.SheafH1Descent

/-! The actual pro-étale H¹ of a constant discrete group vanishes on
a union of two H¹-acyclic opens with connected nonempty intersection. -/

namespace ManuscriptAudit.ProetaleTwoOpenHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open OpenProetaleExtension (restriction)
open ProetaleOpenRestriction (restrictionConstantIso)
open ProetaleOpenLocalLifts
open ProetaleConstantRestriction
open TwoOpenCokernelLift (coverObjects coverArrows)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {U V X : Scheme.{0}} (j : U ⟶ X) (k : V ⟶ X)
  [IsOpenImmersion j] [IsOpenImmersion k]

private abbrev J (Z : Scheme.{0}) := Scheme.ProEt.topology Z
private abbrev G := AddCommGrpCat.{1}

theorem twoOpenCover (hCover : Set.range j ∪ Set.range k = Set.univ) :
    Sieve.ofArrows (coverObjects (openObject j) (openObject k))
      (coverArrows (openArrow j) (openArrow k)) ∈ J X (identityObject X) := by
  apply Precoverage.generate_mem_toGrothendieck
  change (Presieve.ofArrows (coverObjects (openObject j) (openObject k))
    (coverArrows (openArrow j) (openArrow k))).map
      (Scheme.ProEt.forget X ⋙ Over.forget X) ∈ Scheme.proetalePrecoverage X
  rw [Presieve.map_ofArrows]
  apply Scheme.etalePrecoverage_le_proetalePrecoverage _
  apply (Scheme.ofArrows_mem_precoverage_iff @Etale).mpr
  refine ⟨?_, fun i ↦ ?_⟩
  · intro x
    have hx : x ∈ Set.range j ∪ Set.range k := hCover.symm ▸ Set.mem_univ x
    rcases hx with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨false, y, hy⟩
    · exact ⟨true, y, hy⟩
  · cases i
    · change Etale j
      infer_instance
    · change Etale k
      infer_instance

private abbrev R (j : U ⟶ X) [IsOpenImmersion j] :
    Sheaf (J X) G ⥤ Sheaf (J U) G := restriction j G

local instance nativeHasExt (W : Scheme.{0}) : HasExt.{1} (Sheaf (J W) G) :=
  IsGrothendieckAbelian.hasExt (Sheaf (J W) G)

private theorem restricted_HOne_subsingleton (M : Type) [AddCommGroup M]
    (h : Subsingleton (Sheaf.H (constant U M) 1)) :
    Subsingleton (Sheaf.H ((R j).obj (constant X M)) 1) := by
  let A : G := AddCommGrpCat.of (ULift.{1} M)
  let hIso : (R j).obj (constant X M) ≅ constant U M :=
    (restrictionConstantIso.{0} j).app A
  let e := ProetaleCohomologyIso.cohomologyIso (X := U) hIso 1
  exact ⟨fun a b ↦ e.injective (h.elim _ _)⟩

local instance : EnoughInjectives (Sheaf (J X) G) :=
  IsGrothendieckAbelian.enoughInjectives.{1} (C := Sheaf (J X) G)

set_option maxHeartbeats 1500000 in
/-- Native degree-one cohomology vanishes by gluing sections over an
actual two-open covering family. -/
theorem HOne_subsingleton (M : Type) [AddCommGroup M]
    (hCover : Set.range j ∪ Set.range k = Set.univ)
    {D : X.ProEt} [PreconnectedSpace D.left] [Nonempty D.left]
    (a : D ⟶ openObject j) (b : D ⟶ openObject k)
    (hD : IsPullback a b (openArrow j) (openArrow k))
    (hU : Subsingleton (Sheaf.H (constant U M) 1))
    (hV : Subsingleton (Sheaf.H (constant V M) 1)) :
    Subsingleton (Sheaf.H (constant X M) 1) := by
  let F := constant X M
  let I := Injective.under F
  let i : F ⟶ I := Injective.ι F
  let hT : IsTerminal (identityObject X) := MorphismProperty.Over.mkIdTerminal @WeaklyEtale X
  apply SheafH1Descent.H1_subsingleton_of_global_lifts i hT
  intro x
  have hu := restrictedCokernel_sections_surjective j i (restricted_HOne_subsingleton j M hU)
  have hv := restrictedCokernel_sections_surjective k i (restricted_HOne_subsingleton k M hV)
  let Q := cokernel i
  obtain ⟨zU, hzU⟩ := hu (Q.obj.map (openArrow j).op x)
  obtain ⟨zV, hzV⟩ := hv (Q.obj.map (openArrow k).op x)
  exact TwoOpenCokernelLift.exists_global_lift i (openArrow j) (openArrow k) a b hD
    (twoOpenCover j k hCover) (constantRestriction_surjective a M) x zU zV hzU hzV

end
end ManuscriptAudit.ProetaleTwoOpenHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleTwoOpenHOne.twoOpenCover,
      ``ManuscriptAudit.ProetaleTwoOpenHOne.HOne_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
