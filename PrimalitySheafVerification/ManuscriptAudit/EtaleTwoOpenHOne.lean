import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleLocalLifts
import PrimalitySheafVerification.ManuscriptAudit.EtaleConstantRestriction
import PrimalitySheafVerification.ManuscriptAudit.TwoOpenCokernelLift

/-!
# Degree-one constant étale descent over two opens

When the ordinary degree-one groups on two covering opens vanish,
and their overlap is nonempty and preconnected, the constant sheaf
has zero H¹ on the ambient scheme. The argument lifts a representative
locally and corrects its overlap difference using constant sections.
-/

namespace ManuscriptAudit.EtaleTwoOpenHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open OpenEtaleExtension OpenEtaleLocalLifts EtaleConstantRestriction

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

private abbrev G := AddCommGrpCat.{u}

abbrev identityObject (X : Scheme.{u}) : X.Etale := Scheme.Etale.mk (𝟙 X)

def openArrow {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Scheme.Etale.mk j ⟶ identityObject X :=
  MorphismProperty.Over.homMk j (Category.comp_id j)

private theorem openArrow_mono {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Mono (openArrow j) where
  right_cancellation f g h := by
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono j).mp
    exact congrArg (fun a => a.left) h

private abbrev C (X : Scheme.{u}) (M : G.{u}) :=
  (constantSheaf X.smallEtaleTopology G.{u}).obj M

private theorem restricted_HOne_subsingleton {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (M : G.{u}) (h : Subsingleton (Sheaf.H (C U M) 1)) :
    Subsingleton (Sheaf.H ((restriction j G.{u}).obj (C X M)) 1) := by
  let e := ((Sheaf.functorH U.smallEtaleTopology 1).mapIso
    ((restrictionConstantIso j).app M)).addCommGroupIsoToAddEquiv
  exact ⟨fun x y => e.injective (h.allEq (e x) (e y))⟩

/-- The native constant small-étale H¹ vanishes through a connected two-open cover. -/
theorem constantHOne_subsingleton {U V X : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] (M : G.{u})
    (hCover : Set.range j ∪ Set.range k = Set.univ)
    {D : X.Etale} [PreconnectedSpace D.left] [Nonempty D.left]
    (a : D ⟶ Scheme.Etale.mk j) (b : D ⟶ Scheme.Etale.mk k)
    (hD : IsPullback a b (openArrow j) (openArrow k))
    (hU : Subsingleton (Sheaf.H (C U M) 1))
    (hV : Subsingleton (Sheaf.H (C V M) 1)) :
    Subsingleton (Sheaf.H (C X M) 1) := by
  let f := openArrow j
  let g := openArrow k
  letI : Mono f := openArrow_mono j
  letI : Mono g := openArrow_mono k
  have hC : Sieve.ofArrows
      (TwoOpenCokernelLift.coverObjects (Scheme.Etale.mk j) (Scheme.Etale.mk k))
      (TwoOpenCokernelLift.coverArrows f g) ∈ X.smallEtaleTopology (identityObject X) := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ Set.range j ∪ Set.range k := hCover.symm ▸ Set.mem_univ x
    rcases hx with hj | hk
    · exact Set.mem_iUnion.2 ⟨false, hj⟩
    · exact Set.mem_iUnion.2 ⟨true, hk⟩
  let F := C X M
  let I := Injective.under F
  let i : F ⟶ I := Injective.ι F
  letI : Mono i := inferInstanceAs (Mono (Injective.ι F))
  let T := identityObject X
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal @Etale X
  apply SheafH1Descent.H1_subsingleton_of_global_lifts i hT
  intro x
  have hu := restrictedCokernel_sections_surjective j i
    (restricted_HOne_subsingleton j M hU)
  have hv := restrictedCokernel_sections_surjective k i
    (restricted_HOne_subsingleton k M hV)
  let Q := cokernel i
  obtain ⟨zU, hzU⟩ := hu (Q.obj.map f.op x)
  obtain ⟨zV, hzV⟩ := hv (Q.obj.map g.op x)
  exact TwoOpenCokernelLift.exists_global_lift i f g a b hD hC
    (constantRestriction_surjective a M) x zU zV hzU hzV

end

end ManuscriptAudit.EtaleTwoOpenHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.EtaleTwoOpenHOne.constantHOne_subsingleton
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
