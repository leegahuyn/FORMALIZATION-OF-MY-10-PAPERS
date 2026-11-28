import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleFiniteClosedImageHTwo
import PrimalitySheafVerification.ManuscriptAudit.ProetaleNestedOpenBoundary

/-! Finite-coefficient native compact H² agrees with ambient H²
when removing an algebraically closed rational boundary point. -/

namespace ManuscriptAudit.ProetaleFiniteCompactHTwoEquiv

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open ProetaleContinuousDirectImageMaps (functions functionsOver diagonal)
open ProetaleClosedOpenRestriction (extensionFunctionsIsoKernel)
open ProetaleClosedKernelLocalSupport (inc)
open ProetaleCohomologyIso (cohomologyIso)
open OpenProetaleExtension (extensionByZero)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}
private abbrev integers (X : Scheme.{0}) :=
  (constantSheaf (Scheme.ProEt.topology X) A).obj (AddCommGrpCat.of (ULift.{1} ℤ))

set_option maxHeartbeats 3400000 in
/-- In the literal long exact sequence the support map is bijective
when the first two positive groups of the boundary vanish. -/
def shortExactEquiv {X : Scheme.{0}} (S : ShortComplex (Sheaf (Scheme.ProEt.topology X) A))
    (h : S.ShortExact) (h₁ : Subsingleton (Sheaf.H S.X₃ 1)) (h₂ : Subsingleton (Sheaf.H S.X₃ 2)) :
    Sheaf.H S.X₁ 2 ≃+ Sheaf.H S.X₂ 2 := by
  let p := Sheaf.H.map S.f 2
  refine AddEquiv.ofBijective p ⟨?_, ?_⟩
  · intro x y he
    apply sub_eq_zero.mp
    have hz : p (x - y) = 0 := by rw [map_sub, he, sub_self]
    obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ (integers X) h (x - y) hz (show 1 + 1 = 2 by rfl)
    rw [h₁.elim z 0, Ext.zero_comp] at hz
    exact hz.symm
  · intro y
    exact Ext.covariant_sequence_exact₂ (integers X) h y (h₂.elim _ _)

variable (K : Type) [Field K] [IsAlgClosed K] {X : Scheme.{0}}
  (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M] [Finite M]

private theorem closedHOne (i : Spec (CommRingCat.of K) ⟶ X) :
    Subsingleton (Sheaf.H (functionsOver M i) 1) := by
  letI := ProetaleAlgebraicallyClosedCohomology.H_succ_subsingleton K
    (functions M (Spec (CommRingCat.of K))) 0
  exact ProetaleDirectImageHOne.directImage_HOne_subsingleton i _

/-- Actual extension from the complement of one boundary point. -/
def singleEquiv {U : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
    (i : Spec (CommRingCat.of K) ⟶ X) [IsClosedImmersion i]
    (h : Set.range j = (Set.range i)ᶜ) :
    Sheaf.H ((extensionByZero j A).obj (functions M U)) 2 ≃+ Sheaf.H (functions M X) 2 :=
  let S := ShortComplex.mk (inc i M) (diagonal M i) (kernel.condition (diagonal M i))
  (cohomologyIso (X := X) (extensionFunctionsIsoKernel i j M h) 2).trans
    (shortExactEquiv S (ProetaleOpenClosedHOne.closedSequence_shortExact K i M)
      (closedHOne K M i) (ProetaleFiniteClosedImageHTwo.HTwo_subsingleton i M))

/-- Actual nested extension while removing one more closed point. -/
def nestedEquiv {V U : Scheme.{0}} (v : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion v] [IsOpenImmersion j]
    (i : Spec (CommRingCat.of K) ⟶ U) [IsClosedImmersion i] [IsClosedImmersion (i ≫ j)]
    (h : Set.range v = (Set.range i)ᶜ) :
    Sheaf.H ((extensionByZero (v ≫ j) A).obj (functions M V)) 2 ≃+
      Sheaf.H ((extensionByZero j A).obj (functions M U)) 2 := by
  let S := ProetaleNestedOpenBoundary.sequence j K i M
  let hS := ProetaleNestedOpenBoundary.sequence_shortExact j K i M
  let e := ProetaleNestedOpenBoundary.closedIso j K i M
  letI : Subsingleton (Sheaf.H (functionsOver M (i ≫ j)) 1) := closedHOne K M (i ≫ j)
  letI : Subsingleton (Sheaf.H (functionsOver M (i ≫ j)) 2) :=
    ProetaleFiniteClosedImageHTwo.HTwo_subsingleton (i ≫ j) M
  let h₁ := (cohomologyIso (X := X) e 1).injective.subsingleton
  let h₂ := (cohomologyIso (X := X) e 2).injective.subsingleton
  exact (cohomologyIso (X := X) (ProetaleNestedOpenBoundary.smallerIso v j K i M h) 2).trans
    (shortExactEquiv S hS h₁ h₂)

end
end ManuscriptAudit.ProetaleFiniteCompactHTwoEquiv

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleFiniteCompactHTwoEquiv.singleEquiv,
      ``ManuscriptAudit.ProetaleFiniteCompactHTwoEquiv.nestedEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
