import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenExtensionComposition
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenExtensionExact
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenClosedHOne
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenRestrictionDirectImage

/-! The native exact sequence comparing two open supports whose difference
is a rational closed point contained in the larger open. -/

namespace ManuscriptAudit.ProetaleNestedOpenBoundary

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open ProetaleContinuousDirectImageMaps (functions functionsOver diagonal)
open ProetaleClosedKernelLocalSupport (K inc)
open ProetaleClosedOpenRestriction (extensionFunctionsIsoKernel)
open OpenProetaleExtension (extensionByZero)
open ProetaleOpenExtensionComposition (extensionByZeroCompIso)
open ProetaleOpenExtensionExact (extensionByZero_preservesFiniteLimits
  extensionByZero_preservesFiniteColimits)
open ProetaleOpenRestrictionDirectImage (extensionDirectImageIso)
open ProetaleCohomologyIso (cohomologyIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {V U X : Scheme.{0}} (i : V ⟶ U) (j : U ⟶ X)
  [IsOpenImmersion i] [IsOpenImmersion j]
variable (L : Type) [Field L] [IsAlgClosed L]
  (k : Spec (CommRingCat.of L) ⟶ U) [IsClosedImmersion k] [IsClosedImmersion (k ≫ j)]
variable (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M]

private abbrev A := AddCommGrpCat.{1}
private abbrev E := extensionByZero j A

local instance : (E j).Additive := by
  letI := extensionByZero_preservesFiniteLimits j
  exact (E j).additive_of_preserves_binary_products

private abbrev Q := ShortComplex.mk (inc k M) (diagonal M k) (kernel.condition (diagonal M k))

/-- Apply the actual larger extension to the closed-point exact sequence on that open. -/
def sequence : ShortComplex (Sheaf (Scheme.ProEt.topology X) A) :=
  (Q k M).map (E j)

theorem sequence_shortExact : (sequence j k M).ShortExact := by
  letI := extensionByZero_preservesFiniteLimits j
  letI := extensionByZero_preservesFiniteColimits j
  exact (ProetaleOpenClosedHOne.closedSequence_shortExact L k M).map_of_exact (E j)

/-- Its first term is actual extension by zero from the smaller open. -/
def smallerIso (hs : Set.range i = (Set.range k)ᶜ) :
    (extensionByZero (i ≫ j) A).obj (functions M V) ≅ (sequence j k M).X₁ :=
  ((extensionByZeroCompIso i j).symm.app (functions M V)) ≪≫
    (E j).mapIso (extensionFunctionsIsoKernel k i M hs)

/-- Its last term is the actual closed direct image of the removed point. -/
def closedIso : (sequence j k M).X₃ ≅ functionsOver M (k ≫ j) :=
  extensionDirectImageIso j k M

private abbrev integers :=
  (constantSheaf (Scheme.ProEt.topology X) A).obj (AddCommGrpCat.of (ULift.{1} ℤ))

/-- If the larger support has zero cohomology in degrees zero and one, the genuine
connecting arrow identifies smaller compact degree one with the closed point's H⁰. -/
def boundaryEquiv (hs : Set.range i = (Set.range k)ᶜ)
    (h₀ : Subsingleton (Sheaf.H ((E j).obj (functions M U)) 0))
    (h₁ : Subsingleton (Sheaf.H ((E j).obj (functions M U)) 1)) :
    Sheaf.H (functionsOver M (k ≫ j)) 0 ≃+
      Sheaf.H ((extensionByZero (i ≫ j) A).obj (functions M V)) 1 := by
  let S := sequence j k M
  let hS := sequence_shortExact j L k M
  let T := integers (X := X)
  let δ : Sheaf.H S.X₃ 0 →+ Sheaf.H S.X₁ 1 := hS.extClass.postcomp T rfl
  have he := Ext.covariant_sequence_exact₃' T hS 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at he
  have hex : Function.Exact (Sheaf.H.map S.g 0) δ := he
  have hi : Function.Injective δ := by
    intro a b hab
    apply sub_eq_zero.mp
    obtain ⟨z, hz⟩ := (hex (a - b)).mp (by rw [map_sub, hab, sub_self])
    have h : z = 0 := h₀.elim _ _
    rw [h, map_zero] at hz
    exact hz.symm
  have ho : Function.Surjective δ := by
    intro x
    exact Ext.covariant_sequence_exact₁ T hS x (h₁.elim _ _) rfl
  exact (cohomologyIso (X := X) (closedIso j k M).symm 0).trans
    ((AddEquiv.ofBijective δ ⟨hi, ho⟩).trans
      (cohomologyIso (X := X) (smallerIso i j k M hs).symm 1))

end
end ManuscriptAudit.ProetaleNestedOpenBoundary

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleNestedOpenBoundary.sequence_shortExact,
      ``ManuscriptAudit.ProetaleNestedOpenBoundary.smallerIso,
      ``ManuscriptAudit.ProetaleNestedOpenBoundary.closedIso,
      ``ManuscriptAudit.ProetaleNestedOpenBoundary.boundaryEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
