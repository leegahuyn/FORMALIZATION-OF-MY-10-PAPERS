import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportHigherComparison

/-!
# The native five-term sequence for compact support on the cusp

The rational origin contributes only degree-zero cohomology.
The Ext long exact sequence therefore gives the five-term sequence
from degree-zero sections of the puncture to degree-one cohomology
of the whole cusp. The middle arrow is the actual connecting map.
-/

namespace ManuscriptAudit.CuspCompactSupportLowDegrees

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Function
open CuspCompactSupportSequence

universe u

noncomputable section

variable (K : Type u) [Field K] [IsSepClosed K]

attribute [local instance] SmallEtaleCohomologyComparison.fullSiteHasExt

private abbrev J : GrothendieckTopology (CuspProperCompactification.projectiveCusp K).Etale :=
  (CuspProperCompactification.projectiveCusp K).smallEtaleTopology

private abbrev freeConstant : Sheaf (J K) AddCommGrpCat.{u} :=
  (constantSheaf (J K) AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))

private theorem sequenceShortExact (M : AddCommGrpCat.{u}) :
    (compactSupportSequence K M).ShortExact :=
  (compactSupportSequence_shortExact K M).2

/-- The actual connecting morphism in the compact-support comparison. -/
def connecting (M : AddCommGrpCat.{u}) :
    Sheaf.H (compactSupportSequence K M).X₃ 0 →+ punctureHc K M 1 :=
  (sequenceShortExact K M).extClass.postcomp (freeConstant K) (show 0 + 1 = 1 by rfl)

/-- The displayed maps of native cohomology form the degree-zero and degree-one
five-term exact sequence. -/
theorem compactSupportFiveTerm (M : AddCommGrpCat.{u}) :
    Injective (Sheaf.H.map (compactSupportSequence K M).f 0) ∧
    Exact (Sheaf.H.map (compactSupportSequence K M).f 0)
      (Sheaf.H.map (compactSupportSequence K M).g 0) ∧
    Exact (Sheaf.H.map (compactSupportSequence K M).g 0) (connecting K M) ∧
    Exact (connecting K M) (Sheaf.H.map (compactSupportSequence K M).f 1) ∧
    Surjective (Sheaf.H.map (compactSupportSequence K M).f 1) := by
  let Q := compactSupportSequence K M
  let hQ := sequenceShortExact K M
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · letI : Mono Q.f := hQ.mono_f
    intro x y hxy
    apply Ext.addEquiv₀.injective
    have h := congrArg (fun c => (Ext.addEquiv₀ c : freeConstant K ⟶ Q.X₂)) hxy
    simp only [Sheaf.H.addEquiv₀_map] at h
    exact (cancel_mono Q.f).mp h
  · exact (ShortComplex.ab_exact_iff_function_exact _).mp
      (Ext.covariant_sequence_exact₂' (freeConstant K) hQ 0)
  · exact (ShortComplex.ab_exact_iff_function_exact _).mp
      (Ext.covariant_sequence_exact₃' (freeConstant K) hQ 0 1 (by rfl))
  · exact (ShortComplex.ab_exact_iff_function_exact _).mp
      (Ext.covariant_sequence_exact₁' (freeConstant K) hQ 0 1 (by rfl))
  · intro x
    have h : Sheaf.H.map Q.g 1 x = 0 :=
      (CuspCompactSupportHigherComparison.compactSupportBoundaryH_succ_subsingleton K M 0).elim _ _
    exact Ext.covariant_sequence_exact₂ (freeConstant K) hQ x h

end

end ManuscriptAudit.CuspCompactSupportLowDegrees

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CuspCompactSupportLowDegrees.connecting,
      ``ManuscriptAudit.CuspCompactSupportLowDegrees.compactSupportFiveTerm] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
