import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FaithfullyFlatCocycleCoboundary
import PrimalitySheafVerification.ManuscriptAudit.FlatTwistedBaseChangeLine

/-! The actual Picard class of a faithfully flat unit cocycle commutes
with flat scalar extension. -/

namespace ManuscriptAudit.FaithfullyFlatCocycleBaseChangePicard

open TensorProduct TwistedTensorEqualizer FlatTwistedDescentLine
open FlatTwistedBaseChangeLine FaithfullyFlatCocyclePicard

noncomputable section

universe u
variable (A B S : Type u) [CommRing A] [CommRing B] [CommRing S]
variable [Algebra A B] [Algebra A S] [Module.Flat A S]
variable [Module.FaithfullyFlat A B] [Module.FaithfullyFlat S (Cover A B S)]

/-- The usual extension-of-scalars homomorphism on the native Picard
group sends the line of an actual cocycle to the line of its pullback. -/
theorem picardClass_baseChange (t : (Double A B)ˣ) (ht : IsCocycle A B t)
    (hs : IsCocycle S (Cover A B S) (pulledUnit A B S t)) :
    CommRing.Pic.mapAlgebra A S (picardClass A B t ht) =
      picardClass S (Cover A B S) (pulledUnit A B S t) hs := by
  let I := invariants A B t
  let J := invariants S (Cover A B S) (pulledUnit A B S t)
  letI : Module.Invertible A I := invariants_invertible A B t ht
  letI : Module.Invertible S J := invariants_invertible S (Cover A B S) (pulledUnit A B S t) hs
  let e : CommRing.Pic.mk A I ≃ₗ[A] I := CommRing.Pic.mk.linearEquiv A I
  change CommRing.Pic.mk S (S ⊗[A] CommRing.Pic.mk A I) = CommRing.Pic.mk S J
  apply CommRing.Pic.mk_eq_mk_iff.mpr
  exact ⟨(e.baseChange A S _ _).trans (lineBaseChange A B S t)⟩

end

end ManuscriptAudit.FaithfullyFlatCocycleBaseChangePicard

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.FaithfullyFlatCocycleBaseChangePicard.picardClass_baseChange
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
