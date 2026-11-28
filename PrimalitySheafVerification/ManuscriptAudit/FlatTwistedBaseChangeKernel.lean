import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Flat.Basic
import PrimalitySheafVerification.ManuscriptAudit.FlatTwistedDescentLine

/-! The kernel of a native twisted Čech differential commutes with flat
extension of scalars. -/

namespace ManuscriptAudit.FlatTwistedBaseChangeKernel

open TensorProduct FlatTwistedDescentLine TwistedTensorEqualizer

noncomputable section

universe u
variable {A B S : Type u} [CommRing A] [CommRing B] [CommRing S]
variable [Algebra A B] [Algebra A S] [Module.Flat A S]

/-- The tensor extension of an actual cocycle's invariant line is the
kernel of the base-changed actual twisted differential. -/
def invariantsBaseChange (t : (Double A B)ˣ) :
    S ⊗[A] invariants A B t ≃ₗ[S] ((differential A B t).baseChange S).ker := by
  let d := differential A B t
  let I := invariants A B t
  have h : Function.Exact I.subtype d := by
    intro b
    constructor
    · intro hb
      exact ⟨⟨b, hb⟩, rfl⟩
    · rintro ⟨c, rfl⟩
      exact c.property
  have hb := Module.Flat.lTensor_exact S h
  have hr : (I.subtype.baseChange S).range = (d.baseChange S).ker := by
    ext b
    exact (hb b).symm
  exact (Submodule.toBaseChange.toLinearEquiv S I).trans (LinearEquiv.ofEq _ _ hr)

end

end ManuscriptAudit.FlatTwistedBaseChangeKernel

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.FlatTwistedBaseChangeKernel.invariantsBaseChange
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
