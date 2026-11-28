import Lean.Util.CollectAxioms
import Mathlib.GroupTheory.QuotientGroup.Basic
import PrimalitySheafVerification.ManuscriptAudit.EtalePresheafHOneRepresentatives

/-! Restriction comparisons in degree one can be constructed directly
on the actual ambient cokernel-section representatives. -/

namespace ManuscriptAudit.EtalePresheafHOneTransport

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open EtalePresheafHOneRepresentatives

noncomputable section

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

universe u v
variable {X : Scheme.{u}}
variable {F I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (i : F ⟶ I) [Mono i] [Injective I]
variable (U : X.Etale) {H : Type v} [AddCommGroup H]
variable (b : (cokernel i).obj.obj (op U) →+ H) (hb : Function.Surjective b)
variable (hk : ∀ x, connectingAt i U x = 0 ↔ b x = 0)

private theorem same_kernel : (connectingAt i U).ker = b.ker := by
  ext x
  exact hk x

/-- A surjective comparison of actual ambient representatives that
preserves their vanishing induces the actual cohomology comparison. -/
def transport : F.H' 1 U ≃+ H :=
  (QuotientAddGroup.quotientKerEquivOfSurjective (connectingAt i U) (connectingAt_surjective i U)).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq (same_kernel i U b hk)).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective b hb))

/-- The comparison evaluates on the exact chosen ambient representative. -/
theorem transport_connecting (x : (cokernel i).obj.obj (op U)) :
    transport i U b hb hk (connectingAt i U x) = b x := by
  let e := QuotientAddGroup.quotientKerEquivOfSurjective (connectingAt i U) (connectingAt_surjective i U)
  have he : connectingAt i U x = e (QuotientAddGroup.mk x) := rfl
  unfold transport
  rw [he]
  simp only [AddEquiv.trans_apply, AddEquiv.symm_apply_apply, QuotientAddGroup.quotientAddEquivOfEq_mk] <;> rfl

end

end ManuscriptAudit.EtalePresheafHOneTransport

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.EtalePresheafHOneTransport.transport_connecting
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
