import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtalePresheafHOneTransport

/-! A native divisor connecting map can be used directly at every étale
object where the middle sheaf's first cohomology vanishes. -/

namespace ManuscriptAudit.EtaleDivisorConnectingAt

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open OpenEtaleExtension EtaleCohomologyPresheafZero EtalePresheafHOneRepresentatives

noncomputable section

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

universe u v
variable {X : Scheme.{u}}
variable {F I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (i : F ⟶ I) [Mono i]
variable (U : X.Etale) (hI : Subsingleton (I.H' 1 U))

private abbrev J := (freeEtaleRepresentable X).obj U

theorem connecting_surjective : Function.Surjective (connectingAt i U) := by
  have hS : (ShortComplex.cokernelSequence i).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact i) inferInstance inferInstance
  intro x
  have hx : x.comp (Ext.mk₀ i) (add_zero 1) = 0 := hI.allEq _ _
  have h := Ext.covariant_sequence_exact₁' (J U) hS 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  obtain ⟨z, hz⟩ := (h x).1 hx
  refine ⟨equivZero (cokernel i) U z, ?_⟩
  change (hS.extClass.postcomp (J U) (zero_add 1))
    ((equivZero (cokernel i) U).symm (equivZero (cokernel i) U z)) = x
  rw [AddEquiv.symm_apply_apply]
  exact hz

variable {H : Type v} [AddCommGroup H]
variable (b : (cokernel i).obj.obj (op U) →+ H) (hb : Function.Surjective b)

private theorem same_kernel (hk : ∀ x, connectingAt i U x = 0 ↔ b x = 0) :
    (connectingAt i U).ker = b.ker := by
  ext x
  exact hk x

/-- Two surjective realizations of the actual divisor sections with the
same kernel identify the cohomology and divisor class groups. -/
def classEquiv (hk : ∀ x, connectingAt i U x = 0 ↔ b x = 0) : F.H' 1 U ≃+ H :=
  (QuotientAddGroup.quotientKerEquivOfSurjective (connectingAt i U) (connecting_surjective i U hI)).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq (same_kernel i U b hk)).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective b hb))

theorem classEquiv_connecting (hk : ∀ x, connectingAt i U x = 0 ↔ b x = 0)
    (x : (cokernel i).obj.obj (op U)) :
    classEquiv i U hI b hb hk (connectingAt i U x) = b x := by
  let e := QuotientAddGroup.quotientKerEquivOfSurjective (connectingAt i U) (connecting_surjective i U hI)
  let k := QuotientAddGroup.quotientAddEquivOfEq (same_kernel i U b hk)
  let g := QuotientAddGroup.quotientKerEquivOfSurjective b hb
  have he : connectingAt i U x = e (QuotientAddGroup.mk x) := rfl
  change g (k (e.symm (connectingAt i U x))) = b x
  rw [he, AddEquiv.symm_apply_apply]
  unfold k
  rw [QuotientAddGroup.quotientAddEquivOfEq_mk] <;> rfl

end

end ManuscriptAudit.EtaleDivisorConnectingAt

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleDivisorConnectingAt.connecting_surjective,
      ``ManuscriptAudit.EtaleDivisorConnectingAt.classEquiv_connecting] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
