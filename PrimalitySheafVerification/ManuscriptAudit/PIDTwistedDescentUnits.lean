import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.TorsionFree
import PrimalitySheafVerification.ManuscriptAudit.FlatTwistedDescentLine

/-! Every actual unit cocycle for a faithfully flat algebra over a
principal ideal domain is a coboundary. -/

namespace ManuscriptAudit.PIDTwistedDescentUnits

open Algebra TensorProduct
open TwistedTensorEqualizer FlatTwistedDescentLine

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v

variable (A : Type u) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
variable (B : Type v) [CommRing B] [Nontrivial B] [Algebra A B] [Module.FaithfullyFlat A B]

/-- For a faithfully flat cover of the spectrum of a PID, a genuine
multiplicative tensor-square cocycle has an actual unit trivialization. -/
theorem exists_coboundary (t : (Double A B)ˣ) (ht : IsCocycle A B t) :
    ∃ v : Bˣ, (t : Double A B) = second A B (v : B) * first A B (↑(v⁻¹) : B) := by
  let L := invariants A B t
  let e := extensionEquiv A B t ht
  letI : Module.Finite B (B ⊗[A] L) :=
    Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  letI : Module.Finite A L := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B
  letI : Module.IsTorsionFree A B := inferInstance
  letI : Module.IsTorsionFree A L := inferInstance
  letI : Module.Free A L := inferInstance
  let I := Module.Free.ChooseBasisIndex A L
  let a : Module.Basis I A L := Module.Free.chooseBasis A L
  letI : Fintype I := Fintype.ofFinite I
  have hc : Fintype.card I = 1 := calc
    Fintype.card I = Module.finrank B (B ⊗[A] L) :=
      (Module.finrank_eq_card_basis (a.baseChange B)).symm
    _ = Module.finrank B B := LinearEquiv.finrank_eq e
    _ = 1 := Module.finrank_self B
  let b : Module.Basis (Fin 1) A L := a.reindex (Fintype.equivFinOfCardEq hc)
  let c : Module.Basis (Fin 1) B B := (b.baseChange B).map e
  let x := b 0
  have hcx : c 0 = x.val := by
    change e (b.baseChange B 0) = x.val
    rw [Module.Basis.baseChange_apply]
    change extension A B t (1 ⊗ₜ[A] x) = x.val
    simp only [extension_tmul, one_mul]
  let y := c.repr (1 : B) 0
  have hy : y * x.val = 1 := by
    have h := c.sum_repr (1 : B)
    simpa only [Fin.sum_univ_one, smul_eq_mul, hcx] using h
  let v : Bˣ := ⟨x.val, y, (mul_comm _ _).trans hy, hy⟩
  have hx : second A B (v : B) = (t : Double A B) * first A B (v : B) :=
    (mem_invariants A B t x.val).mp x.property
  refine ⟨v, ?_⟩
  calc
    (t : Double A B) = ((t : Double A B) * first A B (v : B)) * first A B (↑(v⁻¹) : B) := by
      rw [mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
    _ = second A B (v : B) * first A B (↑(v⁻¹) : B) := by rw [hx]

end
end ManuscriptAudit.PIDTwistedDescentUnits

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.PIDTwistedDescentUnits.exists_coboundary
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
