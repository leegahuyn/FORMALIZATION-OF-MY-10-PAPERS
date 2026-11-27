import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Card

/-! A finite reduced kernel counts the original cokernel when the reduction kernel is in the image. -/

namespace ManuscriptAudit.ReducedLinearKernelCard

open LinearMap Submodule

noncomputable section

variable {R T V : Type*} [Ring R] [AddCommGroup T] [AddCommGroup V]
  [Module R T] [Module R V]

/-- In a finite abelian module, the kernel and cokernel of an endomorphism have the same order. -/
theorem card_ker_eq_card_cokernel [Finite V] (g : V →ₗ[R] V) :
    Nat.card ↥(LinearMap.ker g) = Nat.card (V ⧸ LinearMap.range g) := by
  have hr := Submodule.card_eq_card_quotient_mul_card (LinearMap.range g)
  have hk := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker g)
  rw [Nat.card_congr g.quotKerEquivRange.toEquiv] at hk
  have he : Nat.card ↥(LinearMap.range g) * Nat.card ↥(LinearMap.ker g) =
      Nat.card ↥(LinearMap.range g) * Nat.card (V ⧸ LinearMap.range g) :=
    (Nat.mul_comm _ _).trans (hk.symm.trans hr)
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos he

/-- Reduction computes the original index from the exact finite reduced kernel. -/
theorem card_ker_of_reduction [Finite V] (eval : T →ₗ[R] V) (hEval : Function.Surjective eval)
    (f : T →ₗ[R] T) (g : V →ₗ[R] V) (h : ∀ x, eval (f x) = g (eval x))
    (hk : LinearMap.ker eval ≤ LinearMap.range f) :
    Nat.card ↥(LinearMap.ker g) = Nat.card (T ⧸ LinearMap.range f) := by
  let q := (LinearMap.range g).mkQ.comp eval
  have hq : Function.Surjective q := ((LinearMap.range g).mkQ_surjective).comp hEval
  have hK : LinearMap.ker q = LinearMap.range f := by
    apply Submodule.ext
    intro x
    rw [LinearMap.mem_ker]
    change (LinearMap.range g).mkQ (eval x) = 0 ↔ x ∈ LinearMap.range f
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨v, hv⟩
      obtain ⟨y, rfl⟩ := hEval v
      have hxy : x - f y ∈ LinearMap.ker eval := LinearMap.mem_ker.mpr (by
        rw [map_sub, h, hv, sub_self])
      have hy : f y ∈ LinearMap.range f := ⟨y, rfl⟩
      simpa only [sub_add_cancel] using (LinearMap.range f).add_mem (hk hxy) hy
    · rintro ⟨y, rfl⟩
      exact ⟨eval y, (h y).symm⟩
  have hc := Nat.card_congr (q.quotKerEquivOfSurjective hq).toEquiv
  rw [hK] at hc
  exact (card_ker_eq_card_cokernel g).trans hc.symm

end
end ManuscriptAudit.ReducedLinearKernelCard

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ReducedLinearKernelCard.card_ker_of_reduction
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
