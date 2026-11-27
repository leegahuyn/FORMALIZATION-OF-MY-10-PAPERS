import Lean.Util.CollectAxioms
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Tactic.Abel

/-! A surjective linear map to a free rank-one module admits an additive
splitting compatible with a supplied exact parametrization of its kernel. -/

namespace ManuscriptAudit.AdicLineQuotientSplitting

noncomputable section

universe u v w z

variable {R : Type u} [Ring R] {A : Type v} [AddCommGroup A]
variable {B : Type w} [AddCommGroup B] [Module R B]
variable {C : Type z} [AddCommGroup C] [Module R C]

/-- Split an actual exact linear projection with free rank-one target, using only an
additive identification of its kernel. -/
def splitEquiv (k : A →+ B) (q : B →ₗ[R] C) (e : R ≃ₗ[R] C)
    (hk : Function.Injective k) (hq : Function.Surjective q) (hExact : Function.Exact k q) :
    A × C ≃+ B := by
  let x := Classical.choose (hq (e 1))
  have hx : q x = e 1 := Classical.choose_spec (hq (e 1))
  let s₀ : R →ₗ[R] B :=
    { toFun := fun r ↦ r • x
      map_add' := fun a b ↦ add_smul a b x
      map_smul' := fun a b ↦ mul_smul a b x }
  let s := s₀.comp e.symm.toLinearMap
  have hs (c : C) : q (s c) = c := by
    change q (e.symm c • x) = c
    rw [map_smul, hx, ← e.map_smul]
    simp
  have hz (a : A) : q (k a) = 0 := (hExact (k a)).mpr ⟨a, rfl⟩
  let f : A × C →+ B :=
    { toFun := fun v ↦ k v.1 + s v.2
      map_zero' := by simp
      map_add' := by
        intro a b
        change k (a.1 + b.1) + s (a.2 + b.2) = (k a.1 + s a.2) + (k b.1 + s b.2)
        rw [map_add, map_add]
        abel }
  have hf (v : A × C) : q (f v) = v.2 := by
    change q (k v.1 + s v.2) = v.2
    rw [map_add, hz, hs, zero_add]
  refine AddEquiv.ofBijective f ⟨?_, ?_⟩
  · intro a b h
    have h₂ := (hf a).symm.trans ((congrArg q h).trans (hf b))
    have h₁ : k a.1 + s a.2 = k b.1 + s b.2 := h
    rw [h₂] at h₁
    exact Prod.ext (hk (add_right_cancel h₁)) h₂
  · intro b
    have h : q (b - s (q b)) = 0 := by rw [map_sub, hs, sub_self]
    obtain ⟨a, ha⟩ := (hExact _).mp h
    refine ⟨(a, q b), ?_⟩
    change k a + s (q b) = b
    rw [ha, sub_add_cancel]

end
end ManuscriptAudit.AdicLineQuotientSplitting

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AdicLineQuotientSplitting.splitEquiv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
