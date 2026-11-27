import Lean.Util.CollectAxioms
import Mathlib.Algebra.Exact.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Reducing a surjective integer order modulo d gives the quotient by its old kernel and d-th powers. -/

namespace ManuscriptAudit.CyclicOrderQuotient

noncomputable section

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- Multiplication by d as an additive homomorphism. -/
def nsmulMap (d : ℕ) : B →+ B where
  toFun x := d • x
  map_zero' := nsmul_zero d
  map_add' _ _ := nsmul_add _ _ _

/-- The cokernel of the old image and the d-multiples is the native cyclic group. -/
def quotientEquiv (i : A →+ B) (v : B →+ ℤ)
    (hExact : Function.Exact i v) (hSurj : Function.Surjective v) (d : ℕ) :
    (B ⧸ (i.range ⊔ (nsmulMap (B := B) d).range)) ≃+ ZMod d := by
  let m := (Int.castAddHom (ZMod d)).comp v
  have hker : m.ker = i.range ⊔ (nsmulMap (B := B) d).range := by
    ext b
    change (v b : ZMod d) = 0 ↔ b ∈ i.range ⊔ (nsmulMap (B := B) d).range
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, AddSubgroup.mem_sup]
    constructor
    · rintro ⟨n, hn⟩
      obtain ⟨z, hz⟩ := hSurj n
      have h : v (b - d • z) = 0 := by
        rw [map_sub, map_nsmul, hz, nsmul_eq_mul, hn, sub_self]
      exact ⟨b - d • z, (hExact _).mp h, d • z, ⟨z, rfl⟩, sub_add_cancel _ _⟩
    · rintro ⟨y, hy, _, ⟨z, rfl⟩, rfl⟩
      refine ⟨v z, ?_⟩
      change v (y + d • z) = (d : ℤ) * v z
      rw [map_add, (hExact y).mpr hy, zero_add, map_nsmul, nsmul_eq_mul]
  rw [← hker]
  exact QuotientAddGroup.quotientKerEquivOfSurjective m (ZMod.intCast_surjective.comp hSurj)

end
end ManuscriptAudit.CyclicOrderQuotient

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CyclicOrderQuotient.quotientEquiv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
