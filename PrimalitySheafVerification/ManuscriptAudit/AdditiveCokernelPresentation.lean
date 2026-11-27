import Lean.Util.CollectAxioms
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! A square with surjective vertical maps identifies the induced cokernel with a quotient of the original target. -/

namespace ManuscriptAudit.AdditiveCokernelPresentation

noncomputable section

variable {A B P Q : Type*} [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup P] [AddCommGroup Q]

/-- For a commutative square with both vertical maps onto, the lower cokernel
is the original target modulo the upper image and the right kernel. -/
def cokernelEquiv (i : A →+ B) (u : A →+ P) (v : B →+ Q) (r : P →+ Q)
    (hu : Function.Surjective u) (hv : Function.Surjective v) (h : v.comp i = r.comp u) :
    (Q ⧸ r.range) ≃+ (B ⧸ (i.range ⊔ v.ker)) := by
  let t := (QuotientAddGroup.mk' r.range).comp v
  have ht : t.ker = i.range ⊔ v.ker := by
    ext b
    change (v b : Q ⧸ r.range) = 0 ↔ b ∈ i.range ⊔ v.ker
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_sup]
    constructor
    · rintro ⟨p, hp⟩
      obtain ⟨a, rfl⟩ := hu p
      have ha : v (i a) = r (u a) := DFunLike.congr_fun h a
      have hb : b - i a ∈ v.ker := by
        change v (b - i a) = 0
        rw [map_sub, ha, hp, sub_self]
      exact ⟨i a, ⟨a, rfl⟩, b - i a, hb, by rw [add_comm, sub_add_cancel]⟩
    · rintro ⟨_, ⟨a, rfl⟩, z, hz, rfl⟩
      refine ⟨u a, ?_⟩
      have ha : v (i a) = r (u a) := DFunLike.congr_fun h a
      change v z = 0 at hz
      rw [map_add, ha, hz, add_zero]
  let e := QuotientAddGroup.quotientKerEquivOfSurjective t
    ((QuotientAddGroup.mk'_surjective r.range).comp hv)
  rw [← ht]
  exact e.symm

end
end ManuscriptAudit.AdditiveCokernelPresentation

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AdditiveCokernelPresentation.cokernelEquiv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
