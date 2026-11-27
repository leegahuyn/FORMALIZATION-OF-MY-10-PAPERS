import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.PowerTorsionTower

/-! Cardinality of the kernel of a composition with a surjective second map. -/

namespace ManuscriptAudit.AdditiveKernelComposition

variable {G H K : Type*} [AddCommGroup G] [AddCommGroup H] [AddCommGroup K]

def restriction (f : H →+ K) (g : G →+ H) : (f.comp g).ker →+ f.ker where
  toFun x := ⟨g x, x.property⟩
  map_zero' := by apply Subtype.ext; exact map_zero g
  map_add' x y := by apply Subtype.ext; exact map_add g x.val y.val

theorem restriction_surjective (f : H →+ K) (g : G →+ H) (hg : Function.Surjective g) :
    Function.Surjective (restriction f g) := by
  intro y
  obtain ⟨x, hx⟩ := hg y
  have h : x ∈ (f.comp g).ker := by
    change f (g x) = 0
    exact (congrArg f hx).trans y.property
  exact ⟨⟨x, h⟩, Subtype.ext hx⟩

def restrictionKernelEquiv (f : H →+ K) (g : G →+ H) : (restriction f g).ker ≃ g.ker where
  toFun x := ⟨x.val.val, congrArg Subtype.val x.property⟩
  invFun x := by
    have h : x.val ∈ (f.comp g).ker := by
      change f (g x.val) = 0
      rw [show g x.val = 0 from x.property, map_zero]
    exact ⟨⟨x.val, h⟩, Subtype.ext x.property⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

theorem card_ker_comp (f : H →+ K) (g : G →+ H) (hg : Function.Surjective g) :
    Nat.card ↥((f.comp g).ker) = Nat.card ↥f.ker * Nat.card ↥g.ker := by
  let r := restriction f g
  have hr : Function.Surjective r := restriction_surjective f g hg
  let e : r.range ≃ f.ker :=
    Equiv.ofBijective Subtype.val ⟨Subtype.val_injective, fun b => by
      obtain ⟨a, ha⟩ := hr b
      exact ⟨⟨b, a, ha⟩, rfl⟩⟩
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup r.ker,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange r).toEquiv,
    Nat.card_congr e, Nat.card_congr (restrictionKernelEquiv f g)]

section Fixed

theorem card_fixed_of_conjugacy (e : G ≃+ H) (f : AddMonoid.End G) (g : AddMonoid.End H)
    (he : ∀ x, g (e x) = e (f x)) :
    Nat.card ↥((1 - g).ker) = Nat.card ↥((1 - f).ker) := by
  let K₁ := (1 - f).ker
  let K₂ := (1 - g).ker
  have h₁ (x : G) : x ∈ K₁ ↔ f x = x := by
    change x - f x = 0 ↔ f x = x
    rw [sub_eq_zero, eq_comm]
  have h₂ (x : H) : x ∈ K₂ ↔ g x = x := by
    change x - g x = 0 ↔ g x = x
    rw [sub_eq_zero, eq_comm]
  let i (x : K₁) : K₂ :=
    ⟨e x.val, (h₂ _).mpr (by rw [he, (h₁ _).mp x.property])⟩
  have hi : Function.Injective i := by
    intro x y h
    exact Subtype.ext (e.injective (congrArg Subtype.val h))
  have hs : Function.Surjective i := by
    intro y
    let x := e.symm y.val
    have hxy : e x = y.val := e.apply_symm_apply _
    have hx : f x = x := by
      apply e.injective
      rw [← he, hxy, (h₂ _).mp y.property]
    exact ⟨⟨x, (h₁ _).mpr hx⟩, Subtype.ext hxy⟩
  exact Nat.card_congr (Equiv.ofBijective i ⟨hi, hs⟩).symm

end Fixed

end ManuscriptAudit.AdditiveKernelComposition

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.AdditiveKernelComposition.card_ker_comp,
      ``ManuscriptAudit.AdditiveKernelComposition.card_fixed_of_conjugacy] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
