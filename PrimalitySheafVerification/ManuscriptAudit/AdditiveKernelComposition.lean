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

end ManuscriptAudit.AdditiveKernelComposition

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AdditiveKernelComposition.card_ker_comp
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
