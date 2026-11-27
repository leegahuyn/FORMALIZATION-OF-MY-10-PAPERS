import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.PadicResidueHomeomorphism

/-! Every finite residue sequence of the actual adic integers is exact
on continuous functions from an arbitrary space. -/

namespace ManuscriptAudit.PadicPowerContinuousExact

open Topology

noncomputable section

variable (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ)

local instance residueTopology (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
local instance residueDiscrete (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩

private theorem power_ne_zero : (ℓ : ℤ_[ℓ]) ^ r ≠ 0 :=
  pow_ne_zero r (Nat.cast_ne_zero.mpr (show ℓ.Prime from Fact.out).ne_zero)

theorem mulPower_injective :
    Function.Injective (fun x : ℤ_[ℓ] ↦ (ℓ : ℤ_[ℓ]) ^ r * x) :=
  fun _ _ h ↦ mul_left_cancel₀ (power_ne_zero ℓ r) h

variable {V : Type*} [TopologicalSpace V]

/-- A continuous function with zero residue has a continuous division by the indicated power. -/
theorem exists_division (f : C(V, ℤ_[ℓ]))
    (h : ∀ x, PadicInt.toZModPow r (f x) = 0) :
    ∃ g : C(V, ℤ_[ℓ]), ∀ x, (ℓ : ℤ_[ℓ]) ^ r * g x = f x := by
  have hdiv (x : V) : (ℓ : ℤ_[ℓ]) ^ r ∣ f x := by
    have hx : f x ∈ RingHom.ker (PadicInt.toZModPow r : ℤ_[ℓ] →+* ZMod (ℓ ^ r)) := h x
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hx
    exact hx
  choose g hg using hdiv
  let m : ℤ_[ℓ] → ℤ_[ℓ] := fun x ↦ (ℓ : ℤ_[ℓ]) ^ r * x
  have hm : Continuous m := continuous_const.mul continuous_id
  have he : IsEmbedding m := (hm.isClosedEmbedding (mulPower_injective ℓ r)).isEmbedding
  have hmg : m ∘ g = f := funext (fun x ↦ (hg x).symm)
  have hgContinuous : Continuous g := he.continuous_iff.mpr (by rw [hmg]; exact f.continuous)
  exact ⟨⟨g, hgContinuous⟩, fun x ↦ (hg x).symm⟩

/-- Every continuous function into the discrete finite residue ring admits a continuous lift. -/
theorem exists_residue_lift (f : C(V, ZMod (ℓ ^ r))) :
    ∃ g : C(V, ℤ_[ℓ]), ∀ x, PadicInt.toZModPow r (g x) = f x := by
  letI : NeZero (ℓ ^ r) := ⟨pow_ne_zero r (show ℓ.Prime from Fact.out).ne_zero⟩
  let e : ZMod (ℓ ^ r) → ℤ_[ℓ] := fun x ↦ x.val
  have he : Continuous e := continuous_of_discreteTopology
  refine ⟨⟨e ∘ f, he.comp f.continuous⟩, fun x ↦ ?_⟩
  change PadicInt.toZModPow r ((f x).val : ℤ_[ℓ]) = f x
  rw [map_natCast, ZMod.natCast_zmod_val]

end

end ManuscriptAudit.PadicPowerContinuousExact

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.PadicPowerContinuousExact.mulPower_injective,
      ``ManuscriptAudit.PadicPowerContinuousExact.exists_division,
      ``ManuscriptAudit.PadicPowerContinuousExact.exists_residue_lift] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
