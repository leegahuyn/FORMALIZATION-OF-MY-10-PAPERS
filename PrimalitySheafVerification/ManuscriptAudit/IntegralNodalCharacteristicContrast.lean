import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.IntegralNodalCharacteristicTwoCohomology

/-! The degree-one jump between literal geometric fibres of one fixed integral family. -/

namespace ManuscriptAudit.IntegralNodalCharacteristicContrast

open AlgebraicGeometry CategoryTheory
open IntegralNodalGeometricPrimePower (properHc affineHc smoothHc)

noncomputable section

set_option backward.isDefEq.respectTransparency false

local instance primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem trivial_of_equiv {B : Type} [AddCommGroup B] (e : B ≃+ ZMod 1) :
    Subsingleton B :=
  ⟨fun x y ↦ e.injective (Subsingleton.elim _ _)⟩

private theorem nontrivial_of_equiv {B : Type} [AddCommGroup B] {d : ℕ}
    (e : B ≃+ ZMod d) (hd : 1 < d) : Nontrivial B := by
  letI : Fact (1 < d) := ⟨hd⟩
  exact ⟨⟨e.symm 0, e.symm 1, fun h ↦ zero_ne_one (e.symm.injective h)⟩⟩

private theorem one_lt_power (ℓ : ℕ) [Fact ℓ.Prime] {r : ℕ} (hr : 0 < r) :
    1 < ℓ ^ r := by
  cases r with
  | zero => exact (Nat.lt_irrefl 0 hr).elim
  | succ r =>
    rw [pow_succ]
    have hp : ℓ.Prime := Fact.out
    have ha : 1 ≤ ℓ ^ r := pow_pos hp.pos r
    exact hp.one_lt.trans_le ((one_mul ℓ).symm.trans_le (Nat.mul_le_mul_right ℓ ha))

/-- At (2), all three literal geometric compact groups in degree one vanish
for every power of an odd prime. -/
theorem at_two (ℓ : ℕ) [Fact ℓ.Prime] (hℓ₂ : ℓ ≠ 2) (r : ℕ) :
    Subsingleton (properHc 2 (ℓ ^ r) 1) ∧
      Subsingleton (affineHc 2 (ℓ ^ r) 1) ∧ Subsingleton (smoothHc 2 (ℓ ^ r) 1) :=
  ⟨trivial_of_equiv (IntegralNodalCharacteristicTwoCohomology.properPrimePowerEquiv ℓ hℓ₂ r 1),
    trivial_of_equiv (IntegralNodalCharacteristicTwoCohomology.affinePrimePowerEquiv ℓ hℓ₂ r 1),
    trivial_of_equiv (IntegralNodalCharacteristicTwoCohomology.smoothPrimePowerEquiv ℓ hℓ₂ r 1)⟩

/-- At every odd residue prime, the same three degree-one groups are nontrivial
for every nontrivial power order prime to the residue characteristic. -/
theorem at_odd (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hp : 2 < p) (hℓp : ℓ ≠ p)
    (r : ℕ) (hr : 0 < r) :
    Nontrivial (properHc p (ℓ ^ r) 1) ∧
      Nontrivial (affineHc p (ℓ ^ r) 1) ∧ Nontrivial (smoothHc p (ℓ ^ r) 1) := by
  have h := one_lt_power ℓ hr
  exact ⟨nontrivial_of_equiv (IntegralNodalGeometricPrimePower.properEquiv p ℓ hp hℓp r 1) h,
    nontrivial_of_equiv (IntegralNodalGeometricPrimePower.affineEquiv p ℓ hp hℓp r 1) h,
    nontrivial_of_equiv (IntegralNodalGeometricPrimePower.smoothEquiv p ℓ hp hℓp r 1) h⟩

private theorem no_equiv {B D : Type} [AddCommGroup B] [AddCommGroup D]
    (hB : Subsingleton B) (hD : Nontrivial D) : IsEmpty (B ≃+ D) :=
  ⟨fun e ↦ by
    obtain ⟨x, y, hxy⟩ := hD.exists_pair_ne
    exact hxy (e.symm.injective (hB.elim _ _))⟩

/-- Fix the coefficient order and compare the degree-one groups on two actual
fibres of the same integral family. None of the three corresponding groups are isomorphic. -/
theorem degree_one_jump (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hp : 2 < p)
    (hℓ₂ : ℓ ≠ 2) (hℓp : ℓ ≠ p) (r : ℕ) (hr : 0 < r) :
    IsEmpty (properHc 2 (ℓ ^ r) 1 ≃+ properHc p (ℓ ^ r) 1) ∧
      IsEmpty (affineHc 2 (ℓ ^ r) 1 ≃+ affineHc p (ℓ ^ r) 1) ∧
      IsEmpty (smoothHc 2 (ℓ ^ r) 1 ≃+ smoothHc p (ℓ ^ r) 1) := by
  obtain ⟨heP, heA, heS⟩ := at_two ℓ hℓ₂ r
  obtain ⟨hoP, hoA, hoS⟩ := at_odd p ℓ hp hℓp r hr
  exact ⟨no_equiv heP hoP, no_equiv heA hoA, no_equiv heS hoS⟩

end
end ManuscriptAudit.IntegralNodalCharacteristicContrast

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralNodalCharacteristicContrast.at_two,
      ``ManuscriptAudit.IntegralNodalCharacteristicContrast.at_odd,
      ``ManuscriptAudit.IntegralNodalCharacteristicContrast.degree_one_jump] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
