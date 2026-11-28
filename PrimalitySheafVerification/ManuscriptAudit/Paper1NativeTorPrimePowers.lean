import Lean.Util.CollectAxioms
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Preadditive.Biproducts
import PrimalitySheafVerification.ManuscriptAudit.IntCyclicDerivedTorGcd
import PrimalitySheafVerification.ManuscriptAudit.Paper1GcdPrimePowers

/-! The manuscript's primewise decomposition holds for the actual
degree-one derived tensor of integer residues. -/

namespace ManuscriptAudit.Paper1NativeTorPrimePowers

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Paper1GcdPrimePowers

noncomputable section

private abbrev C := ModuleCat.{0} ℤ
local instance : HasFiniteBiproducts C := HasFiniteBiproducts.of_hasFiniteProducts

abbrev factor (m n : ℕ) (p : n.primeFactors) : C :=
  ModuleCat.of ℤ (ZMod (localModulus m n p))

/-- Literal native Tor has the finite direct sum over prime divisors with
the minimum of the two exponents in each factor. -/
def torOneIsoPrimePowers (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ((Tor C 1).obj (ModuleCat.of ℤ (ZMod m))).obj (ModuleCat.of ℤ (ZMod n)) ≅
      ⨁ factor m n := by
  let e := (residueEquivPrimePowers m n hm.ne' hn.ne').toAddEquiv
  let el : ZMod (Nat.gcd m n) ≃ₗ[ℤ] (∀ p : n.primeFactors, ZMod (localModulus m n p)) :=
    e.toIntLinearEquiv
  exact IntCyclicDerivedTorGcd.torOneIsoGcdResidues m n hm hn ≪≫
    el.toModuleIso ≪≫ (ModuleCat.piIsoPi (factor m n)).symm ≪≫
    (biproduct.isoProduct (factor m n)).symm

/-- At a single prime the residue exponent is the literal local thickness. -/
def torOneIsoPrimePower (m p k : ℕ) (hm : 0 < m) (hp : p.Prime) :
    ((Tor C 1).obj (ModuleCat.of ℤ (ZMod m))).obj (ModuleCat.of ℤ (ZMod (p ^ k))) ≅
      ModuleCat.of ℤ (ZMod (p ^ min (padicValNat p m) k)) := by
  let e := (ZMod.ringEquivCongr (gcd_prime_power_valuation m hm.ne' hp k)).toAddEquiv
  let el : ZMod (Nat.gcd m (p ^ k)) ≃ₗ[ℤ] ZMod (p ^ min (padicValNat p m) k) :=
    e.toIntLinearEquiv
  exact IntCyclicDerivedTorGcd.torOneIsoGcdResidues m (p ^ k) hm (pow_pos hp.pos k) ≪≫
    el.toModuleIso

end
end ManuscriptAudit.Paper1NativeTorPrimePowers

open Lean Elab Command in
run_cmd do
  let names := [``ManuscriptAudit.Paper1NativeTorPrimePowers.torOneIsoPrimePowers,
    ``ManuscriptAudit.Paper1NativeTorPrimePowers.torOneIsoPrimePower]
  for name in names do
    let ax ← collectAxioms name
    let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
