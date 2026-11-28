import Lean.Util.CollectAxioms
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.ClassGroup.Basic
import Lean.Elab.Tactic.Omega
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassFunctionFieldProductFormula

/-! The geometric Weierstrass divisor classes have an integer degree
which splits the class of the actual rational point at infinity. -/

namespace ManuscriptAudit.WeierstrassDivisorDegree

open FractionalIdeal WithZero WeierstrassCurve.Affine
open WeierstrassFractionalIdealDegree WeierstrassInfinityAdicOrder
open WeierstrassFunctionFieldProductFormula
open scoped nonZeroDivisors

noncomputable section

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
variable (W : WeierstrassCurve.Affine K) [W.IsElliptic]

private abbrev A := W.CoordinateRing
private abbrev F := W.FunctionField
private abbrev FId := FractionalIdeal (A W)⁰ (F W)

/-- Actual divisors represented by a geometric affine fractional ideal and
the multiplicity at the unique rational point at infinity. -/
abbrev Divisors := (FId W)ˣ × Multiplicative ℤ

private theorem valuation_unit_nonzero (f : (F W)ˣ) :
    functionFieldValuation W (f : F W) ≠ 0 :=
  (Units.isUnit f).map (functionFieldValuation W) |>.ne_zero

private def infinityOrder : (F W)ˣ →* Multiplicative ℤ where
  toFun f := Multiplicative.ofAdd (-log (functionFieldValuation W (f : F W)))
  map_one' := by
    apply Multiplicative.toAdd.injective
    change -log (functionFieldValuation W (1 : F W)) = 0
    simp
  map_mul' f g := by
    apply Multiplicative.toAdd.injective
    change -log (functionFieldValuation W (↑f * ↑g)) =
      -log (functionFieldValuation W (f : F W)) + -log (functionFieldValuation W (g : F W))
    rw [map_mul, log_mul (valuation_unit_nonzero W f) (valuation_unit_nonzero W g), neg_add]

/-- The actual principal divisor of a nonzero rational function. -/
def principal : (F W)ˣ →* Divisors W :=
  (toPrincipalIdeal (A W) (F W)).prod (infinityOrder W)

/-- Divisors modulo the principal divisors of actual rational functions. -/
abbrev DivisorClassGroup := Divisors W ⧸ (principal W).range

private theorem degree_one : fractionalDegree W (1 : FId W) = 0 := by
  have h := fractionalDegree_mul W (1 : FId W) 1 one_ne_zero one_ne_zero
  rw [one_mul] at h
  omega

/-- Sum the geometric degrees at the affine points and infinity. -/
def divisorDegree : Divisors W →* Multiplicative ℤ where
  toFun d := Multiplicative.ofAdd (fractionalDegree W d.1.val + d.2.toAdd)
  map_one' := by
    apply Multiplicative.toAdd.injective
    change fractionalDegree W (1 : FId W) + 0 = 0
    rw [degree_one, add_zero]
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    change fractionalDegree W (x.1.val * y.1.val) + (x.2.toAdd + y.2.toAdd) =
      (fractionalDegree W x.1.val + x.2.toAdd) + (fractionalDegree W y.1.val + y.2.toAdd)
    rw [fractionalDegree_mul W _ _ (Units.ne_zero x.1) (Units.ne_zero y.1)]
    ac_rfl

private theorem principal_degree_one (f : (F W)ˣ) :
    divisorDegree W (principal W f) = 1 := by
  apply Multiplicative.toAdd.injective
  change fractionalDegree W ((toPrincipalIdeal (A W) (F W) f : (FId W)ˣ) : FId W) +
    (-log (functionFieldValuation W (f : F W))) = 0
  rw [coe_toPrincipalIdeal]
  exact native_product_formula W (f : F W) (Units.ne_zero f)

/-- Degree descends to the native geometric divisor class group. -/
def classDegree : DivisorClassGroup W →* Multiplicative ℤ :=
  QuotientGroup.lift (principal W).range (divisorDegree W) (by
    intro d hd
    obtain ⟨f, rfl⟩ := MonoidHom.mem_range.mp hd
    exact principal_degree_one W f)

/-- The class of an integer multiple of the actual divisor at infinity. -/
def infinityClass : Multiplicative ℤ →* DivisorClassGroup W :=
  (QuotientGroup.mk' (principal W).range).comp ((1 : Multiplicative ℤ →* (FId W)ˣ).prod
    (MonoidHom.id (Multiplicative ℤ)))

/-- The infinity divisor is primitive in the actual geometric divisor class group. -/
theorem classDegree_infinity (n : Multiplicative ℤ) : classDegree W (infinityClass W n) = n := by
  change (classDegree W) (QuotientGroup.mk (s := (principal W).range) (1, n)) = n
  unfold classDegree
  rw [QuotientGroup.lift_mk]
  apply Multiplicative.toAdd.injective
  change fractionalDegree W (1 : FId W) + n.toAdd = n.toAdd
  rw [degree_one, zero_add]

theorem infinityClass_injective : Function.Injective (infinityClass W) :=
  Function.LeftInverse.injective (classDegree_infinity W)

end

end ManuscriptAudit.WeierstrassDivisorDegree

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassDivisorDegree.classDegree_infinity,
      ``ManuscriptAudit.WeierstrassDivisorDegree.infinityClass_injective] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
