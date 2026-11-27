import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicCoefficientArithmetic
import PrimalitySheafVerification.ManuscriptAudit.CubicFractionCoordinateRules

/-! Executable fraction certificates interpreted as mathematical polynomial fractions. -/

namespace ManuscriptAudit.CubicExecutableFractions

open Polynomial CubicFractionCertificates
open CubicCoefficientArithmetic (expand AllZero)

variable (k : Type*) [CommRing k]

structure CoefficientFraction where
  num : List k
  den : List k

namespace CoefficientFraction

variable {k}

def polynomial (a : List k) : CoefficientFraction k := ⟨a, [1]⟩
def scalar (a : k) : CoefficientFraction k := polynomial [a]
def variableX : CoefficientFraction k := polynomial [0, 1]

instance : Add (CoefficientFraction k) where
  add f g := ⟨CubicCoefficientArithmetic.add (CubicCoefficientArithmetic.mul f.num g.den)
      (CubicCoefficientArithmetic.mul g.num f.den), CubicCoefficientArithmetic.mul f.den g.den⟩

instance : Sub (CoefficientFraction k) where
  sub f g := ⟨CubicCoefficientArithmetic.sub (CubicCoefficientArithmetic.mul f.num g.den)
      (CubicCoefficientArithmetic.mul g.num f.den), CubicCoefficientArithmetic.mul f.den g.den⟩

instance : Mul (CoefficientFraction k) where
  mul f g := ⟨CubicCoefficientArithmetic.mul f.num g.num, CubicCoefficientArithmetic.mul f.den g.den⟩

instance : Div (CoefficientFraction k) where
  div f g := ⟨CubicCoefficientArithmetic.mul f.num g.den, CubicCoefficientArithmetic.mul f.den g.num⟩

instance : Neg (CoefficientFraction k) where
  neg f := ⟨CubicCoefficientArithmetic.neg f.num, f.den⟩

instance : Pow (CoefficientFraction k) ℕ where
  pow f n := ⟨CubicCoefficientArithmetic.pow f.num n, CubicCoefficientArithmetic.pow f.den n⟩

noncomputable def toFraction (f : CoefficientFraction k) : Fraction k :=
  ⟨expand f.num, expand f.den⟩

@[simp] theorem toFraction_polynomial (a : List k) :
    (polynomial a).toFraction = Fraction.polynomial (expand a) := by
  change (⟨expand a, expand [1]⟩ : Fraction k) = ⟨expand a, 1⟩
  simp [CubicCoefficientArithmetic.expand]

@[simp] theorem toFraction_scalar (a : k) : (scalar a).toFraction = Fraction.scalar a := by
  rw [scalar, toFraction_polynomial]
  simp [Fraction.scalar, CubicCoefficientArithmetic.expand]

@[simp] theorem toFraction_variableX : (variableX (k := k)).toFraction = Fraction.variableX := by
  rw [variableX, toFraction_polynomial]
  simp [Fraction.variableX, CubicCoefficientArithmetic.expand]

@[simp] theorem toFraction_add (f g : CoefficientFraction k) :
    (f + g).toFraction = f.toFraction + g.toFraction := by
  change (⟨expand (CubicCoefficientArithmetic.add (CubicCoefficientArithmetic.mul f.num g.den)
      (CubicCoefficientArithmetic.mul g.num f.den)), expand (CubicCoefficientArithmetic.mul f.den g.den)⟩ : Fraction k) =
    ⟨expand f.num * expand g.den + expand g.num * expand f.den, expand f.den * expand g.den⟩
  simp only [CubicCoefficientArithmetic.expand_add, CubicCoefficientArithmetic.expand_mul]

@[simp] theorem toFraction_sub (f g : CoefficientFraction k) :
    (f - g).toFraction = f.toFraction - g.toFraction := by
  change (⟨expand (CubicCoefficientArithmetic.sub (CubicCoefficientArithmetic.mul f.num g.den)
      (CubicCoefficientArithmetic.mul g.num f.den)), expand (CubicCoefficientArithmetic.mul f.den g.den)⟩ : Fraction k) =
    ⟨expand f.num * expand g.den - expand g.num * expand f.den, expand f.den * expand g.den⟩
  simp only [CubicCoefficientArithmetic.expand_sub, CubicCoefficientArithmetic.expand_mul]

@[simp] theorem toFraction_mul (f g : CoefficientFraction k) :
    (f * g).toFraction = f.toFraction * g.toFraction := by
  change (⟨expand (CubicCoefficientArithmetic.mul f.num g.num),
      expand (CubicCoefficientArithmetic.mul f.den g.den)⟩ : Fraction k) =
    ⟨expand f.num * expand g.num, expand f.den * expand g.den⟩
  simp only [CubicCoefficientArithmetic.expand_mul]

@[simp] theorem toFraction_div (f g : CoefficientFraction k) :
    (f / g).toFraction = f.toFraction / g.toFraction := by
  change (⟨expand (CubicCoefficientArithmetic.mul f.num g.den),
      expand (CubicCoefficientArithmetic.mul f.den g.num)⟩ : Fraction k) =
    ⟨expand f.num * expand g.den, expand f.den * expand g.num⟩
  simp only [CubicCoefficientArithmetic.expand_mul]

@[simp] theorem toFraction_neg (f : CoefficientFraction k) :
    (-f).toFraction = -f.toFraction := by
  change (⟨expand (CubicCoefficientArithmetic.neg f.num), expand f.den⟩ : Fraction k) =
    ⟨-expand f.num, expand f.den⟩
  simp only [CubicCoefficientArithmetic.expand_neg]

@[simp] theorem toFraction_pow (f : CoefficientFraction k) (n : ℕ) :
    (f ^ n).toFraction = f.toFraction ^ n := by
  change (⟨expand (CubicCoefficientArithmetic.pow f.num n), expand (CubicCoefficientArithmetic.pow f.den n)⟩ : Fraction k) =
    ⟨expand f.num ^ n, expand f.den ^ n⟩
  simp only [CubicCoefficientArithmetic.expand_pow]

def Check (f g : CoefficientFraction k) : Prop :=
  AllZero (CubicCoefficientArithmetic.sub (CubicCoefficientArithmetic.mul f.num g.den)
    (CubicCoefficientArithmetic.mul g.num f.den))

instance [DecidableEq k] (f g : CoefficientFraction k) : Decidable (Check f g) :=
  inferInstanceAs (Decidable (AllZero _))

theorem check_sound {f g : CoefficientFraction k} (h : Check f g) :
    f.toFraction.CrossEq g.toFraction := by
  change expand f.num * expand g.den = expand g.num * expand f.den
  simpa only [CubicCoefficientArithmetic.expand_mul] using CubicCoefficientArithmetic.expand_eq_of_check h

def secant (u₁ v₁ u₂ v₂ : CoefficientFraction k) : CoefficientFraction k :=
  (v₁ - v₂) / (u₁ - u₂)

def tangent (A : k) (u v : CoefficientFraction k) : CoefficientFraction k :=
  (scalar 3 * variableX * u ^ 2) / (scalar 2 * (variableX + scalar A) * v)

def nextX (A : k) (u₁ u₂ m : CoefficientFraction k) : CoefficientFraction k :=
  (variableX + scalar A) / variableX * m ^ 2 - u₁ - u₂

def nextY (u₁ v₁ u₃ m : CoefficientFraction k) : CoefficientFraction k :=
  m * (u₁ - u₃) - v₁

@[simp] theorem toFraction_secant (u₁ v₁ u₂ v₂ : CoefficientFraction k) :
    (secant u₁ v₁ u₂ v₂).toFraction =
      CubicFractionCoordinateRules.secantFraction u₁.toFraction v₁.toFraction u₂.toFraction v₂.toFraction := by
  simp [secant, CubicFractionCoordinateRules.secantFraction]

@[simp] theorem toFraction_tangent (A : k) (u v : CoefficientFraction k) :
    (tangent A u v).toFraction =
      CubicFractionCoordinateRules.tangentFraction A u.toFraction v.toFraction := by
  simp [tangent, CubicFractionCoordinateRules.tangentFraction]

@[simp] theorem toFraction_nextX (A : k) (u₁ u₂ m : CoefficientFraction k) :
    (nextX A u₁ u₂ m).toFraction =
      CubicFractionCoordinateRules.xFraction A u₁.toFraction u₂.toFraction m.toFraction := by
  simp [nextX, CubicFractionCoordinateRules.xFraction]

@[simp] theorem toFraction_nextY (u₁ v₁ u₃ m : CoefficientFraction k) :
    (nextY u₁ v₁ u₃ m).toFraction =
      CubicFractionCoordinateRules.yFraction u₁.toFraction v₁.toFraction u₃.toFraction m.toFraction := by
  simp [nextY, CubicFractionCoordinateRules.yFraction]

end CoefficientFraction
end ManuscriptAudit.CubicExecutableFractions

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicExecutableFractions.CoefficientFraction.check_sound
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
