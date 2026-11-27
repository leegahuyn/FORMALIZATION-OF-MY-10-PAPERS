import Lean.Util.CollectAxioms
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Polynomial fractions as exact certificates that can be evaluated over a field extension. -/

namespace ManuscriptAudit.CubicFractionCertificates

open Polynomial

noncomputable section

structure Fraction (k : Type*) [CommRing k] where
  num : k[X]
  den : k[X]

namespace Fraction

variable {k : Type*} [CommRing k]

def polynomial (f : k[X]) : Fraction k := ⟨f, 1⟩

def scalar (a : k) : Fraction k := polynomial (C a)

def variableX : Fraction k := polynomial X

instance : Add (Fraction k) where
  add f g := ⟨f.num * g.den + g.num * f.den, f.den * g.den⟩

instance : Sub (Fraction k) where
  sub f g := ⟨f.num * g.den - g.num * f.den, f.den * g.den⟩

instance : Mul (Fraction k) where
  mul f g := ⟨f.num * g.num, f.den * g.den⟩

instance : Div (Fraction k) where
  div f g := ⟨f.num * g.den, f.den * g.num⟩

instance : Neg (Fraction k) where
  neg f := ⟨-f.num, f.den⟩

instance : Pow (Fraction k) ℕ where
  pow f n := ⟨f.num ^ n, f.den ^ n⟩

/-- Cross multiplication is a certificate for equality wherever both fractions are defined. -/
def CrossEq (f g : Fraction k) : Prop := f.num * g.den = g.num * f.den

instance [DecidableEq k] (f g : Fraction k) : Decidable (CrossEq f g) :=
  inferInstanceAs (Decidable (f.num * g.den = g.num * f.den))

variable {L : Type*} [Field L] [Algebra k L]

def evaluate (f : Fraction k) (x : L) : L :=
  f.num.eval₂ (algebraMap k L) x / f.den.eval₂ (algebraMap k L) x

def ValidAt (f : Fraction k) (x : L) : Prop := f.den.eval₂ (algebraMap k L) x ≠ 0

theorem value_eq {f g : Fraction k} {x : L} (hf : f.ValidAt x) (hg : g.ValidAt x)
    (h : f.CrossEq g) : f.evaluate x = g.evaluate x := by
  exact (div_eq_div_iff hf hg).mpr (by
    simpa only [eval₂_mul] using congrArg (fun P : k[X] => P.eval₂ (algebraMap k L) x) h)

@[simp] theorem evaluate_polynomial (f : k[X]) (x : L) :
    (polynomial f).evaluate x = f.eval₂ (algebraMap k L) x := by
  simp [polynomial, evaluate]

@[simp] theorem evaluate_scalar (a : k) (x : L) : (scalar a).evaluate x = algebraMap k L a := by
  simp [scalar]

@[simp] theorem evaluate_variableX (x : L) : (variableX (k := k)).evaluate x = x := by
  simp [variableX]

@[simp] theorem valid_polynomial (f : k[X]) (x : L) : (polynomial f).ValidAt x := by
  simp [ValidAt, polynomial]

theorem valid_add {f g : Fraction k} {x : L} (hf : f.ValidAt x) (hg : g.ValidAt x) :
    (f + g).ValidAt x := by
  unfold ValidAt at *
  change ((f.den * g.den : k[X]).eval₂ (algebraMap k L) x) ≠ 0
  rw [eval₂_mul]
  exact mul_ne_zero hf hg

theorem valid_sub {f g : Fraction k} {x : L} (hf : f.ValidAt x) (hg : g.ValidAt x) :
    (f - g).ValidAt x := by
  change (f + g).ValidAt x
  exact valid_add hf hg

theorem valid_mul {f g : Fraction k} {x : L} (hf : f.ValidAt x) (hg : g.ValidAt x) :
    (f * g).ValidAt x := by
  change (f + g).ValidAt x
  exact valid_add hf hg

theorem valid_div {f g : Fraction k} {x : L} (hf : f.ValidAt x) (hg : g.evaluate x ≠ 0) :
    (f / g).ValidAt x := by
  unfold ValidAt at hf ⊢
  change (f.den * g.num : k[X]).eval₂ (algebraMap k L) x ≠ 0
  rw [eval₂_mul]
  exact mul_ne_zero hf (fun h => hg (by simp only [evaluate, h, zero_div]))

theorem valid_pow {f : Fraction k} {x : L} (hf : f.ValidAt x) (n : ℕ) :
    (f ^ n).ValidAt x := by
  unfold ValidAt at hf ⊢
  change (f.den ^ n).eval₂ (algebraMap k L) x ≠ 0
  rw [eval₂_pow]
  exact pow_ne_zero _ hf

theorem evaluate_add {f g : Fraction k} {x : L} (hf : f.ValidAt x) (hg : g.ValidAt x) :
    (f + g).evaluate x = f.evaluate x + g.evaluate x := by
  unfold ValidAt at hf hg
  unfold evaluate
  change (f.num * g.den + g.num * f.den).eval₂ (algebraMap k L) x /
      (f.den * g.den).eval₂ (algebraMap k L) x = _
  rw [eval₂_add, eval₂_mul, eval₂_mul, eval₂_mul]
  field_simp [hf, hg] <;> ring

theorem evaluate_sub {f g : Fraction k} {x : L} (hf : f.ValidAt x) (hg : g.ValidAt x) :
    (f - g).evaluate x = f.evaluate x - g.evaluate x := by
  unfold ValidAt at hf hg
  unfold evaluate
  change (f.num * g.den - g.num * f.den).eval₂ (algebraMap k L) x /
      (f.den * g.den).eval₂ (algebraMap k L) x = _
  rw [eval₂_sub, eval₂_mul, eval₂_mul, eval₂_mul]
  field_simp [hf, hg] <;> ring

theorem evaluate_mul (f g : Fraction k) (x : L) :
    (f * g).evaluate x = f.evaluate x * g.evaluate x := by
  unfold evaluate
  change (f.num * g.num).eval₂ (algebraMap k L) x /
      (f.den * g.den).eval₂ (algebraMap k L) x = _
  simp only [eval₂_mul, div_eq_mul_inv, mul_inv_rev]
  ring

theorem evaluate_div (f g : Fraction k) (x : L) :
    (f / g).evaluate x = f.evaluate x / g.evaluate x := by
  unfold evaluate
  change (f.num * g.den).eval₂ (algebraMap k L) x /
      (f.den * g.num).eval₂ (algebraMap k L) x = _
  simp only [eval₂_mul, div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

theorem evaluate_neg (f : Fraction k) (x : L) : (-f).evaluate x = -(f.evaluate x) := by
  unfold evaluate
  change (-f.num : k[X]).eval₂ (algebraMap k L) x / f.den.eval₂ (algebraMap k L) x = _
  rw [eval₂_neg, neg_div]

theorem evaluate_pow (f : Fraction k) (x : L) (n : ℕ) : (f ^ n).evaluate x = f.evaluate x ^ n := by
  unfold evaluate
  change (f.num ^ n).eval₂ (algebraMap k L) x / (f.den ^ n).eval₂ (algebraMap k L) x = _
  rw [eval₂_pow, eval₂_pow, div_pow]

end Fraction
end
end ManuscriptAudit.CubicFractionCertificates

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicFractionCertificates.Fraction.value_eq,
      ``ManuscriptAudit.CubicFractionCertificates.Fraction.evaluate_add,
      ``ManuscriptAudit.CubicFractionCertificates.Fraction.evaluate_sub,
      ``ManuscriptAudit.CubicFractionCertificates.Fraction.evaluate_mul,
      ``ManuscriptAudit.CubicFractionCertificates.Fraction.evaluate_div,
      ``ManuscriptAudit.CubicFractionCertificates.Fraction.evaluate_pow] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
