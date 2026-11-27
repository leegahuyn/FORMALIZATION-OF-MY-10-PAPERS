import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Ring

/-! Executable coefficient lists with proved interpretation in Mathlib polynomials. -/

namespace ManuscriptAudit.CubicCoefficientArithmetic

open Polynomial

variable {k : Type*} [CommRing k]

noncomputable def expand : List k → k[X]
  | [] => 0
  | a :: ls => C a + X * expand ls

def add : List k → List k → List k
  | [], b => b
  | a, [] => a
  | a :: as, b :: bs => (a + b) :: add as bs

def neg (a : List k) : List k := a.map Neg.neg

def sub (a b : List k) : List k := add a (neg b)

def scale (a : k) (b : List k) : List k := b.map (a * ·)

def mul : List k → List k → List k
  | [], _ => []
  | a :: as, b => add (scale a b) (0 :: mul as b)

def pow (a : List k) : ℕ → List k
  | 0 => [1]
  | n + 1 => mul (pow a n) a

def AllZero : List k → Prop
  | [] => True
  | x :: xs => x = 0 ∧ AllZero xs

instance allZeroDecidable [DecidableEq k] : (ls : List k) → Decidable (AllZero ls)
  | [] => isTrue trivial
  | x :: xs =>
    letI := allZeroDecidable xs
    inferInstanceAs (Decidable (x = 0 ∧ AllZero xs))

@[simp] theorem expand_add (a b : List k) : expand (add a b) = expand a + expand b := by
  induction a generalizing b with
  | nil => simp [add, expand]
  | cons a as ih =>
    cases b with
    | nil => simp [add, expand]
    | cons b bs =>
      simp only [add, expand, map_add, ih]
      ring

@[simp] theorem expand_neg (a : List k) : expand (neg a) = -expand a := by
  induction a with
  | nil => simp [neg, expand]
  | cons a as ih =>
    change C (-a) + X * expand (neg as) = -(C a + X * expand as)
    rw [map_neg, ih]
    ring

@[simp] theorem expand_sub (a b : List k) : expand (sub a b) = expand a - expand b := by
  simp [sub, sub_eq_add_neg]

@[simp] theorem expand_scale (a : k) (b : List k) : expand (scale a b) = C a * expand b := by
  induction b with
  | nil => simp [scale, expand]
  | cons b bs ih =>
    change C (a * b) + X * expand (scale a bs) = C a * (C b + X * expand bs)
    rw [map_mul, ih]
    ring

@[simp] theorem expand_mul (a b : List k) : expand (mul a b) = expand a * expand b := by
  induction a with
  | nil => simp [mul, expand]
  | cons a as ih =>
    simp only [mul, expand_add, expand_scale, expand, map_zero, zero_add, ih]
    ring

@[simp] theorem expand_pow (a : List k) (n : ℕ) : expand (pow a n) = expand a ^ n := by
  induction n with
  | zero => simp [pow, expand]
  | succ n ih => rw [pow, expand_mul, ih, pow_succ]

theorem expand_zero_of_allZero {a : List k} (h : AllZero a) : expand a = 0 := by
  induction a with
  | nil => rfl
  | cons v vs ih =>
    change v = 0 ∧ AllZero vs at h
    simp only [expand, h.1, map_zero, ih h.2, mul_zero, zero_add]

theorem expand_eq_zero_iff [IsDomain k] (a : List k) : expand a = 0 ↔ AllZero a := by
  refine ⟨?_, expand_zero_of_allZero⟩
  induction a with
  | nil => intro _; trivial
  | cons v vs ih =>
    intro h
    have hv : v = 0 := by
      have he := congrArg (fun f : k[X] => f.coeff 0) h
      simpa only [expand, coeff_add, coeff_C_zero, coeff_X_mul_zero, add_zero, coeff_zero] using he
    have hm : X * expand vs = 0 := by
      simpa only [expand, hv, map_zero, zero_add] using h
    exact ⟨hv, ih ((mul_eq_zero.mp hm).resolve_left X_ne_zero)⟩

theorem expand_ne_zero [IsDomain k] {a : List k} (h : ¬AllZero a) : expand a ≠ 0 :=
  fun ha => h ((expand_eq_zero_iff a).mp ha)

theorem expand_eq_of_check {a b : List k} (h : AllZero (sub a b)) : expand a = expand b :=
  sub_eq_zero.mp (by simpa only [expand_sub] using expand_zero_of_allZero h)

end ManuscriptAudit.CubicCoefficientArithmetic

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicCoefficientArithmetic.expand_add,
      ``ManuscriptAudit.CubicCoefficientArithmetic.expand_mul,
      ``ManuscriptAudit.CubicCoefficientArithmetic.expand_pow,
      ``ManuscriptAudit.CubicCoefficientArithmetic.expand_eq_zero_iff,
      ``ManuscriptAudit.CubicCoefficientArithmetic.expand_eq_of_check] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
