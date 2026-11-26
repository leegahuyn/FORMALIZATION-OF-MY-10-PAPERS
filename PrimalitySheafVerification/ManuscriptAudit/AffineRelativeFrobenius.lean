import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Relative Frobenius for an algebra in prime characteristic

The relative Frobenius is defined on the actual tensor product obtained by
base change along Frobenius. Taking the pth power in that tensor product
recovers the composite of relative Frobenius with the left inclusion.
-/

namespace ManuscriptAudit.AffineRelativeFrobenius

open scoped TensorProduct

noncomputable section

/-- A copy of a ring on which scalar multiplication is twisted by Frobenius. -/
def FrobeniusTwist (_p : ℕ) (R : Type*) := R

instance {p : ℕ} {R : Type*} [CommRing R] : CommRing (FrobeniusTwist p R) :=
  ‹CommRing R›

instance {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {p : ℕ} [ExpChar A p] : Algebra A (FrobeniusTwist p B) :=
  ((show A →+* FrobeniusTwist p B from algebraMap A B).comp (frobenius A p)).toAlgebra

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
variable (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p]

private def frobeniusToTwist : B →ₐ[A] FrobeniusTwist p B where
  __ := (show B →+* FrobeniusTwist p B from frobenius B p)
  commutes' a := by
    change frobenius B p (algebraMap A B a) = algebraMap A B (frobenius A p a)
    exact ((algebraMap A B).map_frobenius p a).symm

private def twistOfAlgebraMap : FrobeniusTwist p A →ₐ[A] FrobeniusTwist p B where
  __ := (show FrobeniusTwist p A →+* FrobeniusTwist p B from algebraMap A B)
  commutes' a := by
    change algebraMap A B (algebraMap A A (frobenius A p a)) =
      algebraMap A B (frobenius A p a)
    rw [Algebra.algebraMap_self_apply]

/-- Relative Frobenius, sending a pure tensor b⊗a to bᵖ · algebraMap(a). -/
def relativeFrobenius : (B ⊗[A] FrobeniusTwist p A) →+* B :=
  (Algebra.TensorProduct.lift (frobeniusToTwist A B p) (twistOfAlgebraMap A B p)
    (fun _ _ => Commute.all _ _)).toRingHom

theorem relativeFrobenius_tmul (b : B) (a : FrobeniusTwist p A) :
    relativeFrobenius A B p (b ⊗ₜ[A] a) = b ^ p * algebraMap A B (show A from a) :=
  rfl

/-- The left inclusion into the Frobenius base change. -/
def leftInclusion : B →+* (B ⊗[A] FrobeniusTwist p A) :=
  Algebra.TensorProduct.includeLeftRingHom

theorem relativeFrobenius_comp_leftInclusion :
    (relativeFrobenius A B p).comp (leftInclusion A B p) = frobenius B p := by
  apply RingHom.ext
  intro b
  change relativeFrobenius A B p (b ⊗ₜ[A] (1 : FrobeniusTwist p A)) = b ^ p
  rw [relativeFrobenius_tmul]
  change b ^ p * algebraMap A B (1 : A) = b ^ p
  rw [map_one, mul_one]

/-- Taking a pth power on the Frobenius base change factors through the
relative Frobenius and the left inclusion. -/
theorem pow_eq_leftInclusion_relativeFrobenius (z : B ⊗[A] FrobeniusTwist p A) :
    z ^ p = leftInclusion A B p (relativeFrobenius A B p z) := by
  have hp : p.Prime := Fact.out
  rcases subsingleton_or_nontrivial (B ⊗[A] FrobeniusTwist p A) with h | h
  · exact h.elim _ _
  · letI : Nontrivial (B ⊗[A] FrobeniusTwist p A) := h
    have hpzero : (p : B ⊗[A] FrobeniusTwist p A) = 0 := by
      rw [← map_natCast (algebraMap A (B ⊗[A] FrobeniusTwist p A)),
        CharP.cast_eq_zero A p, map_zero]
    letI : CharP (B ⊗[A] FrobeniusTwist p A) p :=
      (CharP.charP_iff_prime_eq_zero hp).mpr hpzero
    induction z using TensorProduct.induction_on with
    | zero =>
      simp [zero_pow hp.pos.ne']
    | tmul b a =>
      change (b ⊗ₜ[A] a) ^ p =
        relativeFrobenius A B p (b ⊗ₜ[A] a) ⊗ₜ[A] (1 : FrobeniusTwist p A)
      have htwist : (show A from a) • (1 : FrobeniusTwist p A) = a ^ p := by
        change algebraMap A A (frobenius A p (show A from a)) * 1 = (show A from a) ^ p
        simpa only [Algebra.algebraMap_self_apply, mul_one] using
          (frobenius_def p (show A from a))
      rw [Algebra.TensorProduct.tmul_pow, relativeFrobenius_tmul, ← htwist,
        ← TensorProduct.smul_tmul, Algebra.smul_def]
      exact congrArg (fun b' : B => b' ⊗ₜ[A] (1 : FrobeniusTwist p A)) (mul_comm _ _)
    | add x y hx hy =>
      rw [add_pow_char, hx, hy, map_add, map_add]

theorem relativeFrobenius_kernel_pow_eq_zero {z : B ⊗[A] FrobeniusTwist p A}
    (hz : z ∈ RingHom.ker (relativeFrobenius A B p)) : z ^ p = 0 := by
  change relativeFrobenius A B p z = 0 at hz
  rw [pow_eq_leftInclusion_relativeFrobenius A B p z, hz, map_zero]

end

end ManuscriptAudit.AffineRelativeFrobenius

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineRelativeFrobenius.relativeFrobenius_tmul,
      ``ManuscriptAudit.AffineRelativeFrobenius.relativeFrobenius_comp_leftInclusion,
      ``ManuscriptAudit.AffineRelativeFrobenius.pow_eq_leftInclusion_relativeFrobenius,
      ``ManuscriptAudit.AffineRelativeFrobenius.relativeFrobenius_kernel_pow_eq_zero] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
