import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.AlgebraTower
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! Finite-free algebras obtained by adjoining two specified monomial roots. -/

namespace ManuscriptAudit.RadicalCoordinateAlgebra

open Polynomial Module

noncomputable section

variable {R : Type*} [CommRing R]

def relation (m : ℕ) (a : R) : R[X] := X ^ m - C a

abbrev Extension (m : ℕ) (a : R) := AdjoinRoot (relation m a)

def root (m : ℕ) (a : R) : Extension m a := AdjoinRoot.root (relation m a)

theorem root_pow (m : ℕ) (a : R) : root m a ^ m = algebraMap R (Extension m a) a := by
  have h := AdjoinRoot.eval₂_root (relation m a)
  apply sub_eq_zero.mp
  simpa only [relation, root, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, AdjoinRoot.algebraMap_eq]
    using h

variable {S : Type*} [CommRing S] [Algebra R S]

def lift (m : ℕ) (a : R) (s : S) (h : s ^ m = algebraMap R S a) : Extension m a →ₐ[R] S :=
  AdjoinRoot.liftAlgHom (relation m a) (Algebra.ofId R S) s (by
    simp only [relation, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, Algebra.ofId_apply, h, sub_self])

@[simp] theorem lift_root (m : ℕ) (a : R) (s : S) (h : s ^ m = algebraMap R S a) :
    lift m a s h (root m a) = s := by
  unfold lift root
  exact AdjoinRoot.lift_root _

variable [Nontrivial R]

def basis (m : ℕ) (a : R) (hm : m ≠ 0) : Module.Basis (Fin m) R (Extension m a) :=
  ((AdjoinRoot.powerBasis' (monic_X_pow_sub_C a hm)).basis).reindex
    (finCongr (natDegree_X_pow_sub_C (n := m) (r := a)))

theorem basis_apply (m : ℕ) (a : R) (hm : m ≠ 0) (i : Fin m) :
    basis m a hm i = root m a ^ (i : ℕ) := by
  unfold basis
  rw [Module.Basis.reindex_apply, PowerBasis.basis_eq_pow] <;> rfl

theorem algebraMap_injective (m : ℕ) (a : R) (hm : m ≠ 0) :
    Function.Injective (algebraMap R (Extension m a)) := by
  let B := basis m a hm
  let i : Fin m := ⟨0, Nat.pos_of_ne_zero hm⟩
  have hB : B i = 1 := (basis_apply m a hm i).trans (pow_zero _)
  have hc (x : R) : algebraMap R (Extension m a) x = x • B i := by
    rw [hB, Algebra.smul_def, mul_one]
  intro x y he
  have hRepr := congrArg (fun t : Extension m a => B.repr t i) he
  rw [hc, hc] at hRepr
  simpa only [map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
    smul_eq_mul, mul_one] using hRepr

abbrev DoubleExtension (m n : ℕ) (a b : R) :=
  Extension n (algebraMap R (Extension m a) b)

def firstRoot (m n : ℕ) (a b : R) : DoubleExtension m n a b :=
  algebraMap (Extension m a) (DoubleExtension m n a b) (root m a)

def secondRoot (m n : ℕ) (a b : R) : DoubleExtension m n a b :=
  root n (algebraMap R (Extension m a) b)

theorem firstRoot_pow (m n : ℕ) (a b : R) :
    firstRoot m n a b ^ m = algebraMap R (DoubleExtension m n a b) a := by
  unfold firstRoot
  rw [← map_pow, root_pow, ← IsScalarTower.algebraMap_apply]

theorem secondRoot_pow (m n : ℕ) (a b : R) :
    secondRoot m n a b ^ n = algebraMap R (DoubleExtension m n a b) b := by
  unfold secondRoot
  rw [root_pow, ← IsScalarTower.algebraMap_apply]

theorem double_faithfullyFlat (m n : ℕ) (a b : R) (hm : m ≠ 0) (hn : n ≠ 0) :
    Module.FaithfullyFlat R (DoubleExtension m n a b) := by
  let C := Extension m a
  let D := DoubleExtension m n a b
  letI : Nontrivial C := Nontrivial.of_injective _ (algebraMap_injective m a hm)
  letI : Nontrivial D := Nontrivial.of_injective _
    (algebraMap_injective n (algebraMap R C b) hn)
  letI : Module.Free R D := Module.Free.of_basis
    ((basis m a hm).smulTower (basis n (algebraMap R C b) hn))
  infer_instance

end
end ManuscriptAudit.RadicalCoordinateAlgebra

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.RadicalCoordinateAlgebra.root_pow,
      ``ManuscriptAudit.RadicalCoordinateAlgebra.lift_root,
      ``ManuscriptAudit.RadicalCoordinateAlgebra.basis_apply,
      ``ManuscriptAudit.RadicalCoordinateAlgebra.algebraMap_injective,
      ``ManuscriptAudit.RadicalCoordinateAlgebra.firstRoot_pow,
      ``ManuscriptAudit.RadicalCoordinateAlgebra.secondRoot_pow,
      ``ManuscriptAudit.RadicalCoordinateAlgebra.double_faithfullyFlat] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
