import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The fixed points of native Frobenius on a Weierstrass curve

The coordinatewise p-power map is the actual additive endomorphism on
nonsingular points induced by the prime-field algebra Frobenius.
Its fixed points are exactly the points obtained from the prime field.
This identifies the arithmetic point count with the fixed-point kernel.
-/

namespace ManuscriptAudit.WeierstrassFrobeniusFixed

open Polynomial WeierstrassCurve

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod p) L]

/-- The only roots of X^p-X after any field extension are the prime-field scalars. -/
theorem pow_prime_eq_self_iff (x : L) :
    x ^ p = x ↔ ∃ y : ZMod p, algebraMap (ZMod p) L y = x := by
  constructor
  · intro hx
    let f : (ZMod p)[X] := X ^ p - X
    have hf : f ≠ 0 :=
      FiniteField.X_pow_card_sub_X_ne_zero (ZMod p) (Fact.out : p.Prime).one_lt
    have hRoot : (f.map (algebraMap (ZMod p) L)).IsRoot x := by
      simp [f, Polynomial.IsRoot, hx]
    exact (GaloisField.splits_zmod_X_pow_sub_X p).mem_range_of_isRoot hf hRoot
  · rintro ⟨y, rfl⟩
    rw [← map_pow, ZMod.pow_card]

private theorem algebraFrobenius_apply (x : L) :
    FiniteField.frobeniusAlgHom (ZMod p) L x = x ^ p := by
  change x ^ Fintype.card (ZMod p) = x ^ p
  rw [ZMod.card]

variable [DecidableEq L]

/-- Frobenius on nonsingular points, including the point at infinity. -/
def frobeniusOnPoints (W : Affine (ZMod p)) : (W.baseChange L).Point →+ (W.baseChange L).Point :=
  Affine.Point.map (W' := W) (FiniteField.frobeniusAlgHom (ZMod p) L)

/-- The actual field extension on nonsingular points of the prime-field curve. -/
def primeFieldInclusion (W : Affine (ZMod p)) :
    (W.baseChange (ZMod p)).Point →+ (W.baseChange L).Point :=
  Affine.Point.map (W' := W) (Algebra.ofId (ZMod p) L)

theorem primeFieldInclusion_injective (W : Affine (ZMod p)) :
    Function.Injective (primeFieldInclusion p L W) :=
  Affine.Point.map_injective (W' := W) (Algebra.ofId (ZMod p) L)

/-- A geometric point is fixed precisely when it descends to the prime field. -/
theorem frobenius_eq_self_iff (W : Affine (ZMod p)) (P : (W.baseChange L).Point) :
    frobeniusOnPoints p L W P = P ↔
      ∃ Q : (W.baseChange (ZMod p)).Point, primeFieldInclusion p L W Q = P := by
  constructor
  · intro h
    cases P with
    | zero => exact ⟨0, rfl⟩
    | some x y hxy =>
      rw [frobeniusOnPoints, Affine.Point.map_some] at h
      have hFixed := Affine.Point.some.inj h
      obtain ⟨a, ha⟩ := (pow_prime_eq_self_iff p L x).mp
        (by simpa only [algebraFrobenius_apply] using hFixed.1)
      obtain ⟨b, hb⟩ := (pow_prime_eq_self_iff p L y).mp
        (by simpa only [algebraFrobenius_apply] using hFixed.2)
      let i := Algebra.ofId (ZMod p) L
      have h₀ : (W.baseChange (ZMod p)).Nonsingular a b :=
        (W.baseChange_nonsingular (f := i) i.injective a b).mp
          (by simpa only [i, Algebra.ofId_apply, ha, hb] using hxy)
      refine ⟨.some a b h₀, ?_⟩
      rw [primeFieldInclusion, Affine.Point.map_some]
      simpa only [Algebra.ofId_apply, Affine.Point.some.injEq] using And.intro ha hb
  · rintro ⟨Q, rfl⟩
    exact Affine.Point.map_baseChange (W' := W)
      (FiniteField.frobeniusAlgHom (ZMod p) L) Q

/-- The kernel of Frobenius minus the identity has the arithmetic point count. -/
theorem frobenius_sub_id_kernel_card (W : Affine (ZMod p)) :
    Nat.card (frobeniusOnPoints p L W - AddMonoidHom.id _).ker =
      Nat.card (W.baseChange (ZMod p)).Point := by
  let k := (frobeniusOnPoints p L W - AddMonoidHom.id _).ker
  have hMem (P : (W.baseChange L).Point) :
      P ∈ k ↔ frobeniusOnPoints p L W P = P := by
    rw [AddMonoidHom.mem_ker]
    exact sub_eq_zero
  let i (Q : (W.baseChange (ZMod p)).Point) : k :=
    ⟨primeFieldInclusion p L W Q,
      (hMem _).mpr ((frobenius_eq_self_iff p L W _).mpr ⟨Q, rfl⟩)⟩
  have hInjective : Function.Injective i := by
    intro a b h
    exact primeFieldInclusion_injective p L W (congrArg Subtype.val h)
  have hSurjective : Function.Surjective i := by
    intro Q
    obtain ⟨P, hP⟩ := (frobenius_eq_self_iff p L W Q.val).mp ((hMem Q.val).mp Q.property)
    exact ⟨P, Subtype.ext hP⟩
  exact Nat.card_congr (Equiv.ofBijective i ⟨hInjective, hSurjective⟩).symm

end

end ManuscriptAudit.WeierstrassFrobeniusFixed

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.WeierstrassFrobeniusFixed.pow_prime_eq_self_iff,
      ``ManuscriptAudit.WeierstrassFrobeniusFixed.primeFieldInclusion_injective,
      ``ManuscriptAudit.WeierstrassFrobeniusFixed.frobenius_eq_self_iff,
      ``ManuscriptAudit.WeierstrassFrobeniusFixed.frobenius_sub_id_kernel_card] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
