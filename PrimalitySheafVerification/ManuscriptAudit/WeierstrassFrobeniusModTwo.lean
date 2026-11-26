import Lean.Util.CollectAxioms
import Mathlib.GroupTheory.Perm.Cycle.Type
import PrimalitySheafVerification.ManuscriptAudit.FrobeniusModTwoLinear
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassFrobeniusFixed

/-!
# Arithmetic parity and the Frobenius trace on two-torsion

The actual two-torsion representation sees a nonzero fixed vector
exactly when the rational point group has a nonzero point of order
two. The finite-group Cauchy theorem recognizes this parity.
-/

namespace ManuscriptAudit.WeierstrassFrobeniusModTwo

open WeierstrassCurve FrobeniusModTwoLinear WeierstrassFrobeniusFixed

noncomputable section

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Cauchy and Lagrange detect even order by nonzero elements killed by two. -/
theorem two_dvd_card_iff_nonzero_two_torsion (G : Type*) [AddGroup G] [Finite G] :
    2 ∣ Nat.card G ↔ ∃ x : G, x ≠ 0 ∧ (2 : ℕ) • x = 0 := by
  constructor
  · intro h
    letI := Fintype.ofFinite G
    rw [Nat.card_eq_fintype_card] at h
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card 2 h
    refine ⟨x, ?_, by simpa only [hx] using addOrderOf_nsmul_eq_zero x⟩
    intro h0
    subst x
    simp at hx
  · rintro ⟨x, h0, hx⟩
    have hd : addOrderOf x ∣ 2 := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hx
    have ho : addOrderOf x = 2 :=
      ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
        (fun h => h0 (AddMonoid.addOrderOf_eq_one_iff.mp h))
    simpa only [ho] using addOrderOf_dvd_natCard x

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod p) L] [DecidableEq L]
variable (V : Type*) [AddCommGroup V] [Module (ZMod 2) V]
variable (W : Affine (ZMod p)) (F : V ≃ₗ[ZMod 2] V)
variable (i : V →+ (W.baseChange L).Point)

variable (hi : Function.Injective i)
variable (hImage : ∀ P : (W.baseChange L).Point,
  (∃ v : V, i v = P) ↔ (2 : ℕ) • P = 0)
variable (hF : ∀ v : V, i (F v) = frobeniusOnPoints p L W (i v))

include hi hImage hF

/-- Fixed nonzero geometric two-torsion is exactly rational nonzero two-torsion. -/
theorem nonzero_fixed_iff_rational_two_torsion :
    (∃ v : V, v ≠ 0 ∧ F v = v) ↔
      ∃ Q : (W.baseChange (ZMod p)).Point, Q ≠ 0 ∧ (2 : ℕ) • Q = 0 := by
  constructor
  · rintro ⟨v, hv, hf⟩
    have hFixed : frobeniusOnPoints p L W (i v) = i v := by rw [← hF, hf]
    obtain ⟨Q, hQ⟩ := (frobenius_eq_self_iff p L W (i v)).mp hFixed
    refine ⟨Q, ?_, ?_⟩
    · intro h0
      apply hv
      apply hi
      rw [map_zero, ← hQ, h0, map_zero]
    · apply primeFieldInclusion_injective p L W
      rw [map_nsmul, map_zero, hQ]
      exact (hImage (i v)).mp ⟨v, rfl⟩
  · rintro ⟨Q, hQ, h2Q⟩
    have ht : (2 : ℕ) • primeFieldInclusion p L W Q = 0 := by
      rw [← map_nsmul, h2Q, map_zero]
    obtain ⟨v, hv⟩ := (hImage (primeFieldInclusion p L W Q)).mpr ht
    refine ⟨v, ?_, ?_⟩
    · intro h0
      apply hQ
      apply primeFieldInclusion_injective p L W
      rw [map_zero, ← hv, h0, map_zero]
    · apply hi
      rw [hF, hv]
      exact (frobenius_eq_self_iff p L W _).mpr ⟨Q, rfl⟩

/-- The actual arithmetic point count mod two is the trace on geometric two-torsion. -/
theorem trace_eq_point_count_mod_two (b : Module.Basis (Fin 2) (ZMod 2) V) :
    LinearMap.trace (ZMod 2) V F.toLinearMap =
      (Nat.card (W.baseChange (ZMod p)).Point : ZMod 2) := by
  letI : Finite (W.baseChange (ZMod p)).Point :=
    Finite.of_injective _ (Affine.Point.nonsingularPointEquiv (W.baseChange (ZMod p))).injective
  apply scalar_eq_of_zero_iff
  rw [ZMod.natCast_eq_zero_iff, trace_zero_iff_nonzero_fixed V b F,
    nonzero_fixed_iff_rational_two_torsion p L V W F i hi hImage hF,
    two_dvd_card_iff_nonzero_two_torsion]

/-- For odd p the trace on two-torsion is the signed arithmetic trace reduced mod two. -/
theorem trace_eq_signed_point_count_mod_two (b : Module.Basis (Fin 2) (ZMod 2) V)
    (hpTwo : p ≠ 2) :
    LinearMap.trace (ZMod 2) V F.toLinearMap =
      (((p : ℤ) + 1 - (Nat.card (W.baseChange (ZMod p)).Point : ℤ)) : ZMod 2) := by
  rw [trace_eq_point_count_mod_two p L V W F i hi hImage hF b]
  have hp : (p : ZMod 2) = 1 :=
    ZMod.natCast_eq_one_iff_odd.mpr ((Fact.out : p.Prime).odd_of_ne_two hpTwo)
  simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_one, hp]
  rw [show (1 + 1 : ZMod 2) = 0 by decide, zero_sub, neg_scalar_eq_self]

end

end ManuscriptAudit.WeierstrassFrobeniusModTwo

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
    [``ManuscriptAudit.WeierstrassFrobeniusModTwo.two_dvd_card_iff_nonzero_two_torsion,
      ``ManuscriptAudit.WeierstrassFrobeniusModTwo.nonzero_fixed_iff_rational_two_torsion,
      ``ManuscriptAudit.WeierstrassFrobeniusModTwo.trace_eq_point_count_mod_two,
      ``ManuscriptAudit.WeierstrassFrobeniusModTwo.trace_eq_signed_point_count_mod_two] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
