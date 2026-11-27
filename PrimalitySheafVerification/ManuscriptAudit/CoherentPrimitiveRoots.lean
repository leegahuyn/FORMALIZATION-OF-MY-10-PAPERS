import Lean.Util.CollectAxioms
import Mathlib.Data.Nat.Prime.Pow
import PrimalitySheafVerification.ManuscriptAudit.CuspRootCoefficients
import PrimalitySheafVerification.ManuscriptAudit.PadicResidueSystems

/-! Coherent primitive roots realize the actual residue transition
by the `ℓ`-power map between successive groups of roots of unity. -/

namespace ManuscriptAudit.CoherentPrimitiveRoots

open CuspRootCoefficients (rootsOfUnityEquivZModOfPrimitiveRoot
  rootsOfUnityEquivZModOfPrimitiveRoot_symm_val)

noncomputable section

section Power

variable (R : Type*) [CommRing R] (ℓ : ℕ)

/-- Actual power transition on the algebraic roots-of-unity groups. -/
def rootTransition (n : ℕ) : rootsOfUnity (ℓ ^ (n + 1)) R →* rootsOfUnity (ℓ ^ n) R where
  toFun x := ⟨x.val ^ ℓ, by
    rw [mem_rootsOfUnity, ← pow_mul, Nat.mul_comm ℓ (ℓ ^ n), ← pow_succ]
    exact (mem_rootsOfUnity (ℓ ^ (n + 1)) x.val).mp x.property⟩
  map_one' := Subtype.ext (one_pow ℓ)
  map_mul' x y := Subtype.ext (mul_pow x.val y.val ℓ)

end Power

variable (K : Type*) [Field K] [IsAlgClosed K]
variable (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

private theorem exists_lift (n : ℕ) {x : K} (hx : IsPrimitiveRoot x (ℓ ^ (n + 1))) :
    ∃ y : K, IsPrimitiveRoot y (ℓ ^ ((n + 1) + 1)) ∧ y ^ ℓ = x := by
  have hℓ : ℓ.Prime := Fact.out
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq x hℓ.pos
  have hy' : y ^ ℓ ^ ((n + 1) + 1) = 1 := by
    rw [pow_succ ℓ (n + 1), Nat.mul_comm (ℓ ^ (n + 1)) ℓ, pow_mul, hy, hx.pow_eq_one]
  have hdiv : orderOf y ∣ ℓ ^ ((n + 1) + 1) :=
    ((IsPrimitiveRoot.orderOf y).pow_eq_one_iff_dvd _).mp hy'
  have hndiv : ¬ orderOf y ∣ ℓ ^ (n + 1) := by
    intro h
    have hz := ((IsPrimitiveRoot.orderOf y).pow_eq_one_iff_dvd _).mpr h
    rw [pow_succ ℓ n, Nat.mul_comm (ℓ ^ n) ℓ, pow_mul, hy] at hz
    have hle := (Nat.pow_dvd_pow_iff_le_right hℓ.one_lt).mp ((hx.pow_eq_one_iff_dvd _).mp hz)
    omega
  exact ⟨y, IsPrimitiveRoot.iff_orderOf.mpr (Nat.eq_prime_pow_of_dvd_least_prime_pow hℓ hndiv hdiv), hy⟩

private def positiveRoots (n : ℕ) : {x : K // IsPrimitiveRoot x (ℓ ^ (n + 1))} :=
  Nat.rec
    (by
      obtain ⟨x, hx⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K ℓ
      exact ⟨x, by simpa only [pow_one] using hx⟩)
    (fun n x ↦
      ⟨Classical.choose (exists_lift K ℓ n x.property),
        (Classical.choose_spec (exists_lift K ℓ n x.property)).1⟩) n

/-- Primitive roots chosen coherently at every finite order. -/
def root : ℕ → K
  | 0 => 1
  | n + 1 => (positiveRoots K ℓ n).val

theorem root_primitive (n : ℕ) : IsPrimitiveRoot (root K ℓ n) (ℓ ^ n) := by
  cases n with
  | zero => exact IsPrimitiveRoot.one_left_iff.mpr (pow_zero ℓ)
  | succ n => exact (positiveRoots K ℓ n).property

theorem root_pow (n : ℕ) : (root K ℓ (n + 1)) ^ ℓ = root K ℓ n := by
  cases n with
  | zero =>
    simpa only [root, pow_one] using (positiveRoots K ℓ 0).property.pow_eq_one
  | succ n =>
    exact (Classical.choose_spec (exists_lift K ℓ n (positiveRoots K ℓ n).property)).2

private instance powerNeZero (n : ℕ) : NeZero (ℓ ^ n) :=
  ⟨pow_ne_zero n (show ℓ.Prime from Fact.out).ne_zero⟩

/-- Interpret an actual finite residue class as a root of unity in the coherent basis. -/
def fromExponent (n : ℕ) : Multiplicative (ZMod (ℓ ^ n)) ≃* rootsOfUnity (ℓ ^ n) K :=
  (rootsOfUnityEquivZModOfPrimitiveRoot (root_primitive K ℓ n)).symm

/-- The chosen bases intertwine native coefficient reduction with the power transition. -/
theorem fromExponent_transition (n : ℕ) (a : ZMod (ℓ ^ (n + 1))) :
    rootTransition K ℓ n (fromExponent K ℓ (n + 1) (Multiplicative.ofAdd a)) =
      fromExponent K ℓ n (Multiplicative.ofAdd (PadicResidueSystems.reduction ℓ (Nat.le_succ n) a)) := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective a
  rw [map_intCast]
  apply Subtype.ext
  apply Units.ext
  change (((fromExponent K ℓ (n + 1) (Multiplicative.ofAdd (z : ZMod (ℓ ^ (n + 1))))).val : K) ^ ℓ =
    ((fromExponent K ℓ n (Multiplicative.ofAdd (z : ZMod (ℓ ^ n)))).val : K)
  simp only [fromExponent, rootsOfUnityEquivZModOfPrimitiveRoot_symm_val]
  calc
    _ = root K ℓ (n + 1) ^ (z * (ℓ : ℤ)) := by rw [zpow_mul, zpow_natCast]
    _ = (root K ℓ (n + 1) ^ ℓ) ^ z := by rw [mul_comm, zpow_mul, zpow_natCast]
    _ = _ := by rw [root_pow]

end
end ManuscriptAudit.CoherentPrimitiveRoots

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CoherentPrimitiveRoots.root_primitive,
      ``ManuscriptAudit.CoherentPrimitiveRoots.root_pow,
      ``ManuscriptAudit.CoherentPrimitiveRoots.rootTransition,
      ``ManuscriptAudit.CoherentPrimitiveRoots.fromExponent_transition] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
