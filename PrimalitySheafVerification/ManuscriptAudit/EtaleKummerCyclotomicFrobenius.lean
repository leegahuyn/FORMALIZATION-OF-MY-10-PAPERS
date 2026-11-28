import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CoherentPrimitiveRoots
import PrimalitySheafVerification.ManuscriptAudit.KummerRootLabels
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassNativeFrobeniusPowers

/-! The actual arithmetic Frobenius acts on the coherent roots of unity
by the cyclotomic scalar, at every finite level and every iterate. -/

namespace ManuscriptAudit.EtaleKummerCyclotomicFrobenius

open KummerRootLabels CoherentPrimitiveRoots

noncomputable section

variable (k K : Type) [Field k] [Fintype k] [Field K] [Algebra k K]

/-- On the actual Kummer roots the arithmetic Frobenius acts by raising
to the cardinality of its base field. -/
theorem roots_frobenius_pow (d m : ℕ) (x : rootsOfUnity d K) :
    mapRoots d (((FiniteField.frobeniusAlgHom k K) ^ m).toRingHom) x =
      x ^ ((Fintype.card k) ^ m) := by
  apply Subtype.ext
  apply Units.ext
  change ((FiniteField.frobeniusAlgHom k K) ^ m) (x.val : K) =
    (x.val : K) ^ ((Fintype.card k) ^ m)
  exact WeierstrassNativeFrobeniusPowers.field_frobenius_power_apply k K m _

variable [IsAlgClosed K]
variable (l : ℕ) [Fact l.Prime] [NeZero (l : K)]

/-- In the chosen coherent cyclic coordinates the literal coefficient
Frobenius is the cyclotomic scalar at every \(\ell\)-power level. -/
theorem coherent_frobenius_scalar (n m : ℕ) (a : ZMod (l ^ n)) :
    mapRoots (l ^ n) (((FiniteField.frobeniusAlgHom k K) ^ m).toRingHom)
      (fromExponent K l n (Multiplicative.ofAdd a)) =
    fromExponent K l n (Multiplicative.ofAdd (((Fintype.card k) ^ m) • a)) := by
  rw [roots_frobenius_pow]
  exact ((fromExponent K l n).map_pow (Multiplicative.ofAdd a) ((Fintype.card k) ^ m)).symm

end

end ManuscriptAudit.EtaleKummerCyclotomicFrobenius

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.EtaleKummerCyclotomicFrobenius.coherent_frobenius_scalar
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
