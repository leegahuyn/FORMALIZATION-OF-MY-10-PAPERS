import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Algebraic roots of unity for the cusp Kummer coefficient

Over an algebraically closed field, the group of \(n\)-th roots of unity
is identified with the additive group of \(\mathbb Z/n\mathbb Z\) once a
primitive root has been chosen and \(n\) is nonzero in the field. The group
and the power map in this file are Mathlib's actual algebraic objects.
-/

namespace ManuscriptAudit.CuspRootCoefficients

variable {K : Type*} [Field K]

/-- A primitive root identifies the roots of unity with the cyclic group
of exponents. The codomain uses the multiplicative notation for addition. -/
noncomputable def rootsOfUnityEquivZModOfPrimitiveRoot {n : ℕ} [NeZero n] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) : rootsOfUnity n K ≃* Multiplicative (ZMod n) :=
  (MulEquiv.subgroupCongr (IsPrimitiveRoot.zpowers_eq (hζ.isUnit_unit' (NeZero.ne n))).symm).trans
    (hζ.isUnit_unit' (NeZero.ne n)).zmodEquivZPowers.symm.toMultiplicativeRight

/-- The inverse sends an integer exponent class to the corresponding
power of the chosen primitive root. -/
theorem rootsOfUnityEquivZModOfPrimitiveRoot_symm_val {n : ℕ} [NeZero n] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) (i : ℤ) :
    (((rootsOfUnityEquivZModOfPrimitiveRoot hζ).symm
      (Multiplicative.ofAdd (i : ZMod n))).val : K) = ζ ^ i := by
  simp [rootsOfUnityEquivZModOfPrimitiveRoot, MulEquiv.subgroupCongr_symm_apply]

/-- In an algebraically closed field with \(n\) nonzero, choose a
primitive \(n\)-th root to identify the actual roots of unity with
\(\mathbb Z/n\mathbb Z\). -/
noncomputable def rootsOfUnityEquivZMod (K : Type*) [Field K] [IsAlgClosed K]
    (n : ℕ) [NeZero (n : K)] : rootsOfUnity n K ≃* Multiplicative (ZMod n) := by
  letI : NeZero n := NeZero.of_neZero_natCast K
  exact rootsOfUnityEquivZModOfPrimitiveRoot
    (Classical.choose_spec (HasEnoughRootsOfUnity.exists_primitiveRoot K n))

end ManuscriptAudit.CuspRootCoefficients

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CuspRootCoefficients.rootsOfUnityEquivZModOfPrimitiveRoot,
      ``ManuscriptAudit.CuspRootCoefficients.rootsOfUnityEquivZModOfPrimitiveRoot_symm_val,
      ``ManuscriptAudit.CuspRootCoefficients.rootsOfUnityEquivZMod] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
