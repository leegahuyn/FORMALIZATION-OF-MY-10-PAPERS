import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeAdicHTwoReduction
import PrimalitySheafVerification.ManuscriptAudit.PadicResidueSystems

/-! The genuine finite Laurent-class ranges form the standard adic tower. -/

namespace ManuscriptAudit.CuspNativeAdicHTwoResidueRange

open AlgebraicGeometry CategoryTheory
open CuspProperCompactification (projectiveCusp)
open CuspNativeAdicHTwoLower (adicInclusion)
open CuspNativeAdicHTwoReduction (residueInclusion residueInclusion_injective reduction_adicInclusion)
open ProetaleAdicReductionAllDegrees (nativeCompatible nativeStep reductionMap)
open PadicResidueSystems (reduction)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

private abbrev X := projectiveCusp K

/-- The finite Laurent classes commute with the actual coefficient transitions. -/
theorem residueInclusion_transition (n : ℕ) (r : ZMod (ℓ ^ (n + 1))) :
    nativeStep (X K) ℓ 2 n (residueInclusion K ℓ (n + 1) r) =
      residueInclusion K ℓ n (reduction ℓ (Nat.le_succ n) r) := by
  let a : ℤ_[ℓ] := r.val
  have ha : PadicInt.toZModPow (n + 1) a = r := by
    change PadicInt.toZModPow (n + 1) (r.val : ℤ_[ℓ]) = r
    rw [map_natCast, ZMod.natCast_zmod_val]
  have hreduce : reduction ℓ (Nat.le_succ n) (PadicInt.toZModPow (n + 1) a) =
      PadicInt.toZModPow n a :=
    RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow n (n + 1) (Nat.le_succ n)) a
  rw [← ha, hreduce, ← reduction_adicInclusion K ℓ a (n + 1),
    ← reduction_adicInclusion K ℓ a n]
  exact (reductionMap (X K) ℓ 2 (adicInclusion K ℓ a)).property n

/-- Compatible classes that lie in the finite Laurent ranges have a unique adic coordinate. -/
theorem existsUnique_adicCoordinate (x : nativeCompatible (X K) ℓ 2)
    (hx : ∀ n, x.val n ∈ (residueInclusion K ℓ n).range) :
    ∃! a : ℤ_[ℓ], ∀ n, residueInclusion K ℓ n (PadicInt.toZModPow n a) = x.val n := by
  choose r hr using hx
  have hrStep (n : ℕ) : reduction ℓ (Nat.le_succ n) (r (n + 1)) = r n := by
    apply residueInclusion_injective K ℓ n
    rw [← residueInclusion_transition K ℓ n, hr (n + 1), hr n]
    exact x.property n
  let s : PadicResidueSystems.systems ℓ :=
    ⟨r, PadicResidueSystems.compatible_of_successors ℓ r hrStep⟩
  let e := PadicResidueSystems.padicRingEquiv ℓ
  refine ⟨e.symm s, ?_, ?_⟩
  · intro n
    have hn : PadicInt.toZModPow n (e.symm s) = r n :=
      congrArg (PadicResidueSystems.evaluate ℓ n) (e.apply_symm_apply s)
    rw [hn, hr n]
  · intro a ha
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    apply residueInclusion_injective K ℓ n
    calc
      _ = x.val n := ha n
      _ = residueInclusion K ℓ n (r n) := (hr n).symm
      _ = _ := congrArg (residueInclusion K ℓ n)
        (congrArg (PadicResidueSystems.evaluate ℓ n) (e.apply_symm_apply s)).symm

end
end ManuscriptAudit.CuspNativeAdicHTwoResidueRange

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspNativeAdicHTwoResidueRange.residueInclusion_transition,
      ``ManuscriptAudit.CuspNativeAdicHTwoResidueRange.existsUnique_adicCoordinate] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
