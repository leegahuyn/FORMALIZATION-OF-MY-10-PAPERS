import Lean.Util.CollectAxioms
import Mathlib.RingTheory.ClassGroup.Basic
import PrimalitySheafVerification.ManuscriptAudit.DedekindFractionalCycleEquiv

/-! A finite Dedekind cycle represents zero in the usual class group
exactly when it is the cycle of a genuine rational unit. -/

namespace ManuscriptAudit.DedekindCycleClass

open IsDedekindDomain DedekindPrincipalDivisor DedekindFractionalCycleEquiv
open scoped nonZeroDivisors

noncomputable section

variable (A F : Type) [CommRing A] [IsDedekindDomain A] [Field F] [Algebra A F] [IsFractionRing A F]

private abbrev U := (FractionalIdeal A⁰ F)ˣ
private abbrev P := (toPrincipalIdeal A F).range

private abbrev fractionalClass : Additive (U A F) →+ Additive (U A F ⧸ P A F) :=
  (QuotientGroup.mk' (P A F)).toAdditive

/-- The actual ideal class of a finite height-one cycle. -/
def cycleClass : (HeightOneSpectrum A →₀ ℤ) →+ Additive (ClassGroup A) :=
  ((ClassGroup.equiv (R := A) F).symm.toAdditive.toAddMonoidHom).comp
    ((fractionalClass A F).comp (cycleEquiv A F).symm.toAddMonoidHom)

theorem cycleClass_surjective : Function.Surjective (cycleClass A F) :=
  (ClassGroup.equiv (R := A) F).symm.toAdditive.surjective.comp
    ((QuotientGroup.mk'_surjective (P A F)).comp (cycleEquiv A F).symm.surjective)

private theorem principal_identity (x : Additive Fˣ) :
    (cycleEquiv A F).symm (principalDivisor A F x) =
      Additive.ofMul (toPrincipalIdeal A F x.toMul) := by
  rw [cycleEquiv_principal]
  apply Additive.ext
  apply Units.ext
  exact (coe_toPrincipalIdeal (R := A) x.toMul).symm

theorem cycleClass_eq_zero (d : HeightOneSpectrum A →₀ ℤ) :
    cycleClass A F d = 0 ↔ ∃ x : Additive Fˣ, principalDivisor A F x = d := by
  let e := (ClassGroup.equiv (R := A) F).symm.toAdditive
  let y := (cycleEquiv A F).symm d
  have h : cycleClass A F d = 0 ↔ (fractionalClass A F) y = 0 := by
    exact ⟨fun h => e.injective (h.trans (e.map_zero).symm),
      fun h => (congrArg e h).trans (e.map_zero)⟩
  rw [h]
  change QuotientGroup.mk' (P A F) y.toMul = 1 ↔ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨Additive.ofMul x, (cycleEquiv A F).symm.injective ?_⟩
    exact (principal_identity A F (Additive.ofMul x)).trans (congrArg Additive.ofMul hx)
  · rintro ⟨x, rfl⟩
    refine ⟨x.toMul, ?_⟩
    exact (congrArg Additive.toMul (principal_identity A F x)).symm

end

end ManuscriptAudit.DedekindCycleClass

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.DedekindCycleClass.cycleClass_eq_zero
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
