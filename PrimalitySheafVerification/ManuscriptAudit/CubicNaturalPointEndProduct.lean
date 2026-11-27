import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicGenericAbscissaDichotomy
import PrimalitySheafVerification.ManuscriptAudit.CubicNaturalPointEndFaithful

/-! The composition of two nonzero field-natural centered-cubic endomorphisms is detected at the generic point. -/

namespace ManuscriptAudit.CubicNaturalPointEnd

open CubicNonsplitThreeAdicTrace CubicGenericFunctionField CubicGenericAntiInvariant
open CubicGenericAbscissaDichotomy

noncomputable section
open scoped Classical

universe u

variable {K L : Type u} [Field K] [Field L] [IsAlgClosed L] [DecidableEq L] [Algebra K L]
  {A : K}

/-- If the composed generic output is two-torsion, one natural factor vanishes geometrically. -/
theorem eq_zero_or_eq_zero_of_composite (D E : Family K A)
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
    (h : (2 : ℕ) • D.atField (Model A)
      (E.atField (Model A) (genericPoint A h₂ h₃ hA)) = 0) :
    D.atField L = 0 ∨ E.atField L = 0 := by
  let Q : antiInvariant A := ⟨genericPoint A h₂ h₃ hA, genericPoint_mem_antiInvariant A h₂ h₃ hA⟩
  let P := antiInvariantApply E Q
  rcases two_torsion_or_transcendental h₂ h₃ hA P with hP | ⟨x, y, hxy, hP, hx⟩
  · exact Or.inr (eq_zero_of_two_torsion_generic E h₂ h₃ hA
      (congrArg (fun R : antiInvariant A => R.val) hP))
  · left
    apply eq_zero_of_two_torsion_generic D h₂ h₃ hA
    have h' : (2 : ℕ) • D.atField (Model A) P.val = 0 := h
    rw [hP] at h'
    have hEval := (eval_transcendental (double D) h₂ h₃ hA hxy hx).mp (by
      simpa only [double, AddMonoidHom.nsmul_apply] using h')
    simpa only [double, AddMonoidHom.nsmul_apply] using hEval

end

end ManuscriptAudit.CubicNaturalPointEnd

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicNaturalPointEnd.eq_zero_or_eq_zero_of_composite
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
