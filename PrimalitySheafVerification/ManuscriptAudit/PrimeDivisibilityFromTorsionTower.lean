import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import PrimalitySheafVerification.ManuscriptAudit.PowerTorsionTower

/-! A torsion group is l-divisible when all of its l-primary transitions are onto. -/

namespace ManuscriptAudit.PrimeDivisibilityFromTorsionTower

open PowerTorsionTower TorsionFrobeniusModule

noncomputable section

variable (l : ℕ) [Fact l.Prime] (G : Type*) [AddCommGroup G]

theorem surjective_nsmul_of_surjective_transitions
    (hTorsion : ∀ P : G, ∃ m : ℕ, 0 < m ∧ m • P = 0)
    (hTrans : ∀ n, Function.Surjective (transition l G n)) :
    Function.Surjective (fun P : G => l • P) := by
  intro P
  obtain ⟨m, hm, hAnn⟩ := hTorsion P
  let n := padicValNat l m
  have hDiv : l ^ n ∣ m := (padicValNat_dvd_iff_le hm.ne').mpr le_rfl
  obtain ⟨d, hd⟩ := hDiv
  have hNot : ¬l ∣ d := by
    rintro ⟨e, he⟩
    apply pow_succ_padicValNat_not_dvd hm.ne'
    exact ⟨e, by rw [hd, he, pow_succ, mul_assoc]⟩
  let T : PowerTorsion l G n := ⟨d • P, (mem_iff (l ^ n) G _).mpr (by
    rw [← mul_nsmul', ← hd, hAnn])⟩
  obtain ⟨Q, hQ⟩ := hTrans n T
  have hLift : l • (Q : G) = d • P :=
    congrArg (fun U : PowerTorsion l G n => (U : G)) hQ
  let a := Nat.gcdA l d
  let b := Nat.gcdB l d
  have hc : l.Coprime d := (((Fact.out : l.Prime).coprime_iff_not_dvd).mpr hNot)
  have hBezout : (l : ℤ) * a + (d : ℤ) * b = 1 := by
    have h := Nat.gcd_eq_gcd_ab l d
    rw [hc.gcd_eq_one, Nat.cast_one] at h
    exact h.symm
  refine ⟨a • P + b • (Q : G), ?_⟩
  let f : G →+ G := nsmulAddMonoidHom l
  change f (a • P + b • (Q : G)) = P
  rw [map_add, map_zsmul, map_zsmul]
  change a • (l • P) + b • (l • (Q : G)) = P
  rw [hLift, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, ← add_smul,
    mul_comm a, mul_comm b, hBezout, one_smul]

end
end ManuscriptAudit.PrimeDivisibilityFromTorsionTower

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.PrimeDivisibilityFromTorsionTower.surjective_nsmul_of_surjective_transitions
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
