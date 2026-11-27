import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Tactic.LinearCombination

/-!
# Normalized integral matrices in the eta Kloosterman sum

Ahlgren–Andersen, arXiv:1504.02500v3, §6, defines the sum using matrices
with lower left entry (D>0) and diagonal entries in ([0,D)) when the
cusp width is one. The lower right entry parametrizes these matrices by
the reduced residues. Restriction to Γ₀(N) retains precisely moduli
divisible by N.
-/

namespace ManuscriptAudit.Paper8NormalizedKloostermanRows

open Matrix
open scoped MatrixGroups

noncomputable section

def NormalizedRow (D : ℕ) :=
  {A : SL(2, ℤ) // A 1 0 = (D : ℤ) ∧
    (0 ≤ A 0 0 ∧ A 0 0 < (D : ℤ)) ∧
    (0 ≤ A 1 1 ∧ A 1 1 < (D : ℤ))}

abbrev ReducedResidue (D : ℕ) :=
  {d : Fin D // Nat.Coprime d.val D}

private theorem row_det {D : ℕ} (A : NormalizedRow D) :
    A.1 0 0 * A.1 1 1 - A.1 0 1 * (D : ℤ) = 1 := by
  simpa only [Matrix.det_fin_two, A.property.1] using
    Matrix.SpecialLinearGroup.det_coe A.1

private theorem row_det_zmod {D : ℕ} (A : NormalizedRow D) :
    (A.1 0 0 : ZMod D) * (A.1 1 1 : ZMod D) = 1 := by
  have h := congrArg (fun z : ℤ => (z : ZMod D)) (row_det A)
  simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast,
    ZMod.natCast_self, mul_zero, sub_zero, Int.cast_one] using h

def bottom {D : ℕ} (A : NormalizedRow D) : ReducedResidue D := by
  let d : ℕ := (A.1 1 1).toNat
  have hCast : (d : ℤ) = A.1 1 1 := Int.toNat_of_nonneg A.property.2.2.1
  have hBound : d < D := by
    exact_mod_cast (by rw [hCast]; exact A.property.2.2.2 : (d : ℤ) < (D : ℤ))
  have hMul : (A.1 0 0 : ZMod D) * (d : ZMod D) = 1 := by
    simpa only [← hCast, Int.cast_natCast] using row_det_zmod A
  exact ⟨⟨d, hBound⟩, (ZMod.isUnit_iff_coprime d D).mp
    (isUnit_iff_exists_inv'.mpr ⟨(A.1 0 0 : ZMod D), hMul⟩)⟩

theorem bottom_cast {D : ℕ} (A : NormalizedRow D) :
    ((bottom A).1.val : ℤ) = A.1 1 1 :=
  Int.toNat_of_nonneg A.property.2.2.1

theorem bottom_injective {D : ℕ} (hD : 0 < D) :
    Function.Injective (bottom (D := D)) := by
  intro A B h
  have hBottom : A.1 1 1 = B.1 1 1 := by
    simpa only [bottom_cast] using
      congrArg (fun d : ReducedResidue D => (d.1.val : ℤ)) h
  have hA := row_det_zmod A
  have hB := row_det_zmod B
  rw [← hBottom, mul_comm] at hB
  have hTopZ : (A.1 0 0 : ZMod D) = (B.1 0 0 : ZMod D) := by
    calc
      (A.1 0 0 : ZMod D) =
          (A.1 0 0 : ZMod D) * ((A.1 1 1 : ZMod D) * (B.1 0 0 : ZMod D)) := by
        rw [hB, mul_one]
      _ = (B.1 0 0 : ZMod D) := by rw [← mul_assoc, hA, one_mul]
  have hTop := (ZMod.intCast_eq_intCast_iff' _ _ D).mp hTopZ
  rw [Int.emod_eq_of_lt A.property.2.1.1 A.property.2.1.2,
    Int.emod_eq_of_lt B.property.2.1.1 B.property.2.1.2] at hTop
  have hUpperRight : A.1 0 1 = B.1 0 1 := by
    have hDetA := row_det A
    have hDetB := row_det B
    rw [← hTop, ← hBottom] at hDetB
    have hCancel : (A.1 0 1 - B.1 0 1) * (D : ℤ) = 0 := by
      linear_combination hDetB - hDetA
    have hDInt : (D : ℤ) ≠ 0 := by exact_mod_cast hD.ne'
    exact sub_eq_zero.mp ((mul_eq_zero.mp hCancel).resolve_right hDInt)
  refine Subtype.ext (Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_)
  fin_cases i <;> fin_cases j
  · exact hTop
  · exact hUpperRight
  · exact A.property.1.trans B.property.1.symm
  · exact hBottom

theorem bottom_surjective {D : ℕ} (hD : 0 < D) :
    Function.Surjective (bottom (D := D)) := by
  intro d
  letI : NeZero D := ⟨hD.ne'⟩
  let a : ℕ := ((d.1.val : ZMod D)⁻¹).val
  have hA : a < D := ZMod.val_lt _
  have hInv : (a : ZMod D) * (d.1.val : ZMod D) = 1 :=
    ZMod.val_inv_mul d.property
  have hDvd : (D : ℤ) ∣ (a : ℤ) * (d.1.val : ℤ) - 1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_one, hInv, sub_self]
  obtain ⟨b, hb⟩ := hDvd
  let A : SL(2, ℤ) := ⟨!![(a : ℤ), b; (D : ℤ), (d.1.val : ℤ)], by
    rw [Matrix.det_fin_two_of]
    linear_combination hb⟩
  have hAI : (a : ℤ) < (D : ℤ) := by exact_mod_cast hA
  have hDI : (d.1.val : ℤ) < (D : ℤ) := by exact_mod_cast d.1.isLt
  let R : NormalizedRow D :=
    ⟨A, rfl, ⟨Int.natCast_nonneg _, hAI⟩, ⟨Int.natCast_nonneg _, hDI⟩⟩
  refine ⟨R, Subtype.ext (Fin.ext ?_)⟩
  have hCast : ((bottom R).1.val : ℤ) = (d.1.val : ℤ) := bottom_cast R
  exact_mod_cast hCast

def rowsEquiv {D : ℕ} (hD : 0 < D) : NormalizedRow D ≃ ReducedResidue D :=
  Equiv.ofBijective bottom ⟨bottom_injective hD, bottom_surjective hD⟩

theorem rowsEquiv_bottom_cast {D : ℕ} (hD : 0 < D) (A : NormalizedRow D) :
    ((rowsEquiv hD A).1.val : ℤ) = A.1 1 1 :=
  bottom_cast A

theorem row_mem_level_iff {D : ℕ} (N : ℕ) (A : NormalizedRow D) :
    A.1 ∈ CongruenceSubgroup.Gamma0 N ↔ N ∣ D := by
  rw [CongruenceSubgroup.Gamma0_mem, A.property.1, Int.cast_natCast,
    ZMod.natCast_eq_zero_iff]

end
end ManuscriptAudit.Paper8NormalizedKloostermanRows

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8NormalizedKloostermanRows.bottom_injective,
      ``ManuscriptAudit.Paper8NormalizedKloostermanRows.bottom_surjective,
      ``ManuscriptAudit.Paper8NormalizedKloostermanRows.rowsEquiv_bottom_cast,
      ``ManuscriptAudit.Paper8NormalizedKloostermanRows.row_mem_level_iff] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
