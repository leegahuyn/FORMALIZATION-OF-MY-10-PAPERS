import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.Modular
import PrimalitySheafVerification.ManuscriptAudit.FiniteIndexWeightZeroCosets
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaPeterssonMass
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaLevelIndices

/-! Right-coset translates of the native modular domain give the exact eta mass ratios. -/

namespace ManuscriptAudit.Paper8EtaCosetMass

open Set MeasureTheory UpperHalfPlane
open FiniteIndexWeightZeroCosets Paper8EtaPeterssonMass
open scoped MatrixGroups ENNReal

noncomputable section

def cellRepresentative (H : Subgroup SL(2, ℤ)) (q : RightCoset H) : SL(2, ℤ) :=
  Quotient.out q

theorem cellRepresentative_mk (H : Subgroup SL(2, ℤ)) (q : RightCoset H) :
    rightCosetMk H (cellRepresentative H q) = q := Quotient.out_eq q

def cosetCells (H : Subgroup SL(2, ℤ)) (S : Set ℍ) : Set ℍ :=
  ⋃ q : RightCoset H, translate (cellRepresentative H q) S

private theorem same_coset_of_relative_sign (H : Subgroup SL(2, ℤ))
    (hNeg : (-1 : SL(2, ℤ)) ∈ H) {a b : SL(2, ℤ)}
    (hSign : b⁻¹ * a = 1 ∨ b⁻¹ * a = -1) :
    rightCosetMk H a = rightCosetMk H b := by
  have hA : a = b * (b⁻¹ * a) := by simp
  have hMem : a * b⁻¹ ∈ H := by
    rcases hSign with h | h
    · rw [hA, h, mul_one, mul_inv_cancel]
      exact H.one_mem
    · rw [hA, h, mul_neg, mul_one, neg_mul, mul_inv_cancel]
      exact hNeg
  exact Quotient.sound (QuotientGroup.rightRel_apply.mpr hMem)

theorem open_cells_pairwise_disjoint (H : Subgroup SL(2, ℤ))
    (hNeg : (-1 : SL(2, ℤ)) ∈ H) :
    Pairwise (fun i j : RightCoset H =>
      Disjoint (translate (cellRepresentative H i) ModularGroup.fdo)
        (translate (cellRepresentative H j) ModularGroup.fdo)) := by
  intro i j hij
  refine disjoint_left.mpr ?_
  rintro _ ⟨u, hu, rfl⟩ ⟨v, hv, he⟩
  let a := cellRepresentative H i
  let b := cellRepresentative H j
  change b • v = a • u at he
  have hAct : (b⁻¹ * a) • u = v := by rw [mul_smul, ← he, inv_smul_smul]
  have hSign := ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fdo
    (g := b⁻¹ * a) hu (hAct.symm ▸ hv)
  have h := same_coset_of_relative_sign H hNeg hSign
  exact hij (by simpa only [a, b, cellRepresentative_mk] using h)

theorem closed_cells_meet_every_orbit (H : Subgroup SL(2, ℤ)) (z : ℍ) :
    ∃ h : H, ∃ w ∈ cosetCells H ModularGroup.fd, (h : SL(2, ℤ)) • w = z := by
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
  let q := rightCosetMk H g⁻¹
  let a := cellRepresentative H q
  have haq : rightCosetMk H g⁻¹ = rightCosetMk H a := (cellRepresentative_mk H q).symm
  have hh : g⁻¹ * a⁻¹ ∈ H := QuotientGroup.rightRel_apply.mp (Quotient.exact haq)
  refine ⟨⟨g⁻¹ * a⁻¹, hh⟩, a • (g • z), ?_, ?_⟩
  · exact mem_iUnion.mpr ⟨q, g • z, hg, rfl⟩
  · change (g⁻¹ * a⁻¹) • (a • (g • z)) = z
    rw [mul_smul, inv_smul_smul, inv_smul_smul]

theorem mass_open_coset_cells (H : Subgroup SL(2, ℤ)) [H.FiniteIndex]
    (hNeg : (-1 : SL(2, ℤ)) ∈ H) :
    mass (cosetCells H ModularGroup.fdo) = (H.index : ℝ≥0∞) * mass ModularGroup.fdo := by
  letI := rightCosetFintype H
  letI := H.fintypeQuotientOfFiniteIndex
  have hCard : Fintype.card (RightCoset H) = H.index := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
    exact Fintype.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel H)
  rw [cosetCells, mass_disjoint_translates (cellRepresentative H) ModularGroup.isOpen_fdo.measurableSet
    ((open_cells_pairwise_disjoint H hNeg).mono (fun _ _ h => h.aedisjoint)), hCard]

private theorem neg_one_mem_gammaZero (N : ℕ) : (-1 : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma0 N := by
  have hEntry : ((-1 : SL(2, ℤ)) 1 0) = 0 := by
    change (-(1 : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 = 0
    simp [Matrix.one_apply]
  rw [CongruenceSubgroup.Gamma0_mem, hEntry]
  simp

theorem levelTwo_eta_mass :
    mass (cosetCells (CongruenceSubgroup.Gamma0 2) ModularGroup.fdo) =
      3 * mass ModularGroup.fdo := by
  rw [mass_open_coset_cells _ (neg_one_mem_gammaZero 2), Paper8EtaLevelIndices.levelTwo_index]
  all_goals norm_num

theorem levelFour_eta_mass :
    mass (cosetCells (CongruenceSubgroup.Gamma0 4) ModularGroup.fdo) =
      6 * mass ModularGroup.fdo := by
  rw [mass_open_coset_cells _ (neg_one_mem_gammaZero 4), Paper8EtaLevelIndices.levelFour_index]
  norm_num

end
end ManuscriptAudit.Paper8EtaCosetMass

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EtaCosetMass.open_cells_pairwise_disjoint,
      ``ManuscriptAudit.Paper8EtaCosetMass.closed_cells_meet_every_orbit,
      ``ManuscriptAudit.Paper8EtaCosetMass.mass_open_coset_cells,
      ``ManuscriptAudit.Paper8EtaCosetMass.levelTwo_eta_mass,
      ``ManuscriptAudit.Paper8EtaCosetMass.levelFour_eta_mass] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
