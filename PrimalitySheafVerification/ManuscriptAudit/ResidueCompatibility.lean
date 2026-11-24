import Mathlib.Algebra.Exact.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.Abel

namespace ManuscriptAudit

variable {R : Type*} [CommRing R]

/-- The diagonal residue map from the quotient by the intersection. -/
noncomputable def idealResiduePair (I J : Ideal R) : (R ⧸ (I ⊓ J)) →+ (R ⧸ I) × (R ⧸ J) :=
  (Ideal.Quotient.factor (inf_le_left : I ⊓ J ≤ I)).toAddMonoidHom.prod
    (Ideal.Quotient.factor (inf_le_right : I ⊓ J ≤ J)).toAddMonoidHom

/-- The difference of the two residues in their common quotient. -/
noncomputable def idealResidueDifference (I J : Ideal R) : (R ⧸ I) × (R ⧸ J) →+ R ⧸ (I ⊔ J) :=
  (Ideal.Quotient.factor (le_sup_left : I ≤ I ⊔ J)).toAddMonoidHom.comp
      (AddMonoidHom.fst _ _) -
    (Ideal.Quotient.factor (le_sup_right : J ≤ I ⊔ J)).toAddMonoidHom.comp
      (AddMonoidHom.snd _ _)

private theorem idealResiduePair_mk (I J : Ideal R) (r : R) :
    idealResiduePair I J (Ideal.Quotient.mk (I ⊓ J) r) =
      (Ideal.Quotient.mk I r, Ideal.Quotient.mk J r) := by
  simp [idealResiduePair, Ideal.Quotient.factor_mk]

private theorem idealResidueDifference_mk (I J : Ideal R) (x y : R) :
    idealResidueDifference I J (Ideal.Quotient.mk I x, Ideal.Quotient.mk J y) =
      Ideal.Quotient.mk (I ⊔ J) (x - y) := by
  simp [idealResidueDifference, Ideal.Quotient.factor_mk, map_sub]

/-- The corrected short exact sequence for the manuscript's residue pairs,
with the sum of the ideals in the difference map's target. -/
theorem corrected_ideal_residue_sequence (I J : Ideal R) :
    Function.Injective (idealResiduePair I J) ∧
      Function.Exact (idealResiduePair I J) (idealResidueDifference I J) ∧
      Function.Surjective (idealResidueDifference I J) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y h
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [idealResiduePair_mk, idealResiduePair_mk] at h
    exact Ideal.Quotient.eq.mpr
      ⟨Ideal.Quotient.eq.mp (congrArg Prod.fst h),
        Ideal.Quotient.eq.mp (congrArg Prod.snd h)⟩
  · intro ab
    obtain ⟨a, b⟩ := ab
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    constructor
    · intro h
      rw [idealResidueDifference_mk, Ideal.Quotient.eq_zero_iff_mem] at h
      obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp h
      refine ⟨Ideal.Quotient.mk (I ⊓ J) (x - i), ?_⟩
      rw [idealResiduePair_mk]
      refine Prod.ext (Ideal.Quotient.eq.mpr ?_) (Ideal.Quotient.eq.mpr ?_)
      · rw [show x - i - x = -i by abel]
        exact I.neg_mem hi
      · have heq : x - i - y = j := calc
          x - i - y = (x - y) - i := by abel
          _ = j := by rw [← hij]; abel
        rw [heq]
        exact hj
    · rintro ⟨r, hr⟩
      rw [← hr]
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective r
      rw [idealResiduePair_mk, idealResidueDifference_mk, sub_self, map_zero]
  · intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨(Ideal.Quotient.mk I r, Ideal.Quotient.mk J 0), ?_⟩
    rw [idealResidueDifference_mk, sub_zero]

/-- Two prescribed residues have a common integer or ring representative
exactly when their difference is in the sum ideal. -/
theorem idealResidues_compatible_iff (I J : Ideal R) (x y : R) :
    (∃ z : R, z - x ∈ I ∧ z - y ∈ J) ↔ x - y ∈ I ⊔ J := by
  constructor
  · rintro ⟨z, hx, hy⟩
    have heq : -(z - x) + (z - y) = x - y := by abel
    exact Submodule.mem_sup.mpr ⟨_, I.neg_mem hx, _, hy, heq⟩
  · intro h
    obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp h
    refine ⟨x - i, ?_, ?_⟩
    · rw [show x - i - x = -i by abel]
      exact I.neg_mem hi
    · have heq : x - i - y = j := calc
        x - i - y = (x - y) - i := by abel
        _ = j := by rw [← hij]; abel
      rw [heq]
      exact hj

/-- A common-fiber residue detects equality in both individual residue rings
for every pair exactly when the ideals defining the two rings agree. -/
theorem commonResidue_detects_both_iff (I J : Ideal R) :
    (∀ x y : R, Ideal.Quotient.mk (I ⊔ J) x = Ideal.Quotient.mk (I ⊔ J) y →
      Ideal.Quotient.mk I x = Ideal.Quotient.mk I y ∧
      Ideal.Quotient.mk J x = Ideal.Quotient.mk J y) ↔ I = J := by
  constructor
  · intro h
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · have h0 := Ideal.Quotient.eq_zero_iff_mem.mpr
        (show x ∈ I ⊔ J from (le_sup_left : I ≤ I ⊔ J) hx)
      have hq : Ideal.Quotient.mk (I ⊔ J) x = Ideal.Quotient.mk (I ⊔ J) 0 :=
        h0.trans (map_zero _).symm
      have hh := (h x 0 hq).2
      rw [map_zero] at hh
      exact Ideal.Quotient.eq_zero_iff_mem.mp hh
    · have h0 := Ideal.Quotient.eq_zero_iff_mem.mpr
        (show x ∈ I ⊔ J from (le_sup_right : J ≤ I ⊔ J) hx)
      have hq : Ideal.Quotient.mk (I ⊔ J) x = Ideal.Quotient.mk (I ⊔ J) 0 :=
        h0.trans (map_zero _).symm
      have hh := (h x 0 hq).1
      rw [map_zero] at hh
      exact Ideal.Quotient.eq_zero_iff_mem.mp hh
  · rintro rfl x y h
    have hm : x - y ∈ I ⊔ I := Ideal.Quotient.eq.mp h
    have hm' : x - y ∈ I := by simpa only [sup_idem] using hm
    have he := Ideal.Quotient.eq.mpr hm'
    exact ⟨he, he⟩

/-- For the moduli 6 and 3², the common residue forgets both
individual residue equalities for the pair 4³+3 and 4³. -/
theorem paper1_commonFiber_does_not_detect_double_residue :
    (4 : ZMod 3) ^ 3 + 3 = 4 ^ 3 ∧
      (4 : ZMod 6) ^ 3 + 3 ≠ 4 ^ 3 ∧
      (4 : ZMod 9) ^ 3 + 3 ≠ 4 ^ 3 := by
  decide

end ManuscriptAudit

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.corrected_ideal_residue_sequence,
      ``ManuscriptAudit.idealResidues_compatible_iff,
      ``ManuscriptAudit.commonResidue_detects_both_iff,
      ``ManuscriptAudit.paper1_commonFiber_does_not_detect_double_residue] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
