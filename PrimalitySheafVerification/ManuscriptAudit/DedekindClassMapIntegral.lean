import Lean.Util.CollectAxioms
import Mathlib.RingTheory.ClassGroup.Basic

/-! The native class group isomorphism of a ring isomorphism preserves
the class of each nonzero integral ideal with its literal ideal map. -/

namespace ManuscriptAudit.DedekindClassMapIntegral

open IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

variable {A B : Type*} [CommRing A] [CommRing B] [IsDedekindDomain A] [IsDedekindDomain B]
variable (e : A ≃+* B)

private abbrev F := FractionRing A
private abbrev L := FractionRing B

private theorem map_fractional_coeIdeal (I : Ideal A) :
    FractionalIdeal.ringEquivOfRingEquiv (F (A := A)) (L (B := B)) e
      (I : FractionalIdeal A⁰ (F (A := A))) =
        (Ideal.map e.toRingHom I : FractionalIdeal B⁰ (L (B := B))) := by
  let f := IsFractionRing.ringEquivOfRingEquiv
    (K := F (A := A)) (L := L (B := B)) e
  ext x
  change x ∈ (FractionalIdeal.ringEquivOfRingEquiv (F (A := A)) (L (B := B)) e
    (I : FractionalIdeal A⁰ (F (A := A)))).val ↔ _
  rw [FractionalIdeal.ringEquivOfRingEquiv_apply_val, Submodule.mem_map]
  change (∃ t : F (A := A), t ∈ (I : FractionalIdeal A⁰ (F (A := A))) ∧ f t = x) ↔ _
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal A⁰).mp ht
    apply (FractionalIdeal.mem_coeIdeal B⁰).mpr
    refine ⟨e a, Ideal.mem_map_of_mem e.toRingHom ha, ?_⟩
    exact (IsFractionRing.ringEquivOfRingEquiv_algebraMap e a).symm
  · intro hx
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal B⁰).mp hx
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp hb
    refine ⟨algebraMap A (F (A := A)) a,
      FractionalIdeal.mem_coeIdeal_of_mem A⁰ ha, ?_⟩
    exact IsFractionRing.ringEquivOfRingEquiv_algebraMap e a

/-- Transport an actual nonzero ideal by the literal image under the
ring equivalence. -/
def mapNonzero (I : (Ideal A)⁰) : (Ideal B)⁰ :=
  ⟨Ideal.map e.toRingHom I.val, mem_nonZeroDivisors_iff_ne_zero.mpr (by
    intro h
    apply (mem_nonZeroDivisors_iff_ne_zero.mp I.property)
    exact (Ideal.map_eq_bot_iff_of_injective e.injective).mp h)⟩

theorem class_mk0_map (I : (Ideal A)⁰) :
    ClassGroup.mulEquiv e (ClassGroup.mk0 I) = ClassGroup.mk0 (mapNonzero e I) := by
  apply (ClassGroup.equiv (R := B) (L (B := B))).injective
  simp only [ClassGroup.mulEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    ClassGroup.equiv_mk0, QuotientGroup.congr_mk']
  congr 1
  apply Units.ext
  simpa only [Units.coe_mapEquiv, RingEquiv.coe_toMulEquiv, FractionalIdeal.coe_mk0]
    using map_fractional_coeIdeal e I.val

end

end ManuscriptAudit.DedekindClassMapIntegral

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.DedekindClassMapIntegral.class_mk0_map
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
