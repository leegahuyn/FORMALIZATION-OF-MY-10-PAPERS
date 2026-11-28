import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Ideal.Colon
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleStageStalkInjection

/-! The common annihilator of finitely many stage elements which
vanish on the actual weakly étale chart generates the unit ideal there. -/

namespace ManuscriptAudit.WeaklyEtaleAnnihilatorMap

open AlgebraicGeometry CategoryTheory
open ProetaleAffineTensor (structureMap)
open scoped BigOperators

noncomputable section

universe u

variable {A C B : Type u} [CommRing A] [CommRing C] [CommRing B]
  [Algebra A C] [Algebra A B]
  [WeaklyEtale (structureMap A C)] [WeaklyEtale (structureMap A B)]

abbrev commonAnnihilator {ι : Type u} (z : ι → C) : Ideal C :=
  (⊥ : Submodule C C).colon (Set.range z)

theorem annihilates {ι : Type u} (z : ι → C) (a : commonAnnihilator z) (i : ι) :
    (a : C) * z i = 0 := by
  simpa only [Submodule.mem_bot, smul_eq_mul] using
    (Submodule.mem_colon.mp a.property (z i) (Set.mem_range_self i))

set_option maxHeartbeats 1900000 in
/-- This statement uses faithful flatness of the literal chart
stalks over their image stalks. -/
theorem map_eq_top (k : C →ₐ[A] B) {ι : Type u} [Finite ι] (z : ι → C)
    (hz : ∀ i, k (z i) = 0) :
    (commonAnnihilator z).map k.toRingHom = ⊤ := by
  classical
  letI := Fintype.ofFinite ι
  let J := commonAnnihilator z
  by_contra hTop
  obtain ⟨r, hMax, hSub⟩ := Ideal.exists_le_maximal (J.map k.toRingHom) hTop
  letI : r.IsPrime := hMax.isPrime
  let q := r.comap k.toRingHom
  letI : q.IsPrime := Ideal.IsPrime.comap k.toRingHom
  let S := Localization.AtPrime q
  let T := Localization.AtPrime r
  let f := Localization.localRingHom q r k.toRingHom rfl
  have hf : Function.Injective f := WeaklyEtaleStageStalkInjection.localRingHom_injective k q r rfl
  have h (i : ι) : ∃ a : q.primeCompl, (a : C) * z i = 0 := by
    have hmap : algebraMap C S (z i) = 0 := by
      apply hf
      change f (algebraMap C S (z i)) = f 0
      rw [Localization.localRingHom_to_map, map_zero]
      change algebraMap B T (k (z i)) = 0
      rw [hz, map_zero]
    have hzero : algebraMap C S (z i) = algebraMap C S 0 := by rw [map_zero, hmap]
    obtain ⟨a, ha⟩ := (IsLocalization.eq_iff_exists q.primeCompl S).mp hzero
    exact ⟨a, ha.trans (mul_zero _)⟩
  choose a ha using h
  let t := ∏ i, (a i : C)
  have ht : t ∉ q := fun hmem ↦ by
    obtain ⟨i, _, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact (a i).property hi
  have hJ : t ∈ J := by
    apply Submodule.mem_colon.mpr
    rintro _ ⟨i, rfl⟩
    have hDiv : (a i : C) ∣ t :=
      Finset.dvd_prod_of_mem (fun j ↦ (a j : C)) (Finset.mem_univ i)
    obtain ⟨b, hb⟩ := hDiv
    change t * z i = 0
    rw [hb, mul_right_comm, ha i, zero_mul]
  exact ht (hSub (Ideal.mem_map_of_mem k.toRingHom hJ))

end
end ManuscriptAudit.WeaklyEtaleAnnihilatorMap

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeaklyEtaleAnnihilatorMap.map_eq_top
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
