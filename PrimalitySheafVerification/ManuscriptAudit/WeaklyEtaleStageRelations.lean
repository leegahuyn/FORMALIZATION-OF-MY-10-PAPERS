import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Localization.Away.Basic
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleStageStalkInjection

/-! Finitely many relations already satisfied on the actual chart
can be imposed on one principal shrink of a weakly étale stage. -/

namespace ManuscriptAudit.WeaklyEtaleStageRelations

open AlgebraicGeometry CategoryTheory
open ProetaleAffineTensor (structureMap)
open scoped BigOperators

noncomputable section

universe u

variable {A C B : Type u} [CommRing A] [CommRing C] [CommRing B]
  [Algebra A C] [Algebra A B]
  [WeaklyEtale (structureMap A C)] [WeaklyEtale (structureMap A B)]

/-- A finite family of equations can be witnessed on the actual
stage after a principal localization containing the image point. -/
theorem exists_away_zero (g : C →ₐ[A] B)
    (q : Ideal C) [q.IsPrime] (r : Ideal B) [r.IsPrime] (hq : q = r.comap g.toRingHom)
    {ι : Type u} [Fintype ι] (z : ι → C) (hz : ∀ i, g (z i) = 0) :
    ∃ t : C, t ∉ q ∧ g t ∉ r ∧ ∀ i, algebraMap C (Localization.Away t) (z i) = 0 := by
  classical
  let S := Localization.AtPrime q
  let T := Localization.AtPrime r
  let f := Localization.localRingHom q r g.toRingHom hq
  have hf : Function.Injective f := WeaklyEtaleStageStalkInjection.localRingHom_injective g q r hq
  have h (i : ι) : ∃ a : q.primeCompl, (a : C) * z i = 0 := by
    have hmap : algebraMap C S (z i) = 0 := by
      apply hf
      change f (algebraMap C S (z i)) = f 0
      rw [Localization.localRingHom_to_map, map_zero]
      change algebraMap B T (g (z i)) = 0
      rw [hz, map_zero]
    have hzero : algebraMap C S (z i) = algebraMap C S 0 := by rw [map_zero, hmap]
    obtain ⟨a, ha⟩ := (IsLocalization.eq_iff_exists q.primeCompl S).mp hzero
    exact ⟨a, ha.trans (mul_zero _)⟩
  choose a ha using h
  let t := ∏ i, (a i : C)
  have ht : t ∉ q := fun hmem ↦ by
    obtain ⟨i, _, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact (a i).property hi
  have hgt : g t ∉ r := by
    intro hmem
    apply ht
    rw [hq]
    exact hmem
  refine ⟨t, ht, hgt, fun i ↦ ?_⟩
  let P := Localization.Away t
  have hDiv : (a i : C) ∣ t :=
    Finset.dvd_prod_of_mem (fun j ↦ (a j : C)) (Finset.mem_univ i)
  have hu : IsUnit (algebraMap C P (a i : C)) := IsLocalization.Away.isUnit_of_dvd t hDiv
  apply hu.isRegular.left
  change algebraMap C P (a i : C) * algebraMap C P (z i) = algebraMap C P (a i : C) * 0
  rw [← map_mul, ha, map_zero, mul_zero]

end
end ManuscriptAudit.WeaklyEtaleStageRelations

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeaklyEtaleStageRelations.exists_away_zero
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
