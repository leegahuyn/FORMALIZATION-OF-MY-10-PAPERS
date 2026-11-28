import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Localization.Away.Basic
import PrimalitySheafVerification.ManuscriptAudit.FlatUnramifiedEtaleNeighborhood
import PrimalitySheafVerification.ManuscriptAudit.PrimeLocalizationClearing

/-! A finite family of actual chart sections with local preimages in
a flat unramified stage factors through a single affine étale neighborhood. -/

namespace ManuscriptAudit.EtalePrincipalStageSections

noncomputable section

open scoped BigOperators

universe u

variable {A B D : Type u} [CommRing A] [CommRing B] [CommRing D] [Algebra A B] [Algebra A D]
  [Module.Flat A D] [Algebra.FinitePresentation A D]

set_option maxHeartbeats 2200000 in
/-- A fixed finite family is realized on a common literal principal
étale stage after a principal shrink containing the chart point. -/
theorem exists_etale_stage (g : D →ₐ[A] B) (q : Ideal D) [q.IsPrime]
    (r : Ideal B) [r.IsPrime] (hq : q = r.comap g.toRingHom) [Algebra.IsUnramifiedAt A q]
    {ι : Type u} [Fintype ι] (z : ι → B)
    (hz : ∀ i, ∃ v : Localization.AtPrime q,
      Localization.localRingHom q r g.toRingHom hq v = algebraMap B (Localization.AtPrime r) (z i)) :
    ∃ (f : D) (b : B), f ∉ q ∧ b ∉ r ∧ Algebra.Etale A (Localization.Away f) ∧
      ∃ j : Localization.Away f →ₐ[A] Localization.Away b,
        (∀ d : D, j (algebraMap D _ d) = algebraMap B _ (g d)) ∧
        ∀ i, ∃ x : Localization.Away f, j x = algebraMap B _ (z i) := by
  classical
  have h (i : ι) : ∃ (a e : D) (t : B), e ∉ q ∧ t ∉ r ∧
      t * g a = t * (g e * z i) := by
    obtain ⟨v, hv⟩ := hz i
    exact PrimeLocalizationClearing.exists_cleared g.toRingHom q r hq v (z i) hv
  choose a e t he ht hRel using h
  let E := ∏ i, e i
  let T := ∏ i, t i
  have hE : E ∉ q := fun hE ↦ by
    obtain ⟨i, _, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp hE
    exact he i hi
  have hT : T ∉ r := fun hT ↦ by
    obtain ⟨i, _, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp hT
    exact ht i hi
  obtain ⟨f, hf, hEf, hEt⟩ := FlatUnramifiedEtaleNeighborhood.exists_etale_away A D q E hE
  let b := g f * T
  have hgf : g f ∉ r := by
    intro hgf
    apply hf
    rw [hq]
    exact hgf
  refine ⟨f, b, hf, ‹r.IsPrime›.mul_notMem hgf hT, hEt, ?_⟩
  let S := Localization.Away f
  let P := Localization.Away b
  let k : D →ₐ[A] P := (IsScalarTower.toAlgHom A B P).comp g
  have hUnit : IsUnit (k f) :=
    IsLocalization.Away.isUnit_of_dvd (S := P) b (dvd_mul_right (g f) T)
  let j : S →ₐ[A] P := IsLocalization.Away.liftAlgHom f (f := k) hUnit
  have hj (d : D) : j (algebraMap D S d) = algebraMap B P (g d) :=
    IsLocalization.Away.lift_eq f hUnit d
  refine ⟨j, hj, fun i ↦ ?_⟩
  have hdiv : e i ∣ f := (Finset.dvd_prod_of_mem e (Finset.mem_univ i)).trans hEf
  have hS : IsUnit (algebraMap D S (e i)) := IsLocalization.Away.isUnit_of_dvd f hdiv
  have htP : IsUnit (algebraMap B P (t i)) :=
    IsLocalization.Away.isUnit_of_dvd b
      ((Finset.dvd_prod_of_mem t (Finset.mem_univ i)).trans (dvd_mul_left T (g f)))
  have hEdiv : g (e i) ∣ b := by
    obtain ⟨c, hc⟩ := hdiv
    refine ⟨g c * T, ?_⟩
    change g f * T = g (e i) * (g c * T)
    rw [hc, map_mul, mul_assoc]
  have heP : IsUnit (algebraMap B P (g (e i))) :=
    IsLocalization.Away.isUnit_of_dvd b hEdiv
  have hEq : algebraMap B P (g (a i)) = algebraMap B P (g (e i) * z i) := by
    apply htP.isRegular.left
    rw [← map_mul, ← map_mul, hRel i]
  let y := (↑hS.unit⁻¹ : S) * algebraMap D S (a i)
  have hy : algebraMap D S (e i) * y = algebraMap D S (a i) := by
    change algebraMap D S (e i) * (↑hS.unit⁻¹ * algebraMap D S (a i)) = _
    calc
      _ = ((hS.unit : S) * ↑hS.unit⁻¹) * algebraMap D S (a i) := by
        rw [← mul_assoc, hS.unit_spec]
      _ = _ := by rw [Units.mul_inv, one_mul]
  refine ⟨y, heP.isRegular.left ?_⟩
  calc
    _ = j (algebraMap D S (e i) * y) := by rw [map_mul, hj]
    _ = algebraMap B P (g (a i)) := by rw [hy, hj]
    _ = _ := hEq.trans (map_mul _ _ _)

end
end ManuscriptAudit.EtalePrincipalStageSections

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.EtalePrincipalStageSections.exists_etale_stage
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
