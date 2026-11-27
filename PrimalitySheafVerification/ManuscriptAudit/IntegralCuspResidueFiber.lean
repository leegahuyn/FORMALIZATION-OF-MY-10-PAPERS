import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.ResidueField
import PrimalitySheafVerification.ManuscriptAudit.IntegralCuspNodalAffine

/-! The field pullback over five agrees with the canonical residue
field pullback of the cusp family at the prime ideal (5). -/

namespace ManuscriptAudit.IntegralCuspResidueFiber

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open IntegralCuspNodalAffine (coefficientPoint cuspToInt)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev R := CommRingCat.of ℤ
private abbrev F₅ := ZMod 5
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The closed point selected by reduction modulo five. -/
def primeFive : Spec R := coefficientPoint F₅ (⊥ : PrimeSpectrum F₅)

private theorem primeFive_eq_kernel :
    primeFive.asIdeal = RingHom.ker (algebraMap ℤ F₅) := rfl

/-- Its prime ideal is literally the ideal (5) in the integers. -/
theorem primeFive_ideal : primeFive.asIdeal = Ideal.span ({5} : Set ℤ) := by
  rw [primeFive_eq_kernel]
  ext n
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd n 5

private theorem reduction_inverts_primeCompl :
    primeFive.asIdeal.primeCompl ≤ (IsUnit.submonoid F₅).comap (algebraMap ℤ F₅) := by
  intro n hn
  change IsUnit ((algebraMap ℤ F₅) n)
  apply isUnit_iff_ne_zero.mpr
  intro h
  apply hn
  rw [primeFive_eq_kernel, RingHom.mem_ker]
  exact h

private def residueLift : primeFive.asIdeal.ResidueField →+* F₅ :=
  Ideal.ResidueField.lift primeFive.asIdeal (algebraMap ℤ F₅)
    (le_of_eq primeFive_eq_kernel) reduction_inverts_primeCompl

private theorem residueLift_algebraMap (n : ℤ) :
    residueLift (algebraMap ℤ primeFive.asIdeal.ResidueField n) = algebraMap ℤ F₅ n :=
  Ideal.ResidueField.lift_algebraMap _ _ _ _ n

/-- The residue field of the prime ideal is canonically F₅. -/
def residueFieldEquiv : primeFive.asIdeal.ResidueField ≃+* F₅ :=
  RingEquiv.ofBijective residueLift ⟨residueLift.injective, by
    intro y
    obtain ⟨n, hn⟩ := ZMod.intCast_surjective y
    exact ⟨algebraMap ℤ primeFive.asIdeal.ResidueField n, (residueLift_algebraMap n).trans hn⟩⟩

/-- Spec F₅ is the scheme's actual residue field, over Spec ℤ. -/
def residueSpecIso : Spec (CommRingCat.of F₅) ≅ Spec ((Spec R).residueField primeFive) :=
  Scheme.Spec.mapIso residueFieldEquiv.toCommRingCatIso.op ≪≫
    Scheme.Spec.mapIso (Scheme.Spec.residueFieldIso R primeFive).op

theorem residueSpecIso_over :
    residueSpecIso.hom ≫ (Spec R).fromSpecResidueField primeFive = coefficientPoint F₅ := by
  change (Spec.map residueFieldEquiv.toCommRingCatIso.hom ≫
    Spec.map (Scheme.Spec.residueFieldIso R primeFive).hom) ≫
      (Spec R).fromSpecResidueField primeFive = _
  have hInv : Spec.map (Scheme.Spec.residueFieldIso R primeFive).hom ≫
      (Spec R).fromSpecResidueField primeFive =
        Spec.map (CommRingCat.ofHom (algebraMap ℤ primeFive.asIdeal.ResidueField)) := by
    rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField R primeFive,
      ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.id_comp]
  rw [Category.assoc, hInv, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact residueLift_algebraMap

/-- The actual family fiber at the closed point (5) is the computed arithmetic fiber. -/
def canonicalFiberIso :
    pullback (coefficientPoint F₅) cuspToInt ≅
      pullback ((Spec R).fromSpecResidueField primeFive) cuspToInt :=
  asIso (pullback.map (coefficientPoint F₅) cuspToInt
    ((Spec R).fromSpecResidueField primeFive) cuspToInt
    residueSpecIso.hom (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id] using residueSpecIso_over.symm) (by simp))

end
end ManuscriptAudit.IntegralCuspResidueFiber

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralCuspResidueFiber.primeFive_ideal,
      ``ManuscriptAudit.IntegralCuspResidueFiber.residueFieldEquiv,
      ``ManuscriptAudit.IntegralCuspResidueFiber.residueSpecIso_over,
      ``ManuscriptAudit.IntegralCuspResidueFiber.canonicalFiberIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
