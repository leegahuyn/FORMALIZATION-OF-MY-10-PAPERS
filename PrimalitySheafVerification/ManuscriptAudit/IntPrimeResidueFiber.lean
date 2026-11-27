import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.Algebra.Field.ZMod
import Mathlib.AlgebraicGeometry.Pullbacks

/-! For every rational prime, the map from Spec of ZMod p is the canonical
scheme residue-field map at (p). This identifies its actual fibers for
any scheme over the integers. -/

namespace ManuscriptAudit.IntPrimeResidueFiber

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev R := CommRingCat.of ℤ
variable (p : ℕ) [Fact p.Prime]

/-- The standard coefficient map from the prime field. -/
abbrev coefficientPoint : Spec (CommRingCat.of (ZMod p)) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod p)))

/-- The closed point selected by reduction modulo p. -/
def closedPoint : Spec R := coefficientPoint p (⊥ : PrimeSpectrum (ZMod p))

private theorem closedPoint_eq_kernel :
    (closedPoint p).asIdeal = RingHom.ker (algebraMap ℤ (ZMod p)) := rfl

/-- Its prime ideal is literally the ideal (p) in the integers. -/
theorem closedPoint_ideal : (closedPoint p).asIdeal = Ideal.span ({(p : ℤ)} : Set ℤ) := by
  rw [closedPoint_eq_kernel p]
  ext n
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd n p

private theorem reduction_inverts_primeCompl :
    (closedPoint p).asIdeal.primeCompl ≤ (IsUnit.submonoid (ZMod p)).comap (algebraMap ℤ (ZMod p)) := by
  intro n hn
  change IsUnit ((algebraMap ℤ (ZMod p)) n)
  apply isUnit_iff_ne_zero.mpr
  intro h
  apply hn
  rw [closedPoint_eq_kernel p]
  exact RingHom.mem_ker.mpr h

private def residueLift : (closedPoint p).asIdeal.ResidueField →+* (ZMod p) :=
  Ideal.ResidueField.lift (closedPoint p).asIdeal (algebraMap ℤ (ZMod p))
    (le_of_eq (closedPoint_eq_kernel p)) (reduction_inverts_primeCompl p)

private theorem residueLift_algebraMap (n : ℤ) :
    residueLift p (algebraMap ℤ (closedPoint p).asIdeal.ResidueField n) = algebraMap ℤ (ZMod p) n :=
  Ideal.ResidueField.lift_algebraMap _ _ _ _ n

/-- The residue field of the prime ideal is canonically ZMod p. -/
def residueFieldEquiv : (closedPoint p).asIdeal.ResidueField ≃+* (ZMod p) :=
  RingEquiv.ofBijective (residueLift p) ⟨(residueLift p).injective, by
    intro y
    obtain ⟨n, hn⟩ := ZMod.intCast_surjective y
    exact ⟨algebraMap ℤ (closedPoint p).asIdeal.ResidueField n, (residueLift_algebraMap p n).trans hn⟩⟩

/-- Spec of ZMod p is the scheme's actual residue field, over Spec ℤ. -/
def residueSpecIso : Spec (CommRingCat.of (ZMod p)) ≅ Spec ((Spec R).residueField (closedPoint p)) :=
  Scheme.Spec.mapIso (residueFieldEquiv p).toCommRingCatIso.op ≪≫
    Scheme.Spec.mapIso (Scheme.Spec.residueFieldIso R (closedPoint p)).op

theorem residueSpecIso_over :
    (residueSpecIso p).hom ≫ (Spec R).fromSpecResidueField (closedPoint p) = coefficientPoint p := by
  change (Spec.map (residueFieldEquiv p).toCommRingCatIso.hom ≫
    Spec.map (Scheme.Spec.residueFieldIso R (closedPoint p)).hom) ≫
      (Spec R).fromSpecResidueField (closedPoint p) = _
  have hInv : Spec.map (Scheme.Spec.residueFieldIso R (closedPoint p)).hom ≫
      (Spec R).fromSpecResidueField (closedPoint p) =
        Spec.map (CommRingCat.ofHom (algebraMap ℤ (closedPoint p).asIdeal.ResidueField)) := by
    rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField R (closedPoint p),
      ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.id_comp]
  rw [Category.assoc, hInv, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact residueLift_algebraMap p

/-- For any integral-base scheme, the computed coefficient pullback
is the canonical scheme fiber at the closed point (p). -/
def canonicalFiberIso {X : Scheme.{0}} (g : X ⟶ Spec R) :
    pullback (coefficientPoint p) g ≅
      pullback ((Spec R).fromSpecResidueField (closedPoint p)) g :=
  asIso (pullback.map (coefficientPoint p) g
    ((Spec R).fromSpecResidueField (closedPoint p)) g
    (residueSpecIso p).hom (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id] using (residueSpecIso_over p).symm) (by simp))

theorem canonicalFiberIso_over {X : Scheme.{0}} (g : X ⟶ Spec R) :
    (canonicalFiberIso p g).hom ≫
      pullback.fst ((Spec R).fromSpecResidueField (closedPoint p)) g =
        pullback.fst (coefficientPoint p) g ≫ (residueSpecIso p).hom := by
  simp only [canonicalFiberIso, asIso_hom, pullback.map, pullback.lift_fst]

end
end ManuscriptAudit.IntPrimeResidueFiber

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntPrimeResidueFiber.closedPoint_ideal,
      ``ManuscriptAudit.IntPrimeResidueFiber.residueFieldEquiv,
      ``ManuscriptAudit.IntPrimeResidueFiber.residueSpecIso_over,
      ``ManuscriptAudit.IntPrimeResidueFiber.canonicalFiberIso,
      ``ManuscriptAudit.IntPrimeResidueFiber.canonicalFiberIso_over] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
