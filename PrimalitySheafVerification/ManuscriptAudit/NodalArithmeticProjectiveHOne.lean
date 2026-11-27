import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.KummerRationalOpenClass
import PrimalitySheafVerification.ManuscriptAudit.NodalArithmeticAffineBound
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveHOne
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveHOneRestriction
import PrimalitySheafVerification.ManuscriptAudit.NodalRationalInfinity

/-! Exact arithmetic H¹ of the proper split node once the field class is
separated from the nodal class by restriction to the smooth Y chart. -/

namespace ManuscriptAudit.NodalArithmeticProjectiveHOne

open AlgebraicGeometry CategoryTheory Opposite
open NodalProjectiveClosure (projectiveNode projectiveNodeToBase affineOpen)
open NodalProperYChart (chartOpen)
open EtaleTwoOpenHOne (identityObject openArrow)
open EtaleMayerVietoris (terminalCohomologyIso)
open NodalProjectiveHOneRestriction (primitiveNegOne rootLabelIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K]

private abbrev C := AddCommGrpCat.{0}
private abbrev M := AddCommGrpCat.of (ZMod 2)
private abbrev J := (projectiveNode K).smallEtaleTopology
private abbrev F := (constantSheaf (J K) C).obj M

abbrev properHOne := Sheaf.H (F K) 1

private abbrev term := identityObject (projectiveNode K)
private abbrev ambientPresheafHOne := (F K).H' 1 (term K)

private def yRestriction :
    ambientPresheafHOne K →+ (F K).H' 1 (Scheme.Etale.mk (chartOpen K)) :=
  (((F K).cohomologyPresheaf 1).map (openArrow (chartOpen K)).op).hom

theorem field_class_detected (h2 : (2 : K) ≠ 0) (u : Kˣ)
    (hu : ¬ ∃ v : Kˣ, v ^ (2 : ℕ) = u) :
    ∃ b : ambientPresheafHOne K, yRestriction K b ≠ 0 := by
  letI : NeZero ((2 : ℕ) : K) := ⟨by simpa using h2⟩
  letI : HasEnoughRootsOfUnity K 2 :=
    { prim := ⟨-1, primitiveNegOne K h2⟩
      cyc := rootsOfUnity.isCyclic K 2 }
  let X := projectiveNode K
  let k := projectiveNodeToBase K
  let j := chartOpen K
  let a := openArrow j
  let S := KummerRelativeFull.sequence X 2
  obtain ⟨p, hp⟩ := NodalRationalInfinity.exists_chart_rational_point K
  obtain ⟨b, hb⟩ := KummerRationalOpenClass.exists_class_detected_on_open k j p hp
    2 (by decide) u hu
  let e := (Sheaf.cohomologyPresheafFunctor (J K) 1).mapIso
    (((constantSheaf (J K) C).mapIso (rootLabelIso K h2)).symm ≪≫
      KummerRelativeFull.firstIso (d := 2) k)
  let b' := e.inv.app (op (term K)) b
  refine ⟨b', ?_⟩
  intro h
  have h' := ConcreteCategory.congr_hom (e.hom.naturality a.op) b'
  change e.hom.app (op (Scheme.Etale.mk j)) (yRestriction K b') =
    (S.X₁.cohomologyPresheaf 1).map a.op (e.hom.app (op (term K)) b') at h'
  have h'' : e.hom.app (op (term K)) b' = b := (e.app (op (term K))).inv_hom_id_apply _
  rw [h, map_zero, h''] at h'
  exact hb h'.symm

/-- For an odd-characteristic field with a nonsquare and one binary affine
line cohomology class, the actual proper split node has four arithmetic H¹ elements. -/
theorem finite_card_eq_four (h2 : (2 : K) ≠ 0)
    (hLine : ZMod 2 ≃+ NodalNormalizationHOneComparison.normalizationHOne K)
    (u : Kˣ) (hu : ¬ ∃ v : Kˣ, v ^ (2 : ℕ) = u) :
    Finite (properHOne K) ∧ Nat.card (properHOne K) = 4 := by
  obtain ⟨hAff, hAffCard⟩ := NodalArithmeticAffineBound.finite_card_le_four K h2 hLine
  let r := NodalProjectiveHOneRestriction.restriction K
  have hi := NodalProjectiveHOneRestriction.restriction_injective K h2
  letI : Finite (NodalArithmeticAffineBound.affineHOne K) := hAff
  letI : Finite (properHOne K) := Finite.of_injective r hi
  letI : Fintype (NodalArithmeticAffineBound.affineHOne K) := Fintype.ofFinite _
  letI : Fintype (properHOne K) := Fintype.ofFinite _
  have hUpper : Nat.card (properHOne K) ≤ Nat.card (NodalArithmeticAffineBound.affineHOne K) := by
    simpa only [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective r hi
  let e := (terminalCohomologyIso (F K) 1).addCommGroupIsoToAddEquiv
  letI : Finite (ambientPresheafHOne K) := Finite.of_injective e e.injective
  obtain ⟨a, ha, haY⟩ := NodalProjectiveHOne.exists_class_nonzero_affine_zero_y K h2
  obtain ⟨b, hb⟩ := field_class_detected K h2 u hu
  have hA : a ≠ 0 := fun h => ha (by rw [h, map_zero])
  have hLower₀ : 4 ≤ Nat.card (ambientPresheafHOne K) :=
    BinaryExactCardinality.four_le_card (yRestriction K) a b hA haY hb
  have hLower : 4 ≤ Nat.card (properHOne K) := hLower₀.trans_eq (Nat.card_congr e.toEquiv)
  exact ⟨inferInstance, Nat.le_antisymm (hUpper.trans hAffCard) hLower⟩

end
end ManuscriptAudit.NodalArithmeticProjectiveHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalArithmeticProjectiveHOne.finite_card_eq_four,
      ``ManuscriptAudit.NodalArithmeticProjectiveHOne.field_class_detected] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
