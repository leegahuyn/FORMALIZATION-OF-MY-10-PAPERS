import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.LaurentKummerTowerCover
import PrimalitySheafVerification.ManuscriptAudit.ProetaleLaurentCyclicHOne
import PrimalitySheafVerification.ManuscriptAudit.SheafIntegerGeneratorEpi

/-! On the actual all-root cover every Laurent power of the distinguished
unit has simultaneous lifts under its finite Kummer power maps. -/

namespace ManuscriptAudit.LaurentKummerGeneratorLifts

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open LaurentKummerTowerAlgebra (Tower laurentMap root_power root_isUnit)
open LaurentKummerTowerCover (base coverMap coverObject coverArrow terminalObject)
open ProetaleUnitSheaf (unitSheaf specUnits specUnits_naturality)
open ProetaleKummerPower (J G power power_eval)
open ProetaleLaurentCyclicHOne (exponentUnit)
open ProetaleAffineLineCyclicHOne (unitsHZeroEquiv)
open SheafIntegerGeneratorEpi (integerSheaf generator)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

abbrev terminalIsTerminal : IsTerminal (terminalObject K) :=
  MorphismProperty.Over.mkIdTerminal @WeaklyEtale (base K)

/-- Ext⁰ of the Laurent unit exponent, viewed as the native sheaf morphism. -/
def unitMap (m : ℕ) :
    integerSheaf (J (base K)) ⟶ unitSheaf (base K) :=
  Ext.addEquiv₀ (exponentUnit K (m : ℤ))

private theorem unitMap_generator (m : ℕ) :
    (unitMap K m).hom.app (op (terminalObject K)) (generator (J (base K)) (terminalIsTerminal K)) =
      Sheaf.H.equiv₀ (unitSheaf (base K)) (terminalIsTerminal K) (exponentUnit K (m : ℤ)) := by
  let F := unitSheaf (base K)
  let Z := AddCommGrpCat.of (ULift.{1} ℤ)
  let E := constantSheafAdj (J (base K)) G (terminalIsTerminal K)
  let a := unitMap K m
  have h : E.homEquiv Z F a =
      E.homEquiv Z (integerSheaf (J (base K))) (𝟙 _) ≫ a.hom.app (op (terminalObject K)) := by
    change E.homEquiv Z F a = _ ≫ ((sheafSections (J (base K)) G).obj (op (terminalObject K))).map a
    simpa only [Category.id_comp] using E.homEquiv_naturality_right (𝟙 (integerSheaf (J (base K)))) a
  exact (ConcreteCategory.congr_hom h (⟨1⟩ : Z)).symm

private theorem unitMap_cover (m : ℕ) :
    (unitMap K m).hom.app (op (coverObject K ℓ))
      ((integerSheaf (J (base K))).obj.map (coverArrow K ℓ).op
        (generator (J (base K)) (terminalIsTerminal K))) =
      (unitSheaf (base K)).obj.map (coverArrow K ℓ).op
        (Sheaf.H.equiv₀ (unitSheaf (base K)) (terminalIsTerminal K) (exponentUnit K (m : ℤ))) := by
  exact (NatTrans.naturality_apply (unitMap K m).hom (coverArrow K ℓ).op
    (generator (J (base K)) (terminalIsTerminal K))).trans
    (congrArg ((unitSheaf (base K)).obj.map (coverArrow K ℓ).op) (unitMap_generator K m))

private theorem coordinate_unit (m : ℕ) :
    unitsHZeroEquiv (LaurentPolynomial K) (exponentUnit K (m : ℤ)) =
      LaurentUnitProductCoordinates.unitCoordinates K (0, (m : ℤ)) :=
  (unitsHZeroEquiv (LaurentPolynomial K)).apply_symm_apply _

set_option maxHeartbeats 2400000 in
/-- On the actual common cover the Laurent class of each nonnegative
exponent has a power preimage on every finite level. -/
theorem exists_lift (m n : ℕ) :
    ∃ s : (unitSheaf (base K)).obj.obj (op (coverObject K ℓ)),
      (power (base K) (ℓ ^ n)).hom.app (op (coverObject K ℓ)) s =
        (unitMap K m).hom.app (op (coverObject K ℓ))
          ((integerSheaf (J (base K))).obj.map (coverArrow K ℓ).op
            (generator (J (base K)) (terminalIsTerminal K))) := by
  let X := base K
  let A := CommRingCat.of (LaurentPolynomial K)
  let B := CommRingCat.of (Tower K ℓ)
  let f := CommRingCat.ofHom (laurentMap K ℓ)
  letI : WeaklyEtale (coverMap K ℓ) := LaurentKummerTowerCover.cover_weaklyEtale K ℓ
  letI : WeaklyEtale (Spec.map f ≫ 𝟙 X) := inferInstance
  let e := specUnits B (coverMap K ℓ)
  let u := (root_isUnit K ℓ n).unit
  let z := Sheaf.H.equiv₀ (unitSheaf X) (terminalIsTerminal K) (exponentUnit K (m : ℤ))
  have hn : e ((unitSheaf X).obj.map (coverArrow K ℓ).op z) =
      Additive.ofMul (Units.map f.hom.toMonoidHom (unitsHZeroEquiv (LaurentPolynomial K)
        (exponentUnit K (m : ℤ))).toMul) :=
    specUnits_naturality f (𝟙 X) z
  refine ⟨e.symm (Additive.ofMul (u ^ m)), e.injective ?_⟩
  rw [power_eval, map_nsmul, e.apply_symm_apply, unitMap_cover, hn, coordinate_unit]
  apply Additive.ext
  apply Units.ext
  change (↑((u ^ m) ^ (ℓ ^ n)) : Tower K ℓ) =
    laurentMap K ℓ ((LaurentUnitProductCoordinates.unitCoordinates K (0, (m : ℤ))).toMul : LaurentPolynomial K)
  simp only [Units.val_pow_eq_pow_val]
  have hu : (u : Tower K ℓ) ^ (ℓ ^ n) = laurentMap K ℓ (LaurentPolynomial.T 1) := by
    rw [show (u : Tower K ℓ) = LaurentKummerTowerAlgebra.root K ℓ n from (root_isUnit K ℓ n).unit_spec]
    exact root_power K ℓ n
  rw [LaurentUnitProductCoordinates.unitCoordinates_apply]
  change ((u : Tower K ℓ) ^ m) ^ (ℓ ^ n) =
    laurentMap K ℓ (LaurentPolynomial.C 1 * LaurentPolynomial.T (m : ℤ))
  rw [map_one, one_mul]
  have hm : (LaurentPolynomial.T 1 : LaurentPolynomial K) ^ m = LaurentPolynomial.T (m : ℤ) := by simp
  rw [← hm, map_pow, ← hu, ← pow_mul, ← pow_mul, Nat.mul_comm m]

end
end ManuscriptAudit.LaurentKummerGeneratorLifts

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.LaurentKummerGeneratorLifts.exists_lift
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
