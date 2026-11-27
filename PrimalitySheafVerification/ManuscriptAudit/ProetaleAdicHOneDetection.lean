import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import PrimalitySheafVerification.ManuscriptAudit.CyclicPowerInverseLimit
import PrimalitySheafVerification.ManuscriptAudit.ExtOneProduct
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicProductHOne

/-! Native degree-one adic classes are detected by their actual coherent
finite pro-étale reductions. -/

namespace ManuscriptAudit.ProetaleAdicHOneDetection

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CyclicPowerInverseLimit (compatibleTuples)
open ProetaleAdicNativeExactSequence (sequence)
open ProetaleCoefficientUniverseLift (lift)
open ProetaleResidueSheaves (residueSheaf residueReduction residueTransition residueReduction_comp)
open ProetaleAdicProductKernel (inclusion inclusion_π product)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{0}) (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev Q := sequence X ℓ

/-- Actual finite residue coefficient sheaves in the native cohomology universe. -/
abbrev finiteCoefficient (n : ℕ) := (lift X).obj (residueSheaf X ℓ n)

private abbrev reduction (n : ℕ) : (Q X ℓ).X₁ ⟶ finiteCoefficient X ℓ n :=
  (lift X).map (residueReduction X ℓ n)

private abbrev transition (n : ℕ) : finiteCoefficient X ℓ (n + 1) ⟶ finiteCoefficient X ℓ n :=
  (lift X).map (residueTransition X ℓ n)

/-- Compatible tuples of actual degree-one pro-étale finite-residue classes. -/
abbrev compatibleHOne :=
  compatibleTuples (fun n ↦ Sheaf.H (finiteCoefficient X ℓ n) 1)
    (fun n ↦ Sheaf.H.map (transition X ℓ n) 1)

/-- The native adic degree-one group maps additively to its coherent finite reductions. -/
def reductionMap : X.EllAdicCohomology ℓ 1 →+ compatibleHOne X ℓ where
  toFun x := ⟨fun n ↦ Sheaf.H.map (reduction X ℓ n) 1 x, fun n ↦ by
    change Sheaf.H.map (transition X ℓ n) 1 (Sheaf.H.map (reduction X ℓ (n + 1)) 1 x) =
      Sheaf.H.map (reduction X ℓ n) 1 x
    rw [← Sheaf.H.map_comp_apply]
    change Sheaf.H.map ((lift X).map (residueReduction X ℓ (n + 1)) ≫
      (lift X).map (residueTransition X ℓ n)) 1 x = _
    rw [← (lift X).map_comp, residueReduction_comp]
    rfl⟩
  map_zero' := by
    apply Subtype.ext
    funext n
    exact map_zero (Sheaf.H.map (reduction X ℓ n) 1)
  map_add' x y := by
    apply Subtype.ext
    funext n
    exact map_add (Sheaf.H.map (reduction X ℓ n) 1) x y

private def productIso : (Q X ℓ).X₂ ≅ ∏ᶜ (finiteCoefficient X ℓ) :=
  PreservesProduct.iso (lift X) (residueSheaf X ℓ)

private abbrev projection (n : ℕ) : (Q X ℓ).X₂ ⟶ finiteCoefficient X ℓ n :=
  (lift X).map (Pi.π (residueSheaf X ℓ) n)

private theorem productIso_hom_π (n : ℕ) :
    (productIso X ℓ).hom ≫ Pi.π (finiteCoefficient X ℓ) n = projection X ℓ n := by
  unfold productIso
  rw [PreservesProduct.iso_hom, piComparison_comp_π]

private theorem inclusion_comp_projection (n : ℕ) :
    (Q X ℓ).f ≫ projection X ℓ n = reduction X ℓ n := by
  change (lift X).map (inclusion X ℓ) ≫ (lift X).map (Pi.π (residueSheaf X ℓ) n) =
    (lift X).map (residueReduction X ℓ n)
  rw [← (lift X).map_comp, inclusion_π]

private abbrev integers :=
  (constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{1}).obj
    (AddCommGrpCat.of (ULift.{1} ℤ))

private theorem productCohomology_injective :
    Function.Injective
      (fun x : Sheaf.H (Q X ℓ).X₂ 1 ↦ fun n ↦ Sheaf.H.map (projection X ℓ n) 1 x) := by
  let e := productIso X ℓ
  have hE : Function.LeftInverse (Sheaf.H.map e.inv 1) (Sheaf.H.map e.hom 1) := by
    intro z
    rw [← Sheaf.H.map_comp_apply, e.hom_inv_id, Sheaf.H.map_id_apply]
  intro x y h
  apply hE.injective
  apply ExtOneProduct.projectionMap_injective (finiteCoefficient X ℓ) (integers X)
  funext n
  change Sheaf.H.map (Pi.π (finiteCoefficient X ℓ) n) 1 (Sheaf.H.map e.hom 1 x) =
    Sheaf.H.map (Pi.π (finiteCoefficient X ℓ) n) 1 (Sheaf.H.map e.hom 1 y)
  simp only [← Sheaf.H.map_comp_apply, e, productIso_hom_π]
  exact congrFun h n

/-- Every native degree-one pro-étale adic class is determined by its
coherent pro-étale finite-residue classes. -/
theorem reductionMap_injective : Function.Injective (reductionMap X ℓ) := by
  intro x y h
  apply ProetaleAdicProductHOne.HOne_inclusion_injective X ℓ
  apply productCohomology_injective X ℓ
  funext n
  change Sheaf.H.map (projection X ℓ n) 1 (Sheaf.H.map (Q X ℓ).f 1 x) =
    Sheaf.H.map (projection X ℓ n) 1 (Sheaf.H.map (Q X ℓ).f 1 y)
  simp only [← Sheaf.H.map_comp_apply, inclusion_comp_projection]
  exact congrArg (fun z : compatibleHOne X ℓ ↦ z.val n) h

private theorem difference_comp_projection (n : ℕ) :
    (Q X ℓ).g ≫ projection X ℓ n =
      projection X ℓ n - projection X ℓ (n + 1) ≫ transition X ℓ n := by
  change (lift X).map (ProetaleAdicProductKernel.difference X ℓ) ≫
      (lift X).map (Pi.π (residueSheaf X ℓ) n) =
    (lift X).map (Pi.π (residueSheaf X ℓ) n) -
      (lift X).map (Pi.π (residueSheaf X ℓ) (n + 1)) ≫ (lift X).map (residueTransition X ℓ n)
  rw [← (lift X).map_comp, ProetaleAdicProductKernel.difference_π,
    (lift X).map_sub, (lift X).map_comp]

set_option maxHeartbeats 1600000 in
/-- A coherent family represented by one native product-coefficient class
already comes from actual integral degree one. -/
theorem exists_lift_of_product_class (x : compatibleHOne X ℓ) (z : Sheaf.H (Q X ℓ).X₂ 1)
    (hz : ∀ n, Sheaf.H.map (projection X ℓ n) 1 z = x.val n) :
    ∃ a, reductionMap X ℓ a = x := by
  have hd : Sheaf.H.map (Q X ℓ).g 1 z = 0 := by
    apply productCohomology_injective X ℓ
    funext n
    change Sheaf.H.map (projection X ℓ n) 1 (Sheaf.H.map (Q X ℓ).g 1 z) =
      Sheaf.H.map (projection X ℓ n) 1 0
    rw [map_zero]
    refine (Sheaf.H.map_comp_apply (Q X ℓ).g (projection X ℓ n) z).symm.trans ?_
    rw [difference_comp_projection]
    let t := projection X ℓ (n + 1) ≫ transition X ℓ n
    let P := Sheaf.functorH (Scheme.ProEt.topology X) 1
    have he := ConcreteCategory.congr_hom (P.map_sub (projection X ℓ n) t) z
    change Sheaf.H.map (projection X ℓ n - t) 1 z =
      Sheaf.H.map (projection X ℓ n) 1 z - Sheaf.H.map t 1 z at he
    rw [he]
    change Sheaf.H.map (projection X ℓ n) 1 z -
      Sheaf.H.map (projection X ℓ (n + 1) ≫ transition X ℓ n) 1 z = 0
    rw [Sheaf.H.map_comp_apply (projection X ℓ (n + 1)) (transition X ℓ n) z, hz, hz, x.property n, sub_self]
  obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₂ (integers X)
    (ProetaleAdicNativeExactSequence.shortExact X ℓ) z hd
  refine ⟨a, Subtype.ext ?_⟩
  funext n
  change Sheaf.H.map (reduction X ℓ n) 1 a = x.val n
  change Sheaf.H.map (Q X ℓ).f 1 a = z at ha
  calc
    _ = Sheaf.H.map ((Q X ℓ).f ≫ projection X ℓ n) 1 a :=
      congrArg (fun g ↦ Sheaf.H.map g 1 a) (inclusion_comp_projection X ℓ n).symm
    _ = Sheaf.H.map (projection X ℓ n) 1 (Sheaf.H.map (Q X ℓ).f 1 a) :=
      Sheaf.H.map_comp_apply (Q X ℓ).f (projection X ℓ n) a
    _ = _ := by rw [ha, hz]

/-- The same criterion uses the actual product of the finite residue sheaves. -/
theorem exists_lift_of_actual_product_class (x : compatibleHOne X ℓ)
    (z : Sheaf.H (∏ᶜ (finiteCoefficient X ℓ)) 1)
    (hz : ∀ n, Sheaf.H.map (Pi.π (finiteCoefficient X ℓ) n) 1 z = x.val n) :
    ∃ a, reductionMap X ℓ a = x := by
  let e := productIso X ℓ
  apply exists_lift_of_product_class X ℓ x (Sheaf.H.map e.inv 1 z)
  intro n
  have h : e.inv ≫ projection X ℓ n = Pi.π (finiteCoefficient X ℓ) n := by
    rw [← productIso_hom_π, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  calc
    _ = Sheaf.H.map (e.inv ≫ projection X ℓ n) 1 z :=
      (Sheaf.H.map_comp_apply e.inv (projection X ℓ n) z).symm
    _ = Sheaf.H.map (Pi.π (finiteCoefficient X ℓ) n) 1 z := congrArg (fun g ↦ Sheaf.H.map g 1 z) h
    _ = _ := hz n

end
end ManuscriptAudit.ProetaleAdicHOneDetection

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAdicHOneDetection.reductionMap,
      ``ManuscriptAudit.ProetaleAdicHOneDetection.reductionMap_injective,
      ``ManuscriptAudit.ProetaleAdicHOneDetection.exists_lift_of_actual_product_class] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
