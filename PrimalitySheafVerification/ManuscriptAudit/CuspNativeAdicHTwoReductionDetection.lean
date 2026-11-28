import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleCountableProductEpi
import PrimalitySheafVerification.ManuscriptAudit.ExtTwoCountableProductDetection
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicHTwoProductKernel
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicReductionAllDegrees

/-! Actual finite residue levels detect proper-cusp integral adic degree-two classes. -/

namespace ManuscriptAudit.CuspNativeAdicHTwoReductionDetection

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open ProetaleAdicNativeExactSequence (sequence)
open ProetaleAdicHOneDetection (finiteCoefficient)
open ProetaleCoefficientUniverseLift (lift)
open ProetaleResidueSheaves (residueSheaf residueReduction)
open ProetaleAdicProductKernel (inclusion inclusion_π)
open ProetaleAdicReductionAllDegrees (reductionMap nativeCompatible)
open ProetaleAdicHTwoProductKernel (properCuspSecondEquiv secondEquiv_val)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}
private abbrev C (X : Scheme.{0}) := Sheaf (Scheme.ProEt.topology X) A

private abbrev integers (X : Scheme.{0}) :=
  (constantSheaf (Scheme.ProEt.topology X) A).obj (AddCommGrpCat.of (ULift.{1} ℤ))

private theorem product_degree_two_injective (X : Scheme.{0}) (ℓ : ℕ) [Fact ℓ.Prime] :
    Function.Injective
      (fun a : Sheaf.H (sequence X ℓ).X₂ 2 =>
        fun n => Sheaf.H.map ((lift X).map (Pi.π (residueSheaf X ℓ) n)) 2 a) := by
  letI : EssentiallySmall.{1} X.ProEt := inferInstance
  letI := Sheaf.isGrothendieckAbelian_of_essentiallySmall (Scheme.ProEt.topology X) A
  let E : (sequence X ℓ).X₂ ≅ ∏ᶜ (finiteCoefficient X ℓ) :=
    PreservesProduct.iso (lift X) (residueSheaf X ℓ)
  have hE : Function.LeftInverse (Sheaf.H.map E.inv 2) (Sheaf.H.map E.hom 2) := by
    intro a
    rw [← Sheaf.H.map_comp_apply, E.hom_inv_id, Sheaf.H.map_id_apply]
  have hπ := ExtTwoCountableProductDetection.projections_jointly_injective
    (C := C X) (fun _ _ f hf => ProetaleCountableProductEpi.product_epi f hf)
    (finiteCoefficient X ℓ) (integers X)
  intro a b h
  apply hE.injective
  apply hπ
  funext n
  change Sheaf.H.map (Pi.π (finiteCoefficient X ℓ) n) 2 (Sheaf.H.map E.hom 2 a) =
    Sheaf.H.map (Pi.π (finiteCoefficient X ℓ) n) 2 (Sheaf.H.map E.hom 2 b)
  simp only [← Sheaf.H.map_comp_apply, E, PreservesProduct.iso_hom, piComparison_comp_π]
  exact congrFun h n

private abbrev X (K : Type) [Field K] := CuspProperCompactification.projectiveCusp K

theorem reduction_injective (K : Type) [Field K] [IsAlgClosed K]
    (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)] :
    Function.Injective (reductionMap (X K) ℓ 2) := by
  intro a b hab
  apply (properCuspSecondEquiv K ℓ).injective
  apply Subtype.ext
  change Sheaf.H.map (sequence (X K) ℓ).f 2 a =
    Sheaf.H.map (sequence (X K) ℓ).f 2 b
  apply product_degree_two_injective
  funext n
  have hn : (sequence (X K) ℓ).f ≫ (lift (X K)).map (Pi.π (residueSheaf (X K) ℓ) n) =
      (lift (X K)).map (residueReduction (X K) ℓ n) := by
    change (lift (X K)).map (inclusion (X K) ℓ) ≫
       (lift (X K)).map (Pi.π (residueSheaf (X K) ℓ) n) = _
    rw [← (lift (X K)).map_comp, inclusion_π]
  let A := (sequence (X K) ℓ).X₁
  let P := (sequence (X K) ℓ).X₂
  let F := finiteCoefficient (X K) ℓ n
  let f : A ⟶ P := (sequence (X K) ℓ).f
  let π : P ⟶ F := (lift (X K)).map (Pi.π (residueSheaf (X K) ℓ) n)
  let r : A ⟶ F := (lift (X K)).map (residueReduction (X K) ℓ n)
  have hEq : f ≫ π = r := hn
  let a' : Sheaf.H A 2 := a
  let b' : Sheaf.H A 2 := b
  have hcomp (z : Sheaf.H A 2) :
      Sheaf.H.map π 2 (Sheaf.H.map f 2 z) = Sheaf.H.map r 2 z := by
    rw [← Sheaf.H.map_comp_apply, hEq]
  change Sheaf.H.map π 2 (Sheaf.H.map f 2 a') =
    Sheaf.H.map π 2 (Sheaf.H.map f 2 b')
  exact (hcomp a').trans
    ((congrArg (fun z : nativeCompatible (X K) ℓ 2 => z.val n) hab).trans (hcomp b').symm)

end
end ManuscriptAudit.CuspNativeAdicHTwoReductionDetection

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CuspNativeAdicHTwoReductionDetection.reduction_injective
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
