import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicHTwoProductCoordinates
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicReductionAllDegrees

/-! Every actual compatible native finite residue class in degree two has
an integral adic lift. The proof uses the literal residue product sequence. -/

namespace ManuscriptAudit.ProetaleAdicHTwoReductionSurjective

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open ProetaleAdicNativeExactSequence (sequence)
open ProetaleAdicHOneDetection (finiteCoefficient)
open ProetaleCoefficientUniverseLift (lift)
open ProetaleResidueSheaves (residueSheaf residueReduction residueTransition)
open ProetaleAdicHTwoProductCoordinates (projection coordinates coordinates_bijective)
open ProetaleAdicReductionAllDegrees (nativeCompatible nativeStep reductionMap)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{0}) (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev Q := sequence X ℓ
private abbrev integers :=
  (constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{1}).obj
    (AddCommGrpCat.of (ULift.{1} ℤ))

private abbrev t (n : ℕ) := (lift X).map (residueTransition X ℓ n)
private abbrev r (n : ℕ) := (lift X).map (residueReduction X ℓ n)

private theorem difference_comp_projection (n : ℕ) :
    (Q X ℓ).g ≫ projection X ℓ n =
      projection X ℓ n - projection X ℓ (n+1) ≫ t X ℓ n := by
  change (lift X).map (ProetaleAdicProductKernel.difference X ℓ) ≫
      (lift X).map (Pi.π (residueSheaf X ℓ) n) = _
  rw [← (lift X).map_comp, ProetaleAdicProductKernel.difference_π,
    (lift X).map_sub, (lift X).map_comp]

private theorem inclusion_comp_projection (n : ℕ) :
    (Q X ℓ).f ≫ projection X ℓ n = r X ℓ n := by
  change (lift X).map (ProetaleAdicProductKernel.inclusion X ℓ) ≫
      (lift X).map (Pi.π (residueSheaf X ℓ) n) = _
  rw [← (lift X).map_comp, ProetaleAdicProductKernel.inclusion_π]

private theorem coordinate_difference (z : Sheaf.H (Q X ℓ).X₂ 2) (n : ℕ) :
    coordinates X ℓ (Sheaf.H.map (Q X ℓ).g 2 z) n =
      coordinates X ℓ z n - nativeStep X ℓ 2 n (coordinates X ℓ z (n+1)) := by
  let p := projection X ℓ n
  let q := projection X ℓ (n+1) ≫ t X ℓ n
  let P := (Q X ℓ).X₂
  let F := finiteCoefficient X ℓ n
  have hm : (Ext.mk₀ (p - q) : Ext.{1} P F 0) = Ext.mk₀ p - Ext.mk₀ q :=
    map_sub (Ext.addEquiv₀ (X := P) (Y := F)).symm p q
  have hd : Sheaf.H.map (p-q) 2 z = Sheaf.H.map p 2 z - Sheaf.H.map q 2 z := by
    change z.comp (Ext.mk₀ (p-q)) (add_zero 2) =
      z.comp (Ext.mk₀ p) (add_zero 2) - z.comp (Ext.mk₀ q) (add_zero 2)
    rw [hm]
    exact map_sub (z.precomp F (add_zero 2)) _ _
  calc
    _ = Sheaf.H.map ((Q X ℓ).g ≫ p) 2 z := (Sheaf.H.map_comp_apply _ _ _).symm
    _ = Sheaf.H.map (p-q) 2 z :=
      congrArg (fun f => Sheaf.H.map f 2 z) (difference_comp_projection X ℓ n)
    _ = Sheaf.H.map p 2 z - Sheaf.H.map q 2 z := hd
    _ = _ := congrArg (fun x => Sheaf.H.map p 2 z - x)
      (Sheaf.H.map_comp_apply (projection X ℓ (n+1)) (t X ℓ n) z)

/-- Surjectivity holds for the actual continuous integral coefficient on every native base. -/
theorem reduction_surjective : Function.Surjective (reductionMap X ℓ 2) := by
  intro x
  obtain ⟨z, hz⟩ := (coordinates_bijective X ℓ).surjective x.val
  have hd : Sheaf.H.map (Q X ℓ).g 2 z = 0 := by
    apply (coordinates_bijective X ℓ).injective
    rw [map_zero]
    funext n
    rw [coordinate_difference, congrFun hz n, congrFun hz (n+1), x.property n]
    exact sub_self _
  obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₂ (integers X)
    (ProetaleAdicNativeExactSequence.shortExact X ℓ) z hd
  refine ⟨a, Subtype.ext (funext fun n => ?_)⟩
  change Sheaf.H.map (r X ℓ n) 2 a = x.val n
  change Sheaf.H.map (Q X ℓ).f 2 a = z at ha
  calc
    _ = Sheaf.H.map ((Q X ℓ).f ≫ projection X ℓ n) 2 a :=
      congrArg (fun g => Sheaf.H.map g 2 a) (inclusion_comp_projection X ℓ n).symm
    _ = coordinates X ℓ (Sheaf.H.map (Q X ℓ).f 2 a) n :=
      Sheaf.H.map_comp_apply (Q X ℓ).f (projection X ℓ n) a
    _ = _ := (congrArg (fun y => coordinates X ℓ y n) ha).trans (congrFun hz n)

end
end ManuscriptAudit.ProetaleAdicHTwoReductionSurjective

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleAdicHTwoReductionSurjective.reduction_surjective
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
