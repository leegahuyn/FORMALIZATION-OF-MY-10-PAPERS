import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import PrimalitySheafVerification.ManuscriptAudit.ExtOneSimultaneousPullback
import PrimalitySheafVerification.ManuscriptAudit.SheafIntegerGeneratorEpi

/-! Simultaneous local lifting of the generator on one covering object
makes the genuine simultaneous extension projection epi. -/

namespace ManuscriptAudit.SheafSimultaneousExtensionEpi

open CategoryTheory CategoryTheory.Limits Opposite
open ExtOneSimultaneousPullback (projection)
open SheafIntegerGeneratorEpi (integerSheaf generator epi_of_local_generator)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J AddCommGrpCat.{w}]

private abbrev G := AddCommGrpCat.{w}
private abbrev Z := AddCommGrpCat.of (ULift.{w} ℤ)

private def fromInteger {A : G} (a : A) : Z ⟶ A :=
  AddCommGrpCat.ofHom
    { toFun := fun z ↦ z.down • a
      map_zero' := zero_zsmul _
      map_add' x y := add_zsmul _ _ _ }

private theorem fromInteger_comp {A B : G} (a : A) (q : A ⟶ B) :
    fromInteger a ≫ q = fromInteger (q a) := by
  apply AddCommGrpCat.ext
  intro z
  exact map_zsmul q.hom a z.down

variable {T U : C} (hT : IsTerminal T) (f : U ⟶ T)
variable (S : ℕ → ShortComplex (Sheaf J G))
variable (a : ∀ n, integerSheaf J ⟶ (S n).X₃)

set_option maxHeartbeats 2000000 in
/-- Every power or extension lifting the same generator on one cover is
enough to make the actual pullback of their product locally split. -/
theorem projection_epi
    (hCover : Sieve.ofArrows (fun _ : Unit ↦ U) (fun _ : Unit ↦ f) ∈ J T)
    (hLift : ∀ n, ∃ s : (S n).X₂.obj.obj (op U), (S n).g.hom.app (op U) s =
      (a n).hom.app (op U) ((integerSheaf J).obj.map f.op (generator J hT))) :
    Epi (projection S a) := by
  apply epi_of_local_generator J hT f hCover
  choose b hb using hLift
  let E := sheafToPresheaf J G ⋙ (evaluation Cᵒᵖ G).obj (op U)
  let X₂ (n : ℕ) := (S n).X₂
  let X₃ (n : ℕ) := (S n).X₃
  let v := fromInteger ((integerSheaf J).obj.map f.op (generator J hT))
  let e₂ := PreservesProduct.iso E X₂
  let e₃ := PreservesProduct.iso E X₃
  let q := (Pi.lift (fun n ↦ fromInteger (b n))) ≫ e₂.inv
  let d := Pi.lift a
  let p := Pi.map (fun n ↦ (S n).g)
  have hq (n : ℕ) : q ≫ E.map (Pi.π X₂ n) = fromInteger (b n) := by
    change (Pi.lift (fun n ↦ fromInteger (b n))) ≫ e₂.inv ≫ E.map (Pi.π X₂ n) = _
    rw [show e₂.inv ≫ E.map (Pi.π X₂ n) = Pi.π (fun i ↦ E.obj (X₂ i)) n from
      inv_piComparison_comp_map_π E X₂ n, Pi.lift_π]
  have hd (n : ℕ) : E.map d ≫ E.map (Pi.π X₃ n) = E.map (a n) := by
    rw [← E.map_comp, Pi.lift_π]
  have hp (n : ℕ) : E.map p ≫ E.map (Pi.π X₃ n) = E.map (Pi.π X₂ n) ≫ E.map (S n).g := by
    rw [← E.map_comp, Pi.map_π, E.map_comp]
  have hc : v ≫ E.map d = q ≫ E.map p := by
    apply (cancel_mono e₃.hom).mp
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, e₃, PreservesProduct.iso_hom, piComparison_comp_π, hd, hp]
    rw [← Category.assoc q, hq, fromInteger_comp, fromInteger_comp]
    exact congrArg fromInteger (hb n).symm
  let H := PreservesPullback.iso E d p
  let L := pullback.lift v q hc ≫ H.inv
  have hL : L ≫ E.map (projection S a) = v := by
    change pullback.lift v q hc ≫ H.inv ≫ E.map (pullback.fst d p) = v
    rw [PreservesPullback.iso_inv_fst, pullback.lift_fst]
  refine ⟨L ⟨1⟩, ?_⟩
  have he := ConcreteCategory.congr_hom hL (⟨1⟩ : Z)
  change (projection S a).hom.app (op U) (L ⟨1⟩) =
    (1 : ℤ) • ((integerSheaf J).obj.map f.op (generator J hT)) at he
  simpa only [one_zsmul] using he

end
end ManuscriptAudit.SheafSimultaneousExtensionEpi

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SheafSimultaneousExtensionEpi.projection_epi
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
