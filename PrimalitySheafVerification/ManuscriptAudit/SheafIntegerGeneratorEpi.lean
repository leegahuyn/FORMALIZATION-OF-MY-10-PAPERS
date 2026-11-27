import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.SheafOfTypes

/-! A sheaf map to the constant integers is epi if the distinguished
integer generator has a section lift on one covering object. -/

namespace ManuscriptAudit.SheafIntegerGeneratorEpi

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J AddCommGrpCat.{w}]

private abbrev G := AddCommGrpCat.{w}
private abbrev Z := AddCommGrpCat.of (ULift.{w} ℤ)

/-- The genuine constant integer sheaf. -/
abbrev integerSheaf := (constantSheaf J G).obj Z

variable {T : C} (hT : IsTerminal T)

/-- The section corresponding to the additive integer generator. -/
def generator : (integerSheaf J).obj.obj (op T) :=
  (((constantSheafAdj J G hT).homEquiv Z (integerSheaf J)) (𝟙 _)) ⟨1⟩

set_option maxHeartbeats 1000000 in
/-- Separation on the covering sieve detects any two maps out of the
constant integers by their values on the locally liftable generator. -/
theorem epi_of_local_generator {U : C} (f : U ⟶ T)
    (hCover : Sieve.ofArrows (fun _ : Unit ↦ U) (fun _ : Unit ↦ f) ∈ J T)
    {P : Sheaf J G} (p : P ⟶ integerSheaf J)
    (hLift : ∃ s : P.obj.obj (op U),
      p.hom.app (op U) s = (integerSheaf J).obj.map f.op (generator J hT)) :
    Epi p := by
  obtain ⟨s, hs⟩ := hLift
  constructor
  intro F g h he
  let E := constantSheafAdj J G hT
  have hEval : g.hom.app (op T) (generator J hT) = h.hom.app (op T) (generator J hT) := by
    let R := Presieve.ofArrows (fun _ : Unit ↦ U) (fun _ : Unit ↦ f)
    let B := forget G
    have hF : Presieve.IsSheaf J (F.obj ⋙ B) :=
      (isSheaf_iff_isSheaf_of_type J _).mp ((sheafCompose J B).obj F).property
    apply (hF.isSheafFor R hCover).isSeparatedFor.ext
    rintro _ _ ⟨i⟩
    change F.obj.map f.op (g.hom.app (op T) (generator J hT)) =
      F.obj.map f.op (h.hom.app (op T) (generator J hT))
    have he' := congrArg (fun q : P ⟶ F ↦ q.hom.app (op U) s) he
    calc
      _ = g.hom.app (op U) ((integerSheaf J).obj.map f.op (generator J hT)) :=
        (NatTrans.naturality_apply g.hom f.op (generator J hT)).symm
      _ = g.hom.app (op U) (p.hom.app (op U) s) := congrArg (g.hom.app (op U)) hs.symm
      _ = h.hom.app (op U) (p.hom.app (op U) s) := he'
      _ = h.hom.app (op U) ((integerSheaf J).obj.map f.op (generator J hT)) :=
        congrArg (h.hom.app (op U)) hs
      _ = _ := NatTrans.naturality_apply h.hom f.op (generator J hT)
  apply (E.homEquiv Z F).injective
  have hg : (E.homEquiv Z F) g =
      (E.homEquiv Z (integerSheaf J) (𝟙 _)) ≫ g.hom.app (op T) := by
    simpa only [Category.id_comp] using E.homEquiv_naturality_right (𝟙 (integerSheaf J)) g
  have hh : (E.homEquiv Z F) h =
      (E.homEquiv Z (integerSheaf J) (𝟙 _)) ≫ h.hom.app (op T) := by
    simpa only [Category.id_comp] using E.homEquiv_naturality_right (𝟙 (integerSheaf J)) h
  have hOne : (E.homEquiv Z F) g ⟨1⟩ = (E.homEquiv Z F) h ⟨1⟩ := by
    rw [hg, hh]
    exact hEval
  apply AddCommGrpCat.ext
  intro z
  have hz : z = z.down • (⟨1⟩ : Z) := by
    apply ULift.ext
    change z.down = z.down • (1 : ℤ)
    rw [zsmul_eq_mul, mul_one]
  rw [hz]
  simp only [map_zsmul, hOne]

end
end ManuscriptAudit.SheafIntegerGeneratorEpi

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SheafIntegerGeneratorEpi.epi_of_local_generator
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
