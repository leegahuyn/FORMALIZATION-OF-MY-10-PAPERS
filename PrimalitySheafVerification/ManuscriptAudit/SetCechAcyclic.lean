import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.Opposite
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.CategoryTheory.Abelian.Opposite
import Mathlib.CategoryTheory.Limits.Types.Limits

/-! Positive Čech acyclicity of a surjective map of sets for contravariant coefficients. -/

namespace ManuscriptAudit.SetCechAcyclic

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe u v w

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {A : Type v} [Category.{w} A] [Abelian A]
variable {U T : Type u} (f : U ⟶ T) (P : (Type u)ᵒᵖ ⥤ A)

/-- The actual alternating Čech cochain complex of a map of sets. -/
def cochains : CochainComplex A ℕ :=
  (alternatingCofaceMapComplex A).obj ((Arrow.mk f).cechNerve.rightOp ⋙ P)

private def split (hf : Function.Surjective f) : SplitEpi f where
  section_ := TypeCat.ofHom (fun t ↦ (hf t).choose)
  id := by
    apply ConcreteCategory.hom_ext
    intro t
    exact (hf t).choose_spec

private def mappedAugmented : SimplicialObject.Augmented Aᵒᵖ :=
  ((SimplicialObject.Augmented.whiskering _ _).obj P.rightOp).obj
    (Arrow.mk f).augmentedCechNerve

private abbrev chains : ChainComplex Aᵒᵖ ℕ :=
  AlternatingFaceMapComplex.obj (SimplicialObject.Augmented.drop.obj (mappedAugmented f P))

private def cochainsIsoUnop : cochains f P ≅ (chains f P).unop :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    let X := (Arrow.mk f).cechNerve.rightOp ⋙ P
    let Y := SimplicialObject.Augmented.drop.obj (mappedAugmented f P)
    have h₁ : (cochains f P).d i (i + 1) = AlternatingCofaceMapComplex.objD X i :=
      CochainComplex.of_d _ _ i
    have h₂ : (chains f P).d (i + 1) i = AlternatingFaceMapComplex.objD Y i :=
      ChainComplex.of_d _ _ i
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id, HomologicalComplex.unop_d, h₁, h₂]
    exact (AlternatingCofaceMapComplex.d_eq_unop_d X i).symm)

/-- A surjective set map is split, so its augmented Čech nerve has an
extra degeneracy. Thus all positive Čech cohomology vanishes. -/
theorem H_succ_isZero (hf : Function.Surjective f) (n : ℕ) :
    IsZero ((cochains f P).homology (n + 1)) := by
  let ed : SimplicialObject.Augmented.ExtraDegeneracy (mappedAugmented f P) :=
    (Arrow.AugmentedCechNerve.extraDegeneracy (Arrow.mk f) (split f hf)).map P.rightOp
  let e := ed.homotopyEquiv
  let eH := e.toHomologyIso (n + 1)
  let T₀ := SimplicialObject.Augmented.point.obj (mappedAugmented f P)
  have hz : IsZero (((ChainComplex.single₀ Aᵒᵖ).obj T₀).homology (n + 1)) :=
    HomologicalComplex.isZero_single_obj_homology (.down ℕ) 0 T₀ (n + 1) (Nat.succ_ne_zero n)
  have h := hz.of_iso eH
  let e₀ := (HomologicalComplex.homologyFunctor A (.up ℕ) (n + 1)).mapIso (cochainsIsoUnop f P)
  exact h.unop.of_iso (e₀ ≪≫ (chains f P).homologyUnop (n + 1))

end

end ManuscriptAudit.SetCechAcyclic

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SetCechAcyclic.H_succ_isZero
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
