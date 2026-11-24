import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FaithfullyFlatCoalgebra
import PrimalitySheafVerification.ManuscriptAudit.UnitCocycleTensor

/-!
# Affine unit cocycles over a principal ideal domain

A normalized unit on the actual double overlap satisfying the triple
overlap law defines an extension-restriction coalgebra. After faithfully
flat descent, a basis supplies a coboundary over a PID.
-/

namespace ManuscriptAudit.AffineUnitDescent

open CategoryTheory ModuleCat TensorProduct
open ModuleCat.ChangeOfRings
open UnitCocycleTensor

universe u

noncomputable section

variable {R B : Type u} [CommRing R] [CommRing B]

private abbrev scalarComonad (f : R →+* B) : Comonad (ModuleCat.{u} B) :=
  (extendRestrictScalarsAdj f).toComonad

/-- The overlap cocycle gives an actual coalgebra on the rank-one (B)-module. -/
def coalgebraOfUnitCocycle (f : R →+* B)
    (u : letI : Algebra R B := f.toAlgebra; (B ⊗[R] B)ˣ)
    (hε : letI : Algebra R B := f.toAlgebra; diagonal R B (u : B ⊗[R] B) = 1)
    (hδ : letI : Algebra R B := f.toAlgebra;
      pull12 R B (u : B ⊗[R] B) * pull23 R B (u : B ⊗[R] B) =
        pull13 R B (u : B ⊗[R] B)) :
    (scalarComonad f).Coalgebra := by
  letI : Algebra R B := f.toAlgebra
  let C := scalarComonad f
  let N := ModuleCat.of B B
  let T₂ := (C : ModuleCat.{u} B ⥤ ModuleCat.{u} B).obj N
  let T₃ := (C : ModuleCat.{u} B ⥤ ModuleCat.{u} B).obj T₂
  let a : N ⟶ T₂ :=
    ConcreteCategory.ofHom (C := ModuleCat.{u} B) (X := N) (Y := T₂)
      (show N →ₗ[B] T₂ from twistedCoaction R B u)
  let e₂ : ((restrictScalars f).obj T₂) ≃ₗ[R] (B ⊗[R] B) :=
    { Equiv.refl _ with
      map_add' := fun _ _ => rfl
      map_smul' := fun r z => by
        let z' : B ⊗[R] B := z
        change f r • z' = r • z'
        exact IsScalarTower.algebraMap_smul B r z' }
  let L := (restrictScalars f).obj (ModuleCat.of B B)
  letI : IsScalarTower R B L := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e₀ : L ≃ₗ[B] B := LinearEquiv.refl B B
  let e₃ : T₃ ≃ₗ[B] (B ⊗[R] (B ⊗[R] B)) :=
    TensorProduct.AlgebraTensorModule.congr e₀ e₂
  have hCounit (z : B ⊗[R] B) : (C.ε.app N).hom z = diagonal R B z := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hComult (z : B ⊗[R] B) : e₃ ((C.δ.app N).hom z) = pull13 R B z := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
      change e₃ ((extendScalars f).map
        ((extendRestrictScalarsAdj f).unit.app ((restrictScalars f).obj N))
        (x ⊗ₜ[R,f] (show (restrictScalars f).obj N from y))) = _
      rw [ExtendScalars.map_tmul, extendRestrictScalarsAdj_unit_app_apply,
        pull13_tmul] <;> rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hMap (z : B ⊗[R] B) :
      e₃ (((C : ModuleCat.{u} B ⥤ ModuleCat.{u} B).map a).hom z) =
        tensorCoaction R B u z := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
      change e₃ ((extendScalars f).map ((restrictScalars f).map a)
        (x ⊗ₜ[R,f] (show (restrictScalars f).obj N from y))) = _
      rw [ExtendScalars.map_tmul] <;> rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  refine { A := N, a := a, counit := ?_, coassoc := ?_ }
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply]
    change (C.ε.app N).hom (twistedCoaction R B u b) = b
    rw [hCounit]
    exact twistedCoaction_counit R B u hε b
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    apply e₃.injective
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    change e₃ ((C.δ.app N).hom (twistedCoaction R B u b)) =
      e₃ (((C : ModuleCat.{u} B ⥤ ModuleCat.{u} B).map a).hom (twistedCoaction R B u b))
    rw [hComult, hMap]
    exact (twistedCoaction_coassoc R B u hδ b).symm

/-- A faithfully flat unit cocycle over a PID is the ratio of the two
images of an actual unit on the cover. -/
theorem unit_cocycle_is_coboundary [IsDomain R] [IsPrincipalIdealRing R]
    (f : R →+* B) (hf : f.FaithfullyFlat)
    (u : letI : Algebra R B := f.toAlgebra; (B ⊗[R] B)ˣ)
    (hε : letI : Algebra R B := f.toAlgebra; diagonal R B (u : B ⊗[R] B) = 1)
    (hδ : letI : Algebra R B := f.toAlgebra;
      pull12 R B (u : B ⊗[R] B) * pull23 R B (u : B ⊗[R] B) =
        pull13 R B (u : B ⊗[R] B)) :
    letI : Algebra R B := f.toAlgebra
    ∃ v : Bˣ, u =
      (Units.map (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B).toMonoidHom v)⁻¹ *
      Units.map (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B).toMonoidHom v := by
  letI : Algebra R B := f.toAlgebra
  let A := coalgebraOfUnitCocycle f u hε hδ
  obtain ⟨iso⟩ := FaithfullyFlatCoalgebra.rank_one_coalgebra_is_standard f hf A (Iso.refl _)
  let aIso := ((scalarComonad f).forget.mapIso iso).toLinearEquiv
  let e : B ≃ₗ[B] B :=
    (TensorProduct.AlgebraTensorModule.rid R B B).symm.trans aIso
  have e_eval (x : B) : e x = x * e 1 := by
    calc
      e x = e (x • (1 : B)) := by simp only [smul_eq_mul, mul_one]
      _ = x * e 1 := by rw [map_smul, smul_eq_mul]
  have hInv : e.symm 1 * e 1 = 1 := by
    rw [← e_eval, e.apply_symm_apply]
  let v : Bˣ := ⟨e 1, e.symm 1, (mul_comm _ _).trans hInv, hInv⟩
  let i₁ := Units.map (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B).toMonoidHom
  let i₂ := Units.map (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B).toMonoidHom
  have compat := ConcreteCategory.congr_hom iso.hom.h
    ((1 : B) ⊗ₜ[R,f] (1 : R))
  change (1 : B) ⊗ₜ[R] (v : B) = twistedCoaction R B u (v : B) at compat
  rw [twistedCoaction_apply] at compat
  have hu : i₁ v * u = i₂ v := Units.ext compat.symm
  refine ⟨v, ?_⟩
  calc
    u = (i₁ v)⁻¹ * (i₁ v * u) := by simp [← mul_assoc]
    _ = (i₁ v)⁻¹ * i₂ v := by rw [hu]

end

end ManuscriptAudit.AffineUnitDescent

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineUnitDescent.coalgebraOfUnitCocycle,
      ``ManuscriptAudit.AffineUnitDescent.unit_cocycle_is_coboundary] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
