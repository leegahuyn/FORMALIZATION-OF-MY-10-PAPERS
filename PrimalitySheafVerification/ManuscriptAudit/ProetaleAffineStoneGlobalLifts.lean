import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineSingletonLift
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineStoneCech
import PrimalitySheafVerification.ManuscriptAudit.ProetaleContinuousDirectImageMaps
import PrimalitySheafVerification.ManuscriptAudit.SheafExplicitCechHOne

/-! The quotient of the actual native adic coefficient sheaf in any
monomorphism has section lifts on every affine object over the field. -/

namespace ManuscriptAudit.ProetaleAffineStoneGlobalLifts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleCechPullbackGeometry (D E l r d₀₁ d₀₂ d₁₂ d₀₂_l d₀₂_r d₀₂_l_assoc)
open ProetaleContinuousDirectImageMaps (functions)
open SingletonCoverRefinement (Covers)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] [IsAlgClosed K]
variable (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev Z := Spec (CommRingCat.of K)
private abbrev G := AddCommGrpCat.{1}
private abbrev J := Scheme.ProEt.topology (Z (K := K))
private abbrev C := Sheaf (J (K := K)) G
private abbrev F := functions ℤ_[ℓ] (Z (K := K))

variable {I : C (K := K)} (m : F (K := K) ℓ ⟶ I) [Mono m]
variable {T V : (Z (K := K)).ProEt} (f : V ⟶ T)
  [IsAffine T.left] [IsAffine V.left] [WeaklyEtale f.left]

private theorem pair_structure :
    l f.left ≫ V.hom = r f.left ≫ V.hom := by
  rw [← f.w, ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ T.hom) (pullback.condition (f := f.left) (g := f.left))

private theorem triple_structure :
    d₁₂ f.left ≫ (l f.left ≫ V.hom) =
      d₀₁ f.left ≫ (l f.left ≫ V.hom) := by
  calc
    _ = (d₁₂ f.left ≫ l f.left) ≫ V.hom := (Category.assoc _ _ _).symm
    _ = (d₀₁ f.left ≫ r f.left) ≫ V.hom :=
      congrArg (· ≫ V.hom) (pullback.condition (f := r f.left) (g := l f.left)).symm
    _ = d₀₁ f.left ≫ (r f.left ≫ V.hom) := Category.assoc _ _ _
    _ = _ := congrArg (d₀₁ f.left ≫ ·) (pair_structure f).symm

set_option maxHeartbeats 3400000 in
private theorem from_singleton (hf : Covers (J (K := K)) f) (hs : Surjective f.left)
    (x : (cokernel m).obj.obj (op T)) (y : I.obj.obj (op V))
    (hy : (cokernel.π m).hom.app (op V) y = (cokernel m).obj.map f.op x) :
    ∃ z : I.obj.obj (op T), (cokernel.π m).hom.app (op T) z = x := by
  let p := f.left
  let P : (Z (K := K)).ProEt := Scheme.ProEt.mk (l p ≫ V.hom)
  let e₀ : P ⟶ V := MorphismProperty.Over.homMk (l p) rfl
  let e₁ : P ⟶ V := MorphismProperty.Over.homMk (r p) (pair_structure f).symm
  let Q : (Z (K := K)).ProEt := Scheme.ProEt.mk (d₀₁ p ≫ (l p ≫ V.hom))
  let e₀₁ : Q ⟶ P := MorphismProperty.Over.homMk (d₀₁ p) rfl
  let e₀₂ : Q ⟶ P := MorphismProperty.Over.homMk (d₀₂ p) (d₀₂_l_assoc p V.hom)
  let e₁₂ : Q ⟶ P := MorphismProperty.Over.homMk (d₁₂ p) (triple_structure f)
  have hP : IsPullback e₀ e₁ f f :=
    ProetaleAffineTensor.underlying_isPullback (IsPullback.of_hasPullback p p)
  have h₀ : e₀₂ ≫ e₀ = e₀₁ ≫ e₀ := MorphismProperty.Over.Hom.ext (d₀₂_l p)
  have h₁ : e₁₂ ≫ e₀ = e₀₁ ≫ e₁ :=
    MorphismProperty.Over.Hom.ext (pullback.condition (f := r p) (g := l p)).symm
  have h₂ : e₁₂ ≫ e₁ = e₀₂ ≫ e₁ := MorphismProperty.Over.Hom.ext (d₀₂_r p).symm
  obtain ⟨b, hb, hC⟩ := SheafExplicitCechHOne.exists_cocycle m f e₀ e₁ hP e₀₁ e₀₂ e₁₂
    h₀ h₁ h₂ x y hy
  let b' : C(↥(D p), ℤ_[ℓ]) := b.down
  have hc (z : ↥(E p)) : b' (d₁₂ p z) - b' (d₀₂ p z) + b' (d₀₁ p z) = 0 :=
    congrArg (fun v : (F (K := K) ℓ).obj.obj (op Q) ↦ (show C(↥(E p), ℤ_[ℓ]) from v.down) z)
      hC
  obtain ⟨a, ha⟩ := ProetaleAffineStoneCech.exists_adic_primitive T.hom p ℓ hs b' hc
  let a' : (F (K := K) ℓ).obj.obj (op V) := ⟨a⟩
  apply SheafExplicitCechHOne.exists_global_lift m f e₀ e₁ hP hf x y hy a'
  rw [← hb]
  apply congrArg (m.hom.app (op P))
  apply ULift.ext
  apply ContinuousMap.ext
  exact ha

/-- Every quotient section on the actual affine pro-étale object lifts. -/
theorem every_affine_lift (T : (Z (K := K)).ProEt) [IsAffine T.left]
    (x : (cokernel m).obj.obj (op T)) :
    ∃ z : I.obj.obj (op T), (cokernel.π m).hom.app (op T) z = x := by
  let q := cokernel.π m
  letI : Sheaf.IsLocallySurjective q := (Sheaf.isLocallySurjective_iff_epi' G q).mpr inferInstance
  obtain ⟨W, g, hA, hE, hs, hg, y, hy⟩ :=
    ProetaleAffineSingletonLift.exists_singleton_cover_lift (T := T) q x
  letI : IsAffine W.left := hA
  letI : WeaklyEtale g.left := hE
  exact from_singleton ℓ m g hg hs x y hy

end
end ManuscriptAudit.ProetaleAffineStoneGlobalLifts

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleAffineStoneGlobalLifts.every_affine_lift
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
